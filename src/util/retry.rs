/*
 copyright: (c) 2013-2020 by Blockstack PBC, a public benefit corporation.

 This file is part of Blockstack.

 Blockstack is free software. You may redistribute or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License or
 (at your option) any later version.

 Blockstack is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY, including without the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with Blockstack. If not, see <http://www.gnu.org/licenses/>.
*/

use std::io;
use std::io::prelude::*;
use std::io::{Read, Write};

use util::hash::to_hex;
use util::log;

/// Wrap a Read so that we store a copy of what was read.
/// Used for re-trying reads when we don't know what to expect from the stream.
pub struct RetryReader<'a, R: Read> {
    fd: &'a mut R,
    buf: Vec<u8>,
    i: usize,
}

impl<'a, R: Read> RetryReader<'a, R> {
    pub fn new(fd: &'a mut R) -> RetryReader<'a, R> {
        RetryReader {
            fd: fd,
            buf: vec![],
            i: 0,
        }
    }

    pub fn set_position(&mut self, offset: usize) -> () {
        if offset <= self.buf.len() {
            self.i = offset
        } else {
            self.i = self.buf.len()
        }
    }

    pub fn position(&self) -> usize {
        self.i
    }

    fn read_and_buffer(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let nr = self.fd.read(buf)?;
        self.buf.extend_from_slice(buf);
        self.i += buf.len();
        Ok(nr)
    }
}

impl<'a, R: Read> Read for RetryReader<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let nr_buf = if self.i < self.buf.len() {
            // consume from inner buffer
            let bytes_copied = (&self.buf[self.i..]).read(buf)?;
            self.i += bytes_copied;
            bytes_copied
        } else {
            0
        };

        let nr = self.read_and_buffer(&mut buf[nr_buf..])?;
        Ok(nr + nr_buf)
    }
}

/// A Read that will only read up to a given number of bytes before EOF'ing.
pub struct BoundReader<'a, R: Read> {
    fd: &'a mut R,
    max_len: u64,
    read_so_far: u64,
}

impl<'a, R: Read> BoundReader<'a, R> {
    pub fn from_reader(reader: &'a mut R, max_len: u64) -> BoundReader<'a, R> {
        BoundReader {
            fd: reader,
            max_len: max_len,
            read_so_far: 0,
        }
    }

    pub fn num_read(&self) -> u64 {
        self.read_so_far
    }
}

impl<'a, R: Read> Read for BoundReader<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let intended_read = self
            .read_so_far
            .checked_add(buf.len() as u64)
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::Other, "Read would overflow u64".to_string())
            })?;
        let max_read = if intended_read > self.max_len {
            self.max_len - self.read_so_far
        } else {
            buf.len() as u64
        };

        let nr = self.fd.read(&mut buf[0..(max_read as usize)])?;
        self.read_so_far += nr as u64;
        Ok(nr)
    }
}

/// A Read that will log everything it reads
pub struct LogReader<'a, R: Read> {
    fd: &'a mut R,
    reads: Vec<Vec<u8>>,
}

impl<'a, R: Read> LogReader<'a, R> {
    pub fn from_reader(fd: &'a mut R) -> LogReader<'a, R> {
        LogReader {
            fd: fd,
            reads: vec![],
        }
    }

    pub fn log(&self) -> &Vec<Vec<u8>> {
        &self.reads
    }
}

impl<'a, R: Read> Read for LogReader<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let nr = self.fd.read(buf)?;
        let read = buf[0..nr].to_vec();
        self.reads.push(read);
        Ok(nr)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_retry_reader() {
        let buf = vec![1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4];
        let mut cursor = io::Cursor::new(&buf);
        let mut retry_reader = RetryReader::new(&mut cursor);

        let mut empty_buf = [];
        let nr = retry_reader.read(&mut empty_buf).unwrap();
        assert_eq!(nr, 0);

        for i in 1..5 {
            let mut read_buf = [0u8; 3];
            retry_reader.read_exact(&mut read_buf).unwrap();
            assert_eq!(read_buf, [i as u8, i as u8, i as u8]);
        }

        let mut tmp_buf = [0u8; 3];
        let e = retry_reader.read_exact(&mut tmp_buf);
        assert!(e.is_err(), "{:?}", &e);
        assert!(
            format!("{:?}", &e.as_ref().unwrap_err())
                .find("failed to fill whole buffer")
                .is_some(),
            "{:?}",
            &e
        );

        let res = retry_reader.read(&mut tmp_buf);
        assert!(res.is_ok());
        assert_eq!(res.unwrap(), 0);

        retry_reader.set_position(0);

        for i in 1..5 {
            let mut read_buf = [0u8; 3];
            retry_reader.read_exact(&mut read_buf).unwrap();
            assert_eq!(read_buf, [i as u8, i as u8, i as u8]);
        }
    }

    #[test]
    fn test_bound_reader() {
        let tests = [
            ("aaaaaaaaaa", 10, "aaaaaaaaaa"),
            ("bbbbbbbbbb", 9, "bbbbbbbbb"),
            ("cccccccccc", 1, "c"),
            ("dddddddddd", 0, ""),
        ];

        // read_to_end
        for (data, len, expected) in tests.iter() {
            let mut cursor = io::Cursor::new(data.as_bytes());
            let mut reader = BoundReader::from_reader(&mut cursor, *len as u64);
            let mut buf = vec![];
            reader.read_to_end(&mut buf).unwrap();
            assert_eq!(buf.len(), *len);
            assert_eq!(buf, expected.as_bytes().to_vec());

            // should EOF once length is exceeded
            let mut buf2 = vec![0u8; *len];
            let nr = reader.read(&mut buf2).unwrap();
            assert_eq!(nr, 0);
            assert_eq!(buf2, vec![0u8; *len]);
        }

        // read piecemeal
        for (data, len, expected) in tests.iter() {
            let mut cursor = io::Cursor::new(data.as_bytes());
            let mut reader = BoundReader::from_reader(&mut cursor, *len as u64);
            let mut buf = vec![];

            for i in 0..*len {
                let mut tmp = [0u8; 1];
                let nr = reader.read(&mut tmp).unwrap();
                assert_eq!(nr, 1);
                buf.extend_from_slice(&tmp);
            }

            assert_eq!(buf.len(), *len);
            assert_eq!(buf, expected.as_bytes().to_vec());

            // should EOF once length is exceeded
            let mut buf2 = vec![0u8; *len];
            let nr = reader.read(&mut buf2).unwrap();
            assert_eq!(nr, 0);
            assert_eq!(buf2, vec![0u8; *len]);
        }
    }
}
