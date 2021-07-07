// Rust Bitcoin Library
// Written in 2014 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! Consensus-encodable types
//!
//! This is basically a replacement of the `Encodable` trait which does
//! normalization for endianness, etc., to ensure that the encoding
//! matches for endianness, etc., to ensure that the encoding matches
//! the network consensus encoding.
//!
//! Essentially, anything that must go on the -disk- or -network- must
//! be encoded using the `ConsensusEncodable` trait, since this data
//! must be the same for all systems. Any data going to the -user-, e.g.
//! over JSONRPC, should use the ordinary `Encodable` trait. (This
//! should also be the same across systems, of course, but has some
//! critical differences from the network format, e.g. scripts come
//! with an opcode decode, hashes are big-endian, numbers are typically
//! big-endian decimals, etc.)
//!

use std::collections::HashMap;
use std::hash::Hash;
use std::{mem, u32};

use deps::bitcoin::network::serialize::{self, SimpleDecoder, SimpleEncoder};
use deps::bitcoin::util::hash::Sha256dHash;

/// Maximum size, in bytes, of a vector we are allowed to decode
pub const MAX_VEC_SIZE: usize = 32 * 1024 * 1024;

/// Data which can be encoded in a consensus-consistent way
pub trait ConsensusEncodable<S: SimpleEncoder> {
    /// Encode an object with a well-defined format
    fn consensus_encode(&self, e: &mut S) -> Result<(), serialize::Error>;
}

/// Data which can be encoded in a consensus-consistent way
pub trait ConsensusDecodable<D: SimpleDecoder>: Sized {
    /// Decode an object with a well-defined format
    fn consensus_decode(d: &mut D) -> Result<Self, serialize::Error>;
}

/// A variable-length unsigned integer
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct VarInt(pub u64);

/// Data which must be preceded by a 4-byte checksum
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct CheckedData(pub Vec<u8>);

// Primitive types
macro_rules! impl_int_encodable {
    ($ty:ident, $meth_dec:ident, $meth_enc:ident) => {
        impl<D: SimpleDecoder> ConsensusDecodable<D> for $ty {
            #[inline]
            fn consensus_decode(d: &mut D) -> Result<$ty, serialize::Error> {
                d.$meth_dec().map($ty::from_le)
            }
        }

        impl<S: SimpleEncoder> ConsensusEncodable<S> for $ty {
            #[inline]
            fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
                s.$meth_enc(self.to_le())
            }
        }
    };
}

impl_int_encodable!(u8, read_u8, emit_u8);
impl_int_encodable!(u16, read_u16, emit_u16);
impl_int_encodable!(u32, read_u32, emit_u32);
impl_int_encodable!(u64, read_u64, emit_u64);
impl_int_encodable!(i8, read_i8, emit_i8);
impl_int_encodable!(i16, read_i16, emit_i16);
impl_int_encodable!(i32, read_i32, emit_i32);
impl_int_encodable!(i64, read_i64, emit_i64);

impl VarInt {
    /// Gets the length of this VarInt when encoded.
    /// Returns 1 for 0...0xFC, 3 for 0xFD...(2^16-1), 5 for 0x10000...(2^32-1),
    /// and 9 otherwise.
    #[inline]
    pub fn encoded_length(&self) -> u64 {
        match self.0 {
            0..=0xFC => 1,
            0xFD..=0xFFFF => 3,
            0x10000..=0xFFFFFFFF => 5,
            _ => 9,
        }
    }
}

impl<S: SimpleEncoder> ConsensusEncodable<S> for VarInt {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        match self.0 {
            0..=0xFC => (self.0 as u8).consensus_encode(s),
            0xFD..=0xFFFF => {
                s.emit_u8(0xFD)?;
                (self.0 as u16).consensus_encode(s)
            }
            0x10000..=0xFFFFFFFF => {
                s.emit_u8(0xFE)?;
                (self.0 as u32).consensus_encode(s)
            }
            _ => {
                s.emit_u8(0xFF)?;
                (self.0 as u64).consensus_encode(s)
            }
        }
    }
}

impl<D: SimpleDecoder> ConsensusDecodable<D> for VarInt {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<VarInt, serialize::Error> {
        let n = d.read_u8()?;
        match n {
            0xFF => {
                let x = d.read_u64()?;
                if x < 0x100000000 {
                    Err(serialize::Error::ParseFailed("non-minimal varint"))
                } else {
                    Ok(VarInt(x))
                }
            }
            0xFE => {
                let x = d.read_u32()?;
                if x < 0x10000 {
                    Err(serialize::Error::ParseFailed("non-minimal varint"))
                } else {
                    Ok(VarInt(x as u64))
                }
            }
            0xFD => {
                let x = d.read_u16()?;
                if x < 0xFD {
                    Err(serialize::Error::ParseFailed("non-minimal varint"))
                } else {
                    Ok(VarInt(x as u64))
                }
            }
            n => Ok(VarInt(n as u64)),
        }
    }
}

// Booleans
impl<S: SimpleEncoder> ConsensusEncodable<S> for bool {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        s.emit_u8(if *self { 1 } else { 0 })
    }
}

impl<D: SimpleDecoder> ConsensusDecodable<D> for bool {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<bool, serialize::Error> {
        d.read_u8().map(|n| n != 0)
    }
}

// Strings
impl<S: SimpleEncoder> ConsensusEncodable<S> for String {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        self.as_bytes().consensus_encode(s)
    }
}

impl<D: SimpleDecoder> ConsensusDecodable<D> for String {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<String, serialize::Error> {
        String::from_utf8(ConsensusDecodable::consensus_decode(d)?)
            .map_err(|_| serialize::Error::ParseFailed("String was not valid UTF8"))
    }
}

// Arrays
macro_rules! impl_array {
    ( $size:expr ) => {
        impl<S: SimpleEncoder, T: ConsensusEncodable<S>> ConsensusEncodable<S> for [T; $size] {
            #[inline]
            fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
                for i in self.iter() {
                    i.consensus_encode(s)?;
                }
                Ok(())
            }
        }

        impl<D: SimpleDecoder, T: ConsensusDecodable<D> + Copy> ConsensusDecodable<D>
            for [T; $size]
        {
            #[inline]
            fn consensus_decode(d: &mut D) -> Result<[T; $size], serialize::Error> {
                // Set everything to the first decode
                let mut ret = [ConsensusDecodable::consensus_decode(d)?; $size];
                // Set the rest
                for item in ret.iter_mut().take($size).skip(1) {
                    *item = ConsensusDecodable::consensus_decode(d)?;
                }
                Ok(ret)
            }
        }
    };
}

impl_array!(2);
impl_array!(4);
impl_array!(8);
impl_array!(12);
impl_array!(16);
impl_array!(32);

impl<S: SimpleEncoder, T: ConsensusEncodable<S>> ConsensusEncodable<S> for [T] {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        VarInt(self.len() as u64).consensus_encode(s)?;
        for c in self.iter() {
            c.consensus_encode(s)?;
        }
        Ok(())
    }
}

// Cannot decode a slice

// Vectors
impl<S: SimpleEncoder, T: ConsensusEncodable<S>> ConsensusEncodable<S> for Vec<T> {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        (&self[..]).consensus_encode(s)
    }
}

impl<D: SimpleDecoder, T: ConsensusDecodable<D>> ConsensusDecodable<D> for Vec<T> {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<Vec<T>, serialize::Error> {
        let len = VarInt::consensus_decode(d)?.0;
        let byte_size = (len as usize)
            .checked_mul(mem::size_of::<T>())
            .ok_or(serialize::Error::ParseFailed("Invalid length"))?;
        if byte_size > MAX_VEC_SIZE {
            return Err(serialize::Error::OversizedVectorAllocation {
                requested: byte_size,
                max: MAX_VEC_SIZE,
            });
        }
        let mut ret = Vec::with_capacity(len as usize);
        for _ in 0..len {
            ret.push(ConsensusDecodable::consensus_decode(d)?);
        }
        Ok(ret)
    }
}

impl<S: SimpleEncoder, T: ConsensusEncodable<S>> ConsensusEncodable<S> for Box<[T]> {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        (&self[..]).consensus_encode(s)
    }
}

impl<D: SimpleDecoder, T: ConsensusDecodable<D>> ConsensusDecodable<D> for Box<[T]> {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<Box<[T]>, serialize::Error> {
        let len = VarInt::consensus_decode(d)?.0;
        let len = len as usize;
        if len > MAX_VEC_SIZE {
            return Err(serialize::Error::OversizedVectorAllocation {
                requested: len,
                max: MAX_VEC_SIZE,
            });
        }
        let mut ret = Vec::with_capacity(len);
        for _ in 0..len {
            ret.push(ConsensusDecodable::consensus_decode(d)?);
        }
        Ok(ret.into_boxed_slice())
    }
}

// Options (encoded as vectors of length 0 or 1)
impl<S: SimpleEncoder, T: ConsensusEncodable<S>> ConsensusEncodable<S> for Option<T> {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        match *self {
            Some(ref data) => {
                1u8.consensus_encode(s)?;
                data.consensus_encode(s)?;
            }
            None => {
                0u8.consensus_encode(s)?;
            }
        }
        Ok(())
    }
}

impl<D: SimpleDecoder, T: ConsensusDecodable<D>> ConsensusDecodable<D> for Option<T> {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<Option<T>, serialize::Error> {
        let bit: u8 = ConsensusDecodable::consensus_decode(d)?;
        Ok(if bit != 0 {
            Some(ConsensusDecodable::consensus_decode(d)?)
        } else {
            None
        })
    }
}

/// Do a double-SHA256 on some data and return the first 4 bytes
fn sha2_checksum(data: &[u8]) -> [u8; 4] {
    let checksum = Sha256dHash::from_data(data);
    [checksum[0], checksum[1], checksum[2], checksum[3]]
}

// Checked data
impl<S: SimpleEncoder> ConsensusEncodable<S> for CheckedData {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        (self.0.len() as u32).consensus_encode(s)?;
        sha2_checksum(&self.0).consensus_encode(s)?;
        // We can't just pass to the slice encoder since it'll insert a length
        for ch in &self.0 {
            ch.consensus_encode(s)?;
        }
        Ok(())
    }
}

impl<D: SimpleDecoder> ConsensusDecodable<D> for CheckedData {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<CheckedData, serialize::Error> {
        let len: u32 = ConsensusDecodable::consensus_decode(d)?;
        let checksum: [u8; 4] = ConsensusDecodable::consensus_decode(d)?;
        let mut ret = Vec::with_capacity(len as usize);
        for _ in 0..len {
            ret.push(ConsensusDecodable::consensus_decode(d)?);
        }
        let expected_checksum = sha2_checksum(&ret);
        if expected_checksum != checksum {
            Err(serialize::Error::InvalidChecksum {
                expected: expected_checksum,
                actual: checksum,
            })
        } else {
            Ok(CheckedData(ret))
        }
    }
}

// Tuples
macro_rules! tuple_encode {
    ($($x:ident),*) => (
        impl <S: SimpleEncoder, $($x: ConsensusEncodable<S>),*> ConsensusEncodable<S> for ($($x),*) {
            #[inline]
            #[allow(non_snake_case)]
            fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
                let &($(ref $x),*) = self;
                $( $x.consensus_encode(s)?; )*
                Ok(())
            }
        }

        impl<D: SimpleDecoder, $($x: ConsensusDecodable<D>),*> ConsensusDecodable<D> for ($($x),*) {
            #[inline]
            #[allow(non_snake_case)]
            fn consensus_decode(d: &mut D) -> Result<($($x),*), serialize::Error> {
                Ok(($({let $x = ConsensusDecodable::consensus_decode(d)?; $x }),*))
            }
        }
    );
}

tuple_encode!(T0, T1);
tuple_encode!(T0, T1, T2, T3);
tuple_encode!(T0, T1, T2, T3, T4, T5);
tuple_encode!(T0, T1, T2, T3, T4, T5, T6, T7);

// References
impl<S: SimpleEncoder, T: ConsensusEncodable<S>> ConsensusEncodable<S> for Box<T> {
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        (**self).consensus_encode(s)
    }
}

impl<D: SimpleDecoder, T: ConsensusDecodable<D>> ConsensusDecodable<D> for Box<T> {
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<Box<T>, serialize::Error> {
        ConsensusDecodable::consensus_decode(d).map(Box::new)
    }
}

// HashMap
impl<S, K, V> ConsensusEncodable<S> for HashMap<K, V>
where
    S: SimpleEncoder,
    K: ConsensusEncodable<S> + Eq + Hash,
    V: ConsensusEncodable<S>,
{
    #[inline]
    fn consensus_encode(&self, s: &mut S) -> Result<(), serialize::Error> {
        VarInt(self.len() as u64).consensus_encode(s)?;
        for (key, value) in self.iter() {
            key.consensus_encode(s)?;
            value.consensus_encode(s)?;
        }
        Ok(())
    }
}

impl<D, K, V> ConsensusDecodable<D> for HashMap<K, V>
where
    D: SimpleDecoder,
    K: ConsensusDecodable<D> + Eq + Hash,
    V: ConsensusDecodable<D>,
{
    #[inline]
    fn consensus_decode(d: &mut D) -> Result<HashMap<K, V>, serialize::Error> {
        let len = VarInt::consensus_decode(d)?.0;

        let mut ret = HashMap::with_capacity(len as usize);
        for _ in 0..len {
            ret.insert(
                ConsensusDecodable::consensus_decode(d)?,
                ConsensusDecodable::consensus_decode(d)?,
            );
        }
        Ok(ret)
    }
}

// Tests
#[cfg(test)]
mod tests {
    use super::{CheckedData, VarInt};

    use deps::bitcoin::network::serialize::{deserialize, serialize, Error};

    #[test]
    fn serialize_int_test() {
        // bool
        assert_eq!(serialize(&false).ok(), Some(vec![0u8]));
        assert_eq!(serialize(&true).ok(), Some(vec![1u8]));
        // u8
        assert_eq!(serialize(&1u8).ok(), Some(vec![1u8]));
        assert_eq!(serialize(&0u8).ok(), Some(vec![0u8]));
        assert_eq!(serialize(&255u8).ok(), Some(vec![255u8]));
        // u16
        assert_eq!(serialize(&1u16).ok(), Some(vec![1u8, 0]));
        assert_eq!(serialize(&256u16).ok(), Some(vec![0u8, 1]));
        assert_eq!(serialize(&5000u16).ok(), Some(vec![136u8, 19]));
        // u32
        assert_eq!(serialize(&1u32).ok(), Some(vec![1u8, 0, 0, 0]));
        assert_eq!(serialize(&256u32).ok(), Some(vec![0u8, 1, 0, 0]));
        assert_eq!(serialize(&5000u32).ok(), Some(vec![136u8, 19, 0, 0]));
        assert_eq!(serialize(&500000u32).ok(), Some(vec![32u8, 161, 7, 0]));
        assert_eq!(serialize(&168430090u32).ok(), Some(vec![10u8, 10, 10, 10]));
        // TODO: test negative numbers
        assert_eq!(serialize(&1i32).ok(), Some(vec![1u8, 0, 0, 0]));
        assert_eq!(serialize(&256i32).ok(), Some(vec![0u8, 1, 0, 0]));
        assert_eq!(serialize(&5000i32).ok(), Some(vec![136u8, 19, 0, 0]));
        assert_eq!(serialize(&500000i32).ok(), Some(vec![32u8, 161, 7, 0]));
        assert_eq!(serialize(&168430090i32).ok(), Some(vec![10u8, 10, 10, 10]));
        // u64
        assert_eq!(serialize(&1u64).ok(), Some(vec![1u8, 0, 0, 0, 0, 0, 0, 0]));
        assert_eq!(
            serialize(&256u64).ok(),
            Some(vec![0u8, 1, 0, 0, 0, 0, 0, 0])
        );
        assert_eq!(
            serialize(&5000u64).ok(),
            Some(vec![136u8, 19, 0, 0, 0, 0, 0, 0])
        );
        assert_eq!(
            serialize(&500000u64).ok(),
            Some(vec![32u8, 161, 7, 0, 0, 0, 0, 0])
        );
        assert_eq!(
            serialize(&723401728380766730u64).ok(),
            Some(vec![10u8, 10, 10, 10, 10, 10, 10, 10])
        );
        // TODO: test negative numbers
        assert_eq!(serialize(&1i64).ok(), Some(vec![1u8, 0, 0, 0, 0, 0, 0, 0]));
        assert_eq!(
            serialize(&256i64).ok(),
            Some(vec![0u8, 1, 0, 0, 0, 0, 0, 0])
        );
        assert_eq!(
            serialize(&5000i64).ok(),
            Some(vec![136u8, 19, 0, 0, 0, 0, 0, 0])
        );
        assert_eq!(
            serialize(&500000i64).ok(),
            Some(vec![32u8, 161, 7, 0, 0, 0, 0, 0])
        );
        assert_eq!(
            serialize(&723401728380766730i64).ok(),
            Some(vec![10u8, 10, 10, 10, 10, 10, 10, 10])
        );
    }

    #[test]
    fn serialize_varint_test() {
        assert_eq!(serialize(&VarInt(10)).ok(), Some(vec![10u8]));
        assert_eq!(serialize(&VarInt(0xFC)).ok(), Some(vec![0xFCu8]));
        assert_eq!(serialize(&VarInt(0xFD)).ok(), Some(vec![0xFDu8, 0xFD, 0]));
        assert_eq!(
            serialize(&VarInt(0xFFF)).ok(),
            Some(vec![0xFDu8, 0xFF, 0xF])
        );
        assert_eq!(
            serialize(&VarInt(0xF0F0F0F)).ok(),
            Some(vec![0xFEu8, 0xF, 0xF, 0xF, 0xF])
        );
        assert_eq!(
            serialize(&VarInt(0xF0F0F0F0F0E0)).ok(),
            Some(vec![0xFFu8, 0xE0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0, 0])
        );
    }

    #[test]
    fn deserialize_nonminimal_vec() {
        match deserialize::<Vec<u8>>(&[0xfd, 0x00, 0x00]) {
            Err(Error::ParseFailed("non-minimal varint")) => {}
            x => std::panic::panic_any(x),
        }
        match deserialize::<Vec<u8>>(&[0xfd, 0xfc, 0x00]) {
            Err(Error::ParseFailed("non-minimal varint")) => {}
            x => std::panic::panic_any(x),
        }
        match deserialize::<Vec<u8>>(&[0xfe, 0xff, 0x00, 0x00, 0x00]) {
            Err(Error::ParseFailed("non-minimal varint")) => {}
            x => std::panic::panic_any(x),
        }
        match deserialize::<Vec<u8>>(&[0xfe, 0xff, 0xff, 0x00, 0x00]) {
            Err(Error::ParseFailed("non-minimal varint")) => {}
            x => std::panic::panic_any(x),
        }
        match deserialize::<Vec<u8>>(&[0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) {
            Err(Error::ParseFailed("non-minimal varint")) => {}
            x => std::panic::panic_any(x),
        }
        match deserialize::<Vec<u8>>(&[0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00]) {
            Err(Error::ParseFailed("non-minimal varint")) => {}
            x => std::panic::panic_any(x),
        }

        let mut vec_256 = vec![0; 259];
        vec_256[0] = 0xfd;
        vec_256[1] = 0x00;
        vec_256[2] = 0x01;
        assert!(deserialize::<Vec<u8>>(&vec_256).is_ok());

        let mut vec_253 = vec![0; 256];
        vec_253[0] = 0xfd;
        vec_253[1] = 0xfd;
        vec_253[2] = 0x00;
        assert!(deserialize::<Vec<u8>>(&vec_253).is_ok());
    }

    #[test]
    fn serialize_checkeddata_test() {
        let cd = CheckedData(vec![1u8, 2, 3, 4, 5]);
        assert_eq!(
            serialize(&cd).ok(),
            Some(vec![5, 0, 0, 0, 162, 107, 175, 90, 1, 2, 3, 4, 5])
        );
    }

    #[test]
    fn serialize_vector_test() {
        assert_eq!(serialize(&vec![1u8, 2, 3]).ok(), Some(vec![3u8, 1, 2, 3]));
        assert_eq!(serialize(&[1u8, 2, 3][..]).ok(), Some(vec![3u8, 1, 2, 3]));
        // TODO: test vectors of more interesting objects
    }

    #[test]
    fn serialize_strbuf_test() {
        assert_eq!(
            serialize(&"Andrew".to_string()).ok(),
            Some(vec![6u8, 0x41, 0x6e, 0x64, 0x72, 0x65, 0x77])
        );
    }

    #[test]
    fn serialize_box_test() {
        assert_eq!(serialize(&Box::new(1u8)).ok(), Some(vec![1u8]));
        assert_eq!(serialize(&Box::new(1u16)).ok(), Some(vec![1u8, 0]));
        assert_eq!(
            serialize(&Box::new(1u64)).ok(),
            Some(vec![1u8, 0, 0, 0, 0, 0, 0, 0])
        );
    }

    #[test]
    fn serialize_option_test() {
        let none_ser = serialize(&None::<u8>);
        let some_ser = serialize(&Some(0xFFu8));
        assert_eq!(none_ser.ok(), Some(vec![0]));
        assert_eq!(some_ser.ok(), Some(vec![1, 0xFF]));
    }

    #[test]
    fn deserialize_int_test() {
        // bool
        assert!((deserialize(&[58u8, 0]) as Result<bool, _>).is_err());
        assert_eq!(deserialize(&[58u8]).ok(), Some(true));
        assert_eq!(deserialize(&[1u8]).ok(), Some(true));
        assert_eq!(deserialize(&[0u8]).ok(), Some(false));
        assert!((deserialize(&[0u8, 1]) as Result<bool, _>).is_err());

        // u8
        assert_eq!(deserialize(&[58u8]).ok(), Some(58u8));

        // u16
        assert_eq!(deserialize(&[0x01u8, 0x02]).ok(), Some(0x0201u16));
        assert_eq!(deserialize(&[0xABu8, 0xCD]).ok(), Some(0xCDABu16));
        assert_eq!(deserialize(&[0xA0u8, 0x0D]).ok(), Some(0xDA0u16));
        let failure16: Result<u16, _> = deserialize(&[1u8]);
        assert!(failure16.is_err());

        // u32
        assert_eq!(deserialize(&[0xABu8, 0xCD, 0, 0]).ok(), Some(0xCDABu32));
        assert_eq!(
            deserialize(&[0xA0u8, 0x0D, 0xAB, 0xCD]).ok(),
            Some(0xCDAB0DA0u32)
        );
        let failure32: Result<u32, _> = deserialize(&[1u8, 2, 3]);
        assert!(failure32.is_err());
        // TODO: test negative numbers
        assert_eq!(deserialize(&[0xABu8, 0xCD, 0, 0]).ok(), Some(0xCDABi32));
        assert_eq!(
            deserialize(&[0xA0u8, 0x0D, 0xAB, 0x2D]).ok(),
            Some(0x2DAB0DA0i32)
        );
        let failurei32: Result<i32, _> = deserialize(&[1u8, 2, 3]);
        assert!(failurei32.is_err());

        // u64
        assert_eq!(
            deserialize(&[0xABu8, 0xCD, 0, 0, 0, 0, 0, 0]).ok(),
            Some(0xCDABu64)
        );
        assert_eq!(
            deserialize(&[0xA0u8, 0x0D, 0xAB, 0xCD, 0x99, 0, 0, 0x99]).ok(),
            Some(0x99000099CDAB0DA0u64)
        );
        let failure64: Result<u64, _> = deserialize(&[1u8, 2, 3, 4, 5, 6, 7]);
        assert!(failure64.is_err());
        // TODO: test negative numbers
        assert_eq!(
            deserialize(&[0xABu8, 0xCD, 0, 0, 0, 0, 0, 0]).ok(),
            Some(0xCDABi64)
        );
        assert_eq!(
            deserialize(&[0xA0u8, 0x0D, 0xAB, 0xCD, 0x99, 0, 0, 0x99]).ok(),
            Some(-0x66ffff663254f260i64)
        );
        let failurei64: Result<i64, _> = deserialize(&[1u8, 2, 3, 4, 5, 6, 7]);
        assert!(failurei64.is_err());
    }

    #[test]
    fn deserialize_vec_test() {
        assert_eq!(deserialize(&[3u8, 2, 3, 4]).ok(), Some(vec![2u8, 3, 4]));
        assert!((deserialize(&[4u8, 2, 3, 4, 5, 6]) as Result<Vec<u8>, _>).is_err());
        // found by cargo fuzz
        assert!(deserialize::<Vec<u64>>(&[
            0xff, 0xff, 0xff, 0xff, 0x6b, 0x6b, 0x6b, 0x6b, 0x6b, 0x6b, 0x6b, 0x6b, 0x6b, 0x6b,
            0x6b, 0x6b, 0xa, 0xa, 0x3a
        ])
        .is_err());
    }

    #[test]
    fn deserialize_strbuf_test() {
        assert_eq!(
            deserialize(&[6u8, 0x41, 0x6e, 0x64, 0x72, 0x65, 0x77]).ok(),
            Some("Andrew".to_string())
        );
    }

    #[test]
    fn deserialize_checkeddata_test() {
        let cd: Result<CheckedData, _> =
            deserialize(&[5u8, 0, 0, 0, 162, 107, 175, 90, 1, 2, 3, 4, 5]);
        assert_eq!(cd.ok(), Some(CheckedData(vec![1u8, 2, 3, 4, 5])));
    }

    #[test]
    fn deserialize_option_test() {
        let none: Result<Option<u8>, _> = deserialize(&[0u8]);
        let good: Result<Option<u8>, _> = deserialize(&[1u8, 0xFF]);
        let bad: Result<Option<u8>, _> = deserialize(&[2u8]);
        assert!(bad.is_err());
        assert_eq!(none.ok(), Some(None));
        assert_eq!(good.ok(), Some(Some(0xFF)));
    }

    #[test]
    fn deserialize_box_test() {
        let zero: Result<Box<u8>, _> = deserialize(&[0u8]);
        let one: Result<Box<u8>, _> = deserialize(&[1u8]);
        assert_eq!(zero.ok(), Some(Box::new(0)));
        assert_eq!(one.ok(), Some(Box::new(1)));
    }
}
