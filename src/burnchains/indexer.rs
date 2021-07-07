// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use burnchains::BurnchainBlock;
use burnchains::Error as burnchain_error;
use burnchains::*;

use crate::types::chainstate::BurnchainHeaderHash;

// IPC messages between threads
pub trait BurnHeaderIPC {
    type H: Send + Sync + Clone;

    fn height(&self) -> u64;
    fn header(&self) -> Self::H;
    fn header_hash(&self) -> [u8; 32];
}

pub trait BurnBlockIPC {
    type H: BurnHeaderIPC + Sync + Send + Clone;
    type B: Send + Sync + Clone;

    fn height(&self) -> u64;
    fn header(&self) -> Self::H;
    fn block(&self) -> Self::B;
}

pub trait BurnchainBlockDownloader {
    type H: BurnHeaderIPC + Sync + Send + Clone;
    type B: BurnBlockIPC + Sync + Send + Clone;

    fn download(&mut self, header: &Self::H) -> Result<Self::B, burnchain_error>;
}

pub trait BurnchainBlockParser {
    type D: BurnchainBlockDownloader + Sync + Send;

    fn parse(
        &mut self,
        block: &<<Self as BurnchainBlockParser>::D as BurnchainBlockDownloader>::B,
    ) -> Result<BurnchainBlock, burnchain_error>;
}

pub trait BurnchainIndexer {
    type P: BurnchainBlockParser + Send + Sync;

    fn connect(&mut self) -> Result<(), burnchain_error>;

    fn get_first_block_height(&self) -> u64;
    fn get_first_block_header_hash(&self) -> Result<BurnchainHeaderHash, burnchain_error>;
    fn get_first_block_header_timestamp(&self) -> Result<u64, burnchain_error>;

    fn get_headers_path(&self) -> String;
    fn get_headers_height(&self) -> Result<u64, burnchain_error>;
    fn get_highest_header_height(&self) -> Result<u64, burnchain_error>;
    fn find_chain_reorg(&mut self) -> Result<u64, burnchain_error>;
    fn sync_headers(
        &mut self,
        start_height: u64,
        end_height: Option<u64>,
    ) -> Result<u64, burnchain_error>;
    fn drop_headers(&mut self, new_height: u64) -> Result<(), burnchain_error>;

    fn read_headers(&self, start_block: u64, end_block: u64) -> Result<Vec<<<<Self as BurnchainIndexer>::P as BurnchainBlockParser>::D as BurnchainBlockDownloader>::H>, burnchain_error>;

    fn downloader(&self) -> <<Self as BurnchainIndexer>::P as BurnchainBlockParser>::D;
    fn parser(&self) -> Self::P;
}
