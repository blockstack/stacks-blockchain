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

use std::fmt;

use rusqlite::types::ToSql;
use rusqlite::Row;
use rusqlite::Transaction;
use rusqlite::{Connection, OpenFlags, NO_PARAMS};

use std::convert::From;
use std::convert::TryFrom;
use std::fs;

use util::db::tx_begin_immediate;
use util::db::DBConn;
use util::db::Error as db_error;
use util::db::{query_count, query_row, query_rows, u64_to_sql, FromColumn, FromRow};

use util;
use util::hash::{bin_bytes, hex_bytes, to_bin, to_hex, Hash160, Sha256Sum, Sha512Trunc256Sum};
use util::log;
use util::macros::is_big_endian;
use util::secp256k1::Secp256k1PrivateKey;
use util::secp256k1::Secp256k1PublicKey;

use util::db::tx_busy_handler;

use chainstate::stacks::StacksPrivateKey;
use chainstate::stacks::StacksPublicKey;

use rand::seq::SliceRandom;
use rand::thread_rng;
use rand::Rng;
use rand::RngCore;

use net::asn::ASEntry4;
use net::Neighbor;
use net::NeighborAddress;
use net::NeighborKey;
use net::PeerAddress;
use net::ServiceFlags;

use burnchains::PrivateKey;
use burnchains::PublicKey;

use core::NETWORK_P2P_PORT;

use util::strings::UrlString;

pub const PEERDB_VERSION: &'static str = "1";

const NUM_SLOTS: usize = 8;

impl PeerAddress {
    pub fn to_bin(&self) -> String {
        to_bin(&self.0)
    }
}

impl FromColumn<PeerAddress> for PeerAddress {
    fn from_column<'a>(row: &'a Row, column_name: &str) -> Result<PeerAddress, db_error> {
        let addrbytes_bin: String = row.get_unwrap(column_name);
        if addrbytes_bin.len() != 128 {
            error!("Unparsable peer address {}", addrbytes_bin);
            return Err(db_error::ParseError);
        }
        let addrbytes = bin_bytes(&addrbytes_bin).map_err(|_e| {
            error!("Unparseable peer address {}", addrbytes_bin);
            db_error::ParseError
        })?;

        if addrbytes.len() != 16 {
            error!("Peer address has {} bytes; expected 16", addrbytes.len());
            return Err(db_error::ParseError);
        }

        let mut addrbytes_buf = [0u8; 16];
        addrbytes_buf.copy_from_slice(&addrbytes[0..16]);

        Ok(PeerAddress(addrbytes_buf))
    }
}

#[derive(PartialEq, Clone)]
pub struct LocalPeer {
    pub network_id: u32,
    pub parent_network_id: u32,
    nonce: [u8; 32],
    pub private_key: Secp256k1PrivateKey,
    pub private_key_expire: u64,

    pub addrbytes: PeerAddress,
    pub port: u16,
    pub services: u16,
    pub data_url: UrlString,

    // filled in and curated at runtime
    pub public_ip_address: Option<(PeerAddress, u16)>,
}

impl fmt::Display for LocalPeer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "local.{:x}://(bind={:?})(pub={:?})",
            self.network_id,
            &self.addrbytes.to_socketaddr(self.port),
            &self
                .public_ip_address
                .map(|(ref addrbytes, ref port)| addrbytes.to_socketaddr(*port))
        )
    }
}

impl fmt::Debug for LocalPeer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "local.{:x}://(bind={:?})(pub={:?})",
            self.network_id,
            &self.addrbytes.to_socketaddr(self.port),
            &self
                .public_ip_address
                .map(|(ref addrbytes, ref port)| addrbytes.to_socketaddr(*port))
        )
    }
}

impl LocalPeer {
    pub fn new(
        network_id: u32,
        parent_network_id: u32,
        addrbytes: PeerAddress,
        port: u16,
        privkey: Option<Secp256k1PrivateKey>,
        key_expire: u64,
        data_url: UrlString,
    ) -> LocalPeer {
        let mut pkey = privkey.unwrap_or(Secp256k1PrivateKey::new());
        pkey.set_compress_public(true);

        let mut rng = thread_rng();
        let mut my_nonce = [0u8; 32];

        rng.fill_bytes(&mut my_nonce);

        let addr = addrbytes;
        let port = port;
        let services = ServiceFlags::RELAY;

        info!(
            "Will be authenticating p2p messages with public key: {}",
            Secp256k1PublicKey::from_private(&pkey).to_hex()
        );

        LocalPeer {
            network_id: network_id,
            parent_network_id: parent_network_id,
            nonce: my_nonce,
            private_key: pkey,
            private_key_expire: key_expire,
            addrbytes: addr,
            port: port,
            services: services as u16,
            data_url: data_url,
            public_ip_address: None,
        }
    }

    pub fn to_neighbor_addr(&self) -> NeighborAddress {
        NeighborAddress {
            addrbytes: self.addrbytes.clone(),
            port: self.port,
            public_key_hash: Hash160::from_node_public_key(&StacksPublicKey::from_private(
                &self.private_key,
            )),
        }
    }
}

impl FromRow<LocalPeer> for LocalPeer {
    fn from_row<'a>(row: &'a Row) -> Result<LocalPeer, db_error> {
        let network_id: u32 = row.get_unwrap("network_id");
        let parent_network_id: u32 = row.get_unwrap("parent_network_id");
        let nonce_hex: String = row.get_unwrap("nonce");
        let privkey = Secp256k1PrivateKey::from_column(row, "private_key")?;
        let privkey_expire = u64::from_column(row, "private_key_expire")?;
        let addrbytes: PeerAddress = PeerAddress::from_column(row, "addrbytes")?;
        let port: u16 = row.get_unwrap("port");
        let services: u16 = row.get_unwrap("services");
        let data_url_str: String = row.get_unwrap("data_url");

        let nonce_bytes = hex_bytes(&nonce_hex).map_err(|_e| {
            error!("Unparseable local peer nonce {}", &nonce_hex);
            db_error::ParseError
        })?;

        if nonce_bytes.len() != 32 {
            error!("Peer nonce has {} bytes: {}", nonce_bytes.len(), nonce_hex);
            return Err(db_error::ParseError);
        }

        let mut nonce_buf = [0u8; 32];
        nonce_buf.copy_from_slice(&nonce_bytes[0..32]);

        let data_url = UrlString::try_from(data_url_str).map_err(|_e| db_error::ParseError)?;

        Ok(LocalPeer {
            network_id: network_id,
            parent_network_id: parent_network_id,
            private_key: privkey,
            nonce: nonce_buf,
            private_key_expire: privkey_expire,
            addrbytes: addrbytes,
            port: port,
            services: services,
            data_url: data_url,
            public_ip_address: None,
        })
    }
}

impl FromRow<ASEntry4> for ASEntry4 {
    fn from_row<'a>(row: &'a Row) -> Result<ASEntry4, db_error> {
        let prefix: u32 = row.get_unwrap("prefix");
        let mask: u8 = row.get_unwrap("mask");
        let asn: u32 = row.get_unwrap("asn");
        let org: u32 = row.get_unwrap("org");

        Ok(ASEntry4 {
            prefix,
            mask,
            asn,
            org,
        })
    }
}

impl FromRow<Neighbor> for Neighbor {
    fn from_row<'a>(row: &'a Row) -> Result<Neighbor, db_error> {
        let peer_version: u32 = row.get_unwrap("peer_version");
        let network_id: u32 = row.get_unwrap("network_id");
        let addrbytes: PeerAddress = PeerAddress::from_column(row, "addrbytes")?;
        let port: u16 = row.get_unwrap("port");
        let mut public_key: Secp256k1PublicKey =
            Secp256k1PublicKey::from_column(row, "public_key")?;
        let expire_block_height = u64::from_column(row, "expire_block_height")?;
        let last_contact_time = u64::from_column(row, "last_contact_time")?;
        let asn: u32 = row.get_unwrap("asn");
        let org: u32 = row.get_unwrap("org");
        let allowed: i64 = row.get_unwrap("allowed");
        let denied: i64 = row.get_unwrap("denied");
        let in_degree: u32 = row.get_unwrap("in_degree");
        let out_degree: u32 = row.get_unwrap("out_degree");

        public_key.set_compressed(true);

        Ok(Neighbor {
            addr: NeighborKey {
                peer_version: peer_version,
                network_id: network_id,
                addrbytes: addrbytes,
                port: port,
            },
            public_key: public_key,
            expire_block: expire_block_height,
            last_contact_time: last_contact_time,
            asn: asn,
            org: org,
            allowed: allowed,
            denied: denied,
            in_degree: in_degree,
            out_degree: out_degree,
        })
    }
}

// In what is likely an abuse of Sqlite, the peer database is structured such that the `frontier`
// table stores peers keyed by a deterministically-chosen random "slot," instead of their IP/port.
// (i.e. the slot is determined by a cryptographic the hash of the IP/port).  The reason for this
// is to facilitate randomized peer eviction when the frontier table gets too big -- if a peer's
// possible slots are taken, then the _existing_ peer is pinged to see if it is still online.  If
// it is still online, the new peer will _not_ be inserted.  If it is offline, then it will be.
// This is done to ensure that the frontier represents live, long-lived peers to the greatest
// extent possible.

const PEERDB_INITIAL_SCHEMA: &'static [&'static str] = &[
    r#"
    CREATE TABLE frontier(
        peer_version INTEGER NOT NULL,
        network_id INTEGER NOT NULL,
        addrbytes TEXT NOT NULL,
        port INTEGER NOT NULL,
        public_key TEXT NOT NULL,
        expire_block_height INTEGER NOT NULL,
        last_contact_time INTEGER NOT NULL,
        asn INTEGER NOT NULL,
        org INTEGER NOT NULL,
        allowed INTEGER NOT NULL,
        denied INTEGER NOT NULL,
        initial INTEGER NOT NULL,   -- 1 if this was one of the initial neighbors, 0 otherwise
        in_degree INTEGER NOT NULL,
        out_degree INTEGER NOT NULL,

        -- used to deterministically insert and evict
        slot INTEGER UNIQUE NOT NULL,

        PRIMARY KEY(slot)
    );"#,
    "CREATE INDEX peer_address_index ON frontier(network_id,addrbytes,port);",
    r#"
    CREATE TABLE asn4(
        prefix INTEGER NOT NULL,
        mask INTEGER NOT NULL,

        asn INTEGER NOT NULL,
        org INTEGER,

        PRIMARY KEY(prefix,mask)
    );"#,
    "CREATE TABLE db_config(version TEXT NOT NULL);",
    r#"
    CREATE TABLE local_peer(
        network_id INT NOT NULL,
        parent_network_id INT NOT NULL,
        nonce TEXT NOT NULL,
        private_key TEXT NOT NULL,
        private_key_expire INTEGER NOT NULL,
        addrbytes TEXT NOT NULL,
        port INTEGER NOT NULL,
        services INTEGER NOT NULL,
        data_url TEXT NOT NULL
    );"#,
    r#"
    CREATE TABLE allowed_prefixes(
        prefix TEXT NOT NULL,
        mask INTEGER NOT NULL
    );"#,
    r#"
    CREATE TABLE denied_prefixes(
        prefix TEXT NOT NULL,
        mask INTEGER NOT NULL
    );"#,
];

#[derive(Debug)]
pub struct PeerDB {
    pub conn: Connection,
    pub readwrite: bool,
}

impl PeerDB {
    fn instantiate(
        &mut self,
        network_id: u32,
        parent_network_id: u32,
        privkey_opt: Option<Secp256k1PrivateKey>,
        key_expires: u64,
        data_url: UrlString,
        p2p_addr: PeerAddress,
        p2p_port: u16,
        asn4_entries: &Vec<ASEntry4>,
        initial_neighbors: &Vec<Neighbor>,
    ) -> Result<(), db_error> {
        let localpeer = LocalPeer::new(
            network_id,
            parent_network_id,
            p2p_addr,
            p2p_port,
            privkey_opt,
            key_expires,
            data_url,
        );

        let mut tx = self.tx_begin()?;

        for row_text in PEERDB_INITIAL_SCHEMA {
            tx.execute_batch(row_text).map_err(db_error::SqliteError)?;
        }

        tx.execute(
            "INSERT INTO db_config (version) VALUES (?1)",
            &[&PEERDB_VERSION],
        )
        .map_err(db_error::SqliteError)?;

        let local_peer_args: &[&dyn ToSql] = &[
            &network_id,
            &parent_network_id,
            &to_hex(&localpeer.nonce),
            &to_hex(&localpeer.private_key.to_bytes()),
            &u64_to_sql(key_expires)?,
            &to_bin(localpeer.addrbytes.as_bytes()),
            &localpeer.port,
            &localpeer.services,
            &localpeer.data_url.as_str(),
        ];

        tx.execute("INSERT INTO local_peer (network_id, parent_network_id, nonce, private_key, private_key_expire, addrbytes, port, services, data_url) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9)", local_peer_args)
            .map_err(db_error::SqliteError)?;

        for neighbor in initial_neighbors {
            // do we have this neighbor already?
            test_debug!("Add initial neighbor {:?}", &neighbor);
            let res = PeerDB::try_insert_peer(&mut tx, &neighbor)?;
            if !res {
                warn!("Failed to insert neighbor {:?}", &neighbor);
            }
        }

        for asn4 in asn4_entries {
            PeerDB::asn4_insert(&mut tx, &asn4)?;
        }

        for neighbor in initial_neighbors {
            PeerDB::set_initial_peer(
                &mut tx,
                neighbor.addr.network_id,
                &neighbor.addr.addrbytes,
                neighbor.addr.port,
            )?;
        }

        tx.commit().map_err(db_error::SqliteError)?;

        Ok(())
    }

    fn update_local_peer(
        &mut self,
        network_id: u32,
        parent_network_id: u32,
        data_url: UrlString,
        p2p_port: u16,
    ) -> Result<(), db_error> {
        let local_peer_args: &[&dyn ToSql] = &[
            &p2p_port,
            &data_url.as_str(),
            &network_id,
            &parent_network_id,
        ];

        match self.conn.execute("UPDATE local_peer SET port = ?, data_url = ? WHERE network_id = ? AND parent_network_id = ?",
                                local_peer_args) {
            Ok(_) => Ok(()),
            Err(e) => Err(db_error::SqliteError(e))
        }
    }

    fn reset_denies<'a>(tx: &mut Transaction<'a>) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET denied = 0", NO_PARAMS)
            .map_err(db_error::SqliteError)?;
        Ok(())
    }

    fn reset_allows<'a>(tx: &mut Transaction<'a>) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET allowed = -1", NO_PARAMS)
            .map_err(db_error::SqliteError)?;
        Ok(())
    }

    fn refresh_denies<'a>(tx: &mut Transaction<'a>) -> Result<(), db_error> {
        PeerDB::reset_denies(tx)?;
        let deny_cidrs = PeerDB::get_denied_cidrs(tx)?;
        for (prefix, mask) in deny_cidrs.into_iter() {
            debug!("Refresh deny {}/{}", &prefix, mask);
            PeerDB::apply_cidr_filter(tx, &prefix, mask, "denied", i64::max_value())?;
        }
        Ok(())
    }

    fn refresh_allows<'a>(tx: &mut Transaction<'a>) -> Result<(), db_error> {
        PeerDB::reset_allows(tx)?;
        let allow_cidrs = PeerDB::get_allowed_cidrs(tx)?;
        for (prefix, mask) in allow_cidrs.into_iter() {
            debug!("Refresh allow {}/{}", &prefix, mask);
            PeerDB::apply_cidr_filter(tx, &prefix, mask, "allowed", i64::max_value())?;
        }
        Ok(())
    }

    /// Open the burn database at the given path.  Open read-only or read/write.
    /// If opened for read/write and it doesn't exist, instantiate it.
    pub fn connect(
        path: &String,
        readwrite: bool,
        network_id: u32,
        parent_network_id: u32,
        privkey_opt: Option<Secp256k1PrivateKey>,
        key_expires: u64,
        p2p_addr: PeerAddress,
        p2p_port: u16,
        data_url: UrlString,
        asn4_recs: &Vec<ASEntry4>,
        initial_neighbors: Option<&Vec<Neighbor>>,
    ) -> Result<PeerDB, db_error> {
        let mut create_flag = false;
        let open_flags = if fs::metadata(path).is_err() {
            // need to create
            if readwrite {
                create_flag = true;
                OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
            } else {
                return Err(db_error::NoDBError);
            }
        } else {
            // can just open
            if readwrite {
                OpenFlags::SQLITE_OPEN_READ_WRITE
            } else {
                OpenFlags::SQLITE_OPEN_READ_ONLY
            }
        };

        let conn =
            Connection::open_with_flags(path, open_flags).map_err(|e| db_error::SqliteError(e))?;

        conn.busy_handler(Some(tx_busy_handler))?;
        let mut db = PeerDB {
            conn: conn,
            readwrite: readwrite,
        };

        if create_flag {
            // instantiate!
            match initial_neighbors {
                Some(ref neighbors) => {
                    db.instantiate(
                        network_id,
                        parent_network_id,
                        privkey_opt,
                        key_expires,
                        data_url,
                        p2p_addr,
                        p2p_port,
                        asn4_recs,
                        neighbors,
                    )?;
                }
                None => {
                    db.instantiate(
                        network_id,
                        parent_network_id,
                        privkey_opt,
                        key_expires,
                        data_url,
                        p2p_addr,
                        p2p_port,
                        asn4_recs,
                        &vec![],
                    )?;
                }
            }
        } else {
            db.update_local_peer(network_id, parent_network_id, data_url, p2p_port)?;

            {
                let mut tx = db.tx_begin()?;
                PeerDB::refresh_allows(&mut tx)?;
                PeerDB::refresh_denies(&mut tx)?;
                PeerDB::clear_initial_peers(&mut tx)?;

                if let Some(neighbors) = initial_neighbors {
                    for neighbor in neighbors {
                        PeerDB::set_initial_peer(
                            &mut tx,
                            neighbor.addr.network_id,
                            &neighbor.addr.addrbytes,
                            neighbor.addr.port,
                        )?;
                    }
                }

                tx.commit()?;
            }
        }
        Ok(db)
    }

    /// Open a burn database in memory (used for testing)
    #[cfg(test)]
    pub fn connect_memory(
        network_id: u32,
        parent_network_id: u32,
        key_expires: u64,
        data_url: UrlString,
        asn4_entries: &Vec<ASEntry4>,
        initial_neighbors: &Vec<Neighbor>,
    ) -> Result<PeerDB, db_error> {
        let conn = Connection::open_in_memory().map_err(|e| db_error::SqliteError(e))?;

        let mut db = PeerDB {
            conn: conn,
            readwrite: true,
        };

        db.instantiate(
            network_id,
            parent_network_id,
            None,
            key_expires,
            data_url,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            NETWORK_P2P_PORT,
            asn4_entries,
            initial_neighbors,
        )?;
        Ok(db)
    }

    pub fn conn(&self) -> &Connection {
        &self.conn
    }

    pub fn tx_begin<'a>(&'a mut self) -> Result<Transaction<'a>, db_error> {
        if !self.readwrite {
            return Err(db_error::ReadOnly);
        }

        let tx = tx_begin_immediate(&mut self.conn)?;
        Ok(tx)
    }

    /// Read the local peer record
    pub fn get_local_peer(conn: &DBConn) -> Result<LocalPeer, db_error> {
        let qry = "SELECT * FROM local_peer LIMIT 1".to_string();
        let rows = query_rows::<LocalPeer, _>(conn, &qry, NO_PARAMS)?;

        match rows.len() {
            1 => Ok(rows[0].clone()),
            _ => {
                // only one item here
                panic!("Got multiple LocalPeer rows, or 0");
            }
        }
    }

    /// Set the local IP address and port
    pub fn set_local_ipaddr<'a>(
        tx: &mut Transaction<'a>,
        addrbytes: &PeerAddress,
        port: u16,
    ) -> Result<(), db_error> {
        tx.execute(
            "UPDATE local_peer SET addrbytes = ?1, port = ?2",
            &[&to_bin(&addrbytes.as_bytes().to_vec()), &port as &dyn ToSql],
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Set local service availability
    pub fn set_local_services<'a>(tx: &mut Transaction<'a>, services: u16) -> Result<(), db_error> {
        tx.execute(
            "UPDATE local_peer SET services = ?1",
            &[&services as &dyn ToSql],
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Set local private key and expiry
    pub fn set_local_private_key<'a>(
        tx: &mut Transaction<'a>,
        privkey: &Secp256k1PrivateKey,
        expire_block: u64,
    ) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[&to_hex(&privkey.to_bytes()), &u64_to_sql(expire_block)?];
        tx.execute(
            "UPDATE local_peer SET private_key = ?1, private_key_expire = ?2",
            args,
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Re-key and return the new local peer
    pub fn rekey(&mut self, new_expire_block: u64) -> Result<LocalPeer, db_error> {
        if new_expire_block > ((1 as u64) << 63) - 1 {
            return Err(db_error::Overflow);
        }

        let new_key = Secp256k1PrivateKey::new();
        {
            let mut tx = self.tx_begin()?;

            PeerDB::set_local_private_key(&mut tx, &new_key, new_expire_block)?;
            tx.commit().map_err(db_error::SqliteError)?;
        }

        PeerDB::get_local_peer(self.conn())
    }

    /// Calculate the "slots" in the peer database where this peer can be inserted.
    /// Slots are distributed uniformly at random between 0 and 2**24.
    /// NUM_SLOTS will be returned.
    pub fn peer_slots(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<Vec<u32>, db_error> {
        let local_peer = PeerDB::get_local_peer(conn)?;
        let mut ret = vec![];
        for i in 0..NUM_SLOTS {
            // pack peer address, port, and index.
            // Randomize with local nonce
            let mut bytes = vec![];
            bytes.append(&mut local_peer.nonce.to_vec().clone());
            bytes.push(i as u8);

            for i in 0..16 {
                bytes.push(peer_addr.as_bytes()[i]);
            }

            bytes.push((peer_port & 0xff) as u8);
            bytes.push((peer_port >> 8) as u8);

            bytes.push(((network_id & 0xff000000) >> 24) as u8);
            bytes.push(((network_id & 0x00ff0000) >> 16) as u8);
            bytes.push(((network_id & 0x0000ff00) >> 8) as u8);
            bytes.push((network_id & 0x000000ff) as u8);

            let h = Sha512Trunc256Sum::from_data(&bytes[..]);
            let slot: u32 = (h.as_bytes()[0] as u32)
                | ((h.as_bytes()[1] as u32) << 8)
                | ((h.as_bytes()[2] as u32) << 16);

            ret.push(slot);
        }
        Ok(ret)
    }

    /// Do we have this neighbor already?  If so, look it up.
    /// Panics if the peer was inserted twice -- this shouldn't happen.
    pub fn get_peer(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<Option<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3"
            .to_string();
        let args = [
            &network_id as &dyn ToSql,
            &peer_addr.to_bin() as &dyn ToSql,
            &peer_port as &dyn ToSql,
        ];
        query_row::<Neighbor, _>(conn, &qry, &args)
    }

    /// Get peer by port (used in tests where the IP address doesn't really matter)
    #[cfg(test)]
    pub fn get_peer_by_port(
        conn: &DBConn,
        network_id: u32,
        peer_port: u16,
    ) -> Result<Option<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier WHERE network_id = ?1 AND port = ?2".to_string();
        let args = [&network_id as &dyn ToSql, &peer_port as &dyn ToSql];
        query_row::<Neighbor, _>(conn, &qry, &args)
    }

    /// Get a peer record at a particular slot
    pub fn get_peer_at(
        conn: &DBConn,
        network_id: u32,
        slot: u32,
    ) -> Result<Option<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier WHERE network_id = ?1 AND slot = ?2".to_string();
        let args = [&network_id as &dyn ToSql, &slot as &dyn ToSql];
        query_row::<Neighbor, _>(conn, &qry, &args)
    }

    /// Is a peer denied?
    pub fn is_peer_denied(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<bool, db_error> {
        match PeerDB::get_peer(conn, network_id, peer_addr, peer_port)? {
            Some(neighbor) => {
                if neighbor.is_denied() {
                    return Ok(true);
                }
                if PeerDB::is_address_denied(conn, &neighbor.addr.addrbytes)? {
                    return Ok(true);
                }
                return Ok(false);
            }
            None => {
                if PeerDB::is_address_denied(conn, &peer_addr)? {
                    return Ok(true);
                }
                return Ok(false);
            }
        }
    }

    /// Is a peer always allowed?
    pub fn is_peer_always_allowed(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<bool, db_error> {
        match PeerDB::get_peer(conn, network_id, peer_addr, peer_port)? {
            Some(neighbor) => {
                if neighbor.allowed < 0 {
                    return Ok(true);
                }
                return Ok(false);
            }
            None => {
                return Ok(false);
            }
        }
    }

    /// Get all always-allowed peers
    pub fn get_always_allowed_peers(
        conn: &DBConn,
        network_id: u32,
    ) -> Result<Vec<Neighbor>, db_error> {
        let sql = "SELECT * FROM frontier WHERE allowed < 0 AND network_id = ?1 ORDER BY RANDOM()";
        let allow_rows = query_rows::<Neighbor, _>(conn, sql, &[&network_id])?;
        Ok(allow_rows)
    }

    /// Get the bootstrap peers
    pub fn get_bootstrap_peers(conn: &DBConn, network_id: u32) -> Result<Vec<Neighbor>, db_error> {
        let sql = "SELECT * FROM frontier WHERE initial = 1 AND network_id = ?1 ORDER BY RANDOM()";
        let allow_rows = query_rows::<Neighbor, _>(conn, sql, &[&network_id])?;
        Ok(allow_rows)
    }

    /// Insert or replace a neighbor into a given slot
    pub fn insert_or_replace_peer<'a>(
        tx: &mut Transaction<'a>,
        neighbor: &Neighbor,
        slot: u32,
    ) -> Result<(), db_error> {
        let neighbor_args: &[&dyn ToSql] = &[
            &neighbor.addr.peer_version,
            &neighbor.addr.network_id,
            &to_bin(neighbor.addr.addrbytes.as_bytes()),
            &neighbor.addr.port,
            &to_hex(&neighbor.public_key.to_bytes_compressed()),
            &u64_to_sql(neighbor.expire_block)?,
            &u64_to_sql(neighbor.last_contact_time)?,
            &neighbor.asn,
            &neighbor.org,
            &neighbor.allowed,
            &neighbor.denied,
            &neighbor.in_degree,
            &neighbor.out_degree,
            &0i64,
            &slot,
        ];

        tx.execute("INSERT OR REPLACE INTO frontier (peer_version, network_id, addrbytes, port, public_key, expire_block_height, last_contact_time, asn, org, allowed, denied, in_degree, out_degree, initial, slot) \
                   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15)", neighbor_args)
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Remove a peer from the peer database
    pub fn drop_peer<'a>(
        tx: &mut Transaction<'a>,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<(), db_error> {
        tx.execute(
            "DELETE FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3",
            &[
                &network_id as &dyn ToSql,
                &peer_addr.to_bin() as &dyn ToSql,
                &peer_port as &dyn ToSql,
            ],
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Is a peer one of this node's initial neighbors?
    pub fn is_initial_peer(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<bool, db_error> {
        let res: Option<i64> = query_row(
            conn,
            "SELECT initial FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3",
            &[&network_id as &dyn ToSql, &peer_addr.to_bin(), &peer_port],
        )?;

        match res {
            Some(x) => Ok(x != 0),
            None => Ok(false),
        }
    }

    /// Set a peer as an initial peer
    fn set_initial_peer<'a>(
        tx: &mut Transaction<'a>,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET initial = 1 WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3", 
                    &[&network_id as &dyn ToSql, &peer_addr.to_bin(), &peer_port])
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// clear all initial peers
    fn clear_initial_peers<'a>(tx: &mut Transaction<'a>) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET initial = 0", NO_PARAMS)
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Set/unset allow flag for a peer
    /// Pass -1 for "always"
    pub fn set_allow_peer<'a>(
        tx: &mut Transaction<'a>,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
        allow_deadline: i64,
    ) -> Result<(), db_error> {
        let num_updated = tx.execute("UPDATE frontier SET allowed = ?1 WHERE network_id = ?2 AND addrbytes = ?3 AND port = ?4",
                   &[&allow_deadline as &dyn ToSql, &network_id, &peer_addr.to_bin(), &peer_port])
            .map_err(db_error::SqliteError)?;

        if num_updated == 0 {
            // we're preemptively allowing
            let nk = NeighborKey {
                peer_version: 0,
                network_id: network_id,
                addrbytes: peer_addr.clone(),
                port: peer_port,
            };
            let empty_key = StacksPublicKey::from_private(&StacksPrivateKey::new());
            let mut empty_neighbor = Neighbor::empty(&nk, &empty_key, 0);

            empty_neighbor.allowed = allow_deadline as i64;

            debug!("Preemptively allow peer {:?}", &nk);
            if !PeerDB::try_insert_peer(tx, &empty_neighbor)? {
                let mut slots = PeerDB::peer_slots(tx, network_id, peer_addr, peer_port)?;
                let slot = slots.pop().expect("BUG: no slots");
                warn!(
                    "Forcing replacement of peer at slot {} for allowed peer {:?}",
                    slot, &empty_neighbor.addr
                );
                PeerDB::insert_or_replace_peer(tx, &empty_neighbor, slot)?;
            }
        }

        Ok(())
    }

    /// Set/unset deny flag for a peer
    /// negative values aren't allowed
    pub fn set_deny_peer<'a>(
        tx: &mut Transaction<'a>,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
        deny_deadline: u64,
    ) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[
            &u64_to_sql(deny_deadline)?,
            &network_id,
            &peer_addr.to_bin(),
            &peer_port,
        ];
        let num_updated = tx.execute("UPDATE frontier SET denied = ?1 WHERE network_id = ?2 AND addrbytes = ?3 AND port = ?4", args)
            .map_err(db_error::SqliteError)?;

        if num_updated == 0 {
            // we're preemptively denying
            let nk = NeighborKey {
                peer_version: 0,
                network_id: network_id,
                addrbytes: peer_addr.clone(),
                port: peer_port,
            };
            let empty_key = StacksPublicKey::from_private(&StacksPrivateKey::new());
            let mut empty_neighbor = Neighbor::empty(&nk, &empty_key, 0);

            empty_neighbor.denied = deny_deadline as i64;

            debug!("Preemptively deny peer {:?}", &nk);
            if !PeerDB::try_insert_peer(tx, &empty_neighbor)? {
                let mut slots = PeerDB::peer_slots(tx, network_id, peer_addr, peer_port)?;
                let slot = slots.pop().expect("BUG: no slots");
                warn!(
                    "Forcing replacement of peer at slot {} for denied peer {:?}",
                    slot, &empty_neighbor.addr
                );
                PeerDB::insert_or_replace_peer(tx, &empty_neighbor, slot)?;
            }
        }

        Ok(())
    }

    /// Update an existing peer's entries.  Does nothing if the peer is not present.
    pub fn update_peer<'a>(tx: &mut Transaction<'a>, neighbor: &Neighbor) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[
            &neighbor.addr.peer_version,
            &to_hex(&neighbor.public_key.to_bytes_compressed()),
            &u64_to_sql(neighbor.expire_block)?,
            &u64_to_sql(neighbor.last_contact_time)?,
            &neighbor.asn,
            &neighbor.org,
            &neighbor.allowed,
            &neighbor.denied,
            &neighbor.in_degree,
            &neighbor.out_degree,
            &neighbor.addr.network_id,
            &to_bin(neighbor.addr.addrbytes.as_bytes()),
            &neighbor.addr.port,
        ];

        tx.execute("UPDATE frontier SET peer_version = ?1, public_key = ?2, expire_block_height = ?3, last_contact_time = ?4, asn = ?5, org = ?6, allowed = ?7, denied = ?8, in_degree = ?9, out_degree = ?10 \
                    WHERE network_id = ?11 AND addrbytes = ?12 AND port = ?13", args)
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Try to insert a peer at one of its slots.
    /// Does not insert the peer if it is already present, but will instead try to update it with
    /// this peer's information.
    /// If at least one slot was empty, or if the peer is already present and can be updated, then insert/update the peer and return true.
    /// If all slots are occupied, return false.
    pub fn try_insert_peer<'a>(
        tx: &mut Transaction<'a>,
        neighbor: &Neighbor,
    ) -> Result<bool, db_error> {
        let present = PeerDB::get_peer(
            tx,
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )?;
        if present.is_some() {
            // already here
            PeerDB::update_peer(tx, neighbor)?;
            return Ok(false);
        }

        let slots = PeerDB::peer_slots(
            tx,
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )?;
        for slot in &slots {
            let peer_opt = PeerDB::get_peer_at(tx, neighbor.addr.network_id, *slot)?;
            if peer_opt.is_none() {
                // have a spare slot!
                PeerDB::insert_or_replace_peer(tx, neighbor, *slot)?;
                return Ok(true);
            }
        }

        // no slots free
        return Ok(false);
    }

    /// Add a cidr prefix
    fn add_cidr_prefix<'a>(
        tx: &mut Transaction<'a>,
        table: &str,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[&prefix.to_bin(), &mask];
        tx.execute(
            &format!(
                "INSERT OR REPLACE INTO {} (prefix, mask) VALUES (?1, ?2)",
                table
            ),
            args,
        )
        .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Remove a cidr prefix
    fn remove_cidr_prefix<'a>(
        tx: &mut Transaction<'a>,
        table: &str,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[&prefix.to_bin(), &mask];
        tx.execute(
            &format!("DELETE FROM {} WHERE prefix = ?1 AND mask = ?2", table),
            args,
        )
        .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Get all cidr prefixes from a given table
    fn get_cidr_prefixes(conn: &DBConn, table: &str) -> Result<Vec<(PeerAddress, u32)>, db_error> {
        let sql_query = format!("SELECT prefix, mask FROM {}", table);
        let mut stmt = conn.prepare(&sql_query)?;
        let rows_res_iter = stmt
            .query_and_then(NO_PARAMS, |row| {
                let prefix = PeerAddress::from_column(row, "prefix")?;
                let mask: u32 = row.get_unwrap("mask");
                let res: Result<(PeerAddress, u32), db_error> = Ok((prefix, mask));
                res
            })
            .map_err(db_error::SqliteError)?;

        let mut ret = vec![];
        for row_res in rows_res_iter {
            ret.push(row_res?);
        }

        Ok(ret)
    }

    /// Get all deny CIDR prefixes
    pub fn get_denied_cidrs(conn: &DBConn) -> Result<Vec<(PeerAddress, u32)>, db_error> {
        PeerDB::get_cidr_prefixes(conn, "denied_prefixes")
    }

    /// Get all allow CIDR prefixes
    pub fn get_allowed_cidrs(conn: &DBConn) -> Result<Vec<(PeerAddress, u32)>, db_error> {
        PeerDB::get_cidr_prefixes(conn, "allowed_prefixes")
    }

    /// Check to see if an address is denied by one of the CIDR deny rows
    pub fn is_address_denied(conn: &DBConn, addr: &PeerAddress) -> Result<bool, db_error> {
        let denied_rows = PeerDB::get_denied_cidrs(conn)?;
        let addr_int = u128::from_be_bytes(addr.as_bytes().to_owned());

        for (prefix, mask) in denied_rows.into_iter() {
            let addr_mask = !((1u128 << (128 - mask)) - 1);
            let mask_int = u128::from_be_bytes(prefix.as_bytes().to_owned()) & addr_mask;
            if mask_int == (addr_int & addr_mask) {
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Convert a prefix address and mask to its hex representation
    fn cidr_prefix_to_string(prefix: &PeerAddress, mask: u32) -> String {
        assert!(mask > 0 && mask <= 128);
        let s = to_bin(
            &(u128::from_be_bytes(prefix.as_bytes().to_owned()) & !((1u128 << (128 - mask)) - 1))
                .to_be_bytes(),
        );
        s
    }

    /// Update the given column to be equal to the given value for all addresses that match the given
    /// CIDR prefix
    fn apply_cidr_filter<'a>(
        tx: &mut Transaction<'a>,
        prefix: &PeerAddress,
        mask: u32,
        column: &str,
        value: i64,
    ) -> Result<(), db_error> {
        assert!(mask > 0 && mask <= 128);
        let prefix_txt = PeerDB::cidr_prefix_to_string(prefix, mask);
        let args: &[&dyn ToSql] = &[&value, &mask, &prefix_txt];
        tx.execute(
            &format!(
                "UPDATE frontier SET {} = ?1 WHERE SUBSTR(addrbytes,1,?2) = SUBSTR(?3,1,?2)",
                column
            ),
            args,
        )
        .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Set a allowed CIDR prefix
    pub fn add_allow_cidr<'a>(
        tx: &mut Transaction<'a>,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        assert!(mask > 0 && mask <= 128);
        PeerDB::add_cidr_prefix(tx, "allowed_prefixes", prefix, mask)?;

        debug!("Apply allow {}/{}", &prefix, mask);
        PeerDB::apply_cidr_filter(tx, prefix, mask, "allowed", -1)?;
        Ok(())
    }

    /// Set a denied CIDR prefix
    pub fn add_deny_cidr<'a>(
        tx: &mut Transaction<'a>,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        assert!(mask > 0 && mask <= 128);
        PeerDB::add_cidr_prefix(tx, "denied_prefixes", prefix, mask)?;

        debug!("Apply deny {}/{}", &prefix, mask);
        PeerDB::apply_cidr_filter(tx, prefix, mask, "denied", i64::max_value())?;
        Ok(())
    }

    /// Get random neighbors, optionally always including allowed neighbors
    pub fn get_random_neighbors(
        conn: &DBConn,
        network_id: u32,
        count: u32,
        block_height: u64,
        always_include_allowed: bool,
    ) -> Result<Vec<Neighbor>, db_error> {
        let mut ret = vec![];

        // UTC time
        let now_secs = util::get_epoch_time_secs();

        if always_include_allowed {
            // always include allowed neighbors, freshness be damned
            let allow_qry = "SELECT * FROM frontier WHERE network_id = ?1 AND denied < ?2 AND (allowed < 0 OR ?3 < allowed)".to_string();
            let allow_args: &[&dyn ToSql] =
                &[&network_id, &u64_to_sql(now_secs)?, &u64_to_sql(now_secs)?];
            let mut allow_rows = query_rows::<Neighbor, _>(conn, &allow_qry, allow_args)?;

            if allow_rows.len() >= (count as usize) {
                // return a random subset
                let allow_slice = allow_rows.as_mut_slice();
                allow_slice.shuffle(&mut thread_rng());
                return Ok(allow_slice[0..(count as usize)].to_vec());
            }

            ret.append(&mut allow_rows);
        }

        // fill in with non-allowed, randomly-chosen, fresh peers
        let random_peers_qry = if always_include_allowed {
            "SELECT * FROM frontier WHERE network_id = ?1 AND last_contact_time >= 0 AND ?2 < expire_block_height AND denied < ?3 AND \
                 (allowed >= 0 AND allowed <= ?4) ORDER BY RANDOM() LIMIT ?5".to_string()
        } else {
            "SELECT * FROM frontier WHERE network_id = ?1 AND last_contact_time >= 0 AND ?2 < expire_block_height AND denied < ?3 AND \
                 (allowed < 0 OR (allowed >= 0 AND allowed <= ?4)) ORDER BY RANDOM() LIMIT ?5".to_string()
        };

        let random_peers_args: &[&dyn ToSql] = &[
            &network_id,
            &u64_to_sql(block_height)?,
            &u64_to_sql(now_secs)?,
            &u64_to_sql(now_secs)?,
            &(count - (ret.len() as u32)),
        ];
        let mut random_peers =
            query_rows::<Neighbor, _>(conn, &random_peers_qry, random_peers_args)?;

        ret.append(&mut random_peers);
        Ok(ret)
    }

    /// Get an randomized initial set of peers.
    /// -- always include all allowed neighbors
    /// -- never include denied neighbors
    /// -- for neighbors that are neither allowed nor denied, sample them randomly as long as they're fresh.
    pub fn get_initial_neighbors(
        conn: &DBConn,
        network_id: u32,
        count: u32,
        block_height: u64,
    ) -> Result<Vec<Neighbor>, db_error> {
        PeerDB::get_random_neighbors(conn, network_id, count, block_height, true)
    }

    /// Get a randomized set of peers for walking the peer graph.
    /// -- selects peers at random even if not allowed
    pub fn get_random_walk_neighbors(
        conn: &DBConn,
        network_id: u32,
        count: u32,
        block_height: u64,
    ) -> Result<Vec<Neighbor>, db_error> {
        PeerDB::get_random_neighbors(conn, network_id, count, block_height, false)
    }

    /// Add an IPv4 <--> ASN mapping
    /// Used during db instantiation
    fn asn4_insert<'a>(tx: &mut Transaction<'a>, asn4: &ASEntry4) -> Result<(), db_error> {
        tx.execute(
            "INSERT OR REPLACE INTO asn4 (prefix, mask, asn, org) VALUES (?1, ?2, ?3, ?4)",
            &[
                &asn4.prefix as &dyn ToSql,
                &asn4.mask as &dyn ToSql,
                &asn4.asn as &dyn ToSql,
                &asn4.org as &dyn ToSql,
            ],
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Classify an IPv4 address to its AS number.
    /// This method doesn't have to be particularly efficient since it's off the critical path.
    pub fn asn4_lookup(conn: &DBConn, addrbits: &PeerAddress) -> Result<Option<u32>, db_error> {
        // must be an IPv4 address
        if !addrbits.is_ipv4() {
            return Err(db_error::TypeError);
        }

        // NOTE: sqlite3 will use the machine's endianness here
        let addr_u32 = addrbits.ipv4_bits().unwrap();

        let qry = "SELECT * FROM asn4 WHERE prefix = (?1 & ~((1 << (32 - mask)) - 1)) ORDER BY prefix DESC LIMIT 1".to_string();
        let args = [&addr_u32 as &dyn ToSql];
        let rows = query_rows::<ASEntry4, _>(conn, &qry, &args)?;
        match rows.len() {
            0 => Ok(None),
            _ => Ok(Some(rows[0].asn)),
        }
    }

    /// Classify an IP address to its AS number
    pub fn asn_lookup(conn: &DBConn, addrbits: &PeerAddress) -> Result<Option<u32>, db_error> {
        if addrbits.is_ipv4() {
            PeerDB::asn4_lookup(conn, addrbits)
        } else {
            // TODO
            Ok(None)
        }
    }

    /// Count the number of nodes in a given AS
    pub fn asn_count(conn: &DBConn, asn: u32) -> Result<u64, db_error> {
        let qry = "SELECT COUNT(*) FROM frontier WHERE asn = ?1".to_string();
        let args = [&asn as &dyn ToSql];
        let count = query_count(conn, &qry, &args)?;
        Ok(count as u64)
    }

    pub fn get_frontier_size(conn: &DBConn) -> Result<u64, db_error> {
        let qry = "SELECT COUNT(*) FROM frontier".to_string();
        let count = query_count(conn, &qry, NO_PARAMS)?;
        Ok(count as u64)
    }

    pub fn get_all_peers(conn: &DBConn) -> Result<Vec<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier ORDER BY addrbytes ASC, port ASC".to_string();
        let rows = query_rows::<Neighbor, _>(conn, &qry, NO_PARAMS)?;
        Ok(rows)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use net::Neighbor;
    use net::NeighborKey;
    use net::PeerAddress;

    #[test]
    fn test_local_peer() {
        let db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![],
        )
        .unwrap();
        let local_peer = PeerDB::get_local_peer(db.conn()).unwrap();

        assert_eq!(local_peer.network_id, 0x9abcdef0);
        assert_eq!(local_peer.parent_network_id, 12345);
        assert_eq!(local_peer.private_key_expire, 0);
        assert_eq!(
            local_peer.data_url,
            UrlString::try_from("http://foo.com".to_string()).unwrap()
        );
        assert_eq!(local_peer.port, NETWORK_P2P_PORT);
        assert_eq!(local_peer.addrbytes, PeerAddress::from_ipv4(127, 0, 0, 1));
        assert_eq!(local_peer.services, ServiceFlags::RELAY as u16);
    }

    #[test]
    fn test_peer_insert_and_retrieval() {
        let neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![],
        )
        .unwrap();

        let neighbor_before_opt = PeerDB::get_peer(
            db.conn(),
            0x9abcdef0,
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f,
            ]),
            12345,
        )
        .unwrap();
        assert_eq!(neighbor_before_opt, None);

        {
            let mut tx = db.tx_begin().unwrap();
            PeerDB::insert_or_replace_peer(&mut tx, &neighbor, 0).unwrap();
            tx.commit().unwrap();
        }

        let neighbor_opt = PeerDB::get_peer(
            db.conn(),
            0x9abcdef0,
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f,
            ]),
            12345,
        )
        .unwrap();
        assert_eq!(neighbor_opt, Some(neighbor.clone()));

        let neighbor_at_opt = PeerDB::get_peer_at(db.conn(), 0x9abcdef0, 0).unwrap();
        assert_eq!(neighbor_at_opt, Some(neighbor.clone()));

        let neighbor_not_at_opt = PeerDB::get_peer_at(db.conn(), 0x9abcdef0, 1).unwrap();
        assert_eq!(neighbor_not_at_opt, None);

        let neighbor_not_at_opt_network = PeerDB::get_peer_at(db.conn(), 0x9abcdef1, 0).unwrap();
        assert_eq!(neighbor_not_at_opt_network, None);

        {
            let mut tx = db.tx_begin().unwrap();
            PeerDB::insert_or_replace_peer(&mut tx, &neighbor, 0).unwrap();
            tx.commit().unwrap();
        }
    }

    #[test]
    fn test_try_insert_peer() {
        let neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![],
        )
        .unwrap();

        {
            let mut tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&mut tx, &neighbor).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, true);
        }

        let neighbor_opt = PeerDB::get_peer(
            db.conn(),
            0x9abcdef0,
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f,
            ]),
            12345,
        )
        .unwrap();
        assert_eq!(neighbor_opt, Some(neighbor.clone()));

        {
            let mut tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&mut tx, &neighbor).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, false);
        }
    }

    #[test]
    fn test_initial_neighbors() {
        let mut initial_neighbors = vec![];
        let now_secs = util::get_epoch_time_secs();
        for i in 0..10 {
            initial_neighbors.push(Neighbor {
                addr: NeighborKey {
                    peer_version: 0x12345678,
                    network_id: 0x9abcdef0,
                    addrbytes: PeerAddress([i as u8; 16]),
                    port: i,
                },
                public_key: Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new()),
                expire_block: (i + 23456) as u64,
                last_contact_time: (1552509642 + (i as u64)) as u64,
                allowed: (now_secs + 600) as i64,
                denied: -1,
                asn: (34567 + i) as u32,
                org: (45678 + i) as u32,
                in_degree: 1,
                out_degree: 1,
            });
        }

        for i in 10..20 {
            initial_neighbors.push(Neighbor {
                addr: NeighborKey {
                    peer_version: 0x12345678,
                    network_id: 0x9abcdef0,
                    addrbytes: PeerAddress([i as u8; 16]),
                    port: i,
                },
                public_key: Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new()),
                expire_block: (i + 23456) as u64,
                last_contact_time: (1552509642 + (i as u64)) as u64,
                allowed: 0,
                denied: -1,
                asn: (34567 + i) as u32,
                org: (45678 + i) as u32,
                in_degree: 1,
                out_degree: 1,
            });
        }

        fn are_present(ne: &Vec<Neighbor>, nei: &Vec<Neighbor>) -> bool {
            for n in ne {
                let mut found = false;
                for ni in nei {
                    if *n == *ni {
                        found = true;
                        break;
                    }
                }
                if !found {
                    return false;
                }
            }
            return true;
        }

        let db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &initial_neighbors,
        )
        .unwrap();

        let n5 = PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 5, 23455).unwrap();
        assert!(are_present(&n5, &initial_neighbors));

        let n10 = PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 10, 23455).unwrap();
        assert!(are_present(&n10, &initial_neighbors));

        let n20 = PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 20, 23455).unwrap();
        assert!(are_present(&initial_neighbors, &n20));

        let n15_fresh =
            PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 15, 23456 + 14).unwrap();
        assert!(are_present(
            &n15_fresh[10..15].to_vec(),
            &initial_neighbors[10..20].to_vec()
        ));
        for n in &n15_fresh[10..15] {
            assert!(n.expire_block > 23456 + 14);
            assert!(n.allowed == 0);
        }

        for neighbor in &initial_neighbors {
            assert!(PeerDB::is_initial_peer(
                db.conn(),
                neighbor.addr.network_id,
                &neighbor.addr.addrbytes,
                neighbor.addr.port
            )
            .unwrap());
        }
    }

    #[test]
    fn asn4_insert_lookup() {
        let asn4_table = vec![
            ASEntry4 {
                prefix: 0x01020200,
                mask: 24,
                asn: 1,
                org: 0,
            },
            ASEntry4 {
                prefix: 0x01020200,
                mask: 23,
                asn: 2,
                org: 0,
            },
            ASEntry4 {
                prefix: 0x01020000,
                mask: 16,
                asn: 3,
                org: 0,
            },
            ASEntry4 {
                prefix: 0x02030000,
                mask: 16,
                asn: 4,
                org: 0,
            },
        ];

        let db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &asn4_table,
            &vec![],
        )
        .unwrap();

        let asn1_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x01, 0x02,
            0x02, 0x04,
        ]);
        let asn2_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x01, 0x02,
            0x03, 0x10,
        ]);
        let asn3_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x01, 0x02,
            0x13, 0x10,
        ]);
        let asn4_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x02, 0x03,
            0x13, 0x10,
        ]);

        // classify addresses
        let asn1_opt = PeerDB::asn4_lookup(db.conn(), &asn1_addr).unwrap();
        assert_eq!(asn1_opt, Some(1));

        let asn2_opt = PeerDB::asn4_lookup(db.conn(), &asn2_addr).unwrap();
        assert_eq!(asn2_opt, Some(2));

        let asn3_opt = PeerDB::asn4_lookup(db.conn(), &asn3_addr).unwrap();
        assert_eq!(asn3_opt, Some(3));

        let asn4_opt = PeerDB::asn4_lookup(db.conn(), &asn4_addr).unwrap();
        assert_eq!(asn4_opt, Some(4));

        // invalid -- not an ipv4 address
        let asn4_invalid_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0xff, 0xff, 0x02, 0x03,
            0x13, 0x10,
        ]);
        let asn_invalid_opt = PeerDB::asn4_lookup(db.conn(), &asn4_invalid_addr);
        match asn_invalid_opt {
            Ok(_) => assert!(false),
            Err(db_error::TypeError) => assert!(true),
            Err(_) => assert!(false),
        }

        // not present
        let asn4_missing_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x02, 0x04,
            0x13, 0x10,
        ]);
        let asn_missing_opt = PeerDB::asn4_lookup(db.conn(), &asn4_missing_addr).unwrap();
        assert_eq!(asn_missing_opt, None);
    }

    #[test]
    fn test_peer_preemptive_deny_allow() {
        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![],
        )
        .unwrap();
        {
            let mut tx = db.tx_begin().unwrap();
            PeerDB::set_deny_peer(
                &mut tx,
                0x9abcdef0,
                &PeerAddress([0x1; 16]),
                12345,
                10000000,
            )
            .unwrap();
            PeerDB::set_allow_peer(
                &mut tx,
                0x9abcdef0,
                &PeerAddress([0x2; 16]),
                12345,
                20000000,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let peer_denied = PeerDB::get_peer(db.conn(), 0x9abcdef0, &PeerAddress([0x1; 16]), 12345)
            .unwrap()
            .unwrap();
        let peer_allowed = PeerDB::get_peer(db.conn(), 0x9abcdef0, &PeerAddress([0x2; 16]), 12345)
            .unwrap()
            .unwrap();

        assert_eq!(peer_denied.denied, 10000000);
        assert_eq!(peer_allowed.allowed, 20000000);
    }

    #[test]
    fn test_peer_cidr_lists() {
        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![],
        )
        .unwrap();
        {
            let mut tx = db.tx_begin().unwrap();
            PeerDB::add_cidr_prefix(&mut tx, "denied_prefixes", &PeerAddress([0x1; 16]), 64)
                .unwrap();
            PeerDB::add_cidr_prefix(&mut tx, "allowed_prefixes", &PeerAddress([0x2; 16]), 96)
                .unwrap();
            tx.commit().unwrap();
        }

        let deny_cidrs = PeerDB::get_denied_cidrs(db.conn()).unwrap();
        let allow_cidrs = PeerDB::get_allowed_cidrs(db.conn()).unwrap();

        assert_eq!(deny_cidrs, vec![(PeerAddress([0x1; 16]), 64)]);
        assert_eq!(allow_cidrs, vec![(PeerAddress([0x2; 16]), 96)]);
    }

    #[test]
    fn test_peer_is_denied() {
        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![],
        )
        .unwrap();
        {
            let mut tx = db.tx_begin().unwrap();
            PeerDB::add_deny_cidr(
                &mut tx,
                &PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00,
                ]),
                64,
            )
            .unwrap();
            PeerDB::add_deny_cidr(
                &mut tx,
                &PeerAddress([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x11,
                    0x22, 0x33, 0x44,
                ]),
                128,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        assert!(PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(!PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(!PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x11, 0x22,
                0x33, 0x44
            ])
        )
        .unwrap());
        assert!(!PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x11, 0x22,
                0x33, 0x45
            ])
        )
        .unwrap());
    }

    #[test]
    fn test_peer_deny_allow_cidr() {
        let neighbor_1 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 12345,
            denied: 67890,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let neighbor_2 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
                    0x1d, 0x1e, 0x1f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02287c1f1b280b5dde764b146976f6bad3fb485a3df9b1ad2d8ddc5719e7e91ff2",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 12345,
            denied: 67890,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![neighbor_1.clone(), neighbor_2.clone()],
        )
        .unwrap();

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        assert_eq!(n1.allowed, 12345);
        assert_eq!(n1.denied, 67890);

        {
            // ban peer 1 by banning a prefix
            let mut tx = db.tx_begin().unwrap();
            PeerDB::add_deny_cidr(
                &mut tx,
                &PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00,
                ]),
                64,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();
        assert_eq!(n1.allowed, 12345);
        assert_eq!(n1.denied, i64::max_value());
        assert_eq!(n2.allowed, 12345);
        assert_eq!(n2.denied, 67890);

        {
            // unban peer 1 by unbanning a (different) prefix
            let mut tx = db.tx_begin().unwrap();
            PeerDB::add_allow_cidr(
                &mut tx,
                &PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00,
                ]),
                48,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();

        assert_eq!(n1.allowed, -1);
        assert_eq!(n1.denied, i64::max_value());
        assert_eq!(n2.allowed, 12345);
        assert_eq!(n2.denied, 67890);
    }

    #[test]
    fn test_peer_refresh_cidr() {
        let neighbor_1 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 1234,
            denied: 5678,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let neighbor_2 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
                    0x1d, 0x1e, 0x1f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02287c1f1b280b5dde764b146976f6bad3fb485a3df9b1ad2d8ddc5719e7e91ff2",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 1234,
            denied: 5678,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &vec![],
            &vec![neighbor_1.clone(), neighbor_2.clone()],
        )
        .unwrap();
        {
            let mut tx = db.tx_begin().unwrap();
            PeerDB::add_cidr_prefix(&mut tx, "denied_prefixes", &PeerAddress([0x00; 16]), 8)
                .unwrap();
            PeerDB::add_cidr_prefix(&mut tx, "allowed_prefixes", &PeerAddress([0x01; 16]), 8)
                .unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();

        assert_eq!(n1.denied, 5678);
        assert_eq!(n2.denied, 5678);

        assert_eq!(n1.allowed, 1234);
        assert_eq!(n2.allowed, 1234);

        {
            let mut tx = db.tx_begin().unwrap();
            PeerDB::refresh_denies(&mut tx).unwrap();
            PeerDB::refresh_allows(&mut tx).unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();

        assert_eq!(n1.denied, i64::max_value());
        assert_eq!(n2.denied, 0); // refreshed; no longer denied

        assert_eq!(n1.allowed, -1);
        assert_eq!(n2.allowed, -1);
    }
}
