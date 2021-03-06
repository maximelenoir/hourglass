extern crate byteorder;

use super::{Type, Timezone, Transition, TransRule, TzError, posixtz};
use super::nom::IResult;

use std::sync::Arc;
use std::io::{Read, BufReader, Seek, SeekFrom};
use std::fs::File;
use std::path::PathBuf;
use self::byteorder::{BigEndian, ByteOrder};
use std::str;

pub fn load_timezone(timezone: &str) -> Result<Timezone, TzError> {
    let filename = match timezone {
        // os x doesn't symlink this from /usr/share/zoneinfo
        "localtime" => PathBuf::from("/etc/localtime"),
        _ => {
            let mut filename = PathBuf::from("/usr/share/zoneinfo");
            filename.push(timezone);
            filename
        }
    };
    let filename = filename.as_path();

    let f = try!(File::open(filename));
    let mut r = BufReader::new(f);

    let hdr = try!(parse_header(&mut r));
    let (trans, type_idx, types, abbrs, trule) = match hdr.version {
        1 => {
            let trans = try!(parse_trans_32(&mut r, hdr.transitions));
            let type_idx = try!(parse_type_idx(&mut r, hdr.transitions));
            let types = try!(parse_types(&mut r, hdr.types));
            let abbrs = try!(parse_abbrs(&mut r, hdr.abbr_size));
            (trans, type_idx, types, abbrs, None)
        }
        2 | 3 => {
            // We're skipping the entire v1 file since
            // at least the same data will be found in TZFile 2.
            let to_skip = hdr.transitions * 5 + hdr.types * 6 + hdr.abbr_size * 1 +
                          hdr.leaps * 4 + hdr.stdwalls * 1 +
                          hdr.utclocals * 1;
            try!(skip(&mut r, to_skip));

            // Parse the second header.
            let hdr = try!(parse_header(&mut r));
            if hdr.version != 2 && hdr.version != 3 {
                return Err(TzError::InvalidTzFile);
            }

            // Parse the v2 data.
            let trans = try!(parse_trans_64(&mut r, hdr.transitions));
            let type_idx = try!(parse_type_idx(&mut r, hdr.transitions));
            let types = try!(parse_types(&mut r, hdr.types));
            let abbrs = try!(parse_abbrs(&mut r, hdr.abbr_size));
            let to_skip = hdr.leaps * 8 + hdr.stdwalls * 1 + hdr.utclocals * 1;
            try!(skip(&mut r, to_skip));
            let trule = try!(parse_posix_tz(&mut r));
            (trans, type_idx, types, abbrs, Some(trule))
        }
        _ => unreachable!(),
    };

    let types: Vec<Arc<Type>> = types.iter()
                                    .map(|&(off, is_dst, abbr_idx)| {
                                        Arc::new(Type {
                                            off: off,
                                            is_dst: is_dst,
                                            abbr: abbrs.iter()
                                                       .find(|&&(idx, _)| idx == abbr_idx)
                                                       .map(|&(_, ref a)| a)
                                                       .unwrap()
                                                       .clone(),
                                        })
                                    })
                                    .collect();

    Ok(Timezone {
        trans: trans.iter()
                    .zip(type_idx.iter())
                    .map(|(&tran, &typ_idx)| {
                        Transition {
                            utc: tran as i64,
                            ttype: types[typ_idx as usize].clone(),
                        }
                    })
                    .collect(),
        trule: trule,
    })
}

struct Header {
    version: u8,
    utclocals: i32,
    stdwalls: i32,
    leaps: i32,
    transitions: i32,
    types: i32,
    abbr_size: i32,
}

fn parse_header<R: Read>(mut r: R) -> Result<Header, TzError> {
    let mut buff = [0u8; 44];
    try!(r.read_exact(&mut buff[..]));

    match str::from_utf8(&buff[..4]) {
        Ok("TZif") => (),
        _ => return Err(TzError::InvalidTzFile),
    }

    let version = match buff[4] {
        0x00 => 1,
        0x32 => 2,
        0x33 => 3,
        _ => return Err(TzError::UnsupportedTzFile),
    };

    Ok(Header {
        version: version,
        utclocals: BigEndian::read_i32(&buff[20..24]),
        stdwalls: BigEndian::read_i32(&buff[24..28]),
        leaps: BigEndian::read_i32(&buff[28..32]),
        transitions: BigEndian::read_i32(&buff[32..36]),
        types: BigEndian::read_i32(&buff[36..40]),
        abbr_size: BigEndian::read_i32(&buff[40..44]),
    })
}

fn parse_trans_32<R: Read>(mut r: R, n: i32) -> Result<Vec<i64>, TzError> {
    let mut trans = Vec::with_capacity(n as usize);
    let mut buff = [0u8; 4];
    for _ in 0..n {
        try!(r.read_exact(&mut buff[..]));
        let t = BigEndian::read_i32(&buff[..]);
        trans.push(t as i64);
    }
    Ok(trans)
}

fn parse_trans_64<R: Read>(mut r: R, n: i32) -> Result<Vec<i64>, TzError> {
    let mut trans = Vec::with_capacity(n as usize);
    let mut buff = [0u8; 8];
    for _ in 0..n {
        try!(r.read_exact(&mut buff[..]));
        let t = BigEndian::read_i64(&buff[..]);
        trans.push(t);
    }
    Ok(trans)
}

fn parse_type_idx<R: Read>(mut r: R, n: i32) -> Result<Vec<u8>, TzError> {
    let mut idx = vec![0u8; n as usize];
    try!(r.read_exact(&mut idx[..]));
    Ok(idx)
}

fn parse_types<R: Read>(mut r: R, n: i32) -> Result<Vec<(i32, bool, u8)>, TzError> {
    let mut types = Vec::with_capacity(n as usize);
    let mut buff = [0u8; 6];
    for _ in 0..n {
        try!(r.read_exact(&mut buff[..]));
        types.push((BigEndian::read_i32(&buff[0..4]), buff[4] != 1, buff[5]));
    }
    Ok(types)
}

fn parse_abbrs<R: Read>(mut r: R, len: i32) -> Result<Vec<(u8, String)>, TzError> {
    let mut buff = vec![0u8; len as usize];
    try!(r.read_exact(&mut buff[..]));

    let mut abbrs = vec![];
    let mut idx = 0;
    for (i, _) in buff.iter().enumerate().filter(|&(_, &c)| c == 0) {
        let abbr = (&buff[idx..i]).to_owned();
        let abbr = match String::from_utf8(abbr) {
            Err(_) => return Err(TzError::InvalidTzFile),
            Ok(a) => a,
        };
        abbrs.push((idx as u8, abbr));
        idx = i + 1;
    }

    Ok(abbrs)
}

fn parse_posix_tz<R: Read>(mut r: R) -> Result<TransRule, TzError> {
    let mut s = String::new();
    try!(r.read_to_string(&mut s));

    if !s.starts_with('\n') || !s.ends_with('\n') {
        return Err(TzError::InvalidTzFile);
    }

    match posixtz(s.trim()) {
        IResult::Done(_, t) => Ok(t),
        IResult::Error(_) => Err(TzError::InvalidPosixTz),
        IResult::Incomplete(_) => Err(TzError::InvalidPosixTz),
    }
}

fn skip<R: Seek>(mut r: R, len: i32) -> Result<(), TzError> {
    try!(r.seek(SeekFrom::Current(len as i64)));
    Ok(())
}
