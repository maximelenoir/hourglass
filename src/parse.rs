extern crate byteorder;

use super::{Type, Timezone, Transition};

use std::rc::Rc;
use std::io::{self, Read, BufReader};
use std::fs::File;
use std::path::PathBuf;
use self::byteorder::{BigEndian, ByteOrder};
use std::str;

macro_rules! invalid {
    ($($arg:tt)*) => {
        Err(io::Error::new(io::ErrorKind::InvalidData, format!($($arg)*)));
    }
}

pub fn load_timezone(timezone: &str) -> io::Result<Timezone> {
    let mut filename = PathBuf::from("/usr/share/zoneinfo");
    filename.push(timezone);
    let filename = filename.as_path();

    let f = try!(File::open(filename));
    let mut r = BufReader::new(f);

    let hdr = try!(parse_header(&mut r));
    let trans = try!(parse_trans(&mut r, hdr.transitions));
    let type_idx = try!(parse_type_idx(&mut r, hdr.transitions));
    let types = try!(parse_types(&mut r, hdr.types));
    let abbrs = try!(parse_abbrs(&mut r, hdr.abbr_size));

    let types: Vec<Rc<Type>> = types.iter()
                                    .map(|&(off, is_dst, abbr_idx)| {
                                        Rc::new(Type {
                                            utc_off_sec: off,
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
        name: timezone.to_owned(),
        trans: trans.iter()
                    .zip(type_idx.iter())
                    .map(|(&tran, &typ_idx)| {
                        Transition {
                            utc: tran as i64,
                            ttype: types[typ_idx as usize].clone(),
                        }
                    })
                    .collect(),
    })
}

struct Header {
    _version: u8,
    transitions: i32,
    types: i32,
    abbr_size: i32,
}

fn parse_header<R: io::Read>(mut r: R) -> io::Result<Header> {
    let mut buff = [0u8; 44];
    try!(r.read_exact(&mut buff[..]));

    match str::from_utf8(&buff[..4]) {
        Ok("TZif") => (),
        Ok(_) => return invalid!("not a TZfile"),
        Err(_) => return invalid!("garbage file header"),
    }

    let version = match buff[4] {
        0x00 => 0,
        0x32 => 2,
        0x33 => return invalid!("version 3 is not supported"),
        v => return invalid!("unknown version {:X}", v),
    };

    Ok(Header {
        _version: version,
        transitions: BigEndian::read_i32(&buff[32..36]),
        types: BigEndian::read_i32(&buff[36..40]),
        abbr_size: BigEndian::read_i32(&buff[40..44]),
    })
}

fn parse_trans<R: io::Read>(mut r: R, n: i32) -> io::Result<Vec<i32>> {
    let mut trans = Vec::with_capacity(n as usize);
    let mut buff = [0u8; 4];
    for _ in 0..n {
        try!(r.read_exact(&mut buff[..]));
        let t = BigEndian::read_i32(&buff[..]);
        trans.push(t);
    }
    Ok(trans)
}

fn parse_type_idx<R: io::Read>(mut r: R, n: i32) -> io::Result<Vec<u8>> {
    let mut idx = vec![0u8; n as usize];
    try!(r.read_exact(&mut idx[..]));
    Ok(idx)
}

fn parse_types<R: io::Read>(mut r: R, n: i32) -> io::Result<Vec<(i32, bool, u8)>> {
    let mut types = Vec::with_capacity(n as usize);
    let mut buff = [0u8; 6];
    for _ in 0..n {
        try!(r.read_exact(&mut buff[..]));
        types.push((BigEndian::read_i32(&buff[0..4]), buff[4] != 1, buff[5]));
    }
    Ok(types)
}

fn parse_abbrs<R: io::Read>(mut r: R, len: i32) -> io::Result<Vec<(u8, String)>> {
    let mut buff = vec![0u8; len as usize];
    try!(r.read_exact(&mut buff[..]));

    let mut abbrs = vec![];
    let mut idx = 0;
    for (i, _) in buff.iter().enumerate().filter(|&(_, &c)| c == 0) {
        let abbr = (&buff[idx..i]).to_owned();
        let abbr = match String::from_utf8(abbr) {
            Err(e) => return invalid!("invalid abbrevation: {}", e),
            Ok(a) => a,
        };
        abbrs.push((idx as u8, abbr));
        idx = i + 1;
    }

    Ok(abbrs)
}
