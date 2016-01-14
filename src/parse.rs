extern crate byteorder;
extern crate regex;

use super::{Type, Timezone, Transition, TransRule, GenericDay};

use std::rc::Rc;
use std::io::{self, Read, BufReader, Seek, SeekFrom};
use std::fs::File;
use std::path::PathBuf;
use self::byteorder::{BigEndian, ByteOrder};
use std::str;

macro_rules! e_invalid {
    ($($arg:tt)*) => {
        io::Error::new(io::ErrorKind::InvalidData, format!($($arg)*))
    }
}
macro_rules! invalid {
    ($($arg:tt)*) => {
        Err(e_invalid!($($arg)*))
    }
}

pub fn load_timezone(timezone: &str) -> io::Result<Timezone> {
    let mut filename = PathBuf::from("/usr/share/zoneinfo");
    filename.push(timezone);
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
        2 => {
            // We're skipping the entire v1 file since
            // at least the same data will be found in TZFile 2.
            let to_skip = hdr.transitions * 5 + hdr.types * 6 + hdr.abbr_size * 1 +
                          hdr.leaps * 4 + hdr.stdwalls * 1 +
                          hdr.utclocals * 1;
            try!(skip(&mut r, to_skip));

            // Parse the second header.
            let hdr = try!(parse_header(&mut r));
            if hdr.version != 2 {
                return invalid!("expected TZfile2");
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

    let types: Vec<Rc<Type>> = types.iter()
                                    .map(|&(off, is_dst, abbr_idx)| {
                                        Rc::new(Type {
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

fn parse_header<R: io::Read>(mut r: R) -> io::Result<Header> {
    let mut buff = [0u8; 44];
    try!(r.read_exact(&mut buff[..]));

    match str::from_utf8(&buff[..4]) {
        Ok("TZif") => (),
        Ok(_) => return invalid!("not a TZfile"),
        Err(_) => return invalid!("garbage file header"),
    }

    let version = match buff[4] {
        0x00 => 1,
        0x32 => 2,
        0x33 => return invalid!("version 3 is not supported"),
        v => return invalid!("unknown version {:X}", v),
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

fn parse_trans_32<R: io::Read>(mut r: R, n: i32) -> io::Result<Vec<i64>> {
    let mut trans = Vec::with_capacity(n as usize);
    let mut buff = [0u8; 4];
    for _ in 0..n {
        try!(r.read_exact(&mut buff[..]));
        let t = BigEndian::read_i32(&buff[..]);
        trans.push(t as i64);
    }
    Ok(trans)
}

fn parse_trans_64<R: io::Read>(mut r: R, n: i32) -> io::Result<Vec<i64>> {
    let mut trans = Vec::with_capacity(n as usize);
    let mut buff = [0u8; 8];
    for _ in 0..n {
        try!(r.read_exact(&mut buff[..]));
        let t = BigEndian::read_i64(&buff[..]);
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

fn parse_posix_tz<R: io::Read>(mut r: R) -> io::Result<TransRule> {
    let mut s = String::new();
    try!(r.read_to_string(&mut s));

    // This f**king format... sorry for the regex.
    // std offset[dst[offset][,start[/time],end[/time]]]
    let re = regex::Regex::new("^\\n(?P<std>[A-Z]{3,})(?P<stdoff>[+-]?[0-9]+(:[0-9]+(:\
                                [0-9]+)?)?)((?P<dst>[A-Z]{3,})(?P<dstoff>[+-]?[0-9]+(:[0-9]+(:\
                                [0-9]+)?)?)?)?(,(?P<start>J[0-9]{1,3}|[0-9]{1,3}|M[0-9]{1,2}[.\
                                ][0-9][.][0-9])(/(?P<stime>[0-9]{1,2}(:[0-9]{1,2}(:[0-9]{1,\
                                2})?)?))?,(?P<end>J[0-9]{1,3}|[0-9]{1,3}|M[0-9]{1,2}[.][0-9][.\
                                ][0-9])(/(?P<etime>[0-9]{1,2}(:[0-9]{1,2}(:[0-9]{1,\
                                2})?)?))?)?\\n$")
                 .unwrap();
    let caps = match re.captures(&s[..]) {
        None => return invalid!("invalid POSIX TZ format: {}", s.replace("\n", "<LF>")),
        Some(caps) => caps,
    };

    let std_abbr = match caps.name("std") {
        None => return invalid!("missing mandatory std abbreviation"),
        Some(s) => s,
    };
    let std_off = match caps.name("stdoff") {
        None => return invalid!("missing mandatory std offset"),
        Some(o) => hhmmss_to_sec(o),
    };

    let ext = match caps.name("dst") {
        None => {
            TransRule::Fixed(Type {
                off: -std_off,
                is_dst: false,
                abbr: std_abbr.to_owned(),
            })
        }
        Some(dst_abbr) => {
            let dst_off = match caps.name("dstoff") {
                None => std_off - 3600,
                Some(o) => hhmmss_to_sec(o),
            };
            let start = transition_day(caps.name("start").unwrap());
            let start_time = hhmmss_to_sec(match caps.name("stime") {
                None => "02:00:00",
                Some(t) => t,
            });
            let end = transition_day(caps.name("end").unwrap());
            let end_time = hhmmss_to_sec(match caps.name("etime") {
                None => "02:00:00",
                Some(t) => t,
            });

            TransRule::Alternate {
                dst_start: start,
                dst_stime: start_time,
                dst_end: end,
                dst_etime: end_time,
                std: Type {
                    off: -std_off,
                    is_dst: false,
                    abbr: std_abbr.to_owned(),
                },
                dst: Type {
                    off: -dst_off,
                    is_dst: true,
                    abbr: dst_abbr.to_owned(),
                },
            }
        }
    };

    Ok(ext)
}

fn hhmmss_to_sec(s: &str) -> i32 {
    // [+-]?hh[:mm[:ss]]
    let re = regex::Regex::new("^(?P<hour>[+-]?[0-9]{1,2})(:(?P<minute>[0-9]{1,2})(:\
                                (?P<second>[0-9]{1,2}))?)?$")
                 .unwrap();

    // We can unwrap because the syntax has been verified by the regex.
    let caps = re.captures(&s[..]).unwrap();
    let hour = caps.name("hour").unwrap().parse::<i32>().unwrap();
    let minute = caps.name("minute").unwrap_or("0").parse::<i32>().unwrap();
    let second = caps.name("second").unwrap_or("0").parse::<i32>().unwrap();
    hour * 3600 + minute * 60 + second
}

fn transition_day(s: &str) -> GenericDay {
    // Unwrapping is safe because the syntax has been verified by the caller.
    match s.chars().next().unwrap() {
        'J' => GenericDay::Julian1 { jday: (&s[1..]).parse::<i32>().unwrap() },
        'M' => {
            let mut comp = (&s[1..]).split('.');
            GenericDay::MWDRule {
                month: comp.next().unwrap().parse::<i32>().unwrap(),
                week: comp.next().unwrap().parse::<i32>().unwrap(),
                wday: comp.next().unwrap().parse::<i32>().unwrap(),
            }
        }
        _ => GenericDay::Julian0 { jday: s.parse::<i32>().unwrap() },
    }
}

fn skip<R: io::Seek>(mut r: R, len: i32) -> io::Result<()> {
    try!(r.seek(SeekFrom::Current(len as i64)));
    Ok(())
}
