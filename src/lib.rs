use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::num::ParseIntError;
use std::str::FromStr;

#[derive(Debug)]
pub enum ErrorKind {
	InvalidSyntax,
	InvalidNumeral(ParseIntError),
	MissingSection,
	Empty,
}

#[derive(Debug)]
pub struct Error {
	pub kind: ErrorKind,
	pub line: u32,
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{:?} at line {}", self.kind, self.line)
	}
}

#[allow(non_camel_case_types)]
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Arch {
	any,
	unknown,
	x86_64,
	i686,
	pentium4,
	arm,
	armv6h,
	armv7h,
	aarch64,
}

impl FromStr for Arch {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		use self::Arch::*;

		Ok(match s {
			"x86_64" => x86_64,
			"i686" => i686,
			"pentium4" => pentium4,
			"arm" => arm,
			"armv6h" => armv6h,
			"armv7h" => armv7h,
			"aarch64" => aarch64,
			&_ => unknown,
		})
	}
}

#[derive(Debug, Default)]
pub struct Section {
	pub pkgver: Option<String>,
	pub pkgrel: Option<String>,

	pub epoch: Option<u64>,

	pub pkgdesc: Option<String>,
	pub url: Option<String>,
	pub install: Option<String>,
	pub changelog: Option<String>,

	pub arch: Vec<Arch>,
	pub groups: Vec<String>,
	pub license: Vec<String>,
	pub noextract: Vec<String>,
	pub options: Vec<String>,
	pub backup: Vec<String>,
	pub validpgpkeys: Vec<String>,

	pub source: HashMap<Arch, Vec<String>>,

	pub depends: Vec<String>,
	pub checkdepends: Vec<String>,
	pub makedepends: Vec<String>,
	pub optdepends: Vec<String>,

	pub provides: Vec<String>,
	pub conflicts: Vec<String>,
	pub replaces: Vec<String>,

	pub md5sums: Vec<String>,
	pub sha1sums: Vec<String>,
	pub sha224sums: Vec<String>,
	pub sha256sums: Vec<String>,
	pub sha384sums: Vec<String>,
	pub sha512sums: Vec<String>,
}

#[derive(Debug, Default)]
pub struct SRCINFO {
	pub pkgbase: HashMap<String, Section>,

	pub pkgname: HashMap<String, Section>,
}

impl SRCINFO {
	fn match_key(s: &mut Section, p: (&str, &str)) -> Result<(), ErrorKind> {
		let k = p.0;
		let v = p.1;

		match k {
			"pkgver" => s.pkgver = Some(String::from(v)),
			"pkgrel" => s.pkgrel = Some(String::from(v)),

			"epoch" => {
				s.epoch = Some(match v.parse() {
					Ok(v) => v,
					Err(e) => return Err(ErrorKind::InvalidNumeral(e)),
				});
			}

			"pkgdesc" => s.pkgdesc = Some(String::from(v)),
			"url" => s.url = Some(String::from(v)),
			"install" => s.install = Some(String::from(v)),
			"changelog" => s.changelog = Some(String::from(v)),
			"arch" => s.arch.push(Arch::from_str(v).unwrap()),
			"groups" => s.groups.push(String::from(v)),
			"license" => s.license.push(String::from(v)),
			"noextract" => s.noextract.push(String::from(v)),
			"options" => s.options.push(String::from(v)),
			"backup" => s.backup.push(String::from(v)),
			"validpgpkeys" => s.validpgpkeys.push(String::from(v)),

			"depends" => s.depends.push(String::from(v)),
			"checkdepends" => s.checkdepends.push(String::from(v)),
			"makedepends" => s.makedepends.push(String::from(v)),
			"optdepends" => s.optdepends.push(String::from(v)),
			"provides" => s.provides.push(String::from(v)),
			"conflicts" => s.conflicts.push(String::from(v)),
			"replaces" => s.replaces.push(String::from(v)),
			"md5sums" => s.md5sums.push(String::from(v)),
			"sha1sums" => s.sha1sums.push(String::from(v)),
			"sha224sums" => s.sha224sums.push(String::from(v)),
			"sha256sums" => s.sha256sums.push(String::from(v)),
			"sha384sums" => s.sha384sums.push(String::from(v)),
			"sha512sums" => s.sha512sums.push(String::from(v)),

			"source" => s.source.entry(Arch::any).or_default().push(String::from(v)),
			_ => {
				if k.starts_with("source_") {
					s.source
						.entry(Arch::from_str(&k[7..]).unwrap())
						.or_default()
						.push(String::from(v));
				}
			}
		}

		Ok(())
	}

	fn parse_key_value<'a>(s: &'a str) -> Result<(&'a str, &'a str), ErrorKind> {
		if let Some((k, v)) = s.split_once('=') {
			let k = k.trim();
			let v = v.trim();

			if k.is_empty() || v.is_empty() {
				return Err(ErrorKind::InvalidSyntax);
			}

			return Ok((k, v));
		} else {
			return Err(ErrorKind::InvalidSyntax);
		}
	}

	fn parse_impl<T>(lines: T) -> Result<Self, Error>
	where
		T: Iterator<Item = String>,
	{
		let mut info = SRCINFO::default();

		// this is just so we can avoid creating a new copy of Section
		let mut uninitialized: std::mem::MaybeUninit<Section> = std::mem::MaybeUninit::uninit();
		let mut section = unsafe { uninitialized.assume_init_mut() };
		let mut initialized: bool = false;

		let mut line_num: u32 = 0;

		for line in lines {
			line_num += 1;

			let line = line.trim();
			if line.is_empty() || line.starts_with('#') {
				continue;
			}

			let (k, v) = match Self::parse_key_value(line) {
				Err(e) => {
					return Err(Error {
						kind: e,
						line: line_num,
					});
				}
				Ok(v) => v,
			};

			match k {
				"pkgbase" => {
					initialized = true;
					section = info
						.pkgbase
						.entry(String::from(v))
						.or_insert(Section::default());
				}
				"pkgname" => {
					initialized = true;
					section = info
						.pkgname
						.entry(String::from(v))
						.or_insert(Section::default());
				}
				_ if !initialized => {
					return Err(Error {
						kind: ErrorKind::MissingSection,
						line: line_num,
					});
				}
				_ => match Self::match_key(section, (k, v)) {
					Ok(_) => {}
					Err(e) => {
						return Err(Error {
							kind: e,
							line: line_num,
						});
					}
				},
			}
		}

		if info.pkgbase.len() == 0 && info.pkgname.len() == 0 {
			return Err(Error {
				kind: ErrorKind::Empty,
				line: 0,
			});
		}

		Ok(info)
	}

	/// Parse data from a buffered reader object.
	///
	/// - Example:
	/// ```rust
	/// use std::io::{self, BufReader};
	/// use std::fs::File;
	///
	/// use srcinfo::SRCINFO;
	///
	/// fn main() -> io::Result<()> {
	/// 	let reader = BufReader::new(File::open("./.SRCINFO")?);
	///
	/// 	let srcinfo = SRCINFO::from_reader(reader).unwrap();
	///
	/// 	Ok(())
	/// }
	/// ```
	pub fn from_reader<T>(s: T) -> Result<Self, Error>
	where
		T: BufRead,
	{
		Self::parse_impl(s.lines().into_iter().map(|x| match x {
			Ok(v) => v,
			Err(_) => String::from(""),
		}))
	}

	/// Parse data from a file.
	///
	/// - Example:
	/// ```rust
	/// use std::fs::File;
	/// use std::io;
	///
	/// use srcinfo::SRCINFO;
	///
	/// fn main() -> io::Result<()> {
	/// 	let srcinfo = SRCINFO::from_file(File::open("./.SRCINFO")?).unwrap();
	///
	/// 	Ok(())
	/// }
	/// ```
	pub fn from_file(f: File) -> Result<Self, Error> {
		Self::from_reader(BufReader::new(f))
	}

	/// Parse data from a string in memory.
	///
	/// - Example:
	/// ```rust
	/// use srcinfo::SRCINFO;
	///
	/// fn main() {
	/// 	let data = String::from("pkgbase = foobar\npkgver=1.0.0")
	/// 	let srcinfo = SRCINFO::from_str(&data).unwrap();
	/// }
	/// ```
	pub fn from_str(s: &str) -> Result<Self, Error> {
		Self::parse_impl(s.lines().map(|x| String::from(x)))
	}
}

impl FromStr for SRCINFO {
	type Err = Error;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Self::from_str(s)
	}
}
