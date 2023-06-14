use clap::Parser;
use ic::*;
use std::{fs, path::PathBuf};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
  /// Print elapsed time, rewrites, rewrites-per-second
  #[arg(short, long)]
  stats: bool,

  /// Print net after every reduction step
  #[arg(short, long)]
  debug: bool,

  /// Use fast dispatch for scott-encoded case matching when possible
  #[arg(short, long)]
  fast_dispatch: bool,

  /// File containing the source code of the program
  file_path: PathBuf,
}

fn main() {
  let args = Args::parse();
  DEBUG.set(args.debug).unwrap();

  let code = fs::read_to_string(&args.file_path).expect("Unable to read the file");

  let (term, function_book) = term::from_string(code.as_bytes());

  if args.stats {
    let (norm, reduction_count, elapsed_s) =
      term::normalize_with_stats(&term, &function_book, args.fast_dispatch);
    println!("{}\n", norm);

    let rps_m = reduction_count as f64 / elapsed_s / 1_000_000.0;
    println!("[TIME: {elapsed_s:.2}s | COST: {reduction_count} | RPS: {rps_m:.3}m]");
  } else {
    let norm = term::normalize(&term, &function_book, args.fast_dispatch);
    println!("{}", norm);
  }
}
