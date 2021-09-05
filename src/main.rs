// TODO: add comments
use std::env;
use cpu::*;

mod cpu;
mod bus;

fn main() {
  let args: Vec<String> = env::args().collect();
  if args.len() != 2 {
    println!("引数の数が不正です。");
    println!("引数にはRISC-Vの実行バイナリを指定してください。");
    return;
  }

  let mut cpu = Cpu::new(&args[1], false);

  // entry point
  cpu.pc = 0x80000000;

  let mut clk = 0;
  loop {
    match clk {
      0 => {
        cpu.fetch().expect(&format!("fetchに失敗: at pc=0x{:>08x}", cpu.pc));
      },
      1 => {
        cpu.decode().expect(&format!("decodeに失敗: at pc=0x{:>08x}", cpu.pc));
      },
      2 => {
        cpu.execute().expect(&format!("executeに失敗: at pc=0x{:>08x}", cpu.pc));
      },
      3 => {
        cpu.memory_access().expect(&format!("memory_accessに失敗: at pc=0x{:>08x}", cpu.pc));
      },
      4 => {
        cpu.writeback().expect(&format!("writebackに失敗: at pc=0x{:>08x}", cpu.pc));
      },
      _ => (),
    }
    clk = (clk + 1) % 5;
  }
}
