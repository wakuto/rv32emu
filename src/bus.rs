use std::io::prelude::*;
use super::cpu::Exception;

#[derive(Debug)]
pub struct Uart {
  tx_buf: u8,
  rx_buf: u8,
}

impl Uart {
  fn read(&self, addr: usize) -> Result<u8, Exception> {
    Ok(match addr {
      0x10010004..=0x10010007 => {
        if addr == 0x10010004 {
          self.rx_buf
        } else {
          0
        }
      },
      _ => return Err(Exception::IllegalMemoryAccess(addr as u32)),
    })
  }

  fn write(&mut self, addr: usize, data: u8) -> Result<(), Exception> {
    match addr {
      0x10010000..=0x10010003 => {
        if addr == 0x10010000 {
          self.tx_buf = data;
          print!("{}", (data as char).to_string());
          std::io::stdout().flush().unwrap();
        }
      },
      _ => return Err(Exception::IllegalMemoryAccess(addr as u32)),
    }
    Ok(())
  }
}

#[derive(Debug)]
pub struct Ram {
  pub data: Vec<u8>,
}

pub const RAM_SIZE: usize = 1024 * 1024 * 512;

impl Ram {
  pub fn new() -> Ram {
    Ram { data: vec![0; RAM_SIZE] }
  }

  fn read(&self, addr: usize) -> Result<u8, Exception> {
    Ok(match addr-0x80000000 {
      0x00000000..=RAM_SIZE => self.data[addr-0x80000000],
      _ => return Err(Exception::IllegalMemoryAccess(addr as u32)),
    })
  }

  fn write(&mut self, addr: usize, data: u8) -> Result<(), Exception> {
    match addr-0x80000000 {
      0x00000000..=RAM_SIZE => self.data[addr-0x80000000] = data,
      _ => return Err(Exception::IllegalMemoryAccess(addr as u32)),
    }
    Ok(())
  }
}

#[derive(Debug)]
pub struct Rom {
  data: Vec<u8>,
}

impl Rom {
  pub fn new() -> Rom {
    Rom { data: vec![0; ROM_SIZE] }
  }

  fn read(&self, addr: usize) -> Result<u8, Exception> {
    Ok(match addr-0x1000 {
      0x00000000..=ROM_SIZE => self.data[addr-0x1000],
      _ => return Err(Exception::IllegalMemoryAccess(addr as u32)),
    })
  }
}

#[derive(Debug)]
pub struct Bus {
  pub ram: Ram,
  pub rom: Rom,
  pub uart: Uart,
}

pub const ROM_SIZE: usize = 0xF000;

impl Bus {
  pub fn new() -> Bus {
    Bus {
      ram: Ram::new(),
      rom: Rom::new(),
      uart: Uart { tx_buf: 0, rx_buf: 0 },
    }
  }
  pub fn read(&self, addr: usize) -> Result<u8, Exception> {
    match addr {
      // mrom
      0x1000..=0xFFFF => self.rom.read(addr),
      // uart
      0x10010000..=0x10010FFF => self.uart.read(addr),
      // dram
      0x80000000..=0xFFFFFFFF => self.ram.read(addr),
      _ => return Err(Exception::IllegalMemoryAccess(addr as u32)),
    }
  }

  pub fn write(&mut self, addr: usize, data: u8) -> Result<(), Exception> {
    match addr {
      // uart
      0x10010000..=0x10010FFF => self.uart.write(addr, data),
      // dram
      0x80000000..=0xFFFFFFFF => self.ram.write(addr, data),
      _ => return Err(Exception::IllegalMemoryAccess(addr as u32)),
    }
  }
}

