use std::fs::File;
use std::io::prelude::*;
use super::bus::{Bus, RAM_SIZE, ROM_SIZE};

#[derive(Clone, Copy, Debug)]
enum InstructionType {
  R,
  I,
  S,
  B,
  U,
  J,
}

#[derive(Clone, Copy, Debug)]
pub struct Instruction {
  ope_type: InstructionType,
  opecode: u8,
  rd:     Option<u8>,
  funct3: Option<u8>,
  rs1:    Option<u32>,
  rs2:    Option<u32>,
  funct7: Option<u8>,
  shamt:  Option<u8>,

  imm:    Option<u32>,

  result: Option<u32>,
}

#[derive(Clone, Debug)]
pub enum Exception {
  IllegalInstruction,
  IllegalMemoryAccess(u32),
  //ZeroDivision,
}

#[derive(Clone, Copy, Debug)]
struct IfId {
  inst: u32
}
#[derive(Clone, Copy, Debug)]
struct IdEx {
  inst: Instruction,
}
#[derive(Clone, Copy, Debug)]
struct ExMem {
  inst: Instruction,
  jump_flag: bool,
}
#[derive(Clone, Copy, Debug)]
struct MemWb {
  inst: Instruction,
  jump_flag: bool,
}

#[derive(Debug)]
pub struct Cpu {
  pub reg: [u32; 32],
  pub pc: u32,

  pub bus: Bus,

  if_id_reg: Option<IfId>,
  id_ex_reg: Option<IdEx>,
  ex_mem_reg: Option<ExMem>,
  mem_wb_reg: Option<MemWb>,

  step_processing: bool,
}

impl Cpu {
  pub fn new(filename: &str, step_processing: bool) -> Cpu {
    let mut f = File::open(filename).expect("実行バイナリを開けませんでした。");
    let mut buf = Vec::new();
    f.read_to_end(&mut buf).expect("実行バイナリの読み込みに失敗しました。");

    if buf.len() >= RAM_SIZE {
      println!("実行バイナリのサイズが大きすぎます。");
      println!("{}: {} bytes, max: {} bytes.", filename, buf.len(), ROM_SIZE);
      panic!();
    }

    let mut bus = Bus::new();
    for i in 0..buf.len() {
      bus.ram.data[i] = buf[i];
    }

    Cpu {
      reg: [0; 32],
      pc: 0x1000,
      bus,
      if_id_reg: None,
      id_ex_reg: None,
      ex_mem_reg: None,
      mem_wb_reg: None,
      step_processing,
    }
  }
  // fetch: pcの位置にある命令を命令レジスタに持ってくる
  pub fn fetch(&mut self) -> Result<(), Exception> {
    let mut inst: u32 = 0;
    for i in 0..4 {
      match self.bus.read(self.pc as usize + i) {
        Ok(x) => inst |= (x as u32) << (i * 8),
        Err(e) => return Err(e),
      }
    }
    self.if_id_reg = Some(IfId{ inst });
    Ok(())
  }
  // decode: opecodeとfunc_tを見る
  pub fn decode(&mut self) -> Result<(), Exception> {
    let inst = self.if_id_reg.unwrap().inst;
    let opecode = (inst & 0x7F) as u8;
    let rd      = Some(((inst & (0x1F <<  7)) as u32 >>  7) as u8);
    let funct3  = Some(((inst & (0x07 << 12)) as u32 >> 12) as u8);
    let rs1     = Some(self.reg[(inst & (0x1F << 15)) as usize >> 15]);
    let rs2     = Some(self.reg[(inst & (0x1F << 20)) as usize >> 20]);
    let funct7  = Some(((inst & (0x7F << 25)) as u32 >> 25) as u8);
    let shamt   = Some(((inst & (0x1F << 20)) as u32 >> 20) as u8);
    let imm: Option<u32>;
    let ins: Instruction;
    match opecode {
      // R-Type
      0x33 => {
        ins = Instruction { 
          ope_type: InstructionType::R, 
          opecode, 
          rd, 
          funct3, 
          rs1, 
          rs2, 
          funct7, 
          shamt: None, 
          imm: None, 
          result: None,
        };
      },
      // I-Type
      0x03 | 0x13 | 0x67 => {
        imm = Some((inst & 0xFFF << 20) as u32 >> 20);
        ins = Instruction { 
          ope_type: InstructionType::I, 
          opecode, 
          rd, 
          funct3, 
          rs1, 
          rs2: None, 
          funct7, 
          shamt,
          imm,
          result: None,
        };
      },
      // S-Type
      0x23 => {
        let imm_4_0  = (inst & (0x1F <<  7)) as u32 >> 7;
        let imm_11_5 = (inst & (0x7F << 25)) as u32 >> 25;
        imm = Some((imm_11_5 << 5) | imm_4_0);
        ins = Instruction { 
          ope_type: InstructionType::S, 
          opecode, 
          rd: None,
          funct3, 
          rs1, 
          rs2,
          funct7: None,
          shamt: None,
          imm,
          result: None,
        };
      },
      // J-Type
      0x6F => {
        let imm_20    = (inst & (0x001 << 31)) as u32 >> 31;
        let imm_10_1  = (inst & (0x3FF << 21)) as u32 >> 21;
        let imm_11    = (inst & (0x001 << 20)) as u32 >> 20;
        let imm_19_12 = (inst & (0x0FF << 12)) as u32 >> 12;
        imm = Some((imm_20 << 20) | (imm_19_12 << 12) | (imm_11 << 11) | (imm_10_1 << 1));
        ins = Instruction { 
          ope_type: InstructionType::J, 
          opecode, 
          rd,
          funct3: None,
          rs1: None,
          rs2: None,
          funct7: None,
          shamt: None,
          imm,
          result: None,
        };
      },
      // B-Type
      0x63 => {
        let imm_12 = (inst & (0x01 << 31)) as u32 >> 31;
        let imm_10_5 = (inst & (0x3F << 25)) as u32 >> 25;
        let imm_4_1  = (inst & (0x0F <<  8)) as u32 >>  8;
        let imm_11   = (inst & (0x01 <<  7)) as u32 >>  7;
        imm = Some((imm_12 << 12) | (imm_11 << 11) | (imm_10_5 << 5) | (imm_4_1 << 1));
        ins = Instruction { 
          ope_type: InstructionType::B, 
          opecode, 
          rd: None,
          funct3, 
          rs1, 
          rs2,
          funct7: None,
          shamt: None,
          imm,
          result: None,
        };
      },
      // U-Type
      0x37 | 0x17 => {
        imm = Some((inst & (0xFFFFF << 12)) as u32 >> 12);
        ins = Instruction { 
          ope_type: InstructionType::U, 
          opecode, 
          rd,
          funct3: None,
          rs1: None,
          rs2: None,
          funct7: None,
          shamt: None,
          imm,
          result: None,
        };
      },
      _ => return Err(Exception::IllegalInstruction),
    };
    self.id_ex_reg = Some(IdEx{ inst: ins });
    Ok(())
  }

  // exec: calc branch shiftをここで操作する
  pub fn execute(&mut self) -> Result<(), Exception> {
    let mut inst = self.id_ex_reg.unwrap().inst;
    let mut jump_flag = false;
    let res: u32 = match inst.opecode {
      // R-Type
      0x33 => {
        let funct3 = inst.funct3.unwrap();
        let rs1 = inst.rs1.unwrap();
        let rs2 = inst.rs2.unwrap();
        match funct3 {
          // add, sub
          0b000 => {
            if inst.funct7.unwrap() == 0 {
              rs1.wrapping_add(rs2)
            } else {
              rs1.wrapping_sub(rs2)
            }
          },
          // sll
          0b001 => rs1 << rs2,
          // slt
          0b010 => if (rs1 as i32) < (rs2 as i32) { 1 } else { 0 },
          // sltu
          0b011 => if rs1 < rs2 { 1 } else { 0 },
          // xor
          0b100 => rs1 ^ rs2,
          // srl & sra
          0b101 => Cpu::right_shift(rs1, rs2, inst.funct7.unwrap() == 0b0100000),
          // or
          0b110 => rs1 | rs2,
          // and
          0b111 => rs1 & rs2,
          _ => return Err(Exception::IllegalInstruction),
        }
      },
      // I-Type
      // ld
      0x03 => inst.rs1.unwrap().wrapping_add(Cpu::sign_extend(inst.imm.unwrap(), 12)),
      // immidiate value
      0x13 => {
        let sext = Cpu::sign_extend(inst.imm.unwrap(), 12);
        let rs1 = inst.rs1.unwrap();
        let shamt = inst.shamt.unwrap();
        let funct7 = inst.funct7.unwrap();
        let funct3 = inst.funct3.unwrap();
        match funct3 {
          // addi
          0b000 => rs1.wrapping_add(sext),
          // slli
          0b001 => rs1 << shamt,
          // slti
          0b010 => if (rs1 as i32) < (sext as i32) { 1 } else { 0 },
          // sltui
          0b011 => if rs1 < sext { 1 } else { 0 },
          // xori
          0b100 => rs1 ^ sext,
          // srli & srai
          0b101 => Cpu::right_shift(rs1, shamt as u32, funct7 == 0b0100000),
          // ori
          0b110 => rs1 | sext,
          // andi
          0b111 => rs1 & sext,
          _ => return Err(Exception::IllegalInstruction),
        }
      },
      // immidiate jump
      0x67 => {
        let funct3 = inst.funct3.unwrap();
        match funct3 {
          // jalr
          0b00 => {
            jump_flag = true;
            let rs1 = inst.rs1.unwrap();
            let imm = inst.imm.unwrap();
            let res = rs1.wrapping_add(Cpu::sign_extend(imm, 12));
            res & !0x00000001
          },
          _ => return Err(Exception::IllegalInstruction),
        }
      },
      // S-Type
      0x23 => inst.rs1.unwrap().wrapping_add(Cpu::sign_extend(inst.imm.unwrap(), 12)),
      // J-Type
      0x6F => {
        jump_flag = true;
        Cpu::sign_extend(inst.imm.unwrap(), 20)
      },
      // B-Type
      0x63 => {
        let rs1 = inst.rs1.unwrap();
        let rs2 = inst.rs2.unwrap();
        let sext = Cpu::sign_extend(inst.imm.unwrap(), 12);
        let funct3 = inst.funct3.unwrap();
        match funct3 {
          // beq
          0b000 => {
            if rs1 == rs2 { jump_flag = true; sext } 
            else { 0 }
          },
          // bne
          0b001 => {
            if rs1 != rs2 { jump_flag = true; sext } 
            else { 0 }
          },
          // blt
          0b100 => {
            if (rs1 as i32) < (rs2 as i32) { jump_flag = true; sext } 
            else { 0 }
          },
          // bge
          0b101 => {
            if (rs1 as i32) >= (rs2 as i32) { jump_flag = true; sext } 
            else { 0 }
          },
          // bltu
          0b110 => {
            if rs1 < rs2 { jump_flag = true; sext } 
            else { 0 }
          },
          // bgeu
          0b111 => {
            if rs1 >= rs2 { jump_flag = true; sext } 
            else { 0 }
          },
          _ => return Err(Exception::IllegalInstruction),
        }
      },
      // U-Type
      // lui
      0x37 => {
        Cpu::sign_extend(inst.imm.unwrap(), 20) << 12
      },
      // aui
      0x17 => {
        jump_flag = true;
        Cpu::sign_extend(inst.imm.unwrap(), 20)
      },
      _ => return Err(Exception::IllegalInstruction),
    };

    inst.result = Some(res);
    self.ex_mem_reg = Some(ExMem{ inst, jump_flag });
    Ok(())
  }
  
  // memory access
  pub fn memory_access(&mut self) -> Result<(), Exception> {
    let mut inst = self.ex_mem_reg.unwrap().inst;
    let addr = inst.result.unwrap() as usize;
    let jump_flag = self.ex_mem_reg.unwrap().jump_flag;
    
    let mut result = 0;
    match inst.ope_type {
      InstructionType::I => {
        if inst.opecode == 0x03 {
          match inst.funct3.unwrap() {
            // lb
            0b000 => { result = Cpu::sign_extend(self.bus.read(addr).unwrap() as u32, 8); },
            // lh
            0b001 => {
              let mut res = self.bus.read(addr).unwrap() as u32;
              res |= (self.bus.read(addr+1).unwrap() as u32) << 8;
              result = Cpu::sign_extend(res, 16);
            },
            // lw
            0b010 => {
              let mut res = 0 as u32;
              for i in 0..4 {
                res |= (self.bus.read(addr+i).unwrap() as u32) << (i * 8);
              }
              result = res;
            },
            // lbu
            0b100 => { result = self.bus.read(addr).unwrap() as u32; },
            // lhu
            0b101 => {
              result = self.bus.read(addr).unwrap() as u32;
              result |= (self.bus.read(addr+1).unwrap() as u32) << 8;
            }
            _ => result = inst.result.unwrap(),//return Err(Exception::IllegalInstruction),
          }
        } else {
          result = inst.result.unwrap()
        }
      }
      InstructionType::S => {
        let rs2 = inst.rs2.unwrap();
        match inst.funct3.unwrap() {
          // sb
          0b000 => { self.bus.write(addr, rs2 as u8).unwrap(); },
          // sh
          0b001 => { 
            self.bus.write(addr, rs2 as u8).unwrap();
            self.bus.write(addr+1, (rs2 >> 8) as u8).unwrap();
          }
          // sw
          0b010 => {
            for i in 0..4 {
              self.bus.write(addr+i, (rs2 >> (i * 8)) as u8).unwrap();
            }
          },
          _ => result = inst.result.unwrap(),//return Err(Exception::IllegalInstruction),
        }
      }
      _ => result = inst.result.unwrap(),//return Err(Exception::IllegalInstruction),
    }
    inst.result = Some(result);
    self.mem_wb_reg = Some(MemWb{ inst, jump_flag });
    Ok(())
  }

  // writeback: 書き込む
  pub fn writeback(&mut self) -> Result<(), Exception> {
    let inst = self.mem_wb_reg.unwrap().inst;
    let jump_flag = self.mem_wb_reg.unwrap().jump_flag;
    let result = inst.result.unwrap();
    match inst.opecode {
      // R-Type | ld I-Type | lui
      0x33 | 0x03 | 0x13 | 0x37 => {
        let rd = inst.rd.unwrap() as usize;
        self.reg[rd] = result;
      }, 
      // I-Type
      // ja
      0x67 => {
        let rd = inst.rd.unwrap() as usize;
        let tmp = self.pc + 4;
        self.pc = result;
        self.reg[rd] = tmp;
      },
      // J-Type
      0x6F => {
        let rd = inst.rd.unwrap() as usize;
        self.reg[rd] = self.pc + 4;
        self.pc = self.pc.wrapping_add(result);
      },
      // B-Type | aui
      0x63 | 0x17 => {
        self.pc = self.pc.wrapping_add(result);
      },
      _ => (),//return Err(Exception::IllegalInstruction),
    };

    if !jump_flag {
      self.pc += 4;
    } 
    self.reg[0] = 0;
    
    if self.step_processing {
      let mut s = String::new();
      std::io::stdin().read_line(&mut s).unwrap();
      println!("pc: {:>08x}", self.pc);
      self.print_registers();
    }

    Ok(())
  }

  fn sign_extend(imm: u32, len: u8) -> u32 {
    let mask = 0xFFFFFFFF << (len-1);
    let res: u32;
    if (imm & (0x01 << (len-1))) != 0 {
      res = imm | mask;
    } else {
      res = imm & !mask;
    }
    res
  }

  fn right_shift(imm: u32, shamt: u32, is_althmetic: bool) -> u32 {
    let mut res = imm;
    if !is_althmetic { // logical shift
      for _i in 0..shamt {
        res = (res >> 1) & 0x7FFFFFFF;  // 右へシフトしてmsbを0にセット
      }
    } else {
      let sign = res & 0x80000000; // msbを取り出す
      for _i in 0..shamt {
        res = ((res >> 1) & 0x7FFFFFFF) | sign;
      }
    }
    res
  }

#[allow(dead_code)]
  pub fn print_registers(&self) {
    println!("x00 / zero\t0x{:>08X}\tx01 / ra\t0x{:>08X}\tx02 / sp\t0x{:>08X}\tx03 / gp\t0x{:>08X}", self.reg[0], self.reg[1], self.reg[2], self.reg[3]);
    println!("x04 / tp\t0x{:>08X}\tx05 / t0\t0x{:>08X}\tx06 / t1\t0x{:>08X}\tx07 / t2\t0x{:>08X}", self.reg[4], self.reg[5], self.reg[6], self.reg[7]);
    println!("x08 / s0 / fp\t0x{:>08X}\tx09 / s1\t0x{:>08X}\tx10 / a0\t0x{:>08X}\tx11 / a1\t0x{:>08X}", self.reg[8], self.reg[9], self.reg[10], self.reg[11]);
    println!("x12 / a2\t0x{:>08X}\tx13 / a3\t0x{:>08X}\tx14 / a4\t0x{:>08X}\tx15 / a5\t0x{:>08X}", self.reg[12], self.reg[13], self.reg[14], self.reg[15]);
    println!("x16 / a6\t0x{:>08X}\tx17 / a7\t0x{:>08X}\tx18 / s2\t0x{:>08X}\tx19 / s3\t0x{:>08X}", self.reg[16], self.reg[17], self.reg[18], self.reg[19]);
    println!("x20 / s4\t0x{:>08X}\tx21 / s5\t0x{:>08X}\tx22 / s6\t0x{:>08X}\tx23 / s7\t0x{:>08X}", self.reg[20], self.reg[21], self.reg[22], self.reg[23]);
    println!("x24 / s8\t0x{:>08X}\tx25 / s9\t0x{:>08X}\tx26 / s10\t0x{:>08X}\tx27 / s11\t0x{:>08X}", self.reg[24], self.reg[25], self.reg[26], self.reg[27]);
    println!("x28 / t3\t0x{:>08X}\tx29 / t4\t0x{:>08X}\tx30 / t5\t0x{:>08X}\tx31 / t6\t0x{:>08X}", self.reg[28], self.reg[29], self.reg[30], self.reg[31]);
    std::io::stdout().flush().unwrap();
  }
}

