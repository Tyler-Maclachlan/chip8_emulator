use std::{
    fs,
    io::{self, BufReader, Read},
};

use crate::instruction;

pub struct Chip8 {
    pub memory: [u8; 4096],
    pub v: [u8; 16],
    pub index: u16,
    pub pc: u16,
    pub gfx: [u8; 64 * 32],
    pub delay_timer: u8,
    pub sound_timer: u8,
    pub stack: [u16; 16],
    pub sp: u16,
    pub key: [u8; 16],

    pub draw_flag: bool,
}

const FONT_SET: [u8; 80] = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, // 0
    0x20, 0x60, 0x20, 0x20, 0x70, // 1
    0xF0, 0x10, 0xF0, 0x80, 0xF0, // 2
    0xF0, 0x10, 0xF0, 0x10, 0xF0, // 3
    0x90, 0x90, 0xF0, 0x10, 0x10, // 4
    0xF0, 0x80, 0xF0, 0x10, 0xF0, // 5
    0xF0, 0x80, 0xF0, 0x90, 0xF0, // 6
    0xF0, 0x10, 0x20, 0x40, 0x40, // 7
    0xF0, 0x90, 0xF0, 0x90, 0xF0, // 8
    0xF0, 0x90, 0xF0, 0x10, 0xF0, // 9
    0xF0, 0x90, 0xF0, 0x90, 0x90, // A
    0xE0, 0x90, 0xE0, 0x90, 0xE0, // B
    0xF0, 0x80, 0x80, 0x80, 0xF0, // C
    0xE0, 0x90, 0x90, 0x90, 0xE0, // D
    0xF0, 0x80, 0xF0, 0x80, 0xF0, // E
    0xF0, 0x80, 0xF0, 0x80, 0x80, // F
];

impl Chip8 {
    pub fn new() -> Self {
        let mut chip8 = Chip8 {
            memory: [0; 4096],
            v: [0; 16],
            index: 0,
            pc: 0x200,
            gfx: [0; 64 * 32],
            delay_timer: 0,
            sound_timer: 0,
            stack: [0; 16],
            sp: 0,
            key: [0; 16],
            draw_flag: false,
        };

        chip8.memory[..FONT_SET.len()].copy_from_slice(&FONT_SET);

        chip8
    }

    pub fn read_mem(&self, addr: u16) -> u8 {
        if addr as usize >= self.memory.len() {
            panic!("Memory access out of bounds: 0x{:X}", addr);
        }

        self.memory[addr as usize]
    }

    pub fn write_mem(&mut self, addr: u16, val: u8) {
        if addr as usize >= self.memory.len() {
            panic!("Memory access out of bounds: 0x{:X}", addr);
        }

        self.memory[addr as usize] = val;
    }

    pub fn stack_push(&mut self, addr: u16) {
        if self.sp as usize >= self.stack.len() {
            panic!("Stack overflow");
        }

        self.stack[self.sp as usize] = addr;
        self.sp += 1;
    }

    pub fn stack_pop(&mut self) -> u16 {
        if self.sp == 0 {
            panic!("Stack underflow");
        }

        self.sp -= 1;
        let addr = self.stack[self.sp as usize];
        self.stack[self.sp as usize] = 0;

        addr
    }

    pub fn load_program(&mut self, path: &str) -> io::Result<()> {
        let file = fs::File::open(path)?;
        let reader = BufReader::new(file);

        let mut addr = 0x200;
        for byte in reader.bytes() {
            let b = byte?;

            if addr >= self.memory.len() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Program too large to fit in memory",
                ));
            }

            self.memory[addr] = b;
            addr += 1;
        }

        Ok(())
    }

    pub fn cycle(&mut self) {
        let instr = u16::from(self.memory[self.pc as usize]) << 8
            | u16::from(self.memory[self.pc as usize + 1]);

        instruction::execute_instruction(self, instr);
    }
}
