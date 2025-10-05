// use std::process;

// use crossterm::event::{Event, KeyModifiers, read};
use rand::Rng;

use crate::chip8::Chip8;

pub enum Opcode {
    CLS,      // 0x00E0 - CLS
    RET,      // 0x00EE - RET
    SYS,      // 0x0nnn - SYS addr
    JPaddr,   // 0x1nnn - JP addr
    CALLaddr, // 0x2nnn - CALL addr
    SEvxkk,   // 0x3xkk - SE Vx, byte
    SNEvxkk,  // 0x4xkk - SNE Vx, byte
    SEvxvy,   // 0x5xy0 - SE Vx, Vy
    LDvxkk,   // 0x6xkk - LD Vx, byte
    ADDvxkk,  // 0x7xkk - ADD Vx, byte
    LDvxvy,   // 0x8xy0 - LD Vx, Vy
    ORvxvy,   // 0x8xy1 - OR Vx, Vy
    ANDvxvy,  // 0x8xy2 - AND Vx, Vy
    XORvxvy,  // 0x8xy3 - XOR Vx, Vy
    ADDvxvy,  // 0x8xy4 - ADD Vx, Vy
    SUBvxvy,  // 0x8xy5 - SUB Vx, Vy
    SHR,      // 0x8xy6 - SHR Vx {, Vy}
    SUBN,     // 0x8xy7 - SUBN Vx, Vy
    SHL,      // 0x8xyE - SHL Vx {, Vy}
    SNEvxvy,  // 0x9xy0 - SNE Vx, Vy
    LDiaddr,  // 0xAnnn - LD I, addr
    JPv0addr, // 0xBnnn - JP V0, addr
    RND,      // 0xCxkk - RND Vx, byte
    DRW,      // 0xDxyn - DRW Vx, Vy, nibble
    SKP,      // 0xEx9E - SKP Vx
    SKNP,     // 0xExA1 - SKNP Vx
    LDvxdt,   // 0xFx07 - LD Vx, DT
    LDvxk,    // 0xFx0A - LD Vx, K
    LDdtvx,   // 0xFx15 - LD DT, Vx
    LDstvx,   // 0xFx18 - LD ST, Vx
    ADDivx,   // 0xFx1E - ADD I, Vx
    LDf,      // 0xFx29 - LD F, Vx
    LDb,      // 0xFx33 - LD B, Vx
    LDiv,     // 0xFx55 - LD [I], Vx
    LDvi,     // 0xFx65 - LD Vx, [I]
}

pub fn get_opcode(instr: u16) -> Option<Opcode> {
    match (instr & 0xF000) >> 12 {
        0x0 => {
            if instr == 0x00E0 {
                Some(Opcode::CLS)
            } else if instr == 0x00EE {
                Some(Opcode::RET)
            } else {
                Some(Opcode::SYS)
            }
        }
        0x1 => Some(Opcode::JPaddr),
        0x2 => Some(Opcode::CALLaddr),
        0x3 => Some(Opcode::SEvxkk),
        0x4 => Some(Opcode::SNEvxkk),
        0x5 => {
            if instr & 0x000F == 0 {
                Some(Opcode::SEvxvy)
            } else {
                None
            }
        }
        0x6 => Some(Opcode::LDvxkk),
        0x7 => Some(Opcode::ADDvxkk),
        0x8 => match instr & 0x000F {
            0x0 => Some(Opcode::LDvxvy),
            0x1 => Some(Opcode::ORvxvy),
            0x2 => Some(Opcode::ANDvxvy),
            0x3 => Some(Opcode::XORvxvy),
            0x4 => Some(Opcode::ADDvxvy),
            0x5 => Some(Opcode::SUBvxvy),
            0x6 => Some(Opcode::SHR),
            0x7 => Some(Opcode::SUBN),
            0xE => Some(Opcode::SHL),
            _ => None,
        },
        0x9 => {
            if instr & 0x000F == 0 {
                Some(Opcode::SNEvxvy)
            } else {
                None
            }
        }
        0xA => Some(Opcode::LDiaddr),
        0xB => Some(Opcode::JPv0addr),
        0xC => Some(Opcode::RND),
        0xD => Some(Opcode::DRW),
        0xE => match instr & 0x00FF {
            0x9E => Some(Opcode::SKP),
            0xA1 => Some(Opcode::SKNP),
            _ => None,
        },
        0xF => match instr & 0x00FF {
            0x7 => Some(Opcode::LDvxdt),
            0xA => Some(Opcode::LDvxk),
            0x15 => Some(Opcode::LDdtvx),
            0x18 => Some(Opcode::LDstvx),
            0x1E => Some(Opcode::ADDivx),
            0x29 => Some(Opcode::LDf),
            0x33 => Some(Opcode::LDb),
            0x55 => Some(Opcode::LDiv),
            0x65 => Some(Opcode::LDvi),
            _ => None,
        },
        _ => None,
    }
}

pub fn get_x(instr: u16) -> u8 {
    ((instr & 0x0F00) >> 8) as u8
}

pub fn get_y(instr: u16) -> u8 {
    ((instr & 0x00F0) >> 4) as u8
}

pub fn get_n(instr: u16) -> u8 {
    (instr & 0x000F) as u8
}

pub fn get_kk(instr: u16) -> u8 {
    (instr & 0x00FF) as u8
}

pub fn get_nnn(instr: u16) -> u16 {
    instr & 0x0FFF
}

pub fn execute_instruction(vm: &mut Chip8, instr: u16) {
    let opcode = get_opcode(instr)
        .unwrap_or_else(|| panic!("Invalid instruction {:X} at PC {:X}", instr, vm.pc));

    match opcode {
        Opcode::CLS => {
            vm.gfx.fill(0);

            vm.pc += 2;
        }
        Opcode::RET => {
            vm.pc = vm.stack_pop();
        }
        Opcode::SYS => {
            // technically no-op for modern interpreters
            // vm.pc = get_nnn(instr); // Would just be the same as `JPaddr`
        }
        Opcode::JPaddr => {
            vm.pc = get_nnn(instr);
        }
        Opcode::CALLaddr => {
            vm.stack_push(vm.pc + 2);

            vm.pc = get_nnn(instr);
        }
        Opcode::SEvxkk => {
            let x = get_x(instr);
            let kk = get_kk(instr);

            if vm.v[x as usize] == kk {
                vm.pc += 2;
            }

            vm.pc += 2;
        }
        Opcode::SNEvxkk => {
            let x = get_x(instr);
            let kk = get_kk(instr);

            if vm.v[x as usize] != kk {
                vm.pc += 2;
            }

            vm.pc += 2;
        }
        Opcode::SEvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            if vm.v[x as usize] == vm.v[y as usize] {
                vm.pc += 2;
            }

            vm.pc += 2;
        }
        Opcode::LDvxkk => {
            let x = get_x(instr);
            let kk = get_kk(instr);

            vm.v[x as usize] = kk;

            vm.pc += 2;
        }
        Opcode::ADDvxkk => {
            let x = get_x(instr);
            let kk = get_kk(instr);

            vm.v[x as usize] = vm.v[x as usize].wrapping_add(kk);

            vm.pc += 2;
        }
        Opcode::LDvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            vm.v[x as usize] = vm.v[y as usize];

            vm.pc += 2;
        }
        Opcode::ORvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            vm.v[x as usize] = vm.v[x as usize] | vm.v[y as usize];

            vm.pc += 2;
        }
        Opcode::ANDvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            vm.v[x as usize] = vm.v[x as usize] & vm.v[y as usize];

            vm.pc += 2;
        }
        Opcode::XORvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            vm.v[x as usize] = vm.v[x as usize] ^ vm.v[y as usize];

            vm.pc += 2;
        }
        Opcode::ADDvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            let val_x = vm.v[x as usize];
            let val_y = vm.v[y as usize];

            let (val, did_overflow) = val_x.overflowing_add(val_y);

            vm.v[0xF] = if did_overflow { 1 } else { 0 };
            vm.v[x as usize] = val;

            vm.pc += 2;
        }
        Opcode::SUBvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            let val_x = vm.v[x as usize];
            let val_y = vm.v[y as usize];

            vm.v[0xF] = if val_x > val_y { 1 } else { 0 };

            let val = val_x.wrapping_sub(val_y);
            vm.v[x as usize] = val;

            vm.pc += 2;
        }
        Opcode::SHR => {
            let x = get_x(instr);

            let val_x = vm.v[x as usize];
            let lsb = val_x & 0x1;

            vm.v[0xF] = if lsb == 1 { 1 } else { 0 }; // could also just do vm.v[0xF] = lsb
            vm.v[x as usize] = val_x >> 1;

            vm.pc += 2;
        }
        Opcode::SUBN => {
            let x = get_x(instr);
            let y = get_y(instr);

            let val_x = vm.v[x as usize];
            let val_y = vm.v[y as usize];

            vm.v[0xF] = if val_y > val_x { 1 } else { 0 };
            vm.v[x as usize] = val_y.wrapping_sub(val_x);

            vm.pc += 2;
        }
        Opcode::SHL => {
            let x = get_x(instr);

            let val_x = vm.v[x as usize];
            let msb = (val_x & 0x80) >> 7;

            vm.v[0xF] = if msb == 1 { 1 } else { 0 }; // could also just do vm.v[0xF] = msb;
            vm.v[x as usize] = val_x << 1;

            vm.pc += 2;
        }
        Opcode::SNEvxvy => {
            let x = get_x(instr);
            let y = get_y(instr);

            if vm.v[x as usize] != vm.v[y as usize] {
                vm.pc += 2;
            }

            vm.pc += 2;
        }
        Opcode::LDiaddr => {
            let nnn = get_nnn(instr);

            vm.index = nnn;

            vm.pc += 2;
        }
        Opcode::JPv0addr => {
            let nnn = get_nnn(instr);
            let val_v0 = vm.v[0];

            vm.pc = nnn.wrapping_add(u16::from(val_v0));
        }
        Opcode::RND => {
            let x = get_x(instr);
            let kk = get_kk(instr);

            let mut rng = rand::rng();
            let rand_byte = rng.random::<u8>();

            vm.v[x as usize] = rand_byte & kk;

            vm.pc += 2;
        }
        Opcode::DRW => {
            let x = get_x(instr);
            let y = get_y(instr);
            let n = get_n(instr);

            let x_coord = vm.v[x as usize];
            let y_coord = vm.v[y as usize];

            let mut cleared = false;

            for row in 0..n as usize {
                let byte = vm.read_mem(vm.index + row as u16);

                for bit_index in (0 as usize)..8 {
                    let bit = (byte >> (7 - bit_index)) & 0x1;

                    let pixel_index =
                        get_1d_from_2d(x_coord as usize + bit_index, y_coord as usize + row);

                    if vm.gfx[pixel_index] == 1 && bit == 1 {
                        cleared = true;
                    }

                    vm.gfx[pixel_index] ^= bit;
                }
            }

            vm.v[0xF] = if cleared { 1 } else { 0 };

            vm.draw_flag = true;
            vm.pc += 2;
        }
        Opcode::SKP => {
            let x = get_x(instr);
            let val_x = vm.v[x as usize];

            if vm.key[val_x as usize] == 1 {
                vm.pc += 2;
            }

            vm.pc += 2;
        }
        Opcode::SKNP => {
            let x = get_x(instr);
            let val_x = vm.v[x as usize];

            if vm.key[val_x as usize] == 0 {
                vm.pc += 2;
            }

            vm.pc += 2;
        }
        Opcode::LDvxdt => {
            let x = get_x(instr);

            vm.v[x as usize] = vm.delay_timer;

            vm.pc += 2;
        }
        Opcode::LDvxk => {
            let x = get_x(instr);

            if let Some(key_index) = vm.key.iter().position(|&k| k != 0) {
                vm.v[x as usize] = key_index as u8;
                vm.pc += 2; // advance once a key is pressed
            }
            // else: wait — don't advance PC
        }

        Opcode::LDdtvx => {
            let x = get_x(instr);

            vm.delay_timer = vm.v[x as usize];

            vm.pc += 2;
        }
        Opcode::LDstvx => {
            let x = get_x(instr);

            vm.sound_timer = vm.v[x as usize];

            vm.pc += 2;
        }
        Opcode::ADDivx => {
            let x = get_x(instr);

            vm.index = vm.index.wrapping_add(vm.v[x as usize] as u16);

            vm.pc += 2;
        }
        Opcode::LDf => {
            let x = get_x(instr);

            vm.index = u16::from(vm.v[x as usize]) * 5;

            vm.pc += 2;
        }
        Opcode::LDb => {
            let x = get_x(instr);
            let val = vm.v[x as usize];

            let hundreds = val / 100;
            let tens = (val / 10) % 10;
            let ones = val % 10;

            vm.write_mem(vm.index, hundreds);
            vm.write_mem(vm.index + 1, tens);
            vm.write_mem(vm.index + 2, ones);

            vm.pc += 2;
        }
        Opcode::LDiv => {
            let x = get_x(instr);

            for i in 0..=x {
                vm.write_mem(vm.index + i as u16, vm.v[i as usize]);
            }

            vm.index += u16::from(x) + 1;

            vm.pc += 2;
        }
        Opcode::LDvi => {
            let x = get_x(instr);

            for i in 0..=x as u16 {
                vm.v[i as usize] = vm.read_mem(vm.index + i);
            }

            vm.index += u16::from(x) + 1;

            vm.pc += 2;
        }
    }
}

fn get_1d_from_2d(x: usize, y: usize) -> usize {
    (y as usize % 32) * 64 + (x as usize % 64)
}

// fn char_to_chip8_key(c: char) -> Option<u8> {
//     match c {
//         '1' => Some(0x1),
//         '2' => Some(0x2),
//         '3' => Some(0x3),
//         '4' => Some(0xC),
//         'Q' | 'q' => Some(0x4),
//         'W' | 'w' => Some(0x5),
//         'E' | 'e' => Some(0x6),
//         'R' | 'r' => Some(0xD),
//         'A' | 'a' => Some(0x7),
//         'S' | 's' => Some(0x8),
//         'D' | 'd' => Some(0x9),
//         'F' | 'f' => Some(0xE),
//         'Z' | 'z' => Some(0xA),
//         'X' | 'x' => Some(0x0),
//         'C' | 'c' => Some(0xB),
//         'V' | 'v' => Some(0xF),
//         _ => None,
//     }
// }

// pub fn getc() -> u8 {
//     loop {
//         match read().unwrap() {
//             Event::Key(event) => {
//                 if let Some(c) = event.code.as_char() {
//                     // exit on Ctrl+Z or Ctrl+C
//                     if (c == 'z' || c == 'c') && event.modifiers.contains(KeyModifiers::CONTROL) {
//                         process::exit(0);
//                     }

//                     if let Some(chip8_key) = char_to_chip8_key(c) {
//                         return chip8_key;
//                     }
//                 }
//             }
//             _ => {}
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opcode_decoding() {
        assert!(matches!(get_opcode(0x00E0), Some(Opcode::CLS)));
        assert!(matches!(get_opcode(0x00EE), Some(Opcode::RET)));
        assert!(matches!(get_opcode(0x0ABC), Some(Opcode::SYS)));
        assert!(matches!(get_opcode(0x1ABC), Some(Opcode::JPaddr)));
        assert!(matches!(get_opcode(0x2ABC), Some(Opcode::CALLaddr)));
        assert!(matches!(get_opcode(0x3A12), Some(Opcode::SEvxkk)));
        assert!(matches!(get_opcode(0x4B34), Some(Opcode::SNEvxkk)));
        assert!(matches!(get_opcode(0x5AB0), Some(Opcode::SEvxvy)));
        assert!(matches!(get_opcode(0x6C56), Some(Opcode::LDvxkk)));
        assert!(matches!(get_opcode(0x7D89), Some(Opcode::ADDvxkk)));
        assert!(matches!(get_opcode(0x8AB0), Some(Opcode::LDvxvy)));
        assert!(matches!(get_opcode(0x8AB1), Some(Opcode::ORvxvy)));
        assert!(matches!(get_opcode(0x8AB2), Some(Opcode::ANDvxvy)));
        assert!(matches!(get_opcode(0x8AB3), Some(Opcode::XORvxvy)));
        assert!(matches!(get_opcode(0x8AB4), Some(Opcode::ADDvxvy)));
        assert!(matches!(get_opcode(0x8AB5), Some(Opcode::SUBvxvy)));
        assert!(matches!(get_opcode(0x8AB6), Some(Opcode::SHR)));
        assert!(matches!(get_opcode(0x8AB7), Some(Opcode::SUBN)));
        assert!(matches!(get_opcode(0x8ABE), Some(Opcode::SHL)));
        assert!(matches!(get_opcode(0x9AB0), Some(Opcode::SNEvxvy)));
        assert!(matches!(get_opcode(0xA999), Some(Opcode::LDiaddr)));
        assert!(matches!(get_opcode(0xB222), Some(Opcode::JPv0addr)));
        assert!(matches!(get_opcode(0xCAFE), Some(Opcode::RND)));
        assert!(matches!(get_opcode(0xD125), Some(Opcode::DRW)));
        assert!(matches!(get_opcode(0xE19E), Some(Opcode::SKP)));
        assert!(matches!(get_opcode(0xE1A1), Some(Opcode::SKNP)));
        assert!(matches!(get_opcode(0xF107), Some(Opcode::LDvxdt)));
        assert!(matches!(get_opcode(0xF10A), Some(Opcode::LDvxk)));
        assert!(matches!(get_opcode(0xF115), Some(Opcode::LDdtvx)));
        assert!(matches!(get_opcode(0xF118), Some(Opcode::LDstvx)));
        assert!(matches!(get_opcode(0xF11E), Some(Opcode::ADDivx)));
        assert!(matches!(get_opcode(0xF129), Some(Opcode::LDf)));
        assert!(matches!(get_opcode(0xF133), Some(Opcode::LDb)));
        assert!(matches!(get_opcode(0xF155), Some(Opcode::LDiv)));
        assert!(matches!(get_opcode(0xF165), Some(Opcode::LDvi)));
    }

    #[test]
    fn test_operand_helpers() {
        let instr = 0xABCD; // 1010 1011 1100 1101

        assert_eq!(get_x(instr), 0xB); // bits 8-11
        assert_eq!(get_y(instr), 0xC); // bits 4-7
        assert_eq!(get_n(instr), 0xD); // bits 0-3
        assert_eq!(get_kk(instr), 0xCD); // bits 0-7
        assert_eq!(get_nnn(instr), 0xBCD); // bits 0-11
    }

    #[test]
    fn test_edge_cases() {
        // Ensure invalid instructions return None
        assert!(matches!(get_opcode(0xFFFF), None));
        assert!(matches!(get_opcode(0x8008), None)); // 0x8xy8 isn't defined
        assert!(matches!(get_opcode(0xE000), None));
        assert!(matches!(get_opcode(0xF999), None));
    }
}

#[cfg(test)]
mod instruction_tests {
    use super::*;

    fn setup_chip8() -> Chip8 {
        Chip8::new()
    }

    #[test]
    fn test_cls() {
        let mut chip = setup_chip8();
        chip.gfx.fill(1);
        execute_instruction(&mut chip, 0x00E0);
        assert!(chip.gfx.iter().all(|&b| b == 0));
        assert_eq!(chip.pc, 0x202);
    }

    #[test]
    fn test_ret_and_call() {
        let mut chip = setup_chip8();
        chip.pc = 0x200;
        chip.stack_push(0x300);
        execute_instruction(&mut chip, 0x00EE); // RET
        assert_eq!(chip.pc, 0x300);

        chip.pc = 0x200;
        execute_instruction(&mut chip, 0x2300); // CALL 0x300
        assert_eq!(chip.pc, 0x300);
        assert_eq!(chip.sp, 1);
        assert_eq!(chip.stack[0], 0x202);
    }

    #[test]
    fn test_jpaddr_and_jpv0addr() {
        let mut chip = setup_chip8();
        execute_instruction(&mut chip, 0x1234); // JP 0x234
        assert_eq!(chip.pc, 0x234);

        chip.v[0] = 0x10;
        execute_instruction(&mut chip, 0xB200); // JP V0 + 0x200
        assert_eq!(chip.pc, 0x200 + 0x10);
    }

    #[test]
    fn test_se_and_sne() {
        let mut chip = setup_chip8();
        chip.v[0] = 0x10;
        chip.v[1] = 0x20;

        execute_instruction(&mut chip, 0x3010); // SE V0, 0x10
        assert_eq!(chip.pc, 0x204); // should skip

        chip.pc = 0x200;
        execute_instruction(&mut chip, 0x4011); // SNE V0, 0x11
        assert_eq!(chip.pc, 0x204); // should skip

        chip.pc = 0x200;
        chip.v[1] = 0x10;
        execute_instruction(&mut chip, 0x5010); // SE V0, V1
        assert_eq!(chip.pc, 0x204); // should skip

        chip.pc = 0x200;
        chip.v[1] = 0x20;
        execute_instruction(&mut chip, 0x9010); // SNE V0, V1
        assert_eq!(chip.pc, 0x204); // should skip
    }

    #[test]
    fn test_ld_and_add_vx() {
        let mut chip = setup_chip8();
        execute_instruction(&mut chip, 0x60AA); // LD V0, 0xAA
        assert_eq!(chip.v[0], 0xAA);
        execute_instruction(&mut chip, 0x7005); // ADD V0, 0x05
        assert_eq!(chip.v[0], 0xAF);
    }

    #[test]
    fn test_ld_vx_vy_and_logic_ops() {
        let mut chip = setup_chip8();
        chip.v[1] = 0x0F;
        execute_instruction(&mut chip, 0x8010); // LD V0, V1
        assert_eq!(chip.v[0], 0x0F);

        chip.v[0] = 0xF0;
        execute_instruction(&mut chip, 0x8011); // OR V0, V1
        assert_eq!(chip.v[0], 0xFF);

        execute_instruction(&mut chip, 0x8012); // AND V0, V1
        assert_eq!(chip.v[0], 0x0F);

        execute_instruction(&mut chip, 0x8013); // XOR V0, V1
        assert_eq!(chip.v[0], 0x00);
    }

    #[test]
    fn test_add_sub_shifts() {
        let mut chip = setup_chip8();
        chip.v[0] = 0x10;
        chip.v[1] = 0x20;
        execute_instruction(&mut chip, 0x8014); // ADD V0, V1
        assert_eq!(chip.v[0], 0x30);
        assert_eq!(chip.v[0xF], 0); // no overflow

        chip.v[1] = 0xFF;
        execute_instruction(&mut chip, 0x8014); // ADD V0, V1
        assert_eq!(chip.v[0xF], 1); // overflow occurred

        chip.v[0] = 0x50;
        chip.v[1] = 0x20;
        execute_instruction(&mut chip, 0x8015); // SUB V0, V1
        assert_eq!(chip.v[0], 0x30);
        assert_eq!(chip.v[0xF], 1); // V0 > V1

        execute_instruction(&mut chip, 0x8017); // SUBN V0, V1
        assert_eq!(chip.v[0], 0xF0); // 0x20 - 0x30 wrapping
        assert_eq!(chip.v[0xF], 0); // V1 not greater

        chip.v[0] = 0b1000_0001;
        execute_instruction(&mut chip, 0x800E); // SHL V0
        assert_eq!(chip.v[0], 0b0000_0010);
        assert_eq!(chip.v[0xF], 1);

        chip.v[0] = 0b0000_0011;
        execute_instruction(&mut chip, 0x8006); // SHR V0
        assert_eq!(chip.v[0], 0b0000_0001);
        assert_eq!(chip.v[0xF], 1);
    }

    #[test]
    fn test_ld_i_and_ld_store_load_memory() {
        let mut chip = setup_chip8();
        chip.v[0] = 0x12;
        chip.v[1] = 0x34;
        chip.v[2] = 0x56; // set before storing
        execute_instruction(&mut chip, 0xA300); // LD I, 0x300
        assert_eq!(chip.index, 0x300);

        execute_instruction(&mut chip, 0xF255); // LD [I], V2 (stores V0-V2)
        chip.index = 0x300;
        execute_instruction(&mut chip, 0xF265); // LD V0-V2, [I]
        assert_eq!(chip.v[0], 0x12);
        assert_eq!(chip.v[1], 0x34);
        assert_eq!(chip.v[2], 0x56);
    }

    #[test]
    fn test_ld_dt_st_and_add_i_ldf_ldb() {
        let mut chip = setup_chip8();
        chip.delay_timer = 0x12;
        chip.sound_timer = 0x34;
        chip.v[0] = 0x56;

        execute_instruction(&mut chip, 0xF007); // LD V0, DT
        assert_eq!(chip.v[0], 0x12);

        execute_instruction(&mut chip, 0xF018); // LD ST, V0
        assert_eq!(chip.sound_timer, 0x12);

        chip.v[0] = 0x56;
        execute_instruction(&mut chip, 0xF01E); // ADD I, V0
        assert_eq!(chip.index, 0x56);

        execute_instruction(&mut chip, 0xF029); // LD F, V0
        assert_eq!(chip.index, 0x56 * 5);

        chip.v[0] = 123;
        chip.index = 0x300;
        execute_instruction(&mut chip, 0xF033); // LD B, V0
        assert_eq!(chip.memory[0x300], 1); // hundreds
        assert_eq!(chip.memory[0x301], 2); // tens
        assert_eq!(chip.memory[0x302], 3); // ones
    }

    #[test]
    fn test_drw() {
        let mut chip = setup_chip8();

        // Set up memory for a 3-byte sprite at I
        chip.index = 0x300;
        chip.memory[0x300] = 0b11110000; // first row
        chip.memory[0x301] = 0b10010000; // second row
        chip.memory[0x302] = 0b11110000; // third row

        chip.v[0] = 0; // X coord
        chip.v[1] = 0; // Y coord

        // Execute DRW V0, V1, 3 (3-byte sprite)
        execute_instruction(&mut chip, 0xD013);

        // First row should be set correctly
        assert_eq!(chip.gfx[0], 1);
        assert_eq!(chip.gfx[1], 1);
        assert_eq!(chip.gfx[2], 1);
        assert_eq!(chip.gfx[3], 1);

        // VF should be 0 (no collision yet)
        assert_eq!(chip.v[0xF], 0);
        assert_eq!(chip.pc, 0x202);

        // Draw the same sprite again to cause collisions
        chip.pc = 0x200; // reset PC for testing
        execute_instruction(&mut chip, 0xD013);

        // Pixels should now be toggled back (0)
        assert_eq!(chip.gfx[0], 0);
        assert_eq!(chip.v[0xF], 1); // collision detected

        // PC should advance by 2 after each draw
        assert_eq!(chip.pc, 0x202);
    }

    #[test]
    fn test_skp_and_sknp() {
        let mut chip = setup_chip8();

        // Set V0 to the key we will test
        chip.v[0] = 0x5; // key 5

        // --- SKP: skip if key pressed ---
        chip.key[0x5] = 1; // simulate key pressed
        chip.pc = 0x200;
        execute_instruction(&mut chip, 0xE09E); // SKP V0
        assert_eq!(chip.pc, 0x204); // should skip next instruction (PC + 4)

        // reset PC and key
        chip.pc = 0x200;
        chip.key[0x5] = 0; // key not pressed
        execute_instruction(&mut chip, 0xE09E); // SKP V0
        assert_eq!(chip.pc, 0x202); // should not skip (PC + 2)

        // --- SKNP: skip if key not pressed ---
        chip.key[0x5] = 0; // key not pressed
        chip.pc = 0x200;
        execute_instruction(&mut chip, 0xE0A1); // SKNP V0
        assert_eq!(chip.pc, 0x204); // should skip next instruction (PC + 4)

        // reset PC and key
        chip.pc = 0x200;
        chip.key[0x5] = 1; // key pressed
        execute_instruction(&mut chip, 0xE0A1); // SKNP V0
        assert_eq!(chip.pc, 0x202); // should not skip (PC + 2)
    }
}
