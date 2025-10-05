use minifb::{Key, Window, WindowOptions};
use rodio::{
    OutputStreamBuilder, Sink,
    source::{SineWave, Source},
};
use std::{
    env, process,
    time::{Duration, Instant},
};

use chip8::Chip8; // your Chip8 struct

mod chip8;
mod instruction;

const WIDTH: usize = 64;
const HEIGHT: usize = 32;

const CYCLES_PER_SECOND: u64 = 500;
const CYCLE_DURATION: Duration = Duration::from_micros(1_000_000 / CYCLES_PER_SECOND); // 500 Hz

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("Expected file argument");
        process::exit(1);
    }

    let mut chip = Chip8::new();
    chip.load_program(&args[1])?;

    let mut window = Window::new(
        format!("CHIP-8 Emulator - {}", args[1]).as_str(),
        WIDTH,
        HEIGHT,
        WindowOptions {
            resize: false,
            scale: minifb::Scale::X16, // scale 16x so we can see it
            ..WindowOptions::default()
        },
    )
    .unwrap();

    // Convert CHIP-8 1-bit graphics to u32 pixels for minifb
    let mut buffer: Vec<u32> = vec![0; WIDTH * HEIGHT];

    // Setup audio
    let stream_handle =
        OutputStreamBuilder::open_default_stream().expect("open default audio stream");
    let sink = Sink::connect_new(&stream_handle.mixer());

    // Main loop timing
    let mut last_time = Instant::now();
    let mut last_cycle_time = Instant::now();
    let cycle_delay = Duration::from_millis(16); // ~60Hz

    while window.is_open() && !window.is_key_down(Key::Escape) {
        let now = Instant::now();
        if now.duration_since(last_time) >= cycle_delay {
            if chip.delay_timer > 0 {
                chip.delay_timer -= 1;
            }

            if chip.sound_timer > 0 {
                chip.sound_timer -= 1;

                // Play tone if not already playing
                if sink.empty() {
                    let tone = SineWave::new(440.0)
                        .take_duration(Duration::from_millis(16))
                        .amplify(0.20);
                    sink.append(tone);
                }
            }

            last_time = now;
        }

        poll_keys(&mut chip, &window);

        while now.duration_since(last_cycle_time) >= CYCLE_DURATION {
            chip.cycle();
            last_cycle_time += CYCLE_DURATION;
        }

        // Update display buffer
        for i in 0..chip.gfx.len() {
            buffer[i] = if chip.gfx[i] == 0 { 0x000000 } else { 0xFFFFFF };
        }

        window.update_with_buffer(&buffer, WIDTH, HEIGHT).unwrap();

        // Small sleep to avoid busy loop
        std::thread::sleep(Duration::from_millis(1));
    }

    Ok(())
}

fn poll_keys(chip: &mut Chip8, window: &minifb::Window) {
    chip.key[0x0] = if window.is_key_down(Key::X) { 1 } else { 0 };
    chip.key[0x1] = if window.is_key_down(Key::Key1) { 1 } else { 0 };
    chip.key[0x2] = if window.is_key_down(Key::Key2) { 1 } else { 0 };
    chip.key[0x3] = if window.is_key_down(Key::Key3) { 1 } else { 0 };
    chip.key[0x4] = if window.is_key_down(Key::Q) { 1 } else { 0 };
    chip.key[0x5] = if window.is_key_down(Key::W) { 1 } else { 0 };
    chip.key[0x6] = if window.is_key_down(Key::E) { 1 } else { 0 };
    chip.key[0x7] = if window.is_key_down(Key::A) { 1 } else { 0 };
    chip.key[0x8] = if window.is_key_down(Key::S) { 1 } else { 0 };
    chip.key[0x9] = if window.is_key_down(Key::D) { 1 } else { 0 };
    chip.key[0xA] = if window.is_key_down(Key::Z) { 1 } else { 0 };
    chip.key[0xB] = if window.is_key_down(Key::C) { 1 } else { 0 };
    chip.key[0xC] = if window.is_key_down(Key::Key4) { 1 } else { 0 };
    chip.key[0xD] = if window.is_key_down(Key::R) { 1 } else { 0 };
    chip.key[0xE] = if window.is_key_down(Key::F) { 1 } else { 0 };
    chip.key[0xF] = if window.is_key_down(Key::V) { 1 } else { 0 };
}
