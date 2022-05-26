#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

#[allow(unused_imports)] use netsblox_vm;

use core::panic::PanicInfo;
use core::alloc::{GlobalAlloc, Layout};

struct NoAlloc;
unsafe impl GlobalAlloc for NoAlloc {
    unsafe fn alloc(&self, _: Layout) -> *mut u8 { loop { } }
    unsafe fn dealloc(&self, _: *mut u8, _: Layout) { loop { } }
}

#[global_allocator] static GLOBAL: NoAlloc = NoAlloc;
#[alloc_error_handler] fn alloc_err(_: Layout) -> ! { loop { } }
#[panic_handler] fn panic(_info: &PanicInfo) -> ! { loop { } }
#[no_mangle] extern "C" fn _start() -> ! { loop { } }
