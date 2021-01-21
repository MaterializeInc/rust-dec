use std::ffi::CStr;
use std::mem::MaybeUninit;

use c_str_macro::c_str;
use libc::c_char;

use decnumber_sys::{decContext, decNumber, DEC_INIT_BASE};

#[test]
fn simple_addition() {
    let mut ctx = MaybeUninit::<decContext>::uninit();
    let mut ctx = unsafe {
        decnumber_sys::decContextDefault(ctx.as_mut_ptr(), DEC_INIT_BASE);
        ctx.assume_init()
    };
    ctx.traps = 0;
    ctx.digits = 3;

    let mut a = MaybeUninit::<decNumber>::uninit();
    let mut b = MaybeUninit::<decNumber>::uninit();
    let (mut a, mut b) = unsafe {
        decnumber_sys::decNumberFromString(a.as_mut_ptr(), c_str!("1.23").as_ptr(), &mut ctx);
        decnumber_sys::decNumberFromString(b.as_mut_ptr(), c_str!("4.71").as_ptr(), &mut ctx);
        (a.assume_init(), b.assume_init())
    };

    unsafe {
        decnumber_sys::decNumberAdd(&mut a, &mut a, &mut b, &mut ctx);
    }

    let mut buf = vec![0_u8; 5];
    unsafe {
        decnumber_sys::decNumberToString(&mut a, buf.as_mut_ptr() as *mut c_char);
    }
    let s = CStr::from_bytes_with_nul(&*buf).unwrap().to_str().unwrap();
    assert_eq!(s, "5.94");
}

#[test]
fn endianness() {
    let mut ctx = MaybeUninit::<decContext>::uninit();
    unsafe {
        decnumber_sys::decContextDefault(ctx.as_mut_ptr(), DEC_INIT_BASE);
        assert_eq!(decnumber_sys::decContextTestEndian(0), 0);
    };
}
