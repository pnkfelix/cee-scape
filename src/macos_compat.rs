use std::marker::PhantomData;

/// `JmpBufFields` are the accessible fields when viewed via a JmpBuf pointer.
/// But also: You shouldn't be poking at these!
#[repr(C)]
pub struct JmpBufFields {
    _buf: [u32; 37],
    _neither_send_nor_sync: PhantomData<*const u8>,
}

/// `SigJmpBufFields` are the accessible fields when viewed via a SigJmpBuf pointer.
/// But also: You shouldn't be poking at these!
#[repr(C)]
pub struct SigJmpBufFields {
    _buf: [u32; 38],
    _neither_send_nor_sync: PhantomData<*const u8>,
}

pub type JmpBufStruct = JmpBufFields;
pub type SigJmpBufStruct = SigJmpBufFields;
