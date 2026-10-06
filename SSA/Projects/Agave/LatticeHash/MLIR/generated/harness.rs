#![allow(private_interfaces)]
mod lt_hash { pub struct LtHash(pub [u16; 1024]); }
mod batch {
    const BLOCK_LEN: usize = 64;
    const MAX_LANES: usize = 16;
    type LaneBuf = [u32; 256];
    #[derive(Clone, Copy)]
    struct Batch<'a> { lanes: &'a [LaneBuf], lengths: &'a [usize] }
    impl Batch<'_> { fn len(&self) -> usize { self.lanes.len() } }
    #[path = "../arch.rs"]
    pub mod arch;
}
