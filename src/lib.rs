extern crate netmap_sys;
extern crate libc;

use std::error;
use std::mem;
use std::ptr;
use std::slice;
use std::iter::Iterator;
use std::ffi::{CStr, CString};
use std::fmt;
use netmap_sys::netmap;
use netmap_sys::netmap_user;

/// Forward slot
pub use netmap_sys::netmap::NS_FORWARD;

/// Indicate that buffer was changed
pub use netmap_sys::netmap::NS_BUF_CHANGED;

/// Report when sent
pub use netmap_sys::netmap::NS_REPORT;

/// Enable forwarding on ring
pub use netmap_sys::netmap::NR_FORWARD;

#[derive(Debug)]
#[allow(dead_code)]
pub enum Direction {
    Input,
    Output,
    InputOutput,
}

#[derive(Debug)]
pub struct NetmapError {
    msg: String,
}

impl NetmapError {
    fn new(msg: String) -> Self {
        NetmapError { msg: msg }
    }
}

impl fmt::Display for NetmapError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Netmap Error: {}", self.msg)
    }
}

impl error::Error for NetmapError {
    fn description(&self) -> &str {
        &self.msg
    }

    fn cause(&self) -> Option<&error::Error> {
        None
    }
}

/// Common functions for Rx and Tx slots
pub trait NetmapSlot {
    fn get_len(&self) -> u16;
    fn get_flags(&self) -> u16;
    fn set_flags(&mut self, flag: u16);
    fn get_buf_idx(&self) -> u32;
    fn set_buf_idx(&mut self, idx: u32);
}

/// Rx (receive) slot
pub struct RxSlot(netmap::netmap_slot);

impl NetmapSlot for RxSlot {
    fn get_len(&self) -> u16 {
        self.0.len
    }

    fn set_flags(&mut self, flag: u16) {
        self.0.flags |= flag;
    }

    fn get_flags(&self) -> u16 {
        self.0.flags
    }

    fn get_buf_idx(&self) -> u32 {
        self.0.buf_idx
    }

    fn set_buf_idx(&mut self, idx: u32) {
        self.0.buf_idx = idx
    }
}

impl RxSlot {
    #[inline]
    pub fn get_buf<'b, 'a>(&'a self, ring: &RxRing) -> &'b [u8] {
        let buf_idx = self.0.buf_idx;
        let buf =
            unsafe { netmap_user::NETMAP_BUF(mem::transmute(ring), buf_idx as isize) as *const u8 };
        unsafe { slice::from_raw_parts::<u8>(buf, self.0.len as usize) }
    }
}

pub struct TxSlot(netmap::netmap_slot);

impl NetmapSlot for TxSlot {
    #[inline]
    fn get_len(&self) -> u16 {
        self.0.len
    }

    #[inline]
    fn set_flags(&mut self, flag: u16) {
        self.0.flags |= flag;
    }

    #[inline]
    fn get_flags(&self) -> u16 {
        self.0.flags
    }

    #[inline]
    fn get_buf_idx(&self) -> u32 {
        self.0.buf_idx
    }

    #[inline]
    fn set_buf_idx(&mut self, idx: u32) {
        self.0.buf_idx = idx
    }
}

/// Tx (transfer) slot
impl TxSlot {
    #[inline]
    pub fn get_buf_mut<'b, 'a>(&'a mut self, ring: &TxRing) -> &'b mut [u8] {
        let buf_idx = self.0.buf_idx;
        let buf =
            unsafe { netmap_user::NETMAP_BUF(mem::transmute(ring), buf_idx as isize) as *mut u8 };
        unsafe { slice::from_raw_parts_mut::<u8>(buf, self.0.len as usize) }
    }

    #[inline]
    pub fn set_len(&mut self, len: u16) {
        self.0.len = len;
    }
}

/// Functions common to Tx and Rx netmap rings
pub trait NetmapRing {
    fn id(&self) -> u16;

    fn is_empty(&self) -> bool;

    /// Advance the cur pointer to the next slot in the ring.
    fn next_slot(&mut self);

    fn set_flags(&mut self, flag: u32);

    /// Sync the head pointer to the value of cur.
    fn head_from_cur(&mut self);
}

/// Rx (receive) ring
pub struct RxRing(netmap::netmap_ring);

impl RxRing {
    #[allow(dead_code)]
    #[inline]
    pub fn get_slot_mut<'a, 'b>(&'a self) -> &'b mut RxSlot {
        let cur = self.0.cur;
        let slots = &self.0.slot as *const netmap::netmap_slot;
        unsafe { mem::transmute(slots.offset(cur as isize)) }
    }

    /// Iterate over (slot, buffer) tuples.
    ///
    /// Advances cur as it progresses. Does not advance head.
    #[inline]
    pub fn iter(&mut self) -> RxSlotIter {
        let cur = self.0.cur;
        RxSlotIter {
            ring: self,
            cur: cur,
        }
    }
}

impl NetmapRing for RxRing {
    #[inline]
    fn id(&self) -> u16 {
        self.0.ringid
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.0.cur == self.0.tail
    }

    #[inline]
    fn set_flags(&mut self, flag: u32) {
        self.0.flags |= flag;
    }

    #[inline]
    fn next_slot(&mut self) {
        self.0.cur = if self.0.cur + 1 == self.0.num_slots {
            0
        } else {
            self.0.cur + 1
        };
    }

    #[inline]
    fn head_from_cur(&mut self) {
        self.0.head = self.0.cur;
    }
}


/// Iterator over Rx slots
pub struct RxSlotIter<'a> {
    ring: &'a mut RxRing,
    cur: u32,
}

impl<'a> RxSlotIter<'a> {
    /// Push a single slot back. Useful when using e.g. zip and the iterator will be advanced
    /// without actually wanting to accept that packet.
    pub fn give_back(&mut self) {
        self.cur = if self.cur > 0 {
            self.cur - 1
        } else {
            self.ring.0.num_slots - 1
        };
    }
}

impl<'a> Iterator for RxSlotIter<'a> {
    type Item = (&'a mut RxSlot, &'a [u8]);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.ring.0.cur = self.cur;

        if self.ring.is_empty() {
            return None;
        }
        let cur = self.cur;
        let slots = self.ring.0.slot.as_mut_ptr();
        let slot: &mut RxSlot = unsafe { mem::transmute(slots.offset(cur as isize)) };
        let buf = slot.get_buf(self.ring);
        self.cur = if self.cur + 1 == self.ring.0.num_slots {
            0
        } else {
            self.cur + 1
        };
        Some((slot, buf))
    }
}

impl<'a> Drop for RxSlotIter<'a> {
    fn drop(&mut self) {
        self.ring.0.cur = self.cur;
    }
}

pub struct RxRingIter<'d> {
    cur: u16,
    last: u16,
    netmap: &'d NetmapDescriptor,
}

impl<'d> Iterator for RxRingIter<'d> {
    type Item = &'d mut RxRing;

    #[inline]
    fn next<'a>(&'a mut self) -> Option<&'d mut RxRing> {
        if self.cur > self.last {
            return None;
        }
        let rx_ring = {
            let cur = self.cur.clone();
            self.netmap.get_rx_ring(cur)
        };
        self.cur += 1;
        Some(rx_ring)
    }
}

/// Tx (transfer) ring
pub struct TxRing(netmap::netmap_ring);

impl TxRing {
    #[inline]
    pub fn get_slot_mut<'a, 'b>(&'a self) -> &'b mut TxSlot {
        let cur = self.0.cur;
        let slots = &self.0.slot as *const netmap::netmap_slot;
        unsafe { mem::transmute(slots.offset(cur as isize)) }
    }

    /// Iterate over (slot, buffer) tuples.
    ///
    /// Advances cur as it progresses. Does not advance head.
    #[inline]
    pub fn iter_mut(&mut self) -> TxSlotIterMut {
        let cur = self.0.cur;
        TxSlotIterMut {
            ring: self,
            cur: cur,
        }
    }
}

impl NetmapRing for TxRing {
    #[inline]
    fn id(&self) -> u16 {
        self.0.ringid
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.0.cur == self.0.tail
    }

    #[inline]
    fn set_flags(&mut self, flag: u32) {
        self.0.flags |= flag;
    }

    #[inline]
    fn next_slot(&mut self) {
        self.0.cur = if self.0.cur + 1 == self.0.num_slots {
            0
        } else {
            self.0.cur + 1
        };
    }

    #[inline]
    fn head_from_cur(&mut self) {
        self.0.head = self.0.cur;
    }
}


impl<'a> Iterator for &'a mut TxRing {
    type Item = &'a mut TxSlot;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.0.cur;
        let slots = &self.0.slot as *const netmap::netmap_slot;
        let slot = unsafe { mem::transmute(slots.offset(cur as isize)) };
        self.next_slot();
        slot
    }
}

pub struct TxRingIter<'d> {
    last: u16,
    cur: u16,
    netmap: &'d NetmapDescriptor,
}

impl<'d> Iterator for TxRingIter<'d> {
    type Item = &'d mut TxRing;

    #[inline]
    fn next<'a>(&'a mut self) -> Option<&'d mut TxRing> {
        if self.cur > self.last {
            return None;
        }
        let tx_ring = {
            let cur = self.cur.clone();
            self.netmap.get_tx_ring(cur)
        };
        self.cur += 1;
        Some(tx_ring)
    }
}

/// Slot and buffer iterator
pub struct TxSlotIterMut<'a> {
    ring: &'a mut TxRing,
    cur: u32,
}

impl<'a> TxSlotIterMut<'a> {
    /// Push a single slot back. Useful when using e.g. zip and the iterator will be advanced
    /// without actually wanting to send that packet.
    pub fn give_back(&mut self) {
        self.cur = if self.cur > 0 {
            self.cur - 1
        } else {
            self.ring.0.num_slots - 1
        };
    }
}

impl<'a> Iterator for TxSlotIterMut<'a> {
    type Item = (&'a mut TxSlot, &'a mut [u8]);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.ring.0.cur = self.cur;

        if self.ring.is_empty() {
            return None;
        }
        let cur = self.cur;
        let slots = self.ring.0.slot.as_mut_ptr();
        let slot: &mut TxSlot = unsafe { mem::transmute(slots.offset(cur as isize)) };
        slot.set_len(2048); /* XXX: use buf_size */
        let buf = slot.get_buf_mut(self.ring);
        self.cur = if self.cur + 1 == self.ring.0.num_slots {
            0
        } else {
            self.cur + 1
        };
        Some((slot, buf))
    }
}

impl<'a> Drop for TxSlotIterMut<'a> {
    fn drop(&mut self) {
        self.ring.0.cur = self.cur;
    }
}


/// Netmap descriptor wrapper
pub struct NetmapDescriptor {
    // Never zero.
    pointer: *mut netmap_user::nm_desc,
}

unsafe impl Send for NetmapDescriptor {}

impl NetmapDescriptor {
    /// Open new netmap descriptor on interface (no "netmap:" prefix)
    ///
    /// iface is the port name. e.g. eth0 for eth0.
    ///   	a suffix can indicate the following:
    ///   	^		bind the host (sw) ring pair
    ///   	*		bind host and NIC ring pairs (transparent)
    ///   	-NN		bind individual NIC ring pair
    ///   	{NN		bind master side of pipe NN
    ///   	}NN		bind slave side of pipe NN
    ///   	a suffix starting with / and the following flags,
    ///   	in any order:
    ///   	x		exclusive access
    ///   	z		zero copy monitor
    ///   	t		monitor tx side
    ///   	r		monitor rx side
    ///   	R		bind only RX ring(s)
    ///   	T		bind only TX ring(s)
    ///
    pub fn new(iface: &str) -> Result<Self, NetmapError> {
        let base_nmd: netmap::nmreq = unsafe { mem::zeroed() };
        let netmap_iface = CString::new(format!("netmap:{}", iface)).unwrap();
        NetmapDescriptor::prim_new(&netmap_iface, &base_nmd, 0, ptr::null())
    }

    /// Open new netmap descriptor on interface, sharing memory with parent descriptor
    /// (for zero-copy forwarding between interfaces)
    ///
    /// iface is the port name. e.g. eth0 for eth0.
    ///   	a suffix can indicate the following:
    ///   	^		bind the host (sw) ring pair
    ///   	*		bind host and NIC ring pairs (transparent)
    ///   	-NN		bind individual NIC ring pair
    ///   	{NN		bind master side of pipe NN
    ///   	}NN		bind slave side of pipe NN
    ///   	a suffix starting with / and the following flags,
    ///   	in any order:
    ///   	x		exclusive access
    ///   	z		zero copy monitor
    ///   	t		monitor tx side
    ///   	r		monitor rx side
    ///   	R		bind only RX ring(s)
    ///   	T		bind only TX ring(s)
    ///
    /// parent is another NetmapDescriptor to share the buffer region with.
    pub fn new_with_memory(iface: &str, parent: &NetmapDescriptor) -> Result<Self, NetmapError> {
        let base_nmd: netmap::nmreq = unsafe { mem::zeroed() };
        let netmap_iface = CString::new(format!("netmap:{}", iface)).unwrap();
        NetmapDescriptor::prim_new(&netmap_iface,
                                   &base_nmd,
                                   netmap_user::NM_OPEN_NO_MMAP as u64,
                                   parent.get_sys())
    }

    fn prim_new(netmap_iface: &CString,
                base_nmd: *const netmap::nmreq,
                flags: u64,
                parent: *const netmap_user::nm_desc)
                -> Result<Self, NetmapError> {
        if let Some(nd) = unsafe {
            netmap_user::nm_open(netmap_iface.as_ptr(), base_nmd, flags, parent).as_mut()
        } {
            Ok(NetmapDescriptor { pointer: nd })
        } else {
            Err(NetmapError::new(format!("Can't open {:?}", netmap_iface)))
        }
    }

    pub fn rx_iter<'i, 'd: 'i>(&'d mut self) -> RxRingIter<'i> {
        let (first, last) = self.get_rx_rings();

        RxRingIter {
            last: last,
            cur: first,
            netmap: self,
        }
    }

    pub fn tx_iter<'i, 'd: 'i>(&'d mut self) -> TxRingIter<'i> {
        let (first, last) = self.get_tx_rings();

        TxRingIter {
            last: last,
            cur: first,
            netmap: self,
        }
    }

    /// Open new netmap descriptor using for a particular ring
    pub fn clone_ring(&self, ring: u16, dir: Direction) -> Result<Self, NetmapError> {
        // XXX: I think this does a byte copy of the nm_desc struct...
        // So really this doesn't make super sense, and we should improve netmap_sys in that
        // regard.
        let mut nm_desc: netmap_user::nm_desc = *self.get_sys();

        // XXX: check that we opened it with ALL_NIC before
        let (flag, ring_flag) = match dir {
            Direction::Input => (netmap::NR_RX_RINGS_ONLY, netmap::NETMAP_NO_TX_POLL),
            Direction::Output => (netmap::NR_TX_RINGS_ONLY, 0),
            Direction::InputOutput => (0, 0),
        };
        nm_desc.req.nr_flags = netmap::NR_REG_ONE_NIC as u32 | flag as u32;
        if ring == self.get_rx_rings_count() {
            nm_desc.req.nr_flags = netmap::NR_REG_SW as u32 | flag
        };
        nm_desc.req.nr_ringid = ring | ring_flag as u16;
        nm_desc.self_ = &mut nm_desc;

        let ifname = unsafe { CStr::from_ptr(nm_desc.req.nr_name.as_ptr()).to_str().unwrap() };
        let netmap_ifname = CString::new(format!("netmap:{}", ifname)).unwrap();

        NetmapDescriptor::prim_new(&netmap_ifname,
                                   ptr::null(),
                                   netmap_user::NM_OPEN_NO_MMAP as u64 |
                                   netmap_user::NM_OPEN_IFNAME as u64, // | flag as u64
                                   &nm_desc)
    }

    pub fn get_rx_rings_count(&self) -> u16 {
        let nifp = self.get_sys().nifp;
        unsafe { (*nifp).ni_rx_rings as u16 }
    }

    pub fn get_tx_rings_count(&self) -> u16 {
        let nifp = self.get_sys().nifp;
        unsafe { (*nifp).ni_tx_rings as u16 }
    }

    #[allow(dead_code)]
    pub fn get_flags(&self) -> u32 {
        self.get_sys().req.nr_flags
    }

    /// Returns first and last RX ring
    pub fn get_rx_rings(&self) -> (u16, u16) {
        let &nm_desc = self.get_sys();
        (nm_desc.first_rx_ring, nm_desc.last_rx_ring)
    }

    pub fn get_tx_rings(&self) -> (u16, u16) {
        let &nm_desc = self.get_sys();
        (nm_desc.first_tx_ring, nm_desc.last_tx_ring)
    }

    #[inline]
    fn get_tx_ring(&self, ring: u16) -> &mut TxRing {
        let nifp = self.get_sys().nifp;

        unsafe { mem::transmute(netmap_user::NETMAP_TXRING(nifp, ring as isize)) }
    }

    #[inline]
    fn get_rx_ring(&self, ring: u16) -> &mut RxRing {
        let nifp = self.get_sys().nifp;

        unsafe { mem::transmute(netmap_user::NETMAP_RXRING(nifp, ring as isize)) }
    }

    #[allow(dead_code)]
    fn find_free_tx_ring(&self) -> Option<&mut TxRing> {
        let (first, last) = self.get_tx_rings();

        for ring in first..last + 1 {
            let tx_ring = self.get_tx_ring(ring);
            if !tx_ring.is_empty() {
                return Some(tx_ring);
            }
        }
        return None;
    }

    pub fn get_fd(&self) -> i32 {
        self.get_sys().fd
    }

    #[deprecated]
    pub fn poll(&mut self, dir: Direction) -> Option<()> {
        let mut pollfd: libc::pollfd = unsafe { mem::zeroed() };

        pollfd.fd = self.get_fd();
        pollfd.events = match dir {
            Direction::Input => libc::POLLIN,
            Direction::Output => libc::POLLOUT,
            Direction::InputOutput => libc::POLLIN | libc::POLLOUT,
        };

        let rv = unsafe { libc::poll(&mut pollfd, 1, 1000) };
        if rv <= 0 {
            return None;
        }
        if pollfd.revents & libc::POLLERR == libc::POLLERR {
            return None;
        }
        Some(())
    }
}

// Private functions.
impl NetmapDescriptor {
    /// Take a reference.
    fn get_sys(&self) -> &netmap_user::nm_desc {
        unsafe { &*self.pointer }
    }

    /// Take a mutable reference.
    #[allow(dead_code)]
    fn get_mut_sys(&mut self) -> &mut netmap_user::nm_desc {
        unsafe { &mut *self.pointer }
    }
}


impl fmt::Display for NetmapDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Netmap FD: {}", self.get_sys().fd)
    }
}


impl Drop for NetmapDescriptor {
    fn drop(self: &mut NetmapDescriptor) {
        unsafe {
            netmap_user::nm_close(self.get_mut_sys());
        }
    }
}
