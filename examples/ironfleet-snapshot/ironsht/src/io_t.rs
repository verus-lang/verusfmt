#![verus::trusted]
use builtin::*;
use builtin_macros::*;

use crate::environment_t::*;
use vstd::prelude::*;
use vstd::prelude::*;
//
use crate::abstract_end_point_t::*;
use crate::args_t::*;
use vstd::slice::*;
// for clone_vec placeholder

// For DuctTapeProfiler
use std::collections::HashMap;
use std::time::{Duration, SystemTime};

use std::net::UdpSocket;

verus! {

/// NOTE: no longer need HostEnvironment, its state is inlined in NetClient
///
/// - OkState is replaced with State
/// - NetState is history
/// - NowState is not (yet) implemented
/// - files was empty in Ironfleet
pub struct HostEnvironment {}

//pub struct Environment {
//    ok: bool
//}
// #[derive(Copy, Clone)]
#[derive(PartialEq, Eq, Hash)]
pub struct EndPoint {
    pub id: Vec<u8>,
}

//impl Clone for EndPoint {
//    fn clone(&self) -> (res: EndPoint)
//        ensures res@ == self@
//    {
//        EndPoint{id: clone_vec_u8(&self.id)}
//    }
//}
impl EndPoint {
    // Verus unimpl: Can't call clone through the trait
    pub fn clone_up_to_view(&self) -> (res: EndPoint)
        ensures
            res@ == self@,
    {
        EndPoint { id: clone_vec_u8(&self.id) }
    }

    pub open spec fn view(self) -> AbstractEndPoint {
        AbstractEndPoint { id: self.id@ }
    }

    // EndPointIsAbstractable
    // (this has generally been unused)
    #[verifier(inline)]
    pub open spec fn abstractable(self) -> bool {
        self@.valid_physical_address()
    }

    pub open spec fn valid_public_key(&self) -> bool {
        self@.valid_physical_address()
    }

    // Translates Common/Native/Io.s.dfy
    pub fn valid_physical_address(&self) -> (out: bool)
        ensures
            out == self@.valid_physical_address(),
    {
        self.id.len() < 0x100000
    }
}

pub open spec fn abstractify_end_points(end_points: Vec<EndPoint>) -> Seq<AbstractEndPoint> {
    end_points@.map(|i, end_point: EndPoint| end_point@)
}

pub type NetPacket = LPacket<AbstractEndPoint, Seq<u8>>;

pub type NetEvent = LIoOp<AbstractEndPoint, Seq<u8>>;

pub type History = Seq<NetEvent>;

pub enum State {
    Receiving,
    Sending,
    Error,
}

pub enum NetcReceiveResult {  // Not to be confused with Ironfleet's ReceiveResult type, which contains a parsed message
    Received { sender: EndPoint, message: Vec<u8> },
    TimedOut,
    Error,
}

pub struct IronfleetIOError {
    pub message: String,
}

pub closed spec fn from_trusted_code() -> bool {
    true
}

#[verifier(external_body)]
pub struct NetClientCPointers {
    get_time_func: extern "C" fn () -> u64,
    receive_func: extern "C" fn (
        i32,
        *mut bool,
        *mut bool,
        *mut *mut std::vec::Vec<u8>,
        *mut *mut std::vec::Vec<u8>,
    ),
    send_func: extern "C" fn (u64, *const u8, u64, *const u8) -> bool,
}

#[verifier::external_body]
pub struct DuctTapeProfiler {
    last_event: SystemTime,
    last_report: SystemTime,
    event_counter: HashMap<std::string::String, u64>,
}

impl DuctTapeProfiler {
    #[verifier(external)]
    fn new() -> Self {
        println!("Report-ready");
        DuctTapeProfiler {
            last_event: SystemTime::now(),
            last_report: SystemTime::now(),
            event_counter: HashMap::new(),
        }
    }

    #[verifier(external)]
    fn duration_as_ns(duration: &Duration) -> u64 {
        duration.as_secs() * 1_000_000_000 + duration.subsec_nanos() as u64
    }

    #[verifier(external)]
    fn mark_duration(&mut self, label: &str) {
        let now = SystemTime::now();
        let duration_ns = Self::duration_as_ns(
            &now.duration_since(self.last_event).expect("arrow of time"),
        );
        self.increment_event(label, duration_ns);
        self.last_event = now;
        self.maybe_report(&now);
    }

    #[verifier(external)]
    fn record_event(&mut self, label: &str) {
        self.increment_event(label, 1);
    }

    #[verifier(external)]
    fn increment_event(&mut self, label: &str, incr: u64) {
        if let Some(entry) = self.event_counter.get_mut(label) {
            *entry += incr;
        } else {
            self.event_counter.insert(label.to_string(), incr);
        }
    }

    #[verifier(external)]
    fn maybe_report(&mut self, now: &SystemTime) {
        let report_period = 1 * 1_000_000_000;
        let report_duration_ns = Self::duration_as_ns(
            &now.duration_since(self.last_report).expect("arrow of time"),
        );
        if report_duration_ns > report_period {
            self.increment_event("report-duration-ns", report_duration_ns);
            self.report();
            self.last_report = now.clone();
            self.event_counter = HashMap::new();
        }
    }

    #[verifier(external)]
    fn report(&self) {
        for (key, value) in &self.event_counter {
            if key.ends_with("-ns") {
                let ms = *value as f64 / 1e6;
                println!("{key}: {ms} ms");
            } else {
                println!("{key}: {value} count");
            }
        }
        println!("");
    }
}

pub struct NetClient {
    state: Ghost<State>,
    history: Ghost<History>,
    end_point: EndPoint,
    c_pointers: NetClientCPointers,
    profiler: DuctTapeProfiler,
}

impl NetClient {
    //////////////////////////////////////////////////////////////////////////////
    // player-1 accessible interfaces (note requires from_trusted_code())
    //////////////////////////////////////////////////////////////////////////////
    #[verifier(external)]
    pub fn new(
        end_point: EndPoint,
        get_time_func: extern "C" fn () -> u64,
        receive_func: extern "C" fn (
            i32,
            *mut bool,
            *mut bool,
            *mut *mut std::vec::Vec<u8>,
            *mut *mut std::vec::Vec<u8>,
        ),
        send_func: extern "C" fn (u64, *const u8, u64, *const u8) -> bool,
    ) -> (net_client: Self)
        requires
            from_trusted_code(),
        ensures
            net_client.state() is Receiving,
            net_client.history() == Seq::<NetEvent>::empty(),
            net_client.my_end_point() == end_point,
    {
        NetClient {
            state: Ghost(State::Receiving),
            history: Ghost(seq![]),
            end_point,
            c_pointers: NetClientCPointers {
                get_time_func: get_time_func,
                receive_func: receive_func,
                send_func: send_func,
            },
            profiler: DuctTapeProfiler::new(),
        }
    }

    // Main loop (Player 1 audited code) resets the state after having seen Player 2
    // complete a proof of refinement to an atomic protocol step.
    pub fn reset(&mut self)
        requires
            from_trusted_code(),
        ensures
            self.state() is Receiving,
            self.my_end_point() == old(self).my_end_point(),
    {
        self.state = Ghost(State::Receiving);
    }

    //////////////////////////////////////////////////////////////////////////////
    // player-2 accessible interfaces
    //////////////////////////////////////////////////////////////////////////////
    // This state field is how Player 2 proves that it calls receive before send.
    pub closed spec fn state(&self) -> State {
        self.state@
    }

    /// Translates calls to env.ok.ok().
    pub open spec fn ok(&self) -> bool {
        !(self.state() is Error)
    }

    /// translates NetClient.NetClientIsValid
    pub open spec fn valid(&self) -> bool {
        &&& self.ok()
        &&& self.my_end_point().abstractable()
    }

    pub closed spec fn history(&self) -> History {
        self.history@
    }

    /// Translates MyPublicKey()
    pub closed spec fn my_end_point(&self) -> AbstractEndPoint {
        self.end_point@
    }

    pub fn get_my_end_point(&self) -> (ep: EndPoint)
        ensures
            ep@ == self.my_end_point(),
    {
        self.end_point.clone_up_to_view()
    }

    #[verifier(external)]
    pub fn get_time_internal(&self) -> (time: u64)
        requires
            from_trusted_code(),
    {
        (self.c_pointers.get_time_func)()
    }

    #[verifier(external_body)]
    pub fn get_time(&mut self) -> (time: u64)
        requires
            old(self).state() is Receiving,
        ensures
            ({
                &&& self.state() is Sending
                &&& self.history() == old(self).history() + seq![
                    LIoOp::ReadClock { t: time as int },
                ]
            }),
    {
        let time: u64 = self.get_time_internal();
        self.state = Ghost(State::Sending);
        self.history = Ghost(
            self.history@ + seq![LIoOp::<AbstractEndPoint, Seq<u8>>::ReadClock { t: time as int }],
        );
        time
    }

    #[verifier(external)]
    pub unsafe fn receive_internal(&mut self, time_limit_s: i32) -> (result: NetcReceiveResult) {
        let mut ok: bool = true;
        let mut timed_out: bool = true;
        let mut remote = std::mem::MaybeUninit::<*mut std::vec::Vec<u8>>::uninit();
        let mut buffer = std::mem::MaybeUninit::<*mut std::vec::Vec<u8>>::uninit();

        self.profiler.mark_duration("processing-ns");
        (self.c_pointers.receive_func)(
            time_limit_s,
            &mut ok,
            &mut timed_out,
            remote.as_mut_ptr(),
            buffer.as_mut_ptr(),
        );
        self.profiler.mark_duration("awaiting-receive-ns");

        if ok {
            if timed_out {
                self.profiler.record_event("receive-timedout");
                NetcReceiveResult::TimedOut {  }
            } else {
                self.profiler.record_event("receive-ok");
                let remote_ptr: *mut std::vec::Vec<u8> = remote.assume_init();
                let buffer_ptr: *mut std::vec::Vec<u8> = buffer.assume_init();
                let remote_box: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(
                    remote_ptr,
                );
                let buffer_box: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(
                    buffer_ptr,
                );
                let remote_vec: std::vec::Vec<u8> = *remote_box;
                let buffer_vec: std::vec::Vec<u8> = *buffer_box;
                let mut remote_verus_vec: Vec<u8> = Vec::new();
                remote_verus_vec = remote_vec;
                let mut buffer_verus_vec: Vec<u8> = Vec::new();
                buffer_verus_vec = buffer_vec;
                NetcReceiveResult::Received {
                    sender: EndPoint { id: remote_verus_vec },
                    message: buffer_verus_vec,
                }
            }
        } else {
            self.profiler.record_event("receive-error");
            NetcReceiveResult::Error {  }
        }
    }

    #[verifier(external_body)]
    pub fn receive(&mut self, time_limit_s: i32) -> (result: NetcReceiveResult)
        requires
            old(self).state() is Receiving,
        ensures
            self.my_end_point() == old(self).my_end_point(),
            match result {
                NetcReceiveResult::Received { sender, message } => {
                    &&& self.state() is Receiving
                    &&& sender.abstractable()
                    &&& self.history() == old(self).history() + seq![
                        LIoOp::Receive {
                            r: LPacket { dst: self.my_end_point(), src: sender@, msg: message@ },
                        },
                    ]
                },
                NetcReceiveResult::TimedOut {  } => {
                    &&& self.state() is Sending
                    &&& self.history() == old(self).history() + seq![
                        LIoOp  /*TODO(verus) fix name when qpath fix*/
                        ::TimeoutReceive {  },
                    ]
                },
                NetcReceiveResult::Error {  } => { self.state() is Error },
            },
    {
        let result: NetcReceiveResult = unsafe { self.receive_internal(time_limit_s) };
        match result {
            NetcReceiveResult::Received { ref sender, ref message } => {
                self.history = Ghost(
                    self.history@ + seq![
                        LIoOp::Receive {
                            r: LPacket::<AbstractEndPoint, Seq<u8>> {
                                dst: self.my_end_point(),
                                src: sender@,
                                msg: message@,
                            },
                        },
                    ],
                );
            },
            NetcReceiveResult::TimedOut {  } => {
                self.history = Ghost(self.history@ + seq![LIoOp::TimeoutReceive {  }]);
            },
            NetcReceiveResult::Error {  } => {
                self.state = Ghost(State::Error {  });
            },
        }
        result
    }

    #[verifier(external)]
    pub unsafe fn send_internal(&mut self, remote: &EndPoint, message: &Vec<u8>) -> (result: Result<
        (),
        IronfleetIOError,
    >) {
        let remote_raw: *const u8 = remote.id.as_ptr();
        let message_raw: *const u8 = message.as_ptr();
        let b: bool = (self.c_pointers.send_func)(
            remote.id.len() as u64,
            remote_raw,
            message.len() as u64,
            message_raw,
        );
        if b {
            Ok(())
        } else {
            Err(IronfleetIOError { message: "Failed to send".to_string() })
        }
    }

    #[verifier(external_body)]
    pub fn send_internal_wrapper(&mut self, remote: &EndPoint, message: &Vec<u8>) -> (result:
        Result<(), IronfleetIOError>)
        ensures
            *self == *old(self),
    {
        unsafe { self.send_internal(remote, message) }
    }

    pub fn send(&mut self, recipient: &EndPoint, message: &Vec<u8>) -> (result: Result<
        (),
        IronfleetIOError,
    >)
        requires
            !(old(self).state() is Error),
        ensures
            self.my_end_point() == old(self).my_end_point(),
            self.state() is Error <==> result is Err,
            result is Ok ==> self.state() is Sending,
            result is Ok ==> self.history() == old(self).history() + seq![
                LIoOp::Send {
                    s: LPacket { dst: recipient@, src: self.my_end_point(), msg: message@ },
                },
            ],
    {
        let result: Result<(), IronfleetIOError> = self.send_internal_wrapper(recipient, message);
        match result {
            Ok(_) => {
                self.state = Ghost(State::Sending {  });
                self.history = Ghost(
                    self.history@ + seq![
                        LIoOp::Send {
                            s: LPacket { dst: recipient@, src: self.my_end_point(), msg: message@ },
                        },
                    ],
                );
            },
            Err(_) => {
                self.state = Ghost(State::Error {  });
            },
        };
        result
    }
}

} // verus!
