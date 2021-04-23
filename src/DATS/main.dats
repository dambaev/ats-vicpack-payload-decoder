
#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

#define LIBS_targetloc "../libs" (* search path for external libs *)
#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
staload Vicpack="{$LIBS}/ats-vicpack/src/SATS/vicpack.sats"
staload B64="{$LIBS}/ats-base64/SATS/ats-base64.sats"
staload UN="prelude/SATS/unsafe.sats"

%{

#include "poll.h" // pollfd
#include "sys/ioctl.h" // ioctl
#include "unistd.h" // posix

%}
%{
#define BAND(a,b) ((a) & (b))
%}
extern
fn band
  ( a: sint
  , b: sint
  ): sint = "mac#BAND"
  

typedef pollfd_t = $extype_struct"struct pollfd" of
{ fd = int
, events = sint
, revents = sint
}

extern
val POLLIN:sint = "mac#POLLIN"
extern
val POLLERR:sint = "mac#POLLERR"
typedef nfds_t = $extype"nfds_t"

extern
fn poll
  { n: pos}{l:agz}
  ( fds_pf: !array_v(pollfd_t, l, n)
  | fds: ptr l
  , nfds: size_t n
  , timeout: int
  ) : int = "mac#"

extern
val FIONREAD:int = "mac#FIONREAD"

extern
fn get_fd_pending_bytes
   ( socket: int
   ): size_t
implement get_fd_pending_bytes(socket) = res where {
   var res: size_t = i2sz 0
   val _ = $extfcall( size_t, "ioctl", socket, FIONREAD, addr@res)
}
extern
fn read
  {a: t0ype | sizeof(a) == sizeof(char) || sizeof(a) == sizeof(uchar) }{n: nat}{l:agz}
  ( pf: !array_v( a?, l, n) >> array_v(a, l, n)
  | fd: int
  , ptr l
  , sz: size_t n
  ): ssize_t = "mac#"

fn
  handle_line
  ( i: !$BS.Bytestring0
  ): void = 
let
  val i_sz = length i
in
  ifcase
  | i_sz < 4 => ()
  | i_sz <> i2sz 4 * ( i_sz / i2sz 4) => ()
  | _ => {
    prval _ = $BS.lemma_bytestring_param(i)
    val ( pf | p, sz) = $BS.bs2bytes_ro(i)
    val p_s = ptr2str( pf | p, sz) where {
      extern castfn
        ptr2str
        {n:nat}{l:addr}
        ( !array_v(char, l, n)
        | ptr l
        , size_t n
        ):<> string(n)
    }
    val () =
      case+ $B64.decode1( p_s, sz) of
      | ~None_vt() => $BS.printlnC( $BS.pack "failed to decode base64 line")
      | ~Some_vt( decoded0) => {
        val ( arr, cap, sz) = decoded0
        val () =
          if sz < 6
          then ()
          else {
            val ( arr_pf | arr_p) = arrayptr_takeout_viewptr arr
            var decoded: $BS.Bytestring0?
            val () = decoded := $BS.pack( arr_pf | arr_p, sz, cap)
            val (decoded_ls, unsupported_sz) = $Vicpack.parse decoded
            val () =
              if unsupported_sz > 0
              then $BS.printlnC( $BS.pack "unsupported packages count: "
                + $BS.pack_uint32 ($UN.cast{uint32}unsupported_sz)
                )
            val () = handle_vicpack( decoded_ls) where {
                fun
                  handle_vicpack
                  {n:int | n >= 0}
                  .<n>.
                  ( xs: list_vt( $Vicpack.Vicpack, n)
                  ): void =
                case+ xs of
                | ~list_vt_nil() => ()
                | ~list_vt_cons( head, tail) => handle_vicpack tail where {
                  val () = $Vicpack.print_vicpack( head)
                  val () = $Vicpack.free head
                }
              }
            val () = $BS.free( arr_pf | decoded)
            prval () = arrayptr_addback( arr_pf | arr)
          }
        val () = arrayptr_free arr
      }
    prval () = $BS.bytes_addback( pf | i)
  }
end

fn
  {a:viewt0ype}{env0:viewt0ype}
  list_vt_freelin_funenv
  {fe:eff}{n:nat}
  ( l: list_vt( a, n)
  , env: &env0 >> _
  , f: ( &env0 >> _, a ) -<fe> void
  ):<!wrt,fe>
  void = loop( l, env, f) where {
  fun
    loop
    {n:nat}
    .<n>.
    ( l: list_vt(a, n)
    , env: &env0 >> _
    , f: ( &env0 >> _, a)-<fe> void
    ):<!wrt,fe>
    void =
    case+ l of
    | ~list_vt_nil() => ()
    | ~list_vt_cons( head, tail) => loop( tail, env, f) where {
      val () = f( env, head)
    }
}

fn
  handle_lines
  ( i: &$BS.BytestringNSH0 >> $BS.BytestringNSH0
  ): void = 
let
  prval () = $BS.lemma_bytestring_param( i)
  var lines: List_vt( $BS.Bytestring0)?
  val () = lines := $BS.split_on( '\n', i)
  val last_idx = list_vt_length lines
in
  ifcase
  | last_idx = 0 => {
    val+ ~list_vt_nil() = lines
  }
  | last_idx = 1 => {
    val+ ~list_vt_cons(head, tail) = lines
    val+ ~list_vt_nil() = tail
    val () = println!("no newline detected in the input, appending input to old leftovers")
    val () = $BS.free( head, i)
  }
  | _ => i := last where {
    var last: $BS.Bytestring0?
    val () = last := list_vt_takeout_at( lines, last_idx - 1)
    val () = cleaner( lines, i) where {
      fun
        cleaner
        {n, cap, ucap, refcnt, elen, eoffset:nat | refcnt > n}{dynamic:bool}{l:addr}
        .<n>.
        ( xs: list_vt( [len, offset:nat] $BS.Bytestring_vtype( len, offset, cap, 0, 1, dynamic, l), n)
        , env: &$BS.Bytestring_vtype( elen, eoffset, cap, ucap, refcnt, dynamic, l) >> $BS.Bytestring_vtype( elen, eoffset, cap, ucap, refcnt - n, dynamic, l)
        ):
        void =
      case+ xs of
      | ~list_vt_nil() => ()
      | ~list_vt_cons( head, tail) =>
        if length head > 0
        then cleaner( tail, env) where {
          val () = handle_line( head)
          val () = $BS.free( head, env)
        }
        else cleaner( tail, env) where {
          val () = $BS.free( head, env)   
        }
    }
    val () = $BS.free( i, last)
  }
  
end

fun
  loop
  {n:nat | n > 0}{l:agz}
  ( fds_pf: !array_v(pollfd_t, l, n)
  | buf: &$BS.BytestringNSH0 >> _
  , fds: ptr l
  , fds_sz: size_t n
  ): void =
case+ poll( fds_pf | fds, fds_sz, ~1) of
| some when some = (~1) => loop( fds_pf | buf, fds, fds_sz) where {
  val () = println!("timeouted")
}
| 0 => loop( fds_pf | buf, fds, fds_sz) where {
  val () = println!("interrupted")
}
| fds_available =>
let
  prval (pf1, pf2) = array_v_uncons( fds_pf)
  val pollfd = !fds
  prval () = fds_pf := array_v_cons( pf1, pf2)
in
  if band( pollfd.revents, POLLIN) <> POLLIN
  then handle_line( buf) (* process the rest and exit *)
  else loop (fds_pf | buf, fds, fds_sz) where {
    val available = g1ofg0( get_fd_pending_bytes( pollfd. fd))
    val () = println!("available for read: ", available)
    val () =
      if available > 0
      then {
        val ( pf, fpf | p) = array_ptr_alloc<uchar>( available)
        val readed = read{uchar}( pf | 0, p, available)
        var newinput: $BS.Bytestring0?
        val () = newinput := $BS.pack( pf, fpf | p, available, available)
        val () =
          if length buf > 0
          then {
            prval () = $BS.lemma_bytestring_param(buf)
            val () = buf := buf + newinput
            val () = handle_lines( buf)
          }
          else {
            val () = free buf
            val () = buf := newinput
            val () = handle_lines( buf)
          }
      }
      else ()
  }
end

implement main0() = {
  var buf: $BS.Bytestring0?
  val () = buf := $BS.empty()
  val ( pf, fpf | p) = array_ptr_alloc<pollfd_t>(i2sz 1)
  prval () = initialize{pollfd_t}(pf) where {
    extern prval initialize
      {a:t0ype}{l:addr}{n:nat}
      ( pf: !array_v( a?, l, n) >> array_v(a,l,n)
      ): void
  }
  prval (pf1, pf2) = array_v_uncons pf
  val () = !p := (@{ fd = g0ofg1 0, events = POLLIN, revents = g0int2int_int_sint 0}:pollfd_t)
  prval () = pf := array_v_cons( pf1, pf2)
  val () = loop( pf | buf, p, i2sz 1)
  val () = array_ptr_free( pf, fpf | p)
  val () = $BS.free buf
}