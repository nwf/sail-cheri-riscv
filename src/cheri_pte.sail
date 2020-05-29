/* PTE attributes, permission checks and updates */

type pteAttribs = bits(8)

bitfield PTE_Bits : pteAttribs = {
  D : 7,
  A : 6,
  G : 5,
  U : 4,
  X : 3,
  W : 2,
  R : 1,
  V : 0
}

/*
 * Reserved PTE bits used by extensions on RV64.
 *
 * There are no such bits on RV32/SV32, so we hard-code both StoreCap=1
 * and LoadCap=1 (i.e., there is no ability to disable capability loads
 * from or stores to pages in the SV32 MMU).
 */
type extPte = bits(10)

bitfield Ext_PTE_Bits : extPte = {
  StoreCap     : 9, /* Permit capability stores */
  LoadCap      : 8, /* Permit capability loads */
}

function isPTEPtr(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.R() == 0b0 & a.W() == 0b0 & a.X() == 0b0
}

function isInvalidPTE(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.V() == 0b0 | (a.W() == 0b1 & a.R() == 0b0)
}

union PTE_Check = {
  PTE_Check_Success : ext_ptw,
  PTE_Check_Failure : ext_ptw
}

function checkPTEPermission(ac : AccessType(ext_access_type), priv : Privilege, mxr : bool, do_sum : bool, p : PTE_Bits, ext : extPte, ext_ptw : ext_ptw) -> PTE_Check = {
  let    e = Mk_Ext_PTE_Bits(ext);
  let lcav = if e.LoadCap()  == 0b1 then PTW_LCM_OK else PTW_LCM_CLR;
  let scav = if e.StoreCap() == 0b1 then PTW_SCM_OK else PTW_SCM_TRAP;
  let (succ, ext_ptw') : (bool, ext_ptw) =
  match (ac, priv) {
    (Read(Data),      User)       => (p.U() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)), ext_ptw),
    (Write(Data),     User)       => (p.U() == 0b1 & p.W() == 0b1, ext_ptw),
    (ReadWrite(Data), User)       => (p.U() == 0b1 & p.W() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)), ext_ptw),
    (Execute(),       User)       => (p.U() == 0b1 & p.X() == 0b1, ext_ptw),

    (Read(Data),      Supervisor) => ((p.U() == 0b0 | do_sum) & (p.R() == 0b1 | (p.X() == 0b1 & mxr)), ext_ptw),
    (Write(Data),     Supervisor) => ((p.U() == 0b0 | do_sum) & p.W() == 0b1, ext_ptw),
    (ReadWrite(Data), Supervisor) => ((p.U() == 0b0 | do_sum) & p.W() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)), ext_ptw),
    (Execute(),       Supervisor) => (p.U() == 0b0 & p.X() == 0b1, ext_ptw),

    (Read(Cap),       User)       => { /* load-cap should probably not be affected by mxr. */
                                       if   p.U() == 0b1 & p.R() == 0b1
                                       then
                                         /*
                                          * Allow the address translation to proceed,
                                          * but mark for tag stripping
                                          */
                                         (true, ext_ptw_join_lcm(ext_ptw, lcav))
                                       else (false, ext_ptw)
                                     },

    (Write(Cap),      User)       => { if   p.U() == 0b1 & p.W() == 0b1
                                       then
                                         /*
                                          * Allow the address translation to proceed,
                                          * but mark for faulting on tag store
                                          */
                                         (true, ext_ptw_join_scm(ext_ptw, scav))
                                       else (false, ext_ptw)
                                     },

    (ReadWrite(Cap),  User)       => { if   p.U() == 0b1 & p.R() == 0b1 & p.W() == 0b1
                                       then
                                         /* Both caveats apply */
                                         (true, ext_ptw_join_scm(ext_ptw_join_lcm(ext_ptw, lcav), scav))
                                       else (false, ext_ptw)
                                     },

    (Read(Cap),       Supervisor) => { if   (p.U() == 0b0 | do_sum) & p.R() == 0b1
                                       then (true, ext_ptw_join_lcm(ext_ptw, lcav))
                                       else (false, ext_ptw)
                                     },

    (Write(Cap),      Supervisor) => { if   (p.U() == 0b0 | do_sum) & p.W() == 0b1
                                       then (true, ext_ptw_join_scm(ext_ptw, scav))
                                       else (false, ext_ptw)
                                     },

    (ReadWrite(Cap),  Supervisor) => { if   (p.U() == 0b0 | do_sum) & p.R() == 0b1 & p.W() == 0b1
                                       then (true, ext_ptw_join_scm(ext_ptw_join_lcm(ext_ptw, lcav), scav))
                                       else (false, ext_ptw)
                                     },

    (_,               Machine)    => internal_error("m-mode mem perm check")
  };

  if succ then PTE_Check_Success(ext_ptw') else PTE_Check_Failure(ext_ptw')
}

function update_PTE_Bits(p : PTE_Bits, a : AccessType(ext_access_type), ext : extPte) -> option((PTE_Bits, extPte)) = {
  let update_d = (a == Write(Data) | a == ReadWrite(Data)) & p.D() == 0b0; // dirty-bit
  let update_a = p.A() == 0b0;                                             // accessed-bit
  if update_d | update_a then {
    let np = update_A(p, 0b1);
    let np = if update_d then update_D(np, 0b1) else np;
    Some(np, ext)
  } else None()
}
