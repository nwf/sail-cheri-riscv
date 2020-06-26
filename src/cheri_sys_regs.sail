/* CHERI system CSRs */

/* Capability control csr */

bitfield ccsr : xlenbits = {
  cap_idx : 15 .. 10,
  cause   :  9 .. 5, /* cap cause */
  gclgu   :  3,      /* Global Cap Load Gen bit for User pages */
  gclgs   :  2,      /* Global Cap Load Gen bit for System (not User) pages */
  d       :  1,      /* dirty  */
  e       :  0       /* enable */
}

register mccsr : ccsr
register sccsr : ccsr
register uccsr : ccsr

/* access to CCSRs */

// for now, use a single privilege-independent legalizer
function legalize_ccsr(c : ccsr, v : xlenbits) -> ccsr = {
  // write only the defined bits, leaving the other bits untouched
  // Technically, WPRI does not need a legalizer, since software is
  // assumed to legalize; so we could remove this function.
  let v = Mk_ccsr(v);
  let c = update_cap_idx(c, v.cap_idx());
  let c = update_cause(c, v.cause());
  /* For now these bits are not really supported so hardwired to true */
  let c = update_d(c, 0b1);
  let c = update_e(c, 0b1);
  c
}

// XXX these are currently disabled due to sail bug when compiling C
//mapping clause csr_name_map = 0x8c0 <-> "uccsr"
//mapping clause csr_name_map = 0x9c0 <-> "sccsr"
//mapping clause csr_name_map = 0xBc0 <-> "mccsr"

function clause ext_read_CSR (0x8C0) = Some(uccsr.bits())
function clause ext_read_CSR (0x9C0) = Some(sccsr.bits())
function clause ext_read_CSR (0xBC0) = Some(mccsr.bits())

function clause ext_write_CSR (0x8C0, value) = { uccsr = legalize_ccsr(uccsr, value); Some(uccsr.bits()) }
function clause ext_write_CSR (0x9C0, value) = { sccsr = legalize_ccsr(sccsr, value); Some(sccsr.bits()) }
function clause ext_write_CSR (0xBC0, value) = { mccsr = legalize_ccsr(mccsr, value); Some(mccsr.bits()) }

function clause ext_is_CSR_defined (0x8C0, p) = haveUsrMode()  // uccsr
function clause ext_is_CSR_defined (0x9C0, p) = haveSupMode() & (p == Machine | p == Supervisor) // sccsr
function clause ext_is_CSR_defined (0xBC0, p) = p == Machine | p == Supervisor // mccsr

/*
 * Bits of CHERI that get rolled out across implementations slowly.
 *
 * Implementations may pick which subset of flavors they choose; this may be a
 * singleton, in which case all WARL fields are basically RO.
 */
bitfield scisa : xlenbits = {
  /*
   * SV{39,48,56} PTE Store-Cap control bits (SC, SC_Mod) are tag-bit
   * dependent.  WARL
   *
   * If 0, any capability-store-capable instruction will trap or write-back to
   * the PTE, as if the instruction were storing an asserted tag, if the PTE
   * SC/SC_Mod bits indicate to do so.
   *
   * If 1, capability-store-capable instructions communicate the tag they are
   * storing to the PTW, so only stores of asserted tags will trigger
   * SC/SC_mod-mediated traps or writeback
   */
  pte_cap_sc_datadep : 2,

  /*
   * SV{39,48,56} PTE Load-Cap control bits (LC, LC_Mod, LC_Gen) are tag-bit
   * dependent.  WARL
   *
   * If 0, any capability-load-capable instruction will trap, as if the loaded
   * data contained an asserted tag, if the PTE LC/LC_Mod/LC_Gen/gclg[us] bits
   * indicate to do so.
   *
   * If 1, capability-load-capable instructions will receive "caveated" successful
   * translations from the PTW and will inspect the loaded tag and caveat and
   * raise traps as merited.
   */
  pte_cap_lc_datadep : 1,

  /*
   * SV{39,48,56} PTEs are extended with Cap load/store modify flags.  WARL.
   *
   * If 0, only SC and LC bits will be used and any set SC_Mod, LC_Mod, or
   * LC_Gen bit will result in a PTW_Invalid_PTE trap.  gclgu and gclgs
   * are ignored.
   *
   * If 1, SC_Mod, LC_Mod, and LC_Gen bits are understood and will be used
   * by the PTW.  gclgu and gclgs are used as defined.
   */
  pte_cap_lsmod : 0
}

register scisa : scisa

function legalize_scisa(c : scisa, v : xlenbits) -> scisa = {
  let v = Mk_scisa(v);

  /*
   * This implementation understands all flavors of PTE LC/SC control in cisa.
   *
   * Setting lsmod to 0 means that the datadep bits are meaningless, so force
   * them to 0, too.
   */
  let c = update_pte_cap_lsmod(c, v.pte_cap_lsmod());
  let c = if c.pte_cap_lsmod() == 0b1 then {
            let c = update_pte_cap_lc_datadep(c, v.pte_cap_lc_datadep());
            update_pte_cap_sc_datadep(c, v.pte_cap_sc_datadep());
          } else {
            let c = update_pte_cap_lc_datadep(c, 0b0);
            update_pte_cap_sc_datadep(c, 0b0);
          };

  c
}

function clause ext_read_CSR (0x9C1) = Some(scisa.bits())

function clause ext_write_CSR (0x9C1, value) = { scisa = legalize_scisa(scisa, value); Some(scisa.bits()) }

function clause ext_is_CSR_defined (0x9C1, p) = haveSupMode() & (p == Machine | p == Supervisor)

/* Other architectural registers */

register PCC       : Capability
register nextPCC   : Capability
register DDC       : Capability

register UTCC      : Capability
register UTDC      : Capability
register UScratchC : Capability
register UEPCC     : Capability
register STCC      : Capability
register STDC      : Capability
register SScratchC : Capability
register SEPCC     : Capability
register MTCC      : Capability
register MTDC      : Capability
register MScratchC : Capability
register MEPCC     : Capability

/* Cheri PCC helpers */

function min_instruction_bytes () -> CapAddrInt = {
  if   (~ (sys_enable_writable_misa ())) & (~ (sys_enable_rvc ()))
  then 4  /* RVC is hardwired to be disabled */
  else 2  /* RVC is active or it could become active */
}

/* Checking whether the Xcheri extension is enabled */

function haveXcheri () -> bool =
  /* This is a necessary but not sufficient condition, but should do for now. */
  misa.X() == 0b1


function legalize_tcc(o : Capability, v : Capability) -> Capability = {
  new_base = getCapBaseBits(v);
  /* Ignore writes that attempt to set unaligned TCC base */
  if new_base[0] != bitzero | new_base[1] != bitzero then
    o /* keep original TCC value */
  else {
    /* legalize new TCC offset (RISC-V tvec) */
    new_tvec = v.address - new_base;
    legalized_tvec = legalize_tvec(Mk_Mtvec(getCapOffsetBits(o)), new_tvec);
    setCapOffsetOrNull(v, legalized_tvec.bits())
  }
}

/*
 * Used during readout (but not assignment!) of ?EPCC registers (CSpecialRW,
 * handle_trap_extension) and not during control transfer
 * (prepare_xret_target).
 *
 * The result is that it is only possible to faithfully read out ?EPCC if
 * either
 *  - misa.C is enabled or
 *  - misa.C is disabled and the EPCC offset is sufficiently aligned
 *
 * If misa.C is held constant, as it almost always will be, between fault and
 * readback, ?EPCC will be faithfully read back, because the alignment will
 * adhere to the requirements of the architecture, which is what legalization
 * is intending to enforce.
 *
 * If neither of those conditions hold, the resulting readout will be a lie; if
 * ?EPCC has additionally been set to be a sentry, then the result will be an
 * untagged lie.
 */
function legalize_epcc (v : Capability) -> Capability = {
  let voffset = getCapOffsetBits(v);
  let legalized = legalize_xepc(voffset);

  if   legalized == voffset
  then v /* avoid possibly attempting to set the offset of a sentry */
  else setCapOffsetOrNull(v, legalized)
}
