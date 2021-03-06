/*
 * Extension for CHERI page table walker
 *
 * We are going to carry around a summary of the PTW walk for data-dependent
 * (well, tag-dependent) behaviors by the instructions.
 *
 */

enum ext_ptw_lcm = {
  /* Tags flow as might be expected */
  PTW_LCM_OK,

  /* PTE settings require clearing tags */
  PTW_LCM_CLR,

  /* PTE settings require us to trap */
  PTW_LCM_TRAP
}

enum ext_ptw_scm = {
  /* Tag stores are permitted */
  PTW_SCM_OK,

  /*
   * PTW_SCM_TRAP is only raised in Write(Cap) or ReadWrite(Cap) accesses.
   * The instruction layer can choose whether storing a clear tag gets
   * issued as a Write(Cap) or Write(Data) request.
   */
  PTW_SCM_TRAP
}

struct ext_ptw = {
  ptw_lc_mod : ext_ptw_lcm,
  ptw_sc_mod : ext_ptw_scm
}

function ext_ptw_join_lcm(e : ext_ptw, l : ext_ptw_lcm) -> ext_ptw =
  { e with ptw_lc_mod =
      match l {
        PTW_LCM_OK => e.ptw_lc_mod,
        PTW_LCM_CLR => match e.ptw_lc_mod {
                         PTW_LCM_OK => PTW_LCM_CLR,
                         PTW_LCM_CLR => PTW_LCM_CLR,
                         PTW_LCM_TRAP => PTW_LCM_TRAP
                       },
        PTW_LCM_TRAP => PTW_LCM_TRAP
      }
  }

function ext_ptw_join_scm(e : ext_ptw, s : ext_ptw_scm) -> ext_ptw =
  { e with ptw_sc_mod =
      match s {
        PTW_SCM_OK => e.ptw_sc_mod,
        PTW_SCM_TRAP => s
      }
  }

/* initial value of the PTW accumulator */
let init_ext_ptw : ext_ptw = struct {
  ptw_lc_mod = PTW_LCM_OK,
  ptw_sc_mod = PTW_SCM_OK
}

/* Address translation failures */
enum ext_ptw_fail = {
  EPTWF_NO_PERM,
  EPTWF_INVALID,
  EPTWF_CAP_ERR
}

/* Address translation errors */
enum ext_ptw_error = {AT_CAP_ERR}

/* CHERI exception extensions */

enum ext_exc_type = {
  EXC_LOAD_CAP_PAGE_FAULT,
  EXC_SAMO_CAP_PAGE_FAULT,
  EXC_CHERI
}

/* CHERI conversion of extension exceptions to bits */
val ext_exc_type_to_bits : ext_exc_type -> exc_code
function ext_exc_type_to_bits(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => 0x1a,
    EXC_SAMO_CAP_PAGE_FAULT => 0x1b,
    EXC_CHERI               => 0x1c
  }

/* CHERI conversion of extension exceptions to integers */
val num_of_ext_exc_type : ext_exc_type -> {'n, (0 <= 'n < xlen). int('n)}
function num_of_ext_exc_type(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => 26,
    EXC_SAMO_CAP_PAGE_FAULT => 27,
    EXC_CHERI               => 28
  }

/* CHERI conversion of extension exceptions to strings */
val ext_exc_type_to_str : ext_exc_type -> string
function ext_exc_type_to_str(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => "load-cap-page-fault",
    EXC_SAMO_CAP_PAGE_FAULT => "store/amo-cap-page-fault",
    EXC_CHERI               => "cheri"
  }
