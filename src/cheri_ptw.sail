/* failure modes for address-translation/page-table-walks */

union PTW_Error = {
  PTW_Invalid_Addr  : unit,          /* invalid source address */
  PTW_Access        : unit,          /* physical memory access error for a PTE */
  PTW_Invalid_PTE   : unit,
  PTW_No_Permission : unit,
  PTW_Misaligned    : unit,          /* misaligned superpage */
  PTW_PTE_Update    : unit,          /* PTE update needed but not enabled */
  PTW_Ext_Error     : ext_ptw_error  /* parameterized for errors from extensions */
}

val ptw_error_to_str : PTW_Error -> string
function ptw_error_to_str(e) =
  match (e) {
    PTW_Invalid_Addr()   => "invalid-source-addr",
    PTW_Access()         => "mem-access-error",
    PTW_Invalid_PTE()    => "invalid-pte",
    PTW_No_Permission()  => "no-permission",
    PTW_Misaligned()     => "misaligned-superpage",
    PTW_PTE_Update()     => "pte-update-needed",
    PTW_Ext_Error(e)     => "extension-error"
  }

overload to_str = {ptw_error_to_str}

/*
 * checkPTEPermission has returned a failure; here, ext_ptw is no longer
 * caveats for data dependence, but rather certainly identifies the cause of a
 * trap.
 */
function ext_get_ptw_error(eptwf : ext_ptw_fail) -> PTW_Error =
  match (eptwf) {
    EPTWF_NO_PERM  => PTW_No_Permission(),
    EPTWF_INVALID  => PTW_Invalid_PTE(),
    EPTWF_CAP_ERR  => PTW_Ext_Error(AT_CAP_ERR)
  }

/* conversion of these translation/PTW failures into architectural exceptions */
function translationException(a : AccessType(ext_access_type), f : PTW_Error) -> ExceptionType = {
  let e : ExceptionType =
  match (a, f) {
    /* First handle the vmem extension errors */
    (Read(Cap), PTW_Ext_Error(AT_CAP_ERR))        => E_Extension(EXC_LOAD_CAP_PAGE_FAULT),
    (Write(Cap), PTW_Ext_Error(AT_CAP_ERR))       => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),
    (ReadWrite(Cap,_), PTW_Ext_Error(AT_CAP_ERR)) => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),
    (ReadWrite(_,Cap), PTW_Ext_Error(AT_CAP_ERR)) => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),

    /* For other exceptions, Cap accesses fault similar to Data accesses below. */
    (ReadWrite(Cap,_), PTW_Access())  => E_SAMO_Access_Fault(),
    (ReadWrite(_,Cap), PTW_Access())  => E_SAMO_Access_Fault(),
    (ReadWrite(Cap,_), _)             => E_SAMO_Page_Fault(),
    (ReadWrite(_,Cap), _)             => E_SAMO_Page_Fault(),
    (Read(Cap), PTW_Access())       => E_Load_Access_Fault(),
    (Read(Cap), _)                  => E_Load_Page_Fault(),
    (Write(Cap), PTW_Access())      => E_SAMO_Access_Fault(),
    (Write(Cap), _)                 => E_SAMO_Page_Fault(),

    (ReadWrite(Data,Data), PTW_Access()) => E_SAMO_Access_Fault(),
    (ReadWrite(Data,Data), _)            => E_SAMO_Page_Fault(),
    (Read(Data), PTW_Access())      => E_Load_Access_Fault(),
    (Read(Data), _)                 => E_Load_Page_Fault(),
    (Write(Data), PTW_Access())     => E_SAMO_Access_Fault(),
    (Write(Data), _)                => E_SAMO_Page_Fault(),

    (Execute(), PTW_Access())       => E_Fetch_Access_Fault(),
    (Execute(), _)                  => E_Fetch_Page_Fault()
  } in {
/*  print_mem("translationException(" ^ a ^ ", " ^ f ^ ") -> " ^ e); */
    e
  }
}
