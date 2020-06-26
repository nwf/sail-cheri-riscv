// Specialize the accesstype for memory

enum ext_access_type = {
  Data,
  Cap
}

let default_write_acc : ext_access_type = Data

val accessType_to_str : AccessType(ext_access_type) -> string
function accessType_to_str (a) =
  match (a) {
    Read(Data)           => "R",
    Write(Data)          => "W",
    ReadWrite(Data,Data) => "RW",
    Read(Cap)            => "L",
    Write(Cap)           => "S",
    ReadWrite(Cap,Cap)   => "LS",
    ReadWrite(Data,Cap)  => "RS",
    ReadWrite(Cap,Data)  => "LW",
    Execute()            => "X"
  }

overload to_str = {accessType_to_str}
