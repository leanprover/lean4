/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

module

prelude
public import Init.Data.ToString.Basic

public section

/--
Exceptions that may be thrown in the `IO` monad.

Many of the constructors of `IO.Error` correspond to POSIX error numbers. In these cases, the
documentation string lists POSIX standard error macros that correspond to the error. This list is
not necessarily exhaustive, and these constructor includes a field for the underlying error number.
-/
-- Imitates the structure of IOErrorType in Haskell:
-- https://hackage.haskell.org/package/base-4.12.0.0/docs/System-IO-Error.html#t:IOErrorType
inductive IO.Error where
  /--
  The operation failed because a file already exists.

  This corresponds to POSIX errors `EEXIST`, `EINPROGRESS`, and `EISCONN`.
  -/
  | alreadyExists (filename : Option String) (osCode : UInt32) (details : String)
  /--
  Some error not covered by the other constructors of `IO.Error` occurred.

  This also includes POSIX error `EFAULT`.
  -/
  | otherError (osCode : UInt32) (details : String)
  /--
  A necessary resource was busy.

  This corresponds to POSIX errors `EADDRINUSE`, `EBUSY`, `EDEADLK`, and `ETXTBSY`.
  -/
  | resourceBusy (osCode : UInt32) (details : String)
  /--
  A necessary resource is no longer available.

  This corresponds to POSIX errors `ECONNRESET`, `EIDRM`, `ENETDOWN`, `ENETRESET`, `ENOLINK`, and
  `EPIPE`.
  -/
  | resourceVanished (osCode : UInt32) (details : String)
  /--
  An operation was not supported.

  This corresponds to POSIX errors `EADDRNOTAVAIL`, `EAFNOSUPPORT`, `ENODEV`, `ENOPROTOOPT`
  `ENOSYS`, `EOPNOTSUPP`, `ERANGE`, `ESPIPE`, and `EXDEV`.
  -/
  | unsupportedOperation (osCode : UInt32) (details : String)
  /--
  The operation failed due to a hardware problem, such as an I/O error.

  This corresponds to the POSIX error `EIO`.
  -/
  | hardwareFault (osCode : UInt32) (details : String)
  /--
  A constraint required by an operation was not satisfied (e.g. a directory was not empty).

  This corresponds to the POSIX error `ENOTEMPTY`.
  -/
  | unsatisfiedConstraints (osCode : UInt32) (details : String)
  /--
  An inappropriate I/O control operation was attempted.

  This corresponds to the POSIX error `ENOTTY`.
  -/
  | illegalOperation (osCode : UInt32) (details : String)
  /--
  A protocol error occurred.

  This corresponds to the POSIX errors `EPROTO`, `EPROTONOSUPPORT`, and `EPROTOTYPE`.
  -/
  | protocolError (osCode : UInt32) (details : String)
  /--
  An operation timed out.

  This corresponds to the POSIX errors `ETIME`, and `ETIMEDOUT`.
  -/
  | timeExpired (osCode : UInt32) (details : String)
  /--
  The operation was interrupted.

  This corresponds to the POSIX error `EINTR`.
  -/
  | interrupted (filename : String) (osCode : UInt32) (details : String)
  /--
  No such file or directory.

  This corresponds to the POSIX error `ENOENT`.
  -/
  | noFileOrDirectory (filename : String) (osCode : UInt32) (details : String)
  /--
  An argument to an I/O operation was invalid.

  This corresponds to the POSIX errors `ELOOP`, `ENAMETOOLONG`, `EDESTADDRREQ`, `EILSEQ`, `EINVAL`, `EDOM`, `EBADF`
  `ENOEXEC`, `ENOSTR`, `ENOTCONN`, and `ENOTSOCK`.
  -/
  | invalidArgument (filename : Option String) (osCode : UInt32) (details : String)

  /--
  An operation failed due to insufficient permissions.

  This corresponds to the POSIX errors `EACCES`, `EROFS`, `ECONNABORTED`, `EFBIG`, and `EPERM`.
  -/
  | permissionDenied (filename : Option String) (osCode : UInt32) (details : String)

  /--
  A resource was exhausted.

  This corresponds to the POSIX errors  `EMFILE`, `ENFILE`, `ENOSPC`, `E2BIG`, `EAGAIN`, `EMLINK`,
  `EMSGSIZE`, `ENOBUFS`, `ENOLCK`, `ENOMEM`, and `ENOSR`.
  -/
  | resourceExhausted (filename : Option String) (osCode : UInt32) (details : String)

  /--
  An argument was the wrong type (e.g. a directory when a file was required).

  This corresponds to the POSIX errors `EISDIR`, `EBADMSG`, and `ENOTDIR`.
  -/
  | inappropriateType (filename : Option String) (osCode : UInt32) (details : String)

  /--
  A required resource does not exist.

  This corresponds to the POSIX errors `ENXIO`, `EHOSTUNREACH`, `ENETUNREACH`, `ECHILD`,
  `ECONNREFUSED`, `ENODATA`, `ENOMSG`, and `ESRCH`.
  -/
  | noSuchThing (filename : Option String) (osCode : UInt32) (details : String)

  /-- An unexpected end-of-file marker was encountered. -/
  | unexpectedEof
  /-- Some other error occurred. -/
  | userError (msg : String)

instance : Inhabited IO.Error where
  default := .userError "(`Inhabited.default` for `IO.Error`)"

/--
Constructs an `IO.Error` from a string.

`IO.Error` is the type of exceptions thrown by the `IO` monad.
-/
@[export lean_mk_io_user_error]
def IO.userError (s : String) : IO.Error :=
  IO.Error.userError s

instance : Coe String IO.Error := ⟨IO.userError⟩

namespace IO.Error

@[export lean_mk_io_error_already_exists_file]
def mkAlreadyExistsFile : String → UInt32 → String → IO.Error :=
  alreadyExists ∘ some

@[export lean_mk_io_error_eof]
def mkEofError : Unit → IO.Error := fun _ =>
  unexpectedEof

@[export lean_mk_io_error_inappropriate_type_file]
def mkInappropriateTypeFile : String → UInt32 → String → IO.Error :=
  inappropriateType ∘ some

@[export lean_mk_io_error_interrupted]
def mkInterrupted : String → UInt32 → String → IO.Error :=
  interrupted

@[export lean_mk_io_error_invalid_argument_file]
def mkInvalidArgumentFile : String → UInt32 → String → IO.Error :=
  invalidArgument ∘ some

@[export lean_mk_io_error_no_file_or_directory]
def mkNoFileOrDirectory : String → UInt32 → String → IO.Error :=
  noFileOrDirectory

@[export lean_mk_io_error_no_such_thing_file]
def mkNoSuchThingFile : String → UInt32 → String → IO.Error :=
  noSuchThing ∘ some

@[export lean_mk_io_error_permission_denied_file]
def mkPermissionDeniedFile : String → UInt32 → String → IO.Error :=
  permissionDenied ∘ some

@[export lean_mk_io_error_resource_exhausted_file]
def mkResourceExhaustedFile : String → UInt32 → String → IO.Error :=
  resourceExhausted ∘ some

@[export lean_mk_io_error_unsupported_operation]
def mkUnsupportedOperation : UInt32 → String → IO.Error :=
  unsupportedOperation

@[export lean_mk_io_error_resource_exhausted]
def mkResourceExhausted : UInt32 → String → IO.Error :=
  resourceExhausted none

@[export lean_mk_io_error_already_exists]
def mkAlreadyExists : UInt32 → String → IO.Error :=
  alreadyExists none

@[export lean_mk_io_error_inappropriate_type]
def mkInappropriateType : UInt32 → String → IO.Error :=
  inappropriateType none

@[export lean_mk_io_error_no_such_thing]
def mkNoSuchThing : UInt32 → String → IO.Error :=
  noSuchThing none

@[export lean_mk_io_error_resource_vanished]
def mkResourceVanished : UInt32 → String → IO.Error :=
  resourceVanished

@[export lean_mk_io_error_resource_busy]
def mkResourceBusy : UInt32 → String → IO.Error :=
  resourceBusy

@[export lean_mk_io_error_invalid_argument]
def mkInvalidArgument : UInt32 → String → IO.Error :=
  invalidArgument none

@[export lean_mk_io_error_other_error]
def mkOtherError : UInt32 → String → IO.Error :=
  otherError

@[export lean_mk_io_error_permission_denied]
def mkPermissionDenied : UInt32 → String → IO.Error :=
  permissionDenied none

@[export lean_mk_io_error_hardware_fault]
def mkHardwareFault : UInt32 → String → IO.Error :=
  hardwareFault

@[export lean_mk_io_error_unsatisfied_constraints]
def mkUnsatisfiedConstraints : UInt32 → String → IO.Error :=
  unsatisfiedConstraints

@[export lean_mk_io_error_illegal_operation]
def mkIllegalOperation : UInt32 → String → IO.Error :=
  illegalOperation

@[export lean_mk_io_error_protocol_error]
def mkProtocolError : UInt32 → String → IO.Error :=
  protocolError

@[export lean_mk_io_error_time_expired]
def mkTimeExpired : UInt32 → String → IO.Error :=
  timeExpired

private def downCaseFirst (s : String) : String := s.modify 0 Char.toLower

def fopenErrorToString (gist fn : String) (code : UInt32) : Option String → String
  | some details => downCaseFirst gist ++ " (error code: " ++ toString code ++ ", " ++ downCaseFirst details ++ ")\n  file: " ++ fn
  | none => downCaseFirst gist ++ " (error code: " ++ toString code ++ ")\n  file: " ++ fn

def otherErrorToString (gist : String) (code : UInt32) : Option String → String
  | some details => downCaseFirst gist ++ " (error code: " ++ toString code ++ ", " ++ downCaseFirst details ++ ")"
  | none => downCaseFirst gist ++ " (error code: " ++ toString code ++ ")"

/--
Converts an `IO.Error` to a descriptive string.

`IO.Error.userError` is converted to its embedded message. The other constructors are converted in a
way that preserves structured information, such as error codes and filenames, that can help
diagnose the issue.
-/
@[export lean_io_error_to_string]
def toString : IO.Error → String
  | unexpectedEof                            => "end of file"
  | inappropriateType (some fn) code details => fopenErrorToString "inappropriate type" fn code (some details)
  | inappropriateType none code details      => otherErrorToString "inappropriate type" code (some details)
  | interrupted fn code details              => fopenErrorToString "interrupted system call" fn code (some details)
  | invalidArgument (some fn) code details   => fopenErrorToString "invalid argument" fn code (some details)
  | invalidArgument none code details        => otherErrorToString "invalid argument" code (some details)
  | noFileOrDirectory fn code _              => fopenErrorToString "no such file or directory" fn code none
  | noSuchThing (some fn) code details       => fopenErrorToString "no such thing" fn code (some details)
  | noSuchThing none code details            => otherErrorToString "no such thing" code (some details)
  | permissionDenied (some fn) code details  => fopenErrorToString details fn code none
  | permissionDenied none code details       => otherErrorToString details code none
  | resourceExhausted (some fn) code details => fopenErrorToString "resource exhausted" fn code (some details)
  | resourceExhausted none code details      => otherErrorToString "resource exhausted" code (some details)
  | alreadyExists none code details          => otherErrorToString "already exists" code (some details)
  | alreadyExists (some fn) code details     => fopenErrorToString "already exists" fn code (some details)
  | otherError code details                  => otherErrorToString details code none
  | resourceBusy code details                => otherErrorToString "resource busy" code (some details)
  | resourceVanished code details            => otherErrorToString "resource vanished" code (some details)
  | hardwareFault code _                     => otherErrorToString "hardware fault" code none
  | illegalOperation code details            => otherErrorToString "illegal operation" code (some details)
  | protocolError code details               => otherErrorToString "protocol error" code (some details)
  | timeExpired code details                 => otherErrorToString "time expired" code (some details)
  | unsatisfiedConstraints code _            => otherErrorToString "directory not empty" code none
  | unsupportedOperation code details        => otherErrorToString "unsupported operation" code (some details)
  | userError msg                            => msg

instance : ToString IO.Error := ⟨ IO.Error.toString ⟩

end IO.Error
