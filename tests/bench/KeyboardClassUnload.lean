open Lean Std

namespace KeyboardClassUnload

set_option maxRecDepth 10000
set_option linter.unusedVariables false

@[simp] def assert (ψ β: Prop): Prop := ψ ∧ β
@[simp] def assume (ψ β: Prop): Prop := ψ → β
@[simp] def skip (β: Prop): Prop := β
@[simp] def ret: Prop := true
@[simp] def goto: Prop → Prop := id

-- SMT Array definition
def SMTArray1 (s1 s2: Type) := s1 → s2

def SMTArray2 (s1 s2 s3 : Type) := s1 → s2 → s3

def store1
  [BEq s1]
  (m: SMTArray1 s1 s2) (i: s1) (v: s2): SMTArray1 s1 s2 :=
    fun i' => if i' == i then v else m i'

def select1 (m: SMTArray1 s1 s2) (i: s1): s2 := m i

def store2
  [BEq s1] [BEq s2]
  (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (v: s3): SMTArray2 s1 s2 s3 :=
    fun i' j' => if i' == i && j' == j then v else m i' j'

def select2 (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2): s3 := m i j

theorem SelectStoreSame1
  (s1 s2: Type)
  [BEq s1] [LawfulBEq s1]
  (a: SMTArray1 s1 s2) (i: s1) (e: s2):
  select1 (store1 a i e) i = e :=
    by simp [select1, store1]

theorem SelectStoreDistinct1
  (s1 s2: Type)
  [BEq s1] [LawfulBEq s1]
  (a: SMTArray1 s1 s2) (i: s1) (j: s1) (e: s2):
  i ≠ j → select1 (store1 a i e) j = select1 a j :=
    by simp [select1, store1]
       intro neq eq1
       have eq2: i = j := Eq.symm eq1
       contradiction

theorem SelectStoreSame2
  (s1 s2 s3: Type)
  [BEq s1] [BEq s2]
  [LawfulBEq s1] [LawfulBEq s2]
  (a: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (e: s3):
  select2 (store2 a i j e) i j = e :=
    by simp [select2, store2]

theorem SelectStoreDistinct2
  (s1 s2 s3: Type)
  [BEq s1] [BEq s2]
  [LawfulBEq s1] [LawfulBEq s2]
  (a: SMTArray2 s1 s2 s3) (i: s1) (i': s1) (j: s2) (j' : s2) (e: s3):
  i ≠ i' \/ j ≠ j' → select2 (store2 a i j e) i' j' = select2 a i' j' :=
    by simp [select2, store2]
       intro either eq1 eq2
       cases either
       have eq3: i = i' := Eq.symm eq1
       contradiction
       have eq4: j = j' := Eq.symm eq2
       contradiction

-- TODO: make this translate to the appropriate thing in SMT or prove some
-- theorems and include them as SMT axioms.
def distinct {a : Type} [BEq a] (xs: List a) : Prop :=
  match xs with
  | [] => true
  | x :: rest => x ∉ rest ∧ distinct rest

-- Type constructors
axiom _boogie_byte : Type
instance _boogie_byteBEq : BEq _boogie_byte := by sorry
axiom _boogie_name : Type
instance _boogie_nameBEq : BEq _boogie_name := by sorry

-- Type synonyms

-- Constants
variable (_boogie_UNALLOCATED : _boogie_name)
variable (_boogie_ALLOCATED : _boogie_name)
variable (_boogie_FREED : _boogie_name)
variable (_boogie_BYTE : _boogie_name)
variable (_boogie_T_Guid_WMIGUIDREGINFO : _boogie_name)
variable (_boogie_T_InstanceCount_WMIGUIDREGINFO : _boogie_name)
variable (_boogie_T_Flags_WMIGUIDREGINFO : _boogie_name)
variable (_boogie_T_OperationID__ACCESS_STATE : _boogie_name)
variable (_boogie_T_SecurityEvaluated__ACCESS_STATE : _boogie_name)
variable (_boogie_T_GenerateAudit__ACCESS_STATE : _boogie_name)
variable (_boogie_T_GenerateOnClose__ACCESS_STATE : _boogie_name)
variable (_boogie_T_PrivilegesAllocated__ACCESS_STATE : _boogie_name)
variable (_boogie_T_Flags__ACCESS_STATE : _boogie_name)
variable (_boogie_T_RemainingDesiredAccess__ACCESS_STATE : _boogie_name)
variable (_boogie_T_PreviouslyGrantedAccess__ACCESS_STATE : _boogie_name)
variable (_boogie_T_OriginalDesiredAccess__ACCESS_STATE : _boogie_name)
variable (_boogie_T_SubjectSecurityContext__ACCESS_STATE : _boogie_name)
variable (_boogie_T_SecurityDescriptor__ACCESS_STATE : _boogie_name)
variable (_boogie_T_AuxData__ACCESS_STATE : _boogie_name)
variable (_boogie_T_Privileges__ACCESS_STATE : _boogie_name)
variable (_boogie_T_AuditPrivileges__ACCESS_STATE : _boogie_name)
variable (_boogie_T_ObjectName__ACCESS_STATE : _boogie_name)
variable (_boogie_T_ObjectTypeName__ACCESS_STATE : _boogie_name)
variable (_boogie_T_InterfaceType__CM_FULL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_BusNumber__CM_FULL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_PartialResourceList__CM_FULL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Type__CM_PARTIAL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_ShareDisposition__CM_PARTIAL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_u__CM_PARTIAL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Version__CM_PARTIAL_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_Revision__CM_PARTIAL_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_Count__CM_PARTIAL_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_PartialDescriptors__CM_PARTIAL_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_Count__CM_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_List__CM_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_Size__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_Version__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_DeviceD1__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_DeviceD2__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_LockSupported__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_EjectSupported__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_Removable__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_DockDevice__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_UniqueID__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_SilentInstall__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_RawDeviceOK__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_SurpriseRemovalOK__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_WakeFromD0__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_WakeFromD1__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_WakeFromD2__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_WakeFromD3__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_HardwareDisabled__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_NonDynamic__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_WarmEjectSupported__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_NoDisplayInUI__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_Reserved__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_Address__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_UINumber__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_DeviceState__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_SystemWake__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_DeviceWake__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_D1Latency__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_D2Latency__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_D3Latency__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_Self__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_TrueClassDevice__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_TopPort__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_PDO__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_RemoveLock__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_PnP__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_Started__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_AllowDisable__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_WaitWakeSpinLock__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_TrustedSubsystemCount__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_InputCount__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_SymbolicLinkName__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_InputData__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_DataIn__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_DataOut__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_KeyboardAttributes__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_IndicatorParameters__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_SpinLock__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_ReadQueue__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_SequenceNumber__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_DeviceState__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_SystemState__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_UnitId__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_WmiLibInfo__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_SystemToDeviceState__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_MinDeviceWakeState__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_MinSystemWakeState__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_WaitWakeIrp__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_ExtraWaitWakeIrp__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_TargetNotifyHandle__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_Link__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_File__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_Enabled__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_OkayToLogOverflow__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_WaitWakeEnabled__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_SurpriseRemoved__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_Type__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Size__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_ReferenceCount__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_DriverObject__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_NextDevice__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_AttachedDevice__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_CurrentIrp__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Timer__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Flags__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Characteristics__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Vpb__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_DeviceExtension__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_DeviceType__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_StackSize__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Queue__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_AlignmentRequirement__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_DeviceQueue__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Dpc__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_ActiveThreadCount__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_SecurityDescriptor__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_DeviceLock__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_SectorSize__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Spare1__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_DeviceObjectExtension__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Reserved__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_Type__DEVOBJ_EXTENSION : _boogie_name)
variable (_boogie_T_Size__DEVOBJ_EXTENSION : _boogie_name)
variable (_boogie_T_DeviceObject__DEVOBJ_EXTENSION : _boogie_name)
variable (_boogie_T___unnamed_4_a97c65a1__DISPATCHER_HEADER : _boogie_name)
variable (_boogie_T_SignalState__DISPATCHER_HEADER : _boogie_name)
variable (_boogie_T_WaitListHead__DISPATCHER_HEADER : _boogie_name)
variable (_boogie_T_DriverObject__DRIVER_EXTENSION : _boogie_name)
variable (_boogie_T_AddDevice__DRIVER_EXTENSION : _boogie_name)
variable (_boogie_T_Count__DRIVER_EXTENSION : _boogie_name)
variable (_boogie_T_ServiceKeyName__DRIVER_EXTENSION : _boogie_name)
variable (_boogie_T_Type__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_Size__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DeviceObject__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_Flags__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverStart__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverSize__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverSection__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverExtension__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverName__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_HardwareDatabase__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_FastIoDispatch__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverInit__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverStartIo__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_DriverUnload__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_MajorFunction__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_SystemResourcesList__ERESOURCE : _boogie_name)
variable (_boogie_T_OwnerTable__ERESOURCE : _boogie_name)
variable (_boogie_T_ActiveCount__ERESOURCE : _boogie_name)
variable (_boogie_T_Flag__ERESOURCE : _boogie_name)
variable (_boogie_T_SharedWaiters__ERESOURCE : _boogie_name)
variable (_boogie_T_ExclusiveWaiters__ERESOURCE : _boogie_name)
variable (_boogie_T_OwnerEntry__ERESOURCE : _boogie_name)
variable (_boogie_T_ActiveEntries__ERESOURCE : _boogie_name)
variable (_boogie_T_ContentionCount__ERESOURCE : _boogie_name)
variable (_boogie_T_NumberOfSharedWaiters__ERESOURCE : _boogie_name)
variable (_boogie_T_NumberOfExclusiveWaiters__ERESOURCE : _boogie_name)
variable (_boogie_T___unnamed_4_52c594f7__ERESOURCE : _boogie_name)
variable (_boogie_T_SpinLock__ERESOURCE : _boogie_name)
variable (_boogie_T_SizeOfFastIoDispatch__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoCheckIfPossible__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoRead__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoWrite__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoQueryBasicInfo__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoQueryStandardInfo__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoLock__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoUnlockSingle__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoUnlockAll__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoUnlockAllByKey__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoDeviceControl__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_AcquireFileForNtCreateSection__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_ReleaseFileForNtCreateSection__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoDetachDevice__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoQueryNetworkOpenInfo__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_AcquireForModWrite__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_MdlRead__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_MdlReadComplete__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_PrepareMdlWrite__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_MdlWriteComplete__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoReadCompressed__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoWriteCompressed__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_MdlReadCompleteCompressed__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_MdlWriteCompleteCompressed__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_FastIoQueryOpen__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_ReleaseForModWrite__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_AcquireForCcFlush__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_ReleaseForCcFlush__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_Count__FAST_MUTEX : _boogie_name)
variable (_boogie_T_Owner__FAST_MUTEX : _boogie_name)
variable (_boogie_T_Contention__FAST_MUTEX : _boogie_name)
variable (_boogie_T_Gate__FAST_MUTEX : _boogie_name)
variable (_boogie_T_OldIrql__FAST_MUTEX : _boogie_name)
variable (_boogie_T_CreationTime__FILE_BASIC_INFORMATION : _boogie_name)
variable (_boogie_T_LastAccessTime__FILE_BASIC_INFORMATION : _boogie_name)
variable (_boogie_T_LastWriteTime__FILE_BASIC_INFORMATION : _boogie_name)
variable (_boogie_T_ChangeTime__FILE_BASIC_INFORMATION : _boogie_name)
variable (_boogie_T_FileAttributes__FILE_BASIC_INFORMATION : _boogie_name)
variable (_boogie_T_CreationTime__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_LastAccessTime__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_LastWriteTime__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_ChangeTime__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_AllocationSize__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_EndOfFile__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_FileAttributes__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_Type__FILE_OBJECT : _boogie_name)
variable (_boogie_T_Size__FILE_OBJECT : _boogie_name)
variable (_boogie_T_DeviceObject__FILE_OBJECT : _boogie_name)
variable (_boogie_T_Vpb__FILE_OBJECT : _boogie_name)
variable (_boogie_T_FsContext__FILE_OBJECT : _boogie_name)
variable (_boogie_T_FsContext2__FILE_OBJECT : _boogie_name)
variable (_boogie_T_SectionObjectPointer__FILE_OBJECT : _boogie_name)
variable (_boogie_T_PrivateCacheMap__FILE_OBJECT : _boogie_name)
variable (_boogie_T_FinalStatus__FILE_OBJECT : _boogie_name)
variable (_boogie_T_RelatedFileObject__FILE_OBJECT : _boogie_name)
variable (_boogie_T_LockOperation__FILE_OBJECT : _boogie_name)
variable (_boogie_T_DeletePending__FILE_OBJECT : _boogie_name)
variable (_boogie_T_ReadAccess__FILE_OBJECT : _boogie_name)
variable (_boogie_T_WriteAccess__FILE_OBJECT : _boogie_name)
variable (_boogie_T_DeleteAccess__FILE_OBJECT : _boogie_name)
variable (_boogie_T_SharedRead__FILE_OBJECT : _boogie_name)
variable (_boogie_T_SharedWrite__FILE_OBJECT : _boogie_name)
variable (_boogie_T_SharedDelete__FILE_OBJECT : _boogie_name)
variable (_boogie_T_Flags__FILE_OBJECT : _boogie_name)
variable (_boogie_T_FileName__FILE_OBJECT : _boogie_name)
variable (_boogie_T_CurrentByteOffset__FILE_OBJECT : _boogie_name)
variable (_boogie_T_Waiters__FILE_OBJECT : _boogie_name)
variable (_boogie_T_Busy__FILE_OBJECT : _boogie_name)
variable (_boogie_T_LastLock__FILE_OBJECT : _boogie_name)
variable (_boogie_T_Lock__FILE_OBJECT : _boogie_name)
variable (_boogie_T_Event__FILE_OBJECT : _boogie_name)
variable (_boogie_T_CompletionContext__FILE_OBJECT : _boogie_name)
variable (_boogie_T_IrpListLock__FILE_OBJECT : _boogie_name)
variable (_boogie_T_IrpList__FILE_OBJECT : _boogie_name)
variable (_boogie_T_FileObjectExtension__FILE_OBJECT : _boogie_name)
variable (_boogie_T_AllocationSize__FILE_STANDARD_INFORMATION : _boogie_name)
variable (_boogie_T_EndOfFile__FILE_STANDARD_INFORMATION : _boogie_name)
variable (_boogie_T_NumberOfLinks__FILE_STANDARD_INFORMATION : _boogie_name)
variable (_boogie_T_DeletePending__FILE_STANDARD_INFORMATION : _boogie_name)
variable (_boogie_T_Directory__FILE_STANDARD_INFORMATION : _boogie_name)
variable (_boogie_T_Debug__GLOBALS : _boogie_name)
variable (_boogie_T_GrandMaster__GLOBALS : _boogie_name)
variable (_boogie_T_AssocClassList__GLOBALS : _boogie_name)
variable (_boogie_T_NumAssocClass__GLOBALS : _boogie_name)
variable (_boogie_T_Opens__GLOBALS : _boogie_name)
variable (_boogie_T_NumberLegacyPorts__GLOBALS : _boogie_name)
variable (_boogie_T_Mutex__GLOBALS : _boogie_name)
variable (_boogie_T_ConnectOneClassToOnePort__GLOBALS : _boogie_name)
variable (_boogie_T_SendOutputToAllPorts__GLOBALS : _boogie_name)
variable (_boogie_T_PortsServiced__GLOBALS : _boogie_name)
variable (_boogie_T_InitExtension__GLOBALS : _boogie_name)
variable (_boogie_T_RegistryPath__GLOBALS : _boogie_name)
variable (_boogie_T_BaseClassName__GLOBALS : _boogie_name)
variable (_boogie_T_BaseClassBuffer__GLOBALS : _boogie_name)
variable (_boogie_T_LegacyDeviceList__GLOBALS : _boogie_name)
variable (_boogie_T_Data1__GUID : _boogie_name)
variable (_boogie_T_Data2__GUID : _boogie_name)
variable (_boogie_T_Data3__GUID : _boogie_name)
variable (_boogie_T_Data4__GUID : _boogie_name)
variable (_boogie_T_PrivilegeCount__INITIAL_PRIVILEGE_SET : _boogie_name)
variable (_boogie_T_Control__INITIAL_PRIVILEGE_SET : _boogie_name)
variable (_boogie_T_Privilege__INITIAL_PRIVILEGE_SET : _boogie_name)
variable (_boogie_T_Size__INTERFACE : _boogie_name)
variable (_boogie_T_Version__INTERFACE : _boogie_name)
variable (_boogie_T_Context__INTERFACE : _boogie_name)
variable (_boogie_T_InterfaceReference__INTERFACE : _boogie_name)
variable (_boogie_T_InterfaceDereference__INTERFACE : _boogie_name)
variable (_boogie_T_Port__IO_COMPLETION_CONTEXT : _boogie_name)
variable (_boogie_T_Key__IO_COMPLETION_CONTEXT : _boogie_name)
variable (_boogie_T_Common__IO_REMOVE_LOCK : _boogie_name)
variable (_boogie_T_Dbg__IO_REMOVE_LOCK : _boogie_name)
variable (_boogie_T_Removed__IO_REMOVE_LOCK_COMMON_BLOCK : _boogie_name)
variable (_boogie_T_Reserved__IO_REMOVE_LOCK_COMMON_BLOCK : _boogie_name)
variable (_boogie_T_IoCount__IO_REMOVE_LOCK_COMMON_BLOCK : _boogie_name)
variable (_boogie_T_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK : _boogie_name)
variable (_boogie_T_Signature__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_LockList__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_Spin__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_Reserved1__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_Reserved2__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_Blocks__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T_Option__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Type__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_ShareDisposition__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Spare1__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Flags__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Spare2__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_u__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_Version__IO_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_Revision__IO_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_Count__IO_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_Descriptors__IO_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_ListSize__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_InterfaceType__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_BusNumber__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_SlotNumber__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_Reserved__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_AlternativeLists__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_List__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_SecurityQos__IO_SECURITY_CONTEXT : _boogie_name)
variable (_boogie_T_AccessState__IO_SECURITY_CONTEXT : _boogie_name)
variable (_boogie_T_DesiredAccess__IO_SECURITY_CONTEXT : _boogie_name)
variable (_boogie_T_FullCreateOptions__IO_SECURITY_CONTEXT : _boogie_name)
variable (_boogie_T_MajorFunction__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_MinorFunction__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_Flags__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_Control__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_Parameters__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_DeviceObject__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_FileObject__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_CompletionRoutine__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_Context__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T___unnamed_4_d99b6e2b__IO_STATUS_BLOCK : _boogie_name)
variable (_boogie_T_Information__IO_STATUS_BLOCK : _boogie_name)
variable (_boogie_T_Type__IRP : _boogie_name)
variable (_boogie_T_Size__IRP : _boogie_name)
variable (_boogie_T_MdlAddress__IRP : _boogie_name)
variable (_boogie_T_Flags__IRP : _boogie_name)
variable (_boogie_T_AssociatedIrp__IRP : _boogie_name)
variable (_boogie_T_ThreadListEntry__IRP : _boogie_name)
variable (_boogie_T_IoStatus__IRP : _boogie_name)
variable (_boogie_T_RequestorMode__IRP : _boogie_name)
variable (_boogie_T_PendingReturned__IRP : _boogie_name)
variable (_boogie_T_StackCount__IRP : _boogie_name)
variable (_boogie_T_CurrentLocation__IRP : _boogie_name)
variable (_boogie_T_Cancel__IRP : _boogie_name)
variable (_boogie_T_CancelIrql__IRP : _boogie_name)
variable (_boogie_T_ApcEnvironment__IRP : _boogie_name)
variable (_boogie_T_AllocationFlags__IRP : _boogie_name)
variable (_boogie_T_UserIosb__IRP : _boogie_name)
variable (_boogie_T_UserEvent__IRP : _boogie_name)
variable (_boogie_T_Overlay__IRP : _boogie_name)
variable (_boogie_T_CancelRoutine__IRP : _boogie_name)
variable (_boogie_T_UserBuffer__IRP : _boogie_name)
variable (_boogie_T_Tail__IRP : _boogie_name)
variable (_boogie_T_Type__KAPC : _boogie_name)
variable (_boogie_T_SpareByte0__KAPC : _boogie_name)
variable (_boogie_T_Size__KAPC : _boogie_name)
variable (_boogie_T_SpareByte1__KAPC : _boogie_name)
variable (_boogie_T_SpareLong0__KAPC : _boogie_name)
variable (_boogie_T_Thread__KAPC : _boogie_name)
variable (_boogie_T_ApcListEntry__KAPC : _boogie_name)
variable (_boogie_T_KernelRoutine__KAPC : _boogie_name)
variable (_boogie_T_RundownRoutine__KAPC : _boogie_name)
variable (_boogie_T_NormalRoutine__KAPC : _boogie_name)
variable (_boogie_T_NormalContext__KAPC : _boogie_name)
variable (_boogie_T_SystemArgument1__KAPC : _boogie_name)
variable (_boogie_T_SystemArgument2__KAPC : _boogie_name)
variable (_boogie_T_ApcStateIndex__KAPC : _boogie_name)
variable (_boogie_T_ApcMode__KAPC : _boogie_name)
variable (_boogie_T_Inserted__KAPC : _boogie_name)
variable (_boogie_T_Type__KDEVICE_QUEUE : _boogie_name)
variable (_boogie_T_Size__KDEVICE_QUEUE : _boogie_name)
variable (_boogie_T_DeviceListHead__KDEVICE_QUEUE : _boogie_name)
variable (_boogie_T_Lock__KDEVICE_QUEUE : _boogie_name)
variable (_boogie_T_Busy__KDEVICE_QUEUE : _boogie_name)
variable (_boogie_T_DeviceListEntry__KDEVICE_QUEUE_ENTRY : _boogie_name)
variable (_boogie_T_SortKey__KDEVICE_QUEUE_ENTRY : _boogie_name)
variable (_boogie_T_Inserted__KDEVICE_QUEUE_ENTRY : _boogie_name)
variable (_boogie_T_Type__KDPC : _boogie_name)
variable (_boogie_T_Importance__KDPC : _boogie_name)
variable (_boogie_T_Number__KDPC : _boogie_name)
variable (_boogie_T_DpcListEntry__KDPC : _boogie_name)
variable (_boogie_T_DeferredRoutine__KDPC : _boogie_name)
variable (_boogie_T_DeferredContext__KDPC : _boogie_name)
variable (_boogie_T_SystemArgument1__KDPC : _boogie_name)
variable (_boogie_T_SystemArgument2__KDPC : _boogie_name)
variable (_boogie_T_DpcData__KDPC : _boogie_name)
variable (_boogie_T_Header__KEVENT : _boogie_name)
variable (_boogie_T_KeyboardIdentifier__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_KeyboardMode__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_NumberOfIndicators__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_NumberOfKeysTotal__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_InputDataQueueLength__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_KeyRepeatMinimum__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_KeyRepeatMaximum__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T_Type__KEYBOARD_ID : _boogie_name)
variable (_boogie_T_Subtype__KEYBOARD_ID : _boogie_name)
variable (_boogie_T_UnitId__KEYBOARD_INDICATOR_PARAMETERS : _boogie_name)
variable (_boogie_T_LedFlags__KEYBOARD_INDICATOR_PARAMETERS : _boogie_name)
variable (_boogie_T_UnitId__KEYBOARD_INPUT_DATA : _boogie_name)
variable (_boogie_T_MakeCode__KEYBOARD_INPUT_DATA : _boogie_name)
variable (_boogie_T_Flags__KEYBOARD_INPUT_DATA : _boogie_name)
variable (_boogie_T_Reserved__KEYBOARD_INPUT_DATA : _boogie_name)
variable (_boogie_T_ExtraInformation__KEYBOARD_INPUT_DATA : _boogie_name)
variable (_boogie_T_UnitId__KEYBOARD_TYPEMATIC_PARAMETERS : _boogie_name)
variable (_boogie_T_Rate__KEYBOARD_TYPEMATIC_PARAMETERS : _boogie_name)
variable (_boogie_T_Delay__KEYBOARD_TYPEMATIC_PARAMETERS : _boogie_name)
variable (_boogie_T_Header__KSEMAPHORE : _boogie_name)
variable (_boogie_T_Limit__KSEMAPHORE : _boogie_name)
variable (_boogie_T___unnamed_8_58ee4a31__LARGE_INTEGER : _boogie_name)
variable (_boogie_T_u__LARGE_INTEGER : _boogie_name)
variable (_boogie_T_QuadPart__LARGE_INTEGER : _boogie_name)
variable (_boogie_T_Flink__LIST_ENTRY : _boogie_name)
variable (_boogie_T_Blink__LIST_ENTRY : _boogie_name)
variable (_boogie_T_LowPart__LUID : _boogie_name)
variable (_boogie_T_HighPart__LUID : _boogie_name)
variable (_boogie_T_Luid__LUID_AND_ATTRIBUTES : _boogie_name)
variable (_boogie_T_Attributes__LUID_AND_ATTRIBUTES : _boogie_name)
variable (_boogie_T_Next__MDL : _boogie_name)
variable (_boogie_T_Size__MDL : _boogie_name)
variable (_boogie_T_MdlFlags__MDL : _boogie_name)
variable (_boogie_T_Process__MDL : _boogie_name)
variable (_boogie_T_MappedSystemVa__MDL : _boogie_name)
variable (_boogie_T_StartVa__MDL : _boogie_name)
variable (_boogie_T_ByteCount__MDL : _boogie_name)
variable (_boogie_T_ByteOffset__MDL : _boogie_name)
variable (_boogie_T_OwnerThread__OWNER_ENTRY : _boogie_name)
variable (_boogie_T___unnamed_4_6f9ac8e1__OWNER_ENTRY : _boogie_name)
variable (_boogie_T_File__PORT : _boogie_name)
variable (_boogie_T_Port__PORT : _boogie_name)
variable (_boogie_T_Enabled__PORT : _boogie_name)
variable (_boogie_T_Reserved__PORT : _boogie_name)
variable (_boogie_T_Free__PORT : _boogie_name)
variable (_boogie_T_SequenceD1__POWER_SEQUENCE : _boogie_name)
variable (_boogie_T_SequenceD2__POWER_SEQUENCE : _boogie_name)
variable (_boogie_T_SequenceD3__POWER_SEQUENCE : _boogie_name)
variable (_boogie_T_SystemState__POWER_STATE : _boogie_name)
variable (_boogie_T_DeviceState__POWER_STATE : _boogie_name)
variable (_boogie_T_PrivilegeCount__PRIVILEGE_SET : _boogie_name)
variable (_boogie_T_Control__PRIVILEGE_SET : _boogie_name)
variable (_boogie_T_Privilege__PRIVILEGE_SET : _boogie_name)
variable (_boogie_T_DataSectionObject__SECTION_OBJECT_POINTERS : _boogie_name)
variable (_boogie_T_SharedCacheMap__SECTION_OBJECT_POINTERS : _boogie_name)
variable (_boogie_T_ImageSectionObject__SECTION_OBJECT_POINTERS : _boogie_name)
variable (_boogie_T_Length__SECURITY_QUALITY_OF_SERVICE : _boogie_name)
variable (_boogie_T_ImpersonationLevel__SECURITY_QUALITY_OF_SERVICE : _boogie_name)
variable (_boogie_T_ContextTrackingMode__SECURITY_QUALITY_OF_SERVICE : _boogie_name)
variable (_boogie_T_EffectiveOnly__SECURITY_QUALITY_OF_SERVICE : _boogie_name)
variable (_boogie_T_ClientToken__SECURITY_SUBJECT_CONTEXT : _boogie_name)
variable (_boogie_T_ImpersonationLevel__SECURITY_SUBJECT_CONTEXT : _boogie_name)
variable (_boogie_T_PrimaryToken__SECURITY_SUBJECT_CONTEXT : _boogie_name)
variable (_boogie_T_ProcessAuditId__SECURITY_SUBJECT_CONTEXT : _boogie_name)
variable (_boogie_T___unnamed_4_3a2fdc5e__SYSTEM_POWER_STATE_CONTEXT : _boogie_name)
variable (_boogie_T_Length__UNICODE_STRING : _boogie_name)
variable (_boogie_T_MaximumLength__UNICODE_STRING : _boogie_name)
variable (_boogie_T_Buffer__UNICODE_STRING : _boogie_name)
variable (_boogie_T_Type__VPB : _boogie_name)
variable (_boogie_T_Size__VPB : _boogie_name)
variable (_boogie_T_Flags__VPB : _boogie_name)
variable (_boogie_T_VolumeLabelLength__VPB : _boogie_name)
variable (_boogie_T_DeviceObject__VPB : _boogie_name)
variable (_boogie_T_RealDevice__VPB : _boogie_name)
variable (_boogie_T_SerialNumber__VPB : _boogie_name)
variable (_boogie_T_ReferenceCount__VPB : _boogie_name)
variable (_boogie_T_VolumeLabel__VPB : _boogie_name)
variable (_boogie_T_WaitQueueEntry__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T_DeviceRoutine__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T_DeviceContext__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T_NumberOfMapRegisters__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T_DeviceObject__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T_CurrentIrp__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T_BufferChainingDpc__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T_GuidCount__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_GuidList__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_QueryWmiRegInfo__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_QueryWmiDataBlock__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_SetWmiDataBlock__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_SetWmiDataItem__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_ExecuteWmiMethod__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_WmiFunctionControl__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T_Reserved___unnamed_12_0d6a30de : _boogie_name)
variable (_boogie_T_MessageCount___unnamed_12_0d6a30de : _boogie_name)
variable (_boogie_T_Vector___unnamed_12_0d6a30de : _boogie_name)
variable (_boogie_T_Affinity___unnamed_12_0d6a30de : _boogie_name)
variable (_boogie_T_Start___unnamed_12_17f5c211 : _boogie_name)
variable (_boogie_T_Length48___unnamed_12_17f5c211 : _boogie_name)
variable (_boogie_T_Start___unnamed_12_1fb42e39 : _boogie_name)
variable (_boogie_T_Length___unnamed_12_1fb42e39 : _boogie_name)
variable (_boogie_T_Reserved___unnamed_12_1fb42e39 : _boogie_name)
variable (_boogie_T_Start___unnamed_12_2a1563c6 : _boogie_name)
variable (_boogie_T_Length___unnamed_12_2a1563c6 : _boogie_name)
variable (_boogie_T_DataSize___unnamed_12_31347272 : _boogie_name)
variable (_boogie_T_Reserved1___unnamed_12_31347272 : _boogie_name)
variable (_boogie_T_Reserved2___unnamed_12_31347272 : _boogie_name)
variable (_boogie_T_Raw___unnamed_12_429aadc0 : _boogie_name)
variable (_boogie_T_Translated___unnamed_12_429aadc0 : _boogie_name)
variable (_boogie_T_Start___unnamed_12_4719de1a : _boogie_name)
variable (_boogie_T_Length___unnamed_12_4719de1a : _boogie_name)
variable (_boogie_T_Data___unnamed_12_4be56faa : _boogie_name)
variable (_boogie_T_Data___unnamed_12_5ce25b92 : _boogie_name)
variable (_boogie_T_Generic___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Port___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Interrupt___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_MessageInterrupt___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Memory___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Dma___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_DevicePrivate___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_BusNumber___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_DeviceSpecificData___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Memory40___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Memory48___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Memory64___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T_Start___unnamed_12_87c0de8d : _boogie_name)
variable (_boogie_T_Length64___unnamed_12_87c0de8d : _boogie_name)
variable (_boogie_T_Start___unnamed_12_98bfc55a : _boogie_name)
variable (_boogie_T_Length40___unnamed_12_98bfc55a : _boogie_name)
variable (_boogie_T_Priority___unnamed_12_ab1bd9d7 : _boogie_name)
variable (_boogie_T_Reserved1___unnamed_12_ab1bd9d7 : _boogie_name)
variable (_boogie_T_Reserved2___unnamed_12_ab1bd9d7 : _boogie_name)
variable (_boogie_T_Level___unnamed_12_b0429be9 : _boogie_name)
variable (_boogie_T_Vector___unnamed_12_b0429be9 : _boogie_name)
variable (_boogie_T_Affinity___unnamed_12_b0429be9 : _boogie_name)
variable (_boogie_T_ListEntry___unnamed_12_b43e8de8 : _boogie_name)
variable (_boogie_T___unnamed_4_f19b65c1___unnamed_12_b43e8de8 : _boogie_name)
variable (_boogie_T_Level___unnamed_12_bfdb39ee : _boogie_name)
variable (_boogie_T_Vector___unnamed_12_bfdb39ee : _boogie_name)
variable (_boogie_T_Affinity___unnamed_12_bfdb39ee : _boogie_name)
variable (_boogie_T_Start___unnamed_12_cd42b3c3 : _boogie_name)
variable (_boogie_T_Length___unnamed_12_cd42b3c3 : _boogie_name)
variable (_boogie_T___unnamed_12_429aadc0___unnamed_12_e668effc : _boogie_name)
variable (_boogie_T_Channel___unnamed_12_e80d029e : _boogie_name)
variable (_boogie_T_Port___unnamed_12_e80d029e : _boogie_name)
variable (_boogie_T_Reserved1___unnamed_12_e80d029e : _boogie_name)
variable (_boogie_T_Length___unnamed_16_07c0bcc5 : _boogie_name)
variable (_boogie_T_MinBusNumber___unnamed_16_07c0bcc5 : _boogie_name)
variable (_boogie_T_MaxBusNumber___unnamed_16_07c0bcc5 : _boogie_name)
variable (_boogie_T_Reserved___unnamed_16_07c0bcc5 : _boogie_name)
variable (_boogie_T_InterfaceType___unnamed_16_29cb9f2f : _boogie_name)
variable (_boogie_T_Size___unnamed_16_29cb9f2f : _boogie_name)
variable (_boogie_T_Version___unnamed_16_29cb9f2f : _boogie_name)
variable (_boogie_T_Interface___unnamed_16_29cb9f2f : _boogie_name)
variable (_boogie_T_InterfaceSpecificData___unnamed_16_29cb9f2f : _boogie_name)
variable (_boogie_T_SecurityContext___unnamed_16_30f11dbf : _boogie_name)
variable (_boogie_T_Options___unnamed_16_30f11dbf : _boogie_name)
variable (_boogie_T_FileAttributes___unnamed_16_30f11dbf : _boogie_name)
variable (_boogie_T_ShareAccess___unnamed_16_30f11dbf : _boogie_name)
variable (_boogie_T_EaLength___unnamed_16_30f11dbf : _boogie_name)
variable (_boogie_T_DriverContext___unnamed_16_35034f68 : _boogie_name)
variable (_boogie_T_Length___unnamed_16_487a9498 : _boogie_name)
variable (_boogie_T_FileName___unnamed_16_487a9498 : _boogie_name)
variable (_boogie_T_FileInformationClass___unnamed_16_487a9498 : _boogie_name)
variable (_boogie_T_FileIndex___unnamed_16_487a9498 : _boogie_name)
variable (_boogie_T_OutputBufferLength___unnamed_16_5f6a8844 : _boogie_name)
variable (_boogie_T_InputBufferLength___unnamed_16_5f6a8844 : _boogie_name)
variable (_boogie_T_FsControlCode___unnamed_16_5f6a8844 : _boogie_name)
variable (_boogie_T_Type3InputBuffer___unnamed_16_5f6a8844 : _boogie_name)
variable (_boogie_T_Length___unnamed_16_7177b9f3 : _boogie_name)
variable (_boogie_T_FileInformationClass___unnamed_16_7177b9f3 : _boogie_name)
variable (_boogie_T_FileObject___unnamed_16_7177b9f3 : _boogie_name)
variable (_boogie_T___unnamed_4_43913aa5___unnamed_16_7177b9f3 : _boogie_name)
variable (_boogie_T_Length___unnamed_16_88e91ef6 : _boogie_name)
variable (_boogie_T_Key___unnamed_16_88e91ef6 : _boogie_name)
variable (_boogie_T_ByteOffset___unnamed_16_88e91ef6 : _boogie_name)
variable (_boogie_T_Length___unnamed_16_8c506c98 : _boogie_name)
variable (_boogie_T_Key___unnamed_16_8c506c98 : _boogie_name)
variable (_boogie_T_ByteOffset___unnamed_16_8c506c98 : _boogie_name)
variable (_boogie_T_WhichSpace___unnamed_16_9ac2e5f8 : _boogie_name)
variable (_boogie_T_Buffer___unnamed_16_9ac2e5f8 : _boogie_name)
variable (_boogie_T_Offset___unnamed_16_9ac2e5f8 : _boogie_name)
variable (_boogie_T_Length___unnamed_16_9ac2e5f8 : _boogie_name)
variable (_boogie_T_Create___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_Read___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_Write___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryDirectory___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_NotifyDirectory___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryFile___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_SetFile___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryEa___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_SetEa___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryVolume___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_SetVolume___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_FileSystemControl___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_LockControl___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_DeviceIoControl___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QuerySecurity___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_SetSecurity___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_MountVolume___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_VerifyVolume___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_Scsi___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryQuota___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_SetQuota___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryDeviceRelations___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryInterface___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_DeviceCapabilities___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_FilterResourceRequirements___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_ReadWriteConfig___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_SetLock___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryId___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_QueryDeviceText___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_UsageNotification___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_WaitWake___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_PowerSequence___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_Power___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_StartDevice___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_WMI___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_Others___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T_Length___unnamed_16_b9c62eab : _boogie_name)
variable (_boogie_T_Key___unnamed_16_b9c62eab : _boogie_name)
variable (_boogie_T_ByteOffset___unnamed_16_b9c62eab : _boogie_name)
variable (_boogie_T___unnamed_4_7d9d0c7e___unnamed_16_bb584060 : _boogie_name)
variable (_boogie_T_Type___unnamed_16_bb584060 : _boogie_name)
variable (_boogie_T_State___unnamed_16_bb584060 : _boogie_name)
variable (_boogie_T_ShutdownType___unnamed_16_bb584060 : _boogie_name)
variable (_boogie_T_OutputBufferLength___unnamed_16_dba55c7c : _boogie_name)
variable (_boogie_T_InputBufferLength___unnamed_16_dba55c7c : _boogie_name)
variable (_boogie_T_IoControlCode___unnamed_16_dba55c7c : _boogie_name)
variable (_boogie_T_Type3InputBuffer___unnamed_16_dba55c7c : _boogie_name)
variable (_boogie_T_DeviceQueueEntry___unnamed_16_e70c268b : _boogie_name)
variable (_boogie_T___unnamed_16_35034f68___unnamed_16_e70c268b : _boogie_name)
variable (_boogie_T_Argument1___unnamed_16_e734d694 : _boogie_name)
variable (_boogie_T_Argument2___unnamed_16_e734d694 : _boogie_name)
variable (_boogie_T_Argument3___unnamed_16_e734d694 : _boogie_name)
variable (_boogie_T_Argument4___unnamed_16_e734d694 : _boogie_name)
variable (_boogie_T_ProviderId___unnamed_16_eac6dbea : _boogie_name)
variable (_boogie_T_DataPath___unnamed_16_eac6dbea : _boogie_name)
variable (_boogie_T_BufferSize___unnamed_16_eac6dbea : _boogie_name)
variable (_boogie_T_Buffer___unnamed_16_eac6dbea : _boogie_name)
variable (_boogie_T_Length___unnamed_16_f6cae4c2 : _boogie_name)
variable (_boogie_T_EaList___unnamed_16_f6cae4c2 : _boogie_name)
variable (_boogie_T_EaListLength___unnamed_16_f6cae4c2 : _boogie_name)
variable (_boogie_T_EaIndex___unnamed_16_f6cae4c2 : _boogie_name)
variable (_boogie_T_Length___unnamed_16_fe36e4f4 : _boogie_name)
variable (_boogie_T_StartSid___unnamed_16_fe36e4f4 : _boogie_name)
variable (_boogie_T_SidList___unnamed_16_fe36e4f4 : _boogie_name)
variable (_boogie_T_SidListLength___unnamed_16_fe36e4f4 : _boogie_name)
variable (_boogie_T_Abandoned___unnamed_1_29794256 : _boogie_name)
variable (_boogie_T_Absolute___unnamed_1_29794256 : _boogie_name)
variable (_boogie_T_NpxIrql___unnamed_1_29794256 : _boogie_name)
variable (_boogie_T_Signalling___unnamed_1_29794256 : _boogie_name)
variable (_boogie_T_Inserted___unnamed_1_2dc63b48 : _boogie_name)
variable (_boogie_T_DebugActive___unnamed_1_2dc63b48 : _boogie_name)
variable (_boogie_T_DpcActive___unnamed_1_2dc63b48 : _boogie_name)
variable (_boogie_T_Size___unnamed_1_2ef8da39 : _boogie_name)
variable (_boogie_T_Hand___unnamed_1_2ef8da39 : _boogie_name)
variable (_boogie_T_Lock___unnamed_1_faa7dc71 : _boogie_name)
variable (_boogie_T_MinimumVector___unnamed_20_f4d2e6d8 : _boogie_name)
variable (_boogie_T_MaximumVector___unnamed_20_f4d2e6d8 : _boogie_name)
variable (_boogie_T_AffinityPolicy___unnamed_20_f4d2e6d8 : _boogie_name)
variable (_boogie_T_PriorityPolicy___unnamed_20_f4d2e6d8 : _boogie_name)
variable (_boogie_T_TargetedProcessors___unnamed_20_f4d2e6d8 : _boogie_name)
variable (_boogie_T_Length___unnamed_24_41cbc8c0 : _boogie_name)
variable (_boogie_T_Alignment___unnamed_24_41cbc8c0 : _boogie_name)
variable (_boogie_T_MinimumAddress___unnamed_24_41cbc8c0 : _boogie_name)
variable (_boogie_T_MaximumAddress___unnamed_24_41cbc8c0 : _boogie_name)
variable (_boogie_T_Length48___unnamed_24_5419c914 : _boogie_name)
variable (_boogie_T_Alignment48___unnamed_24_5419c914 : _boogie_name)
variable (_boogie_T_MinimumAddress___unnamed_24_5419c914 : _boogie_name)
variable (_boogie_T_MaximumAddress___unnamed_24_5419c914 : _boogie_name)
variable (_boogie_T_Length___unnamed_24_67a5ff10 : _boogie_name)
variable (_boogie_T_Alignment___unnamed_24_67a5ff10 : _boogie_name)
variable (_boogie_T_MinimumAddress___unnamed_24_67a5ff10 : _boogie_name)
variable (_boogie_T_MaximumAddress___unnamed_24_67a5ff10 : _boogie_name)
variable (_boogie_T_Port___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Memory___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Interrupt___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Dma___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Generic___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_DevicePrivate___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_BusNumber___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_ConfigData___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Memory40___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Memory48___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Memory64___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T_Length64___unnamed_24_a26050bb : _boogie_name)
variable (_boogie_T_Alignment64___unnamed_24_a26050bb : _boogie_name)
variable (_boogie_T_MinimumAddress___unnamed_24_a26050bb : _boogie_name)
variable (_boogie_T_MaximumAddress___unnamed_24_a26050bb : _boogie_name)
variable (_boogie_T_Length___unnamed_24_b8f476db : _boogie_name)
variable (_boogie_T_Alignment___unnamed_24_b8f476db : _boogie_name)
variable (_boogie_T_MinimumAddress___unnamed_24_b8f476db : _boogie_name)
variable (_boogie_T_MaximumAddress___unnamed_24_b8f476db : _boogie_name)
variable (_boogie_T_Length40___unnamed_24_d09044b4 : _boogie_name)
variable (_boogie_T_Alignment40___unnamed_24_d09044b4 : _boogie_name)
variable (_boogie_T_MinimumAddress___unnamed_24_d09044b4 : _boogie_name)
variable (_boogie_T_MaximumAddress___unnamed_24_d09044b4 : _boogie_name)
variable (_boogie_T_ReplaceIfExists___unnamed_2_46cc4597 : _boogie_name)
variable (_boogie_T_AdvanceOnly___unnamed_2_46cc4597 : _boogie_name)
variable (_boogie_T___unnamed_16_e70c268b___unnamed_40_7218f704 : _boogie_name)
variable (_boogie_T_Thread___unnamed_40_7218f704 : _boogie_name)
variable (_boogie_T_AuxiliaryBuffer___unnamed_40_7218f704 : _boogie_name)
variable (_boogie_T___unnamed_12_b43e8de8___unnamed_40_7218f704 : _boogie_name)
variable (_boogie_T_OriginalFileObject___unnamed_40_7218f704 : _boogie_name)
variable (_boogie_T_ListEntry___unnamed_40_c55c9377 : _boogie_name)
variable (_boogie_T_Wcb___unnamed_40_c55c9377 : _boogie_name)
variable (_boogie_T_InitialPrivilegeSet___unnamed_44_5584090d : _boogie_name)
variable (_boogie_T_PrivilegeSet___unnamed_44_5584090d : _boogie_name)
variable (_boogie_T_Overlay___unnamed_48_cf99b13f : _boogie_name)
variable (_boogie_T_Apc___unnamed_48_cf99b13f : _boogie_name)
variable (_boogie_T_CompletionKey___unnamed_48_cf99b13f : _boogie_name)
variable (_boogie_T_PowerState___unnamed_4_069846fb : _boogie_name)
variable (_boogie_T_IdType___unnamed_4_224c32f4 : _boogie_name)
variable (_boogie_T_Capabilities___unnamed_4_2de698da : _boogie_name)
variable (_boogie_T___unnamed_4_c3479730___unnamed_4_3a2fdc5e : _boogie_name)
variable (_boogie_T_ContextAsUlong___unnamed_4_3a2fdc5e : _boogie_name)
variable (_boogie_T_Length___unnamed_4_3a4c1a13 : _boogie_name)
variable (_boogie_T___unnamed_2_46cc4597___unnamed_4_43913aa5 : _boogie_name)
variable (_boogie_T_ClusterCount___unnamed_4_43913aa5 : _boogie_name)
variable (_boogie_T_DeleteHandle___unnamed_4_43913aa5 : _boogie_name)
variable (_boogie_T_UserApcRoutine___unnamed_4_4e8dd2ba : _boogie_name)
variable (_boogie_T_IssuingProcess___unnamed_4_4e8dd2ba : _boogie_name)
variable (_boogie_T_Srb___unnamed_4_52603077 : _boogie_name)
variable (_boogie_T_Address___unnamed_4_52c594f7 : _boogie_name)
variable (_boogie_T_CreatorBackTraceIndex___unnamed_4_52c594f7 : _boogie_name)
variable (_boogie_T_Type___unnamed_4_5ca00198 : _boogie_name)
variable (_boogie_T___unnamed_1_29794256___unnamed_4_5ca00198 : _boogie_name)
variable (_boogie_T___unnamed_1_2ef8da39___unnamed_4_5ca00198 : _boogie_name)
variable (_boogie_T___unnamed_1_2dc63b48___unnamed_4_5ca00198 : _boogie_name)
variable (_boogie_T_MasterIrp___unnamed_4_6ac6463c : _boogie_name)
variable (_boogie_T_IrpCount___unnamed_4_6ac6463c : _boogie_name)
variable (_boogie_T_SystemBuffer___unnamed_4_6ac6463c : _boogie_name)
variable (_boogie_T_OwnerCount___unnamed_4_6f9ac8e1 : _boogie_name)
variable (_boogie_T_TableSize___unnamed_4_6f9ac8e1 : _boogie_name)
variable (_boogie_T_PowerSequence___unnamed_4_7a02167b : _boogie_name)
variable (_boogie_T_SystemContext___unnamed_4_7d9d0c7e : _boogie_name)
variable (_boogie_T_SystemPowerStateContext___unnamed_4_7d9d0c7e : _boogie_name)
variable (_boogie_T_IoResourceRequirementList___unnamed_4_82f7a864 : _boogie_name)
variable (_boogie_T_Length___unnamed_4_9aec220b : _boogie_name)
variable (_boogie_T___unnamed_4_5ca00198___unnamed_4_a97c65a1 : _boogie_name)
variable (_boogie_T_Lock___unnamed_4_a97c65a1 : _boogie_name)
variable (_boogie_T_Reserved1___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T_TargetSystemState___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T_EffectiveSystemState___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T_CurrentSystemState___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T_IgnoreHibernationPath___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T_PseudoTransition___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T_Reserved2___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T_Status___unnamed_4_d99b6e2b : _boogie_name)
variable (_boogie_T_Pointer___unnamed_4_d99b6e2b : _boogie_name)
variable (_boogie_T_CurrentStackLocation___unnamed_4_f19b65c1 : _boogie_name)
variable (_boogie_T_PacketType___unnamed_4_f19b65c1 : _boogie_name)
variable (_boogie_T_Type___unnamed_4_fa10fc16 : _boogie_name)
variable (_boogie_T_SecurityInformation___unnamed_8_01efa60d : _boogie_name)
variable (_boogie_T_Length___unnamed_8_01efa60d : _boogie_name)
variable (_boogie_T_MinimumChannel___unnamed_8_08d4cef8 : _boogie_name)
variable (_boogie_T_MaximumChannel___unnamed_8_08d4cef8 : _boogie_name)
variable (_boogie_T___unnamed_4_4e8dd2ba___unnamed_8_0a898c0c : _boogie_name)
variable (_boogie_T_UserApcContext___unnamed_8_0a898c0c : _boogie_name)
variable (_boogie_T_SecurityInformation___unnamed_8_1330f93a : _boogie_name)
variable (_boogie_T_SecurityDescriptor___unnamed_8_1330f93a : _boogie_name)
variable (_boogie_T_AsynchronousParameters___unnamed_8_181d0de9 : _boogie_name)
variable (_boogie_T_AllocationSize___unnamed_8_181d0de9 : _boogie_name)
variable (_boogie_T_Vpb___unnamed_8_4812764d : _boogie_name)
variable (_boogie_T_DeviceObject___unnamed_8_4812764d : _boogie_name)
variable (_boogie_T_Length___unnamed_8_559a91e6 : _boogie_name)
variable (_boogie_T_FsInformationClass___unnamed_8_559a91e6 : _boogie_name)
variable (_boogie_T_Length___unnamed_8_5845b309 : _boogie_name)
variable (_boogie_T_FileInformationClass___unnamed_8_5845b309 : _boogie_name)
variable (_boogie_T_LowPart___unnamed_8_58ee4a31 : _boogie_name)
variable (_boogie_T_HighPart___unnamed_8_58ee4a31 : _boogie_name)
variable (_boogie_T_AllocatedResources___unnamed_8_61acf4ce : _boogie_name)
variable (_boogie_T_AllocatedResourcesTranslated___unnamed_8_61acf4ce : _boogie_name)
variable (_boogie_T_DeviceTextType___unnamed_8_6acfee04 : _boogie_name)
variable (_boogie_T_LocaleId___unnamed_8_6acfee04 : _boogie_name)
variable (_boogie_T_Length___unnamed_8_7f26a9dd : _boogie_name)
variable (_boogie_T_CompletionFilter___unnamed_8_7f26a9dd : _boogie_name)
variable (_boogie_T_Vpb___unnamed_8_87add0bd : _boogie_name)
variable (_boogie_T_DeviceObject___unnamed_8_87add0bd : _boogie_name)
variable (_boogie_T_InPath___unnamed_8_b2773e4c : _boogie_name)
variable (_boogie_T_Reserved___unnamed_8_b2773e4c : _boogie_name)
variable (_boogie_T_Type___unnamed_8_b2773e4c : _boogie_name)
variable (_boogie_T_Length___unnamed_8_de890d4e : _boogie_name)
variable (_boogie_T_FsInformationClass___unnamed_8_de890d4e : _boogie_name)
variable (_boogie_T_LowPart___unnamed_8_ef9ba0d3 : _boogie_name)
variable (_boogie_T_HighPart___unnamed_8_ef9ba0d3 : _boogie_name)
variable (_boogie_T_A11CHAR : _boogie_name)
variable (_boogie_T_A19CHAR : _boogie_name)
variable (_boogie_T_A1_CM_FULL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_A1_CM_PARTIAL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_A1_IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T_A1_IO_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_A1_LUID_AND_ATTRIBUTES : _boogie_name)
variable (_boogie_T_A256UINT2 : _boogie_name)
variable (_boogie_T_A28PFDRIVER_DISPATCH : _boogie_name)
variable (_boogie_T_A2UCHAR : _boogie_name)
variable (_boogie_T_A32UINT2 : _boogie_name)
variable (_boogie_T_A36CHAR : _boogie_name)
variable (_boogie_T_A37CHAR : _boogie_name)
variable (_boogie_T_A39CHAR : _boogie_name)
variable (_boogie_T_A3UCHAR : _boogie_name)
variable (_boogie_T_A3UINT4 : _boogie_name)
variable (_boogie_T_A3_LUID_AND_ATTRIBUTES : _boogie_name)
variable (_boogie_T_A43CHAR : _boogie_name)
variable (_boogie_T_A4PVOID : _boogie_name)
variable (_boogie_T_A4UINT4 : _boogie_name)
variable (_boogie_T_A5_DEVICE_POWER_STATE : _boogie_name)
variable (_boogie_T_A74CHAR : _boogie_name)
variable (_boogie_T_A7_DEVICE_POWER_STATE : _boogie_name)
variable (_boogie_T_A8UCHAR : _boogie_name)
variable (_boogie_T_BUS_QUERY_ID_TYPE : _boogie_name)
variable (_boogie_T_CHAR : _boogie_name)
variable (_boogie_T_DEVICE_TEXT_TYPE : _boogie_name)
variable (_boogie_T_F0 : _boogie_name)
variable (_boogie_T_F1 : _boogie_name)
variable (_boogie_T_F10 : _boogie_name)
variable (_boogie_T_F11 : _boogie_name)
variable (_boogie_T_F12 : _boogie_name)
variable (_boogie_T_F13 : _boogie_name)
variable (_boogie_T_F14 : _boogie_name)
variable (_boogie_T_F15 : _boogie_name)
variable (_boogie_T_F16 : _boogie_name)
variable (_boogie_T_F17 : _boogie_name)
variable (_boogie_T_F18 : _boogie_name)
variable (_boogie_T_F19 : _boogie_name)
variable (_boogie_T_F2 : _boogie_name)
variable (_boogie_T_F20 : _boogie_name)
variable (_boogie_T_F21 : _boogie_name)
variable (_boogie_T_F22 : _boogie_name)
variable (_boogie_T_F23 : _boogie_name)
variable (_boogie_T_F24 : _boogie_name)
variable (_boogie_T_F25 : _boogie_name)
variable (_boogie_T_F26 : _boogie_name)
variable (_boogie_T_F27 : _boogie_name)
variable (_boogie_T_F28 : _boogie_name)
variable (_boogie_T_F29 : _boogie_name)
variable (_boogie_T_F3 : _boogie_name)
variable (_boogie_T_F30 : _boogie_name)
variable (_boogie_T_F31 : _boogie_name)
variable (_boogie_T_F32 : _boogie_name)
variable (_boogie_T_F33 : _boogie_name)
variable (_boogie_T_F34 : _boogie_name)
variable (_boogie_T_F35 : _boogie_name)
variable (_boogie_T_F36 : _boogie_name)
variable (_boogie_T_F37 : _boogie_name)
variable (_boogie_T_F38 : _boogie_name)
variable (_boogie_T_F4 : _boogie_name)
variable (_boogie_T_F5 : _boogie_name)
variable (_boogie_T_F6 : _boogie_name)
variable (_boogie_T_F7 : _boogie_name)
variable (_boogie_T_F8 : _boogie_name)
variable (_boogie_T_F9 : _boogie_name)
variable (_boogie_T_FDRIVER_ADD_DEVICE : _boogie_name)
variable (_boogie_T_FDRIVER_CANCEL : _boogie_name)
variable (_boogie_T_FDRIVER_CONTROL : _boogie_name)
variable (_boogie_T_FDRIVER_DISPATCH : _boogie_name)
variable (_boogie_T_FDRIVER_INITIALIZE : _boogie_name)
variable (_boogie_T_FDRIVER_STARTIO : _boogie_name)
variable (_boogie_T_FDRIVER_UNLOAD : _boogie_name)
variable (_boogie_T_FFAST_IO_ACQUIRE_FILE : _boogie_name)
variable (_boogie_T_FFAST_IO_ACQUIRE_FOR_CCFLUSH : _boogie_name)
variable (_boogie_T_FFAST_IO_ACQUIRE_FOR_MOD_WRITE : _boogie_name)
variable (_boogie_T_FFAST_IO_CHECK_IF_POSSIBLE : _boogie_name)
variable (_boogie_T_FFAST_IO_DETACH_DEVICE : _boogie_name)
variable (_boogie_T_FFAST_IO_DEVICE_CONTROL : _boogie_name)
variable (_boogie_T_FFAST_IO_LOCK : _boogie_name)
variable (_boogie_T_FFAST_IO_MDL_READ : _boogie_name)
variable (_boogie_T_FFAST_IO_MDL_READ_COMPLETE : _boogie_name)
variable (_boogie_T_FFAST_IO_MDL_READ_COMPLETE_COMPRESSED : _boogie_name)
variable (_boogie_T_FFAST_IO_MDL_WRITE_COMPLETE : _boogie_name)
variable (_boogie_T_FFAST_IO_MDL_WRITE_COMPLETE_COMPRESSED : _boogie_name)
variable (_boogie_T_FFAST_IO_PREPARE_MDL_WRITE : _boogie_name)
variable (_boogie_T_FFAST_IO_QUERY_BASIC_INFO : _boogie_name)
variable (_boogie_T_FFAST_IO_QUERY_NETWORK_OPEN_INFO : _boogie_name)
variable (_boogie_T_FFAST_IO_QUERY_OPEN : _boogie_name)
variable (_boogie_T_FFAST_IO_QUERY_STANDARD_INFO : _boogie_name)
variable (_boogie_T_FFAST_IO_READ : _boogie_name)
variable (_boogie_T_FFAST_IO_READ_COMPRESSED : _boogie_name)
variable (_boogie_T_FFAST_IO_RELEASE_FILE : _boogie_name)
variable (_boogie_T_FFAST_IO_RELEASE_FOR_CCFLUSH : _boogie_name)
variable (_boogie_T_FFAST_IO_RELEASE_FOR_MOD_WRITE : _boogie_name)
variable (_boogie_T_FFAST_IO_UNLOCK_ALL : _boogie_name)
variable (_boogie_T_FFAST_IO_UNLOCK_ALL_BY_KEY : _boogie_name)
variable (_boogie_T_FFAST_IO_UNLOCK_SINGLE : _boogie_name)
variable (_boogie_T_FFAST_IO_WRITE : _boogie_name)
variable (_boogie_T_FFAST_IO_WRITE_COMPRESSED : _boogie_name)
variable (_boogie_T_FIO_COMPLETION_ROUTINE : _boogie_name)
variable (_boogie_T_FKDEFERRED_ROUTINE : _boogie_name)
variable (_boogie_T_INT2 : _boogie_name)
variable (_boogie_T_INT4 : _boogie_name)
variable (_boogie_T_INT8 : _boogie_name)
variable (_boogie_T_PA11CHAR : _boogie_name)
variable (_boogie_T_PA19CHAR : _boogie_name)
variable (_boogie_T_PA36CHAR : _boogie_name)
variable (_boogie_T_PA37CHAR : _boogie_name)
variable (_boogie_T_PA39CHAR : _boogie_name)
variable (_boogie_T_PA43CHAR : _boogie_name)
variable (_boogie_T_PA74CHAR : _boogie_name)
variable (_boogie_T_PCHAR : _boogie_name)
variable (_boogie_T_PF19 : _boogie_name)
variable (_boogie_T_PF21 : _boogie_name)
variable (_boogie_T_PF23 : _boogie_name)
variable (_boogie_T_PF24 : _boogie_name)
variable (_boogie_T_PF25 : _boogie_name)
variable (_boogie_T_PF33 : _boogie_name)
variable (_boogie_T_PF34 : _boogie_name)
variable (_boogie_T_PF35 : _boogie_name)
variable (_boogie_T_PF36 : _boogie_name)
variable (_boogie_T_PF37 : _boogie_name)
variable (_boogie_T_PF38 : _boogie_name)
variable (_boogie_T_PFDRIVER_ADD_DEVICE : _boogie_name)
variable (_boogie_T_PFDRIVER_CANCEL : _boogie_name)
variable (_boogie_T_PFDRIVER_CONTROL : _boogie_name)
variable (_boogie_T_PFDRIVER_DISPATCH : _boogie_name)
variable (_boogie_T_PFDRIVER_INITIALIZE : _boogie_name)
variable (_boogie_T_PFDRIVER_STARTIO : _boogie_name)
variable (_boogie_T_PFDRIVER_UNLOAD : _boogie_name)
variable (_boogie_T_PFFAST_IO_ACQUIRE_FILE : _boogie_name)
variable (_boogie_T_PFFAST_IO_ACQUIRE_FOR_CCFLUSH : _boogie_name)
variable (_boogie_T_PFFAST_IO_ACQUIRE_FOR_MOD_WRITE : _boogie_name)
variable (_boogie_T_PFFAST_IO_CHECK_IF_POSSIBLE : _boogie_name)
variable (_boogie_T_PFFAST_IO_DETACH_DEVICE : _boogie_name)
variable (_boogie_T_PFFAST_IO_DEVICE_CONTROL : _boogie_name)
variable (_boogie_T_PFFAST_IO_LOCK : _boogie_name)
variable (_boogie_T_PFFAST_IO_MDL_READ : _boogie_name)
variable (_boogie_T_PFFAST_IO_MDL_READ_COMPLETE : _boogie_name)
variable (_boogie_T_PFFAST_IO_MDL_READ_COMPLETE_COMPRESSED : _boogie_name)
variable (_boogie_T_PFFAST_IO_MDL_WRITE_COMPLETE : _boogie_name)
variable (_boogie_T_PFFAST_IO_MDL_WRITE_COMPLETE_COMPRESSED : _boogie_name)
variable (_boogie_T_PFFAST_IO_PREPARE_MDL_WRITE : _boogie_name)
variable (_boogie_T_PFFAST_IO_QUERY_BASIC_INFO : _boogie_name)
variable (_boogie_T_PFFAST_IO_QUERY_NETWORK_OPEN_INFO : _boogie_name)
variable (_boogie_T_PFFAST_IO_QUERY_OPEN : _boogie_name)
variable (_boogie_T_PFFAST_IO_QUERY_STANDARD_INFO : _boogie_name)
variable (_boogie_T_PFFAST_IO_READ : _boogie_name)
variable (_boogie_T_PFFAST_IO_READ_COMPRESSED : _boogie_name)
variable (_boogie_T_PFFAST_IO_RELEASE_FILE : _boogie_name)
variable (_boogie_T_PFFAST_IO_RELEASE_FOR_CCFLUSH : _boogie_name)
variable (_boogie_T_PFFAST_IO_RELEASE_FOR_MOD_WRITE : _boogie_name)
variable (_boogie_T_PFFAST_IO_UNLOCK_ALL : _boogie_name)
variable (_boogie_T_PFFAST_IO_UNLOCK_ALL_BY_KEY : _boogie_name)
variable (_boogie_T_PFFAST_IO_UNLOCK_SINGLE : _boogie_name)
variable (_boogie_T_PFFAST_IO_WRITE : _boogie_name)
variable (_boogie_T_PFFAST_IO_WRITE_COMPRESSED : _boogie_name)
variable (_boogie_T_PFIO_COMPLETION_ROUTINE : _boogie_name)
variable (_boogie_T_PFKDEFERRED_ROUTINE : _boogie_name)
variable (_boogie_T_PINT4 : _boogie_name)
variable (_boogie_T_POWER_ACTION : _boogie_name)
variable (_boogie_T_PPCHAR : _boogie_name)
variable (_boogie_T_PPF24 : _boogie_name)
variable (_boogie_T_PPP_FILE_OBJECT : _boogie_name)
variable (_boogie_T_PPVOID : _boogie_name)
variable (_boogie_T_PP_DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_PP_DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_PP_DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_PP_ERESOURCE : _boogie_name)
variable (_boogie_T_PP_FILE_OBJECT : _boogie_name)
variable (_boogie_T_PP_IRP : _boogie_name)
variable (_boogie_T_PP_LIST_ENTRY : _boogie_name)
variable (_boogie_T_PP_MDL : _boogie_name)
variable (_boogie_T_PP_PORT : _boogie_name)
variable (_boogie_T_PP_UNICODE_STRING : _boogie_name)
variable (_boogie_T_PUCHAR : _boogie_name)
variable (_boogie_T_PUINT2 : _boogie_name)
variable (_boogie_T_PUINT4 : _boogie_name)
variable (_boogie_T_PVOID : _boogie_name)
variable (_boogie_T_PWMIGUIDREGINFO : _boogie_name)
variable (_boogie_T_P_ACCESS_STATE : _boogie_name)
variable (_boogie_T_P_CM_RESOURCE_LIST : _boogie_name)
variable (_boogie_T_P_COMPRESSED_DATA_INFO : _boogie_name)
variable (_boogie_T_P_DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T_P_DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T_P_DEVICE_OBJECT : _boogie_name)
variable (_boogie_T_P_DEVOBJ_EXTENSION : _boogie_name)
variable (_boogie_T_P_DRIVER_EXTENSION : _boogie_name)
variable (_boogie_T_P_DRIVER_OBJECT : _boogie_name)
variable (_boogie_T_P_EPROCESS : _boogie_name)
variable (_boogie_T_P_ERESOURCE : _boogie_name)
variable (_boogie_T_P_ETHREAD : _boogie_name)
variable (_boogie_T_P_FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T_P_FILE_BASIC_INFORMATION : _boogie_name)
variable (_boogie_T_P_FILE_GET_QUOTA_INFORMATION : _boogie_name)
variable (_boogie_T_P_FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T_P_FILE_OBJECT : _boogie_name)
variable (_boogie_T_P_FILE_STANDARD_INFORMATION : _boogie_name)
variable (_boogie_T_P_GLOBALS : _boogie_name)
variable (_boogie_T_P_GUID : _boogie_name)
variable (_boogie_T_P_INTERFACE : _boogie_name)
variable (_boogie_T_P_IO_COMPLETION_CONTEXT : _boogie_name)
variable (_boogie_T_P_IO_REMOVE_LOCK_TRACKING_BLOCK : _boogie_name)
variable (_boogie_T_P_IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T_P_IO_SECURITY_CONTEXT : _boogie_name)
variable (_boogie_T_P_IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T_P_IO_STATUS_BLOCK : _boogie_name)
variable (_boogie_T_P_IO_TIMER : _boogie_name)
variable (_boogie_T_P_IRP : _boogie_name)
variable (_boogie_T_P_KAPC : _boogie_name)
variable (_boogie_T_P_KDPC : _boogie_name)
variable (_boogie_T_P_KEVENT : _boogie_name)
variable (_boogie_T_P_KEYBOARD_INPUT_DATA : _boogie_name)
variable (_boogie_T_P_KSEMAPHORE : _boogie_name)
variable (_boogie_T_P_KTHREAD : _boogie_name)
variable (_boogie_T_P_LARGE_INTEGER : _boogie_name)
variable (_boogie_T_P_LIST_ENTRY : _boogie_name)
variable (_boogie_T_P_MDL : _boogie_name)
variable (_boogie_T_P_OWNER_ENTRY : _boogie_name)
variable (_boogie_T_P_PORT : _boogie_name)
variable (_boogie_T_P_POWER_SEQUENCE : _boogie_name)
variable (_boogie_T_P_SCSI_REQUEST_BLOCK : _boogie_name)
variable (_boogie_T_P_SECTION_OBJECT_POINTERS : _boogie_name)
variable (_boogie_T_P_SECURITY_QUALITY_OF_SERVICE : _boogie_name)
variable (_boogie_T_P_UNICODE_STRING : _boogie_name)
variable (_boogie_T_P_VPB : _boogie_name)
variable (_boogie_T_UCHAR : _boogie_name)
variable (_boogie_T_UINT2 : _boogie_name)
variable (_boogie_T_UINT4 : _boogie_name)
variable (_boogie_T_VOID : _boogie_name)
variable (_boogie_T_WMIENABLEDISABLECONTROL : _boogie_name)
variable (_boogie_T_WMIGUIDREGINFO : _boogie_name)
variable (_boogie_T__ACCESS_STATE : _boogie_name)
variable (_boogie_T__CM_FULL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T__CM_PARTIAL_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T__CM_PARTIAL_RESOURCE_LIST : _boogie_name)
variable (_boogie_T__CM_RESOURCE_LIST : _boogie_name)
variable (_boogie_T__COMPRESSED_DATA_INFO : _boogie_name)
variable (_boogie_T__DEVICE_CAPABILITIES : _boogie_name)
variable (_boogie_T__DEVICE_EXTENSION : _boogie_name)
variable (_boogie_T__DEVICE_OBJECT : _boogie_name)
variable (_boogie_T__DEVICE_POWER_STATE : _boogie_name)
variable (_boogie_T__DEVICE_RELATION_TYPE : _boogie_name)
variable (_boogie_T__DEVICE_USAGE_NOTIFICATION_TYPE : _boogie_name)
variable (_boogie_T__DEVOBJ_EXTENSION : _boogie_name)
variable (_boogie_T__DISPATCHER_HEADER : _boogie_name)
variable (_boogie_T__DRIVER_EXTENSION : _boogie_name)
variable (_boogie_T__DRIVER_OBJECT : _boogie_name)
variable (_boogie_T__EPROCESS : _boogie_name)
variable (_boogie_T__ERESOURCE : _boogie_name)
variable (_boogie_T__ETHREAD : _boogie_name)
variable (_boogie_T__FAST_IO_DISPATCH : _boogie_name)
variable (_boogie_T__FAST_MUTEX : _boogie_name)
variable (_boogie_T__FILE_BASIC_INFORMATION : _boogie_name)
variable (_boogie_T__FILE_GET_QUOTA_INFORMATION : _boogie_name)
variable (_boogie_T__FILE_INFORMATION_CLASS : _boogie_name)
variable (_boogie_T__FILE_NETWORK_OPEN_INFORMATION : _boogie_name)
variable (_boogie_T__FILE_OBJECT : _boogie_name)
variable (_boogie_T__FILE_STANDARD_INFORMATION : _boogie_name)
variable (_boogie_T__FSINFOCLASS : _boogie_name)
variable (_boogie_T__GLOBALS : _boogie_name)
variable (_boogie_T__GUID : _boogie_name)
variable (_boogie_T__INITIAL_PRIVILEGE_SET : _boogie_name)
variable (_boogie_T__INTERFACE : _boogie_name)
variable (_boogie_T__INTERFACE_TYPE : _boogie_name)
variable (_boogie_T__IO_ALLOCATION_ACTION : _boogie_name)
variable (_boogie_T__IO_COMPLETION_CONTEXT : _boogie_name)
variable (_boogie_T__IO_REMOVE_LOCK : _boogie_name)
variable (_boogie_T__IO_REMOVE_LOCK_COMMON_BLOCK : _boogie_name)
variable (_boogie_T__IO_REMOVE_LOCK_DBG_BLOCK : _boogie_name)
variable (_boogie_T__IO_REMOVE_LOCK_TRACKING_BLOCK : _boogie_name)
variable (_boogie_T__IO_RESOURCE_DESCRIPTOR : _boogie_name)
variable (_boogie_T__IO_RESOURCE_LIST : _boogie_name)
variable (_boogie_T__IO_RESOURCE_REQUIREMENTS_LIST : _boogie_name)
variable (_boogie_T__IO_SECURITY_CONTEXT : _boogie_name)
variable (_boogie_T__IO_STACK_LOCATION : _boogie_name)
variable (_boogie_T__IO_STATUS_BLOCK : _boogie_name)
variable (_boogie_T__IO_TIMER : _boogie_name)
variable (_boogie_T__IRP : _boogie_name)
variable (_boogie_T__IRQ_DEVICE_POLICY : _boogie_name)
variable (_boogie_T__IRQ_PRIORITY : _boogie_name)
variable (_boogie_T__KAPC : _boogie_name)
variable (_boogie_T__KDEVICE_QUEUE : _boogie_name)
variable (_boogie_T__KDEVICE_QUEUE_ENTRY : _boogie_name)
variable (_boogie_T__KDPC : _boogie_name)
variable (_boogie_T__KEVENT : _boogie_name)
variable (_boogie_T__KEYBOARD_ATTRIBUTES : _boogie_name)
variable (_boogie_T__KEYBOARD_ID : _boogie_name)
variable (_boogie_T__KEYBOARD_INDICATOR_PARAMETERS : _boogie_name)
variable (_boogie_T__KEYBOARD_INPUT_DATA : _boogie_name)
variable (_boogie_T__KEYBOARD_TYPEMATIC_PARAMETERS : _boogie_name)
variable (_boogie_T__KSEMAPHORE : _boogie_name)
variable (_boogie_T__KTHREAD : _boogie_name)
variable (_boogie_T__LARGE_INTEGER : _boogie_name)
variable (_boogie_T__LIST_ENTRY : _boogie_name)
variable (_boogie_T__LUID : _boogie_name)
variable (_boogie_T__LUID_AND_ATTRIBUTES : _boogie_name)
variable (_boogie_T__MDL : _boogie_name)
variable (_boogie_T__OWNER_ENTRY : _boogie_name)
variable (_boogie_T__PORT : _boogie_name)
variable (_boogie_T__POWER_SEQUENCE : _boogie_name)
variable (_boogie_T__POWER_STATE : _boogie_name)
variable (_boogie_T__POWER_STATE_TYPE : _boogie_name)
variable (_boogie_T__PRIVILEGE_SET : _boogie_name)
variable (_boogie_T__SCSI_REQUEST_BLOCK : _boogie_name)
variable (_boogie_T__SECTION_OBJECT_POINTERS : _boogie_name)
variable (_boogie_T__SECURITY_IMPERSONATION_LEVEL : _boogie_name)
variable (_boogie_T__SECURITY_QUALITY_OF_SERVICE : _boogie_name)
variable (_boogie_T__SECURITY_SUBJECT_CONTEXT : _boogie_name)
variable (_boogie_T__SYSTEM_POWER_STATE : _boogie_name)
variable (_boogie_T__SYSTEM_POWER_STATE_CONTEXT : _boogie_name)
variable (_boogie_T__UNICODE_STRING : _boogie_name)
variable (_boogie_T__VPB : _boogie_name)
variable (_boogie_T__WAIT_CONTEXT_BLOCK : _boogie_name)
variable (_boogie_T__WMILIB_CONTEXT : _boogie_name)
variable (_boogie_T___unnamed_12_0d6a30de : _boogie_name)
variable (_boogie_T___unnamed_12_17f5c211 : _boogie_name)
variable (_boogie_T___unnamed_12_1fb42e39 : _boogie_name)
variable (_boogie_T___unnamed_12_2a1563c6 : _boogie_name)
variable (_boogie_T___unnamed_12_31347272 : _boogie_name)
variable (_boogie_T___unnamed_12_429aadc0 : _boogie_name)
variable (_boogie_T___unnamed_12_4719de1a : _boogie_name)
variable (_boogie_T___unnamed_12_4be56faa : _boogie_name)
variable (_boogie_T___unnamed_12_5ce25b92 : _boogie_name)
variable (_boogie_T___unnamed_12_7a698b72 : _boogie_name)
variable (_boogie_T___unnamed_12_87c0de8d : _boogie_name)
variable (_boogie_T___unnamed_12_98bfc55a : _boogie_name)
variable (_boogie_T___unnamed_12_ab1bd9d7 : _boogie_name)
variable (_boogie_T___unnamed_12_b0429be9 : _boogie_name)
variable (_boogie_T___unnamed_12_b43e8de8 : _boogie_name)
variable (_boogie_T___unnamed_12_bfdb39ee : _boogie_name)
variable (_boogie_T___unnamed_12_cd42b3c3 : _boogie_name)
variable (_boogie_T___unnamed_12_e668effc : _boogie_name)
variable (_boogie_T___unnamed_12_e80d029e : _boogie_name)
variable (_boogie_T___unnamed_16_07c0bcc5 : _boogie_name)
variable (_boogie_T___unnamed_16_29cb9f2f : _boogie_name)
variable (_boogie_T___unnamed_16_30f11dbf : _boogie_name)
variable (_boogie_T___unnamed_16_35034f68 : _boogie_name)
variable (_boogie_T___unnamed_16_487a9498 : _boogie_name)
variable (_boogie_T___unnamed_16_5f6a8844 : _boogie_name)
variable (_boogie_T___unnamed_16_7177b9f3 : _boogie_name)
variable (_boogie_T___unnamed_16_88e91ef6 : _boogie_name)
variable (_boogie_T___unnamed_16_8c506c98 : _boogie_name)
variable (_boogie_T___unnamed_16_9ac2e5f8 : _boogie_name)
variable (_boogie_T___unnamed_16_b93842ad : _boogie_name)
variable (_boogie_T___unnamed_16_b9c62eab : _boogie_name)
variable (_boogie_T___unnamed_16_bb584060 : _boogie_name)
variable (_boogie_T___unnamed_16_dba55c7c : _boogie_name)
variable (_boogie_T___unnamed_16_e70c268b : _boogie_name)
variable (_boogie_T___unnamed_16_e734d694 : _boogie_name)
variable (_boogie_T___unnamed_16_eac6dbea : _boogie_name)
variable (_boogie_T___unnamed_16_f6cae4c2 : _boogie_name)
variable (_boogie_T___unnamed_16_fe36e4f4 : _boogie_name)
variable (_boogie_T___unnamed_1_29794256 : _boogie_name)
variable (_boogie_T___unnamed_1_2dc63b48 : _boogie_name)
variable (_boogie_T___unnamed_1_2ef8da39 : _boogie_name)
variable (_boogie_T___unnamed_1_faa7dc71 : _boogie_name)
variable (_boogie_T___unnamed_20_f4d2e6d8 : _boogie_name)
variable (_boogie_T___unnamed_24_41cbc8c0 : _boogie_name)
variable (_boogie_T___unnamed_24_5419c914 : _boogie_name)
variable (_boogie_T___unnamed_24_67a5ff10 : _boogie_name)
variable (_boogie_T___unnamed_24_72c3976e : _boogie_name)
variable (_boogie_T___unnamed_24_a26050bb : _boogie_name)
variable (_boogie_T___unnamed_24_b8f476db : _boogie_name)
variable (_boogie_T___unnamed_24_d09044b4 : _boogie_name)
variable (_boogie_T___unnamed_2_46cc4597 : _boogie_name)
variable (_boogie_T___unnamed_40_7218f704 : _boogie_name)
variable (_boogie_T___unnamed_40_c55c9377 : _boogie_name)
variable (_boogie_T___unnamed_44_5584090d : _boogie_name)
variable (_boogie_T___unnamed_48_cf99b13f : _boogie_name)
variable (_boogie_T___unnamed_4_069846fb : _boogie_name)
variable (_boogie_T___unnamed_4_224c32f4 : _boogie_name)
variable (_boogie_T___unnamed_4_2de698da : _boogie_name)
variable (_boogie_T___unnamed_4_3a2fdc5e : _boogie_name)
variable (_boogie_T___unnamed_4_3a4c1a13 : _boogie_name)
variable (_boogie_T___unnamed_4_43913aa5 : _boogie_name)
variable (_boogie_T___unnamed_4_4e8dd2ba : _boogie_name)
variable (_boogie_T___unnamed_4_52603077 : _boogie_name)
variable (_boogie_T___unnamed_4_52c594f7 : _boogie_name)
variable (_boogie_T___unnamed_4_5ca00198 : _boogie_name)
variable (_boogie_T___unnamed_4_6ac6463c : _boogie_name)
variable (_boogie_T___unnamed_4_6f9ac8e1 : _boogie_name)
variable (_boogie_T___unnamed_4_7a02167b : _boogie_name)
variable (_boogie_T___unnamed_4_7d9d0c7e : _boogie_name)
variable (_boogie_T___unnamed_4_82f7a864 : _boogie_name)
variable (_boogie_T___unnamed_4_9aec220b : _boogie_name)
variable (_boogie_T___unnamed_4_a97c65a1 : _boogie_name)
variable (_boogie_T___unnamed_4_c3479730 : _boogie_name)
variable (_boogie_T___unnamed_4_d99b6e2b : _boogie_name)
variable (_boogie_T___unnamed_4_f19b65c1 : _boogie_name)
variable (_boogie_T___unnamed_4_fa10fc16 : _boogie_name)
variable (_boogie_T___unnamed_8_01efa60d : _boogie_name)
variable (_boogie_T___unnamed_8_08d4cef8 : _boogie_name)
variable (_boogie_T___unnamed_8_0a898c0c : _boogie_name)
variable (_boogie_T___unnamed_8_1330f93a : _boogie_name)
variable (_boogie_T___unnamed_8_181d0de9 : _boogie_name)
variable (_boogie_T___unnamed_8_4812764d : _boogie_name)
variable (_boogie_T___unnamed_8_559a91e6 : _boogie_name)
variable (_boogie_T___unnamed_8_5845b309 : _boogie_name)
variable (_boogie_T___unnamed_8_58ee4a31 : _boogie_name)
variable (_boogie_T___unnamed_8_61acf4ce : _boogie_name)
variable (_boogie_T___unnamed_8_6acfee04 : _boogie_name)
variable (_boogie_T___unnamed_8_7f26a9dd : _boogie_name)
variable (_boogie_T___unnamed_8_87add0bd : _boogie_name)
variable (_boogie_T___unnamed_8_b2773e4c : _boogie_name)
variable (_boogie_T___unnamed_8_de890d4e : _boogie_name)
variable (_boogie_T___unnamed_8_ef9ba0d3 : _boogie_name)
variable (_boogie_Globals : Int)

-- Unique const axioms
axiom unique0: distinct [_boogie_UNALLOCATED, _boogie_ALLOCATED, _boogie_FREED, _boogie_BYTE, _boogie_T_Guid_WMIGUIDREGINFO, _boogie_T_InstanceCount_WMIGUIDREGINFO, _boogie_T_Flags_WMIGUIDREGINFO, _boogie_T_OperationID__ACCESS_STATE, _boogie_T_SecurityEvaluated__ACCESS_STATE, _boogie_T_GenerateAudit__ACCESS_STATE, _boogie_T_GenerateOnClose__ACCESS_STATE, _boogie_T_PrivilegesAllocated__ACCESS_STATE, _boogie_T_Flags__ACCESS_STATE, _boogie_T_RemainingDesiredAccess__ACCESS_STATE, _boogie_T_PreviouslyGrantedAccess__ACCESS_STATE, _boogie_T_OriginalDesiredAccess__ACCESS_STATE, _boogie_T_SubjectSecurityContext__ACCESS_STATE, _boogie_T_SecurityDescriptor__ACCESS_STATE, _boogie_T_AuxData__ACCESS_STATE, _boogie_T_Privileges__ACCESS_STATE, _boogie_T_AuditPrivileges__ACCESS_STATE, _boogie_T_ObjectName__ACCESS_STATE, _boogie_T_ObjectTypeName__ACCESS_STATE, _boogie_T_InterfaceType__CM_FULL_RESOURCE_DESCRIPTOR, _boogie_T_BusNumber__CM_FULL_RESOURCE_DESCRIPTOR, _boogie_T_PartialResourceList__CM_FULL_RESOURCE_DESCRIPTOR, _boogie_T_Type__CM_PARTIAL_RESOURCE_DESCRIPTOR, _boogie_T_ShareDisposition__CM_PARTIAL_RESOURCE_DESCRIPTOR, _boogie_T_Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR, _boogie_T_u__CM_PARTIAL_RESOURCE_DESCRIPTOR, _boogie_T_Version__CM_PARTIAL_RESOURCE_LIST, _boogie_T_Revision__CM_PARTIAL_RESOURCE_LIST, _boogie_T_Count__CM_PARTIAL_RESOURCE_LIST, _boogie_T_PartialDescriptors__CM_PARTIAL_RESOURCE_LIST, _boogie_T_Count__CM_RESOURCE_LIST, _boogie_T_List__CM_RESOURCE_LIST, _boogie_T_Size__DEVICE_CAPABILITIES, _boogie_T_Version__DEVICE_CAPABILITIES, _boogie_T_DeviceD1__DEVICE_CAPABILITIES, _boogie_T_DeviceD2__DEVICE_CAPABILITIES, _boogie_T_LockSupported__DEVICE_CAPABILITIES, _boogie_T_EjectSupported__DEVICE_CAPABILITIES, _boogie_T_Removable__DEVICE_CAPABILITIES, _boogie_T_DockDevice__DEVICE_CAPABILITIES, _boogie_T_UniqueID__DEVICE_CAPABILITIES, _boogie_T_SilentInstall__DEVICE_CAPABILITIES, _boogie_T_RawDeviceOK__DEVICE_CAPABILITIES, _boogie_T_SurpriseRemovalOK__DEVICE_CAPABILITIES, _boogie_T_WakeFromD0__DEVICE_CAPABILITIES, _boogie_T_WakeFromD1__DEVICE_CAPABILITIES, _boogie_T_WakeFromD2__DEVICE_CAPABILITIES, _boogie_T_WakeFromD3__DEVICE_CAPABILITIES, _boogie_T_HardwareDisabled__DEVICE_CAPABILITIES, _boogie_T_NonDynamic__DEVICE_CAPABILITIES, _boogie_T_WarmEjectSupported__DEVICE_CAPABILITIES, _boogie_T_NoDisplayInUI__DEVICE_CAPABILITIES, _boogie_T_Reserved__DEVICE_CAPABILITIES, _boogie_T_Address__DEVICE_CAPABILITIES, _boogie_T_UINumber__DEVICE_CAPABILITIES, _boogie_T_DeviceState__DEVICE_CAPABILITIES, _boogie_T_SystemWake__DEVICE_CAPABILITIES, _boogie_T_DeviceWake__DEVICE_CAPABILITIES, _boogie_T_D1Latency__DEVICE_CAPABILITIES, _boogie_T_D2Latency__DEVICE_CAPABILITIES, _boogie_T_D3Latency__DEVICE_CAPABILITIES, _boogie_T_Self__DEVICE_EXTENSION, _boogie_T_TrueClassDevice__DEVICE_EXTENSION, _boogie_T_TopPort__DEVICE_EXTENSION, _boogie_T_PDO__DEVICE_EXTENSION, _boogie_T_RemoveLock__DEVICE_EXTENSION, _boogie_T_PnP__DEVICE_EXTENSION, _boogie_T_Started__DEVICE_EXTENSION, _boogie_T_AllowDisable__DEVICE_EXTENSION, _boogie_T_WaitWakeSpinLock__DEVICE_EXTENSION, _boogie_T_TrustedSubsystemCount__DEVICE_EXTENSION, _boogie_T_InputCount__DEVICE_EXTENSION, _boogie_T_SymbolicLinkName__DEVICE_EXTENSION, _boogie_T_InputData__DEVICE_EXTENSION, _boogie_T_DataIn__DEVICE_EXTENSION, _boogie_T_DataOut__DEVICE_EXTENSION, _boogie_T_KeyboardAttributes__DEVICE_EXTENSION, _boogie_T_IndicatorParameters__DEVICE_EXTENSION, _boogie_T_SpinLock__DEVICE_EXTENSION, _boogie_T_ReadQueue__DEVICE_EXTENSION, _boogie_T_SequenceNumber__DEVICE_EXTENSION, _boogie_T_DeviceState__DEVICE_EXTENSION, _boogie_T_SystemState__DEVICE_EXTENSION, _boogie_T_UnitId__DEVICE_EXTENSION, _boogie_T_WmiLibInfo__DEVICE_EXTENSION, _boogie_T_SystemToDeviceState__DEVICE_EXTENSION, _boogie_T_MinDeviceWakeState__DEVICE_EXTENSION, _boogie_T_MinSystemWakeState__DEVICE_EXTENSION, _boogie_T_WaitWakeIrp__DEVICE_EXTENSION, _boogie_T_ExtraWaitWakeIrp__DEVICE_EXTENSION, _boogie_T_TargetNotifyHandle__DEVICE_EXTENSION, _boogie_T_Link__DEVICE_EXTENSION, _boogie_T_File__DEVICE_EXTENSION, _boogie_T_Enabled__DEVICE_EXTENSION, _boogie_T_OkayToLogOverflow__DEVICE_EXTENSION, _boogie_T_WaitWakeEnabled__DEVICE_EXTENSION, _boogie_T_SurpriseRemoved__DEVICE_EXTENSION, _boogie_T_Type__DEVICE_OBJECT, _boogie_T_Size__DEVICE_OBJECT, _boogie_T_ReferenceCount__DEVICE_OBJECT, _boogie_T_DriverObject__DEVICE_OBJECT, _boogie_T_NextDevice__DEVICE_OBJECT, _boogie_T_AttachedDevice__DEVICE_OBJECT, _boogie_T_CurrentIrp__DEVICE_OBJECT, _boogie_T_Timer__DEVICE_OBJECT, _boogie_T_Flags__DEVICE_OBJECT, _boogie_T_Characteristics__DEVICE_OBJECT, _boogie_T_Vpb__DEVICE_OBJECT, _boogie_T_DeviceExtension__DEVICE_OBJECT, _boogie_T_DeviceType__DEVICE_OBJECT, _boogie_T_StackSize__DEVICE_OBJECT, _boogie_T_Queue__DEVICE_OBJECT, _boogie_T_AlignmentRequirement__DEVICE_OBJECT, _boogie_T_DeviceQueue__DEVICE_OBJECT, _boogie_T_Dpc__DEVICE_OBJECT, _boogie_T_ActiveThreadCount__DEVICE_OBJECT, _boogie_T_SecurityDescriptor__DEVICE_OBJECT, _boogie_T_DeviceLock__DEVICE_OBJECT, _boogie_T_SectorSize__DEVICE_OBJECT, _boogie_T_Spare1__DEVICE_OBJECT, _boogie_T_DeviceObjectExtension__DEVICE_OBJECT, _boogie_T_Reserved__DEVICE_OBJECT, _boogie_T_Type__DEVOBJ_EXTENSION, _boogie_T_Size__DEVOBJ_EXTENSION, _boogie_T_DeviceObject__DEVOBJ_EXTENSION, _boogie_T___unnamed_4_a97c65a1__DISPATCHER_HEADER, _boogie_T_SignalState__DISPATCHER_HEADER, _boogie_T_WaitListHead__DISPATCHER_HEADER, _boogie_T_DriverObject__DRIVER_EXTENSION, _boogie_T_AddDevice__DRIVER_EXTENSION, _boogie_T_Count__DRIVER_EXTENSION, _boogie_T_ServiceKeyName__DRIVER_EXTENSION, _boogie_T_Type__DRIVER_OBJECT, _boogie_T_Size__DRIVER_OBJECT, _boogie_T_DeviceObject__DRIVER_OBJECT, _boogie_T_Flags__DRIVER_OBJECT, _boogie_T_DriverStart__DRIVER_OBJECT, _boogie_T_DriverSize__DRIVER_OBJECT, _boogie_T_DriverSection__DRIVER_OBJECT, _boogie_T_DriverExtension__DRIVER_OBJECT, _boogie_T_DriverName__DRIVER_OBJECT, _boogie_T_HardwareDatabase__DRIVER_OBJECT, _boogie_T_FastIoDispatch__DRIVER_OBJECT, _boogie_T_DriverInit__DRIVER_OBJECT, _boogie_T_DriverStartIo__DRIVER_OBJECT, _boogie_T_DriverUnload__DRIVER_OBJECT, _boogie_T_MajorFunction__DRIVER_OBJECT, _boogie_T_SystemResourcesList__ERESOURCE, _boogie_T_OwnerTable__ERESOURCE, _boogie_T_ActiveCount__ERESOURCE, _boogie_T_Flag__ERESOURCE, _boogie_T_SharedWaiters__ERESOURCE, _boogie_T_ExclusiveWaiters__ERESOURCE, _boogie_T_OwnerEntry__ERESOURCE, _boogie_T_ActiveEntries__ERESOURCE, _boogie_T_ContentionCount__ERESOURCE, _boogie_T_NumberOfSharedWaiters__ERESOURCE, _boogie_T_NumberOfExclusiveWaiters__ERESOURCE, _boogie_T___unnamed_4_52c594f7__ERESOURCE, _boogie_T_SpinLock__ERESOURCE, _boogie_T_SizeOfFastIoDispatch__FAST_IO_DISPATCH, _boogie_T_FastIoCheckIfPossible__FAST_IO_DISPATCH, _boogie_T_FastIoRead__FAST_IO_DISPATCH, _boogie_T_FastIoWrite__FAST_IO_DISPATCH, _boogie_T_FastIoQueryBasicInfo__FAST_IO_DISPATCH, _boogie_T_FastIoQueryStandardInfo__FAST_IO_DISPATCH, _boogie_T_FastIoLock__FAST_IO_DISPATCH, _boogie_T_FastIoUnlockSingle__FAST_IO_DISPATCH, _boogie_T_FastIoUnlockAll__FAST_IO_DISPATCH, _boogie_T_FastIoUnlockAllByKey__FAST_IO_DISPATCH, _boogie_T_FastIoDeviceControl__FAST_IO_DISPATCH, _boogie_T_AcquireFileForNtCreateSection__FAST_IO_DISPATCH, _boogie_T_ReleaseFileForNtCreateSection__FAST_IO_DISPATCH, _boogie_T_FastIoDetachDevice__FAST_IO_DISPATCH, _boogie_T_FastIoQueryNetworkOpenInfo__FAST_IO_DISPATCH, _boogie_T_AcquireForModWrite__FAST_IO_DISPATCH, _boogie_T_MdlRead__FAST_IO_DISPATCH, _boogie_T_MdlReadComplete__FAST_IO_DISPATCH, _boogie_T_PrepareMdlWrite__FAST_IO_DISPATCH, _boogie_T_MdlWriteComplete__FAST_IO_DISPATCH, _boogie_T_FastIoReadCompressed__FAST_IO_DISPATCH, _boogie_T_FastIoWriteCompressed__FAST_IO_DISPATCH, _boogie_T_MdlReadCompleteCompressed__FAST_IO_DISPATCH, _boogie_T_MdlWriteCompleteCompressed__FAST_IO_DISPATCH, _boogie_T_FastIoQueryOpen__FAST_IO_DISPATCH, _boogie_T_ReleaseForModWrite__FAST_IO_DISPATCH, _boogie_T_AcquireForCcFlush__FAST_IO_DISPATCH, _boogie_T_ReleaseForCcFlush__FAST_IO_DISPATCH, _boogie_T_Count__FAST_MUTEX, _boogie_T_Owner__FAST_MUTEX, _boogie_T_Contention__FAST_MUTEX, _boogie_T_Gate__FAST_MUTEX, _boogie_T_OldIrql__FAST_MUTEX, _boogie_T_CreationTime__FILE_BASIC_INFORMATION, _boogie_T_LastAccessTime__FILE_BASIC_INFORMATION, _boogie_T_LastWriteTime__FILE_BASIC_INFORMATION, _boogie_T_ChangeTime__FILE_BASIC_INFORMATION, _boogie_T_FileAttributes__FILE_BASIC_INFORMATION, _boogie_T_CreationTime__FILE_NETWORK_OPEN_INFORMATION, _boogie_T_LastAccessTime__FILE_NETWORK_OPEN_INFORMATION, _boogie_T_LastWriteTime__FILE_NETWORK_OPEN_INFORMATION, _boogie_T_ChangeTime__FILE_NETWORK_OPEN_INFORMATION, _boogie_T_AllocationSize__FILE_NETWORK_OPEN_INFORMATION, _boogie_T_EndOfFile__FILE_NETWORK_OPEN_INFORMATION, _boogie_T_FileAttributes__FILE_NETWORK_OPEN_INFORMATION, _boogie_T_Type__FILE_OBJECT, _boogie_T_Size__FILE_OBJECT, _boogie_T_DeviceObject__FILE_OBJECT, _boogie_T_Vpb__FILE_OBJECT, _boogie_T_FsContext__FILE_OBJECT, _boogie_T_FsContext2__FILE_OBJECT, _boogie_T_SectionObjectPointer__FILE_OBJECT, _boogie_T_PrivateCacheMap__FILE_OBJECT, _boogie_T_FinalStatus__FILE_OBJECT, _boogie_T_RelatedFileObject__FILE_OBJECT, _boogie_T_LockOperation__FILE_OBJECT, _boogie_T_DeletePending__FILE_OBJECT, _boogie_T_ReadAccess__FILE_OBJECT, _boogie_T_WriteAccess__FILE_OBJECT, _boogie_T_DeleteAccess__FILE_OBJECT, _boogie_T_SharedRead__FILE_OBJECT, _boogie_T_SharedWrite__FILE_OBJECT, _boogie_T_SharedDelete__FILE_OBJECT, _boogie_T_Flags__FILE_OBJECT, _boogie_T_FileName__FILE_OBJECT, _boogie_T_CurrentByteOffset__FILE_OBJECT, _boogie_T_Waiters__FILE_OBJECT, _boogie_T_Busy__FILE_OBJECT, _boogie_T_LastLock__FILE_OBJECT, _boogie_T_Lock__FILE_OBJECT, _boogie_T_Event__FILE_OBJECT, _boogie_T_CompletionContext__FILE_OBJECT, _boogie_T_IrpListLock__FILE_OBJECT, _boogie_T_IrpList__FILE_OBJECT, _boogie_T_FileObjectExtension__FILE_OBJECT, _boogie_T_AllocationSize__FILE_STANDARD_INFORMATION, _boogie_T_EndOfFile__FILE_STANDARD_INFORMATION, _boogie_T_NumberOfLinks__FILE_STANDARD_INFORMATION, _boogie_T_DeletePending__FILE_STANDARD_INFORMATION, _boogie_T_Directory__FILE_STANDARD_INFORMATION, _boogie_T_Debug__GLOBALS, _boogie_T_GrandMaster__GLOBALS, _boogie_T_AssocClassList__GLOBALS, _boogie_T_NumAssocClass__GLOBALS, _boogie_T_Opens__GLOBALS, _boogie_T_NumberLegacyPorts__GLOBALS, _boogie_T_Mutex__GLOBALS, _boogie_T_ConnectOneClassToOnePort__GLOBALS, _boogie_T_SendOutputToAllPorts__GLOBALS, _boogie_T_PortsServiced__GLOBALS, _boogie_T_InitExtension__GLOBALS, _boogie_T_RegistryPath__GLOBALS, _boogie_T_BaseClassName__GLOBALS, _boogie_T_BaseClassBuffer__GLOBALS, _boogie_T_LegacyDeviceList__GLOBALS, _boogie_T_Data1__GUID, _boogie_T_Data2__GUID, _boogie_T_Data3__GUID, _boogie_T_Data4__GUID, _boogie_T_PrivilegeCount__INITIAL_PRIVILEGE_SET, _boogie_T_Control__INITIAL_PRIVILEGE_SET, _boogie_T_Privilege__INITIAL_PRIVILEGE_SET, _boogie_T_Size__INTERFACE, _boogie_T_Version__INTERFACE, _boogie_T_Context__INTERFACE, _boogie_T_InterfaceReference__INTERFACE, _boogie_T_InterfaceDereference__INTERFACE, _boogie_T_Port__IO_COMPLETION_CONTEXT, _boogie_T_Key__IO_COMPLETION_CONTEXT, _boogie_T_Common__IO_REMOVE_LOCK, _boogie_T_Dbg__IO_REMOVE_LOCK, _boogie_T_Removed__IO_REMOVE_LOCK_COMMON_BLOCK, _boogie_T_Reserved__IO_REMOVE_LOCK_COMMON_BLOCK, _boogie_T_IoCount__IO_REMOVE_LOCK_COMMON_BLOCK, _boogie_T_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK, _boogie_T_Signature__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_LockList__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_Spin__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_Reserved1__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_Reserved2__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_Blocks__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T_Option__IO_RESOURCE_DESCRIPTOR, _boogie_T_Type__IO_RESOURCE_DESCRIPTOR, _boogie_T_ShareDisposition__IO_RESOURCE_DESCRIPTOR, _boogie_T_Spare1__IO_RESOURCE_DESCRIPTOR, _boogie_T_Flags__IO_RESOURCE_DESCRIPTOR, _boogie_T_Spare2__IO_RESOURCE_DESCRIPTOR, _boogie_T_u__IO_RESOURCE_DESCRIPTOR, _boogie_T_Version__IO_RESOURCE_LIST, _boogie_T_Revision__IO_RESOURCE_LIST, _boogie_T_Count__IO_RESOURCE_LIST, _boogie_T_Descriptors__IO_RESOURCE_LIST, _boogie_T_ListSize__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_InterfaceType__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_BusNumber__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_SlotNumber__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_Reserved__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_AlternativeLists__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_List__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_SecurityQos__IO_SECURITY_CONTEXT, _boogie_T_AccessState__IO_SECURITY_CONTEXT, _boogie_T_DesiredAccess__IO_SECURITY_CONTEXT, _boogie_T_FullCreateOptions__IO_SECURITY_CONTEXT, _boogie_T_MajorFunction__IO_STACK_LOCATION, _boogie_T_MinorFunction__IO_STACK_LOCATION, _boogie_T_Flags__IO_STACK_LOCATION, _boogie_T_Control__IO_STACK_LOCATION, _boogie_T_Parameters__IO_STACK_LOCATION, _boogie_T_DeviceObject__IO_STACK_LOCATION, _boogie_T_FileObject__IO_STACK_LOCATION, _boogie_T_CompletionRoutine__IO_STACK_LOCATION, _boogie_T_Context__IO_STACK_LOCATION, _boogie_T___unnamed_4_d99b6e2b__IO_STATUS_BLOCK, _boogie_T_Information__IO_STATUS_BLOCK, _boogie_T_Type__IRP, _boogie_T_Size__IRP, _boogie_T_MdlAddress__IRP, _boogie_T_Flags__IRP, _boogie_T_AssociatedIrp__IRP, _boogie_T_ThreadListEntry__IRP, _boogie_T_IoStatus__IRP, _boogie_T_RequestorMode__IRP, _boogie_T_PendingReturned__IRP, _boogie_T_StackCount__IRP, _boogie_T_CurrentLocation__IRP, _boogie_T_Cancel__IRP, _boogie_T_CancelIrql__IRP, _boogie_T_ApcEnvironment__IRP, _boogie_T_AllocationFlags__IRP, _boogie_T_UserIosb__IRP, _boogie_T_UserEvent__IRP, _boogie_T_Overlay__IRP, _boogie_T_CancelRoutine__IRP, _boogie_T_UserBuffer__IRP, _boogie_T_Tail__IRP, _boogie_T_Type__KAPC, _boogie_T_SpareByte0__KAPC, _boogie_T_Size__KAPC, _boogie_T_SpareByte1__KAPC, _boogie_T_SpareLong0__KAPC, _boogie_T_Thread__KAPC, _boogie_T_ApcListEntry__KAPC, _boogie_T_KernelRoutine__KAPC, _boogie_T_RundownRoutine__KAPC, _boogie_T_NormalRoutine__KAPC, _boogie_T_NormalContext__KAPC, _boogie_T_SystemArgument1__KAPC, _boogie_T_SystemArgument2__KAPC, _boogie_T_ApcStateIndex__KAPC, _boogie_T_ApcMode__KAPC, _boogie_T_Inserted__KAPC, _boogie_T_Type__KDEVICE_QUEUE, _boogie_T_Size__KDEVICE_QUEUE, _boogie_T_DeviceListHead__KDEVICE_QUEUE, _boogie_T_Lock__KDEVICE_QUEUE, _boogie_T_Busy__KDEVICE_QUEUE, _boogie_T_DeviceListEntry__KDEVICE_QUEUE_ENTRY, _boogie_T_SortKey__KDEVICE_QUEUE_ENTRY, _boogie_T_Inserted__KDEVICE_QUEUE_ENTRY, _boogie_T_Type__KDPC, _boogie_T_Importance__KDPC, _boogie_T_Number__KDPC, _boogie_T_DpcListEntry__KDPC, _boogie_T_DeferredRoutine__KDPC, _boogie_T_DeferredContext__KDPC, _boogie_T_SystemArgument1__KDPC, _boogie_T_SystemArgument2__KDPC, _boogie_T_DpcData__KDPC, _boogie_T_Header__KEVENT, _boogie_T_KeyboardIdentifier__KEYBOARD_ATTRIBUTES, _boogie_T_KeyboardMode__KEYBOARD_ATTRIBUTES, _boogie_T_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES, _boogie_T_NumberOfIndicators__KEYBOARD_ATTRIBUTES, _boogie_T_NumberOfKeysTotal__KEYBOARD_ATTRIBUTES, _boogie_T_InputDataQueueLength__KEYBOARD_ATTRIBUTES, _boogie_T_KeyRepeatMinimum__KEYBOARD_ATTRIBUTES, _boogie_T_KeyRepeatMaximum__KEYBOARD_ATTRIBUTES, _boogie_T_Type__KEYBOARD_ID, _boogie_T_Subtype__KEYBOARD_ID, _boogie_T_UnitId__KEYBOARD_INDICATOR_PARAMETERS, _boogie_T_LedFlags__KEYBOARD_INDICATOR_PARAMETERS, _boogie_T_UnitId__KEYBOARD_INPUT_DATA, _boogie_T_MakeCode__KEYBOARD_INPUT_DATA, _boogie_T_Flags__KEYBOARD_INPUT_DATA, _boogie_T_Reserved__KEYBOARD_INPUT_DATA, _boogie_T_ExtraInformation__KEYBOARD_INPUT_DATA, _boogie_T_UnitId__KEYBOARD_TYPEMATIC_PARAMETERS, _boogie_T_Rate__KEYBOARD_TYPEMATIC_PARAMETERS, _boogie_T_Delay__KEYBOARD_TYPEMATIC_PARAMETERS, _boogie_T_Header__KSEMAPHORE, _boogie_T_Limit__KSEMAPHORE, _boogie_T___unnamed_8_58ee4a31__LARGE_INTEGER, _boogie_T_u__LARGE_INTEGER, _boogie_T_QuadPart__LARGE_INTEGER, _boogie_T_Flink__LIST_ENTRY, _boogie_T_Blink__LIST_ENTRY, _boogie_T_LowPart__LUID, _boogie_T_HighPart__LUID, _boogie_T_Luid__LUID_AND_ATTRIBUTES, _boogie_T_Attributes__LUID_AND_ATTRIBUTES, _boogie_T_Next__MDL, _boogie_T_Size__MDL, _boogie_T_MdlFlags__MDL, _boogie_T_Process__MDL, _boogie_T_MappedSystemVa__MDL, _boogie_T_StartVa__MDL, _boogie_T_ByteCount__MDL, _boogie_T_ByteOffset__MDL, _boogie_T_OwnerThread__OWNER_ENTRY, _boogie_T___unnamed_4_6f9ac8e1__OWNER_ENTRY, _boogie_T_File__PORT, _boogie_T_Port__PORT, _boogie_T_Enabled__PORT, _boogie_T_Reserved__PORT, _boogie_T_Free__PORT, _boogie_T_SequenceD1__POWER_SEQUENCE, _boogie_T_SequenceD2__POWER_SEQUENCE, _boogie_T_SequenceD3__POWER_SEQUENCE, _boogie_T_SystemState__POWER_STATE, _boogie_T_DeviceState__POWER_STATE, _boogie_T_PrivilegeCount__PRIVILEGE_SET, _boogie_T_Control__PRIVILEGE_SET, _boogie_T_Privilege__PRIVILEGE_SET, _boogie_T_DataSectionObject__SECTION_OBJECT_POINTERS, _boogie_T_SharedCacheMap__SECTION_OBJECT_POINTERS, _boogie_T_ImageSectionObject__SECTION_OBJECT_POINTERS, _boogie_T_Length__SECURITY_QUALITY_OF_SERVICE, _boogie_T_ImpersonationLevel__SECURITY_QUALITY_OF_SERVICE, _boogie_T_ContextTrackingMode__SECURITY_QUALITY_OF_SERVICE, _boogie_T_EffectiveOnly__SECURITY_QUALITY_OF_SERVICE, _boogie_T_ClientToken__SECURITY_SUBJECT_CONTEXT, _boogie_T_ImpersonationLevel__SECURITY_SUBJECT_CONTEXT, _boogie_T_PrimaryToken__SECURITY_SUBJECT_CONTEXT, _boogie_T_ProcessAuditId__SECURITY_SUBJECT_CONTEXT, _boogie_T___unnamed_4_3a2fdc5e__SYSTEM_POWER_STATE_CONTEXT, _boogie_T_Length__UNICODE_STRING, _boogie_T_MaximumLength__UNICODE_STRING, _boogie_T_Buffer__UNICODE_STRING, _boogie_T_Type__VPB, _boogie_T_Size__VPB, _boogie_T_Flags__VPB, _boogie_T_VolumeLabelLength__VPB, _boogie_T_DeviceObject__VPB, _boogie_T_RealDevice__VPB, _boogie_T_SerialNumber__VPB, _boogie_T_ReferenceCount__VPB, _boogie_T_VolumeLabel__VPB, _boogie_T_WaitQueueEntry__WAIT_CONTEXT_BLOCK, _boogie_T_DeviceRoutine__WAIT_CONTEXT_BLOCK, _boogie_T_DeviceContext__WAIT_CONTEXT_BLOCK, _boogie_T_NumberOfMapRegisters__WAIT_CONTEXT_BLOCK, _boogie_T_DeviceObject__WAIT_CONTEXT_BLOCK, _boogie_T_CurrentIrp__WAIT_CONTEXT_BLOCK, _boogie_T_BufferChainingDpc__WAIT_CONTEXT_BLOCK, _boogie_T_GuidCount__WMILIB_CONTEXT, _boogie_T_GuidList__WMILIB_CONTEXT, _boogie_T_QueryWmiRegInfo__WMILIB_CONTEXT, _boogie_T_QueryWmiDataBlock__WMILIB_CONTEXT, _boogie_T_SetWmiDataBlock__WMILIB_CONTEXT, _boogie_T_SetWmiDataItem__WMILIB_CONTEXT, _boogie_T_ExecuteWmiMethod__WMILIB_CONTEXT, _boogie_T_WmiFunctionControl__WMILIB_CONTEXT, _boogie_T_Reserved___unnamed_12_0d6a30de, _boogie_T_MessageCount___unnamed_12_0d6a30de, _boogie_T_Vector___unnamed_12_0d6a30de, _boogie_T_Affinity___unnamed_12_0d6a30de, _boogie_T_Start___unnamed_12_17f5c211, _boogie_T_Length48___unnamed_12_17f5c211, _boogie_T_Start___unnamed_12_1fb42e39, _boogie_T_Length___unnamed_12_1fb42e39, _boogie_T_Reserved___unnamed_12_1fb42e39, _boogie_T_Start___unnamed_12_2a1563c6, _boogie_T_Length___unnamed_12_2a1563c6, _boogie_T_DataSize___unnamed_12_31347272, _boogie_T_Reserved1___unnamed_12_31347272, _boogie_T_Reserved2___unnamed_12_31347272, _boogie_T_Raw___unnamed_12_429aadc0, _boogie_T_Translated___unnamed_12_429aadc0, _boogie_T_Start___unnamed_12_4719de1a, _boogie_T_Length___unnamed_12_4719de1a, _boogie_T_Data___unnamed_12_4be56faa, _boogie_T_Data___unnamed_12_5ce25b92, _boogie_T_Generic___unnamed_12_7a698b72, _boogie_T_Port___unnamed_12_7a698b72, _boogie_T_Interrupt___unnamed_12_7a698b72, _boogie_T_MessageInterrupt___unnamed_12_7a698b72, _boogie_T_Memory___unnamed_12_7a698b72, _boogie_T_Dma___unnamed_12_7a698b72, _boogie_T_DevicePrivate___unnamed_12_7a698b72, _boogie_T_BusNumber___unnamed_12_7a698b72, _boogie_T_DeviceSpecificData___unnamed_12_7a698b72, _boogie_T_Memory40___unnamed_12_7a698b72, _boogie_T_Memory48___unnamed_12_7a698b72, _boogie_T_Memory64___unnamed_12_7a698b72, _boogie_T_Start___unnamed_12_87c0de8d, _boogie_T_Length64___unnamed_12_87c0de8d, _boogie_T_Start___unnamed_12_98bfc55a, _boogie_T_Length40___unnamed_12_98bfc55a, _boogie_T_Priority___unnamed_12_ab1bd9d7, _boogie_T_Reserved1___unnamed_12_ab1bd9d7, _boogie_T_Reserved2___unnamed_12_ab1bd9d7, _boogie_T_Level___unnamed_12_b0429be9, _boogie_T_Vector___unnamed_12_b0429be9, _boogie_T_Affinity___unnamed_12_b0429be9, _boogie_T_ListEntry___unnamed_12_b43e8de8, _boogie_T___unnamed_4_f19b65c1___unnamed_12_b43e8de8, _boogie_T_Level___unnamed_12_bfdb39ee, _boogie_T_Vector___unnamed_12_bfdb39ee, _boogie_T_Affinity___unnamed_12_bfdb39ee, _boogie_T_Start___unnamed_12_cd42b3c3, _boogie_T_Length___unnamed_12_cd42b3c3, _boogie_T___unnamed_12_429aadc0___unnamed_12_e668effc, _boogie_T_Channel___unnamed_12_e80d029e, _boogie_T_Port___unnamed_12_e80d029e, _boogie_T_Reserved1___unnamed_12_e80d029e, _boogie_T_Length___unnamed_16_07c0bcc5, _boogie_T_MinBusNumber___unnamed_16_07c0bcc5, _boogie_T_MaxBusNumber___unnamed_16_07c0bcc5, _boogie_T_Reserved___unnamed_16_07c0bcc5, _boogie_T_InterfaceType___unnamed_16_29cb9f2f, _boogie_T_Size___unnamed_16_29cb9f2f, _boogie_T_Version___unnamed_16_29cb9f2f, _boogie_T_Interface___unnamed_16_29cb9f2f, _boogie_T_InterfaceSpecificData___unnamed_16_29cb9f2f, _boogie_T_SecurityContext___unnamed_16_30f11dbf, _boogie_T_Options___unnamed_16_30f11dbf, _boogie_T_FileAttributes___unnamed_16_30f11dbf, _boogie_T_ShareAccess___unnamed_16_30f11dbf, _boogie_T_EaLength___unnamed_16_30f11dbf, _boogie_T_DriverContext___unnamed_16_35034f68, _boogie_T_Length___unnamed_16_487a9498, _boogie_T_FileName___unnamed_16_487a9498, _boogie_T_FileInformationClass___unnamed_16_487a9498, _boogie_T_FileIndex___unnamed_16_487a9498, _boogie_T_OutputBufferLength___unnamed_16_5f6a8844, _boogie_T_InputBufferLength___unnamed_16_5f6a8844, _boogie_T_FsControlCode___unnamed_16_5f6a8844, _boogie_T_Type3InputBuffer___unnamed_16_5f6a8844, _boogie_T_Length___unnamed_16_7177b9f3, _boogie_T_FileInformationClass___unnamed_16_7177b9f3, _boogie_T_FileObject___unnamed_16_7177b9f3, _boogie_T___unnamed_4_43913aa5___unnamed_16_7177b9f3, _boogie_T_Length___unnamed_16_88e91ef6, _boogie_T_Key___unnamed_16_88e91ef6, _boogie_T_ByteOffset___unnamed_16_88e91ef6, _boogie_T_Length___unnamed_16_8c506c98, _boogie_T_Key___unnamed_16_8c506c98, _boogie_T_ByteOffset___unnamed_16_8c506c98, _boogie_T_WhichSpace___unnamed_16_9ac2e5f8, _boogie_T_Buffer___unnamed_16_9ac2e5f8, _boogie_T_Offset___unnamed_16_9ac2e5f8, _boogie_T_Length___unnamed_16_9ac2e5f8, _boogie_T_Create___unnamed_16_b93842ad, _boogie_T_Read___unnamed_16_b93842ad, _boogie_T_Write___unnamed_16_b93842ad, _boogie_T_QueryDirectory___unnamed_16_b93842ad, _boogie_T_NotifyDirectory___unnamed_16_b93842ad, _boogie_T_QueryFile___unnamed_16_b93842ad, _boogie_T_SetFile___unnamed_16_b93842ad, _boogie_T_QueryEa___unnamed_16_b93842ad, _boogie_T_SetEa___unnamed_16_b93842ad, _boogie_T_QueryVolume___unnamed_16_b93842ad, _boogie_T_SetVolume___unnamed_16_b93842ad, _boogie_T_FileSystemControl___unnamed_16_b93842ad, _boogie_T_LockControl___unnamed_16_b93842ad, _boogie_T_DeviceIoControl___unnamed_16_b93842ad, _boogie_T_QuerySecurity___unnamed_16_b93842ad, _boogie_T_SetSecurity___unnamed_16_b93842ad, _boogie_T_MountVolume___unnamed_16_b93842ad, _boogie_T_VerifyVolume___unnamed_16_b93842ad, _boogie_T_Scsi___unnamed_16_b93842ad, _boogie_T_QueryQuota___unnamed_16_b93842ad, _boogie_T_SetQuota___unnamed_16_b93842ad, _boogie_T_QueryDeviceRelations___unnamed_16_b93842ad, _boogie_T_QueryInterface___unnamed_16_b93842ad, _boogie_T_DeviceCapabilities___unnamed_16_b93842ad, _boogie_T_FilterResourceRequirements___unnamed_16_b93842ad, _boogie_T_ReadWriteConfig___unnamed_16_b93842ad, _boogie_T_SetLock___unnamed_16_b93842ad, _boogie_T_QueryId___unnamed_16_b93842ad, _boogie_T_QueryDeviceText___unnamed_16_b93842ad, _boogie_T_UsageNotification___unnamed_16_b93842ad, _boogie_T_WaitWake___unnamed_16_b93842ad, _boogie_T_PowerSequence___unnamed_16_b93842ad, _boogie_T_Power___unnamed_16_b93842ad, _boogie_T_StartDevice___unnamed_16_b93842ad, _boogie_T_WMI___unnamed_16_b93842ad, _boogie_T_Others___unnamed_16_b93842ad, _boogie_T_Length___unnamed_16_b9c62eab, _boogie_T_Key___unnamed_16_b9c62eab, _boogie_T_ByteOffset___unnamed_16_b9c62eab, _boogie_T___unnamed_4_7d9d0c7e___unnamed_16_bb584060, _boogie_T_Type___unnamed_16_bb584060, _boogie_T_State___unnamed_16_bb584060, _boogie_T_ShutdownType___unnamed_16_bb584060, _boogie_T_OutputBufferLength___unnamed_16_dba55c7c, _boogie_T_InputBufferLength___unnamed_16_dba55c7c, _boogie_T_IoControlCode___unnamed_16_dba55c7c, _boogie_T_Type3InputBuffer___unnamed_16_dba55c7c, _boogie_T_DeviceQueueEntry___unnamed_16_e70c268b, _boogie_T___unnamed_16_35034f68___unnamed_16_e70c268b, _boogie_T_Argument1___unnamed_16_e734d694, _boogie_T_Argument2___unnamed_16_e734d694, _boogie_T_Argument3___unnamed_16_e734d694, _boogie_T_Argument4___unnamed_16_e734d694, _boogie_T_ProviderId___unnamed_16_eac6dbea, _boogie_T_DataPath___unnamed_16_eac6dbea, _boogie_T_BufferSize___unnamed_16_eac6dbea, _boogie_T_Buffer___unnamed_16_eac6dbea, _boogie_T_Length___unnamed_16_f6cae4c2, _boogie_T_EaList___unnamed_16_f6cae4c2, _boogie_T_EaListLength___unnamed_16_f6cae4c2, _boogie_T_EaIndex___unnamed_16_f6cae4c2, _boogie_T_Length___unnamed_16_fe36e4f4, _boogie_T_StartSid___unnamed_16_fe36e4f4, _boogie_T_SidList___unnamed_16_fe36e4f4, _boogie_T_SidListLength___unnamed_16_fe36e4f4, _boogie_T_Abandoned___unnamed_1_29794256, _boogie_T_Absolute___unnamed_1_29794256, _boogie_T_NpxIrql___unnamed_1_29794256, _boogie_T_Signalling___unnamed_1_29794256, _boogie_T_Inserted___unnamed_1_2dc63b48, _boogie_T_DebugActive___unnamed_1_2dc63b48, _boogie_T_DpcActive___unnamed_1_2dc63b48, _boogie_T_Size___unnamed_1_2ef8da39, _boogie_T_Hand___unnamed_1_2ef8da39, _boogie_T_Lock___unnamed_1_faa7dc71, _boogie_T_MinimumVector___unnamed_20_f4d2e6d8, _boogie_T_MaximumVector___unnamed_20_f4d2e6d8, _boogie_T_AffinityPolicy___unnamed_20_f4d2e6d8, _boogie_T_PriorityPolicy___unnamed_20_f4d2e6d8, _boogie_T_TargetedProcessors___unnamed_20_f4d2e6d8, _boogie_T_Length___unnamed_24_41cbc8c0, _boogie_T_Alignment___unnamed_24_41cbc8c0, _boogie_T_MinimumAddress___unnamed_24_41cbc8c0, _boogie_T_MaximumAddress___unnamed_24_41cbc8c0, _boogie_T_Length48___unnamed_24_5419c914, _boogie_T_Alignment48___unnamed_24_5419c914, _boogie_T_MinimumAddress___unnamed_24_5419c914, _boogie_T_MaximumAddress___unnamed_24_5419c914, _boogie_T_Length___unnamed_24_67a5ff10, _boogie_T_Alignment___unnamed_24_67a5ff10, _boogie_T_MinimumAddress___unnamed_24_67a5ff10, _boogie_T_MaximumAddress___unnamed_24_67a5ff10, _boogie_T_Port___unnamed_24_72c3976e, _boogie_T_Memory___unnamed_24_72c3976e, _boogie_T_Interrupt___unnamed_24_72c3976e, _boogie_T_Dma___unnamed_24_72c3976e, _boogie_T_Generic___unnamed_24_72c3976e, _boogie_T_DevicePrivate___unnamed_24_72c3976e, _boogie_T_BusNumber___unnamed_24_72c3976e, _boogie_T_ConfigData___unnamed_24_72c3976e, _boogie_T_Memory40___unnamed_24_72c3976e, _boogie_T_Memory48___unnamed_24_72c3976e, _boogie_T_Memory64___unnamed_24_72c3976e, _boogie_T_Length64___unnamed_24_a26050bb, _boogie_T_Alignment64___unnamed_24_a26050bb, _boogie_T_MinimumAddress___unnamed_24_a26050bb, _boogie_T_MaximumAddress___unnamed_24_a26050bb, _boogie_T_Length___unnamed_24_b8f476db, _boogie_T_Alignment___unnamed_24_b8f476db, _boogie_T_MinimumAddress___unnamed_24_b8f476db, _boogie_T_MaximumAddress___unnamed_24_b8f476db, _boogie_T_Length40___unnamed_24_d09044b4, _boogie_T_Alignment40___unnamed_24_d09044b4, _boogie_T_MinimumAddress___unnamed_24_d09044b4, _boogie_T_MaximumAddress___unnamed_24_d09044b4, _boogie_T_ReplaceIfExists___unnamed_2_46cc4597, _boogie_T_AdvanceOnly___unnamed_2_46cc4597, _boogie_T___unnamed_16_e70c268b___unnamed_40_7218f704, _boogie_T_Thread___unnamed_40_7218f704, _boogie_T_AuxiliaryBuffer___unnamed_40_7218f704, _boogie_T___unnamed_12_b43e8de8___unnamed_40_7218f704, _boogie_T_OriginalFileObject___unnamed_40_7218f704, _boogie_T_ListEntry___unnamed_40_c55c9377, _boogie_T_Wcb___unnamed_40_c55c9377, _boogie_T_InitialPrivilegeSet___unnamed_44_5584090d, _boogie_T_PrivilegeSet___unnamed_44_5584090d, _boogie_T_Overlay___unnamed_48_cf99b13f, _boogie_T_Apc___unnamed_48_cf99b13f, _boogie_T_CompletionKey___unnamed_48_cf99b13f, _boogie_T_PowerState___unnamed_4_069846fb, _boogie_T_IdType___unnamed_4_224c32f4, _boogie_T_Capabilities___unnamed_4_2de698da, _boogie_T___unnamed_4_c3479730___unnamed_4_3a2fdc5e, _boogie_T_ContextAsUlong___unnamed_4_3a2fdc5e, _boogie_T_Length___unnamed_4_3a4c1a13, _boogie_T___unnamed_2_46cc4597___unnamed_4_43913aa5, _boogie_T_ClusterCount___unnamed_4_43913aa5, _boogie_T_DeleteHandle___unnamed_4_43913aa5, _boogie_T_UserApcRoutine___unnamed_4_4e8dd2ba, _boogie_T_IssuingProcess___unnamed_4_4e8dd2ba, _boogie_T_Srb___unnamed_4_52603077, _boogie_T_Address___unnamed_4_52c594f7, _boogie_T_CreatorBackTraceIndex___unnamed_4_52c594f7, _boogie_T_Type___unnamed_4_5ca00198, _boogie_T___unnamed_1_29794256___unnamed_4_5ca00198, _boogie_T___unnamed_1_2ef8da39___unnamed_4_5ca00198, _boogie_T___unnamed_1_2dc63b48___unnamed_4_5ca00198, _boogie_T_MasterIrp___unnamed_4_6ac6463c, _boogie_T_IrpCount___unnamed_4_6ac6463c, _boogie_T_SystemBuffer___unnamed_4_6ac6463c, _boogie_T_OwnerCount___unnamed_4_6f9ac8e1, _boogie_T_TableSize___unnamed_4_6f9ac8e1, _boogie_T_PowerSequence___unnamed_4_7a02167b, _boogie_T_SystemContext___unnamed_4_7d9d0c7e, _boogie_T_SystemPowerStateContext___unnamed_4_7d9d0c7e, _boogie_T_IoResourceRequirementList___unnamed_4_82f7a864, _boogie_T_Length___unnamed_4_9aec220b, _boogie_T___unnamed_4_5ca00198___unnamed_4_a97c65a1, _boogie_T_Lock___unnamed_4_a97c65a1, _boogie_T_Reserved1___unnamed_4_c3479730, _boogie_T_TargetSystemState___unnamed_4_c3479730, _boogie_T_EffectiveSystemState___unnamed_4_c3479730, _boogie_T_CurrentSystemState___unnamed_4_c3479730, _boogie_T_IgnoreHibernationPath___unnamed_4_c3479730, _boogie_T_PseudoTransition___unnamed_4_c3479730, _boogie_T_Reserved2___unnamed_4_c3479730, _boogie_T_Status___unnamed_4_d99b6e2b, _boogie_T_Pointer___unnamed_4_d99b6e2b, _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1, _boogie_T_PacketType___unnamed_4_f19b65c1, _boogie_T_Type___unnamed_4_fa10fc16, _boogie_T_SecurityInformation___unnamed_8_01efa60d, _boogie_T_Length___unnamed_8_01efa60d, _boogie_T_MinimumChannel___unnamed_8_08d4cef8, _boogie_T_MaximumChannel___unnamed_8_08d4cef8, _boogie_T___unnamed_4_4e8dd2ba___unnamed_8_0a898c0c, _boogie_T_UserApcContext___unnamed_8_0a898c0c, _boogie_T_SecurityInformation___unnamed_8_1330f93a, _boogie_T_SecurityDescriptor___unnamed_8_1330f93a, _boogie_T_AsynchronousParameters___unnamed_8_181d0de9, _boogie_T_AllocationSize___unnamed_8_181d0de9, _boogie_T_Vpb___unnamed_8_4812764d, _boogie_T_DeviceObject___unnamed_8_4812764d, _boogie_T_Length___unnamed_8_559a91e6, _boogie_T_FsInformationClass___unnamed_8_559a91e6, _boogie_T_Length___unnamed_8_5845b309, _boogie_T_FileInformationClass___unnamed_8_5845b309, _boogie_T_LowPart___unnamed_8_58ee4a31, _boogie_T_HighPart___unnamed_8_58ee4a31, _boogie_T_AllocatedResources___unnamed_8_61acf4ce, _boogie_T_AllocatedResourcesTranslated___unnamed_8_61acf4ce, _boogie_T_DeviceTextType___unnamed_8_6acfee04, _boogie_T_LocaleId___unnamed_8_6acfee04, _boogie_T_Length___unnamed_8_7f26a9dd, _boogie_T_CompletionFilter___unnamed_8_7f26a9dd, _boogie_T_Vpb___unnamed_8_87add0bd, _boogie_T_DeviceObject___unnamed_8_87add0bd, _boogie_T_InPath___unnamed_8_b2773e4c, _boogie_T_Reserved___unnamed_8_b2773e4c, _boogie_T_Type___unnamed_8_b2773e4c, _boogie_T_Length___unnamed_8_de890d4e, _boogie_T_FsInformationClass___unnamed_8_de890d4e, _boogie_T_LowPart___unnamed_8_ef9ba0d3, _boogie_T_HighPart___unnamed_8_ef9ba0d3, _boogie_T_A11CHAR, _boogie_T_A19CHAR, _boogie_T_A1_CM_FULL_RESOURCE_DESCRIPTOR, _boogie_T_A1_CM_PARTIAL_RESOURCE_DESCRIPTOR, _boogie_T_A1_IO_RESOURCE_DESCRIPTOR, _boogie_T_A1_IO_RESOURCE_LIST, _boogie_T_A1_LUID_AND_ATTRIBUTES, _boogie_T_A256UINT2, _boogie_T_A28PFDRIVER_DISPATCH, _boogie_T_A2UCHAR, _boogie_T_A32UINT2, _boogie_T_A36CHAR, _boogie_T_A37CHAR, _boogie_T_A39CHAR, _boogie_T_A3UCHAR, _boogie_T_A3UINT4, _boogie_T_A3_LUID_AND_ATTRIBUTES, _boogie_T_A43CHAR, _boogie_T_A4PVOID, _boogie_T_A4UINT4, _boogie_T_A5_DEVICE_POWER_STATE, _boogie_T_A74CHAR, _boogie_T_A7_DEVICE_POWER_STATE, _boogie_T_A8UCHAR, _boogie_T_BUS_QUERY_ID_TYPE, _boogie_T_CHAR, _boogie_T_DEVICE_TEXT_TYPE, _boogie_T_F0, _boogie_T_F1, _boogie_T_F10, _boogie_T_F11, _boogie_T_F12, _boogie_T_F13, _boogie_T_F14, _boogie_T_F15, _boogie_T_F16, _boogie_T_F17, _boogie_T_F18, _boogie_T_F19, _boogie_T_F2, _boogie_T_F20, _boogie_T_F21, _boogie_T_F22, _boogie_T_F23, _boogie_T_F24, _boogie_T_F25, _boogie_T_F26, _boogie_T_F27, _boogie_T_F28, _boogie_T_F29, _boogie_T_F3, _boogie_T_F30, _boogie_T_F31, _boogie_T_F32, _boogie_T_F33, _boogie_T_F34, _boogie_T_F35, _boogie_T_F36, _boogie_T_F37, _boogie_T_F38, _boogie_T_F4, _boogie_T_F5, _boogie_T_F6, _boogie_T_F7, _boogie_T_F8, _boogie_T_F9, _boogie_T_FDRIVER_ADD_DEVICE, _boogie_T_FDRIVER_CANCEL, _boogie_T_FDRIVER_CONTROL, _boogie_T_FDRIVER_DISPATCH, _boogie_T_FDRIVER_INITIALIZE, _boogie_T_FDRIVER_STARTIO, _boogie_T_FDRIVER_UNLOAD, _boogie_T_FFAST_IO_ACQUIRE_FILE, _boogie_T_FFAST_IO_ACQUIRE_FOR_CCFLUSH, _boogie_T_FFAST_IO_ACQUIRE_FOR_MOD_WRITE, _boogie_T_FFAST_IO_CHECK_IF_POSSIBLE, _boogie_T_FFAST_IO_DETACH_DEVICE, _boogie_T_FFAST_IO_DEVICE_CONTROL, _boogie_T_FFAST_IO_LOCK, _boogie_T_FFAST_IO_MDL_READ, _boogie_T_FFAST_IO_MDL_READ_COMPLETE, _boogie_T_FFAST_IO_MDL_READ_COMPLETE_COMPRESSED, _boogie_T_FFAST_IO_MDL_WRITE_COMPLETE, _boogie_T_FFAST_IO_MDL_WRITE_COMPLETE_COMPRESSED, _boogie_T_FFAST_IO_PREPARE_MDL_WRITE, _boogie_T_FFAST_IO_QUERY_BASIC_INFO, _boogie_T_FFAST_IO_QUERY_NETWORK_OPEN_INFO, _boogie_T_FFAST_IO_QUERY_OPEN, _boogie_T_FFAST_IO_QUERY_STANDARD_INFO, _boogie_T_FFAST_IO_READ, _boogie_T_FFAST_IO_READ_COMPRESSED, _boogie_T_FFAST_IO_RELEASE_FILE, _boogie_T_FFAST_IO_RELEASE_FOR_CCFLUSH, _boogie_T_FFAST_IO_RELEASE_FOR_MOD_WRITE, _boogie_T_FFAST_IO_UNLOCK_ALL, _boogie_T_FFAST_IO_UNLOCK_ALL_BY_KEY, _boogie_T_FFAST_IO_UNLOCK_SINGLE, _boogie_T_FFAST_IO_WRITE, _boogie_T_FFAST_IO_WRITE_COMPRESSED, _boogie_T_FIO_COMPLETION_ROUTINE, _boogie_T_FKDEFERRED_ROUTINE, _boogie_T_INT2, _boogie_T_INT4, _boogie_T_INT8, _boogie_T_PA11CHAR, _boogie_T_PA19CHAR, _boogie_T_PA36CHAR, _boogie_T_PA37CHAR, _boogie_T_PA39CHAR, _boogie_T_PA43CHAR, _boogie_T_PA74CHAR, _boogie_T_PCHAR, _boogie_T_PF19, _boogie_T_PF21, _boogie_T_PF23, _boogie_T_PF24, _boogie_T_PF25, _boogie_T_PF33, _boogie_T_PF34, _boogie_T_PF35, _boogie_T_PF36, _boogie_T_PF37, _boogie_T_PF38, _boogie_T_PFDRIVER_ADD_DEVICE, _boogie_T_PFDRIVER_CANCEL, _boogie_T_PFDRIVER_CONTROL, _boogie_T_PFDRIVER_DISPATCH, _boogie_T_PFDRIVER_INITIALIZE, _boogie_T_PFDRIVER_STARTIO, _boogie_T_PFDRIVER_UNLOAD, _boogie_T_PFFAST_IO_ACQUIRE_FILE, _boogie_T_PFFAST_IO_ACQUIRE_FOR_CCFLUSH, _boogie_T_PFFAST_IO_ACQUIRE_FOR_MOD_WRITE, _boogie_T_PFFAST_IO_CHECK_IF_POSSIBLE, _boogie_T_PFFAST_IO_DETACH_DEVICE, _boogie_T_PFFAST_IO_DEVICE_CONTROL, _boogie_T_PFFAST_IO_LOCK, _boogie_T_PFFAST_IO_MDL_READ, _boogie_T_PFFAST_IO_MDL_READ_COMPLETE, _boogie_T_PFFAST_IO_MDL_READ_COMPLETE_COMPRESSED, _boogie_T_PFFAST_IO_MDL_WRITE_COMPLETE, _boogie_T_PFFAST_IO_MDL_WRITE_COMPLETE_COMPRESSED, _boogie_T_PFFAST_IO_PREPARE_MDL_WRITE, _boogie_T_PFFAST_IO_QUERY_BASIC_INFO, _boogie_T_PFFAST_IO_QUERY_NETWORK_OPEN_INFO, _boogie_T_PFFAST_IO_QUERY_OPEN, _boogie_T_PFFAST_IO_QUERY_STANDARD_INFO, _boogie_T_PFFAST_IO_READ, _boogie_T_PFFAST_IO_READ_COMPRESSED, _boogie_T_PFFAST_IO_RELEASE_FILE, _boogie_T_PFFAST_IO_RELEASE_FOR_CCFLUSH, _boogie_T_PFFAST_IO_RELEASE_FOR_MOD_WRITE, _boogie_T_PFFAST_IO_UNLOCK_ALL, _boogie_T_PFFAST_IO_UNLOCK_ALL_BY_KEY, _boogie_T_PFFAST_IO_UNLOCK_SINGLE, _boogie_T_PFFAST_IO_WRITE, _boogie_T_PFFAST_IO_WRITE_COMPRESSED, _boogie_T_PFIO_COMPLETION_ROUTINE, _boogie_T_PFKDEFERRED_ROUTINE, _boogie_T_PINT4, _boogie_T_POWER_ACTION, _boogie_T_PPCHAR, _boogie_T_PPF24, _boogie_T_PPP_FILE_OBJECT, _boogie_T_PPVOID, _boogie_T_PP_DEVICE_EXTENSION, _boogie_T_PP_DEVICE_OBJECT, _boogie_T_PP_DRIVER_OBJECT, _boogie_T_PP_ERESOURCE, _boogie_T_PP_FILE_OBJECT, _boogie_T_PP_IRP, _boogie_T_PP_LIST_ENTRY, _boogie_T_PP_MDL, _boogie_T_PP_PORT, _boogie_T_PP_UNICODE_STRING, _boogie_T_PUCHAR, _boogie_T_PUINT2, _boogie_T_PUINT4, _boogie_T_PVOID, _boogie_T_PWMIGUIDREGINFO, _boogie_T_P_ACCESS_STATE, _boogie_T_P_CM_RESOURCE_LIST, _boogie_T_P_COMPRESSED_DATA_INFO, _boogie_T_P_DEVICE_CAPABILITIES, _boogie_T_P_DEVICE_EXTENSION, _boogie_T_P_DEVICE_OBJECT, _boogie_T_P_DEVOBJ_EXTENSION, _boogie_T_P_DRIVER_EXTENSION, _boogie_T_P_DRIVER_OBJECT, _boogie_T_P_EPROCESS, _boogie_T_P_ERESOURCE, _boogie_T_P_ETHREAD, _boogie_T_P_FAST_IO_DISPATCH, _boogie_T_P_FILE_BASIC_INFORMATION, _boogie_T_P_FILE_GET_QUOTA_INFORMATION, _boogie_T_P_FILE_NETWORK_OPEN_INFORMATION, _boogie_T_P_FILE_OBJECT, _boogie_T_P_FILE_STANDARD_INFORMATION, _boogie_T_P_GLOBALS, _boogie_T_P_GUID, _boogie_T_P_INTERFACE, _boogie_T_P_IO_COMPLETION_CONTEXT, _boogie_T_P_IO_REMOVE_LOCK_TRACKING_BLOCK, _boogie_T_P_IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T_P_IO_SECURITY_CONTEXT, _boogie_T_P_IO_STACK_LOCATION, _boogie_T_P_IO_STATUS_BLOCK, _boogie_T_P_IO_TIMER, _boogie_T_P_IRP, _boogie_T_P_KAPC, _boogie_T_P_KDPC, _boogie_T_P_KEVENT, _boogie_T_P_KEYBOARD_INPUT_DATA, _boogie_T_P_KSEMAPHORE, _boogie_T_P_KTHREAD, _boogie_T_P_LARGE_INTEGER, _boogie_T_P_LIST_ENTRY, _boogie_T_P_MDL, _boogie_T_P_OWNER_ENTRY, _boogie_T_P_PORT, _boogie_T_P_POWER_SEQUENCE, _boogie_T_P_SCSI_REQUEST_BLOCK, _boogie_T_P_SECTION_OBJECT_POINTERS, _boogie_T_P_SECURITY_QUALITY_OF_SERVICE, _boogie_T_P_UNICODE_STRING, _boogie_T_P_VPB, _boogie_T_UCHAR, _boogie_T_UINT2, _boogie_T_UINT4, _boogie_T_VOID, _boogie_T_WMIENABLEDISABLECONTROL, _boogie_T_WMIGUIDREGINFO, _boogie_T__ACCESS_STATE, _boogie_T__CM_FULL_RESOURCE_DESCRIPTOR, _boogie_T__CM_PARTIAL_RESOURCE_DESCRIPTOR, _boogie_T__CM_PARTIAL_RESOURCE_LIST, _boogie_T__CM_RESOURCE_LIST, _boogie_T__COMPRESSED_DATA_INFO, _boogie_T__DEVICE_CAPABILITIES, _boogie_T__DEVICE_EXTENSION, _boogie_T__DEVICE_OBJECT, _boogie_T__DEVICE_POWER_STATE, _boogie_T__DEVICE_RELATION_TYPE, _boogie_T__DEVICE_USAGE_NOTIFICATION_TYPE, _boogie_T__DEVOBJ_EXTENSION, _boogie_T__DISPATCHER_HEADER, _boogie_T__DRIVER_EXTENSION, _boogie_T__DRIVER_OBJECT, _boogie_T__EPROCESS, _boogie_T__ERESOURCE, _boogie_T__ETHREAD, _boogie_T__FAST_IO_DISPATCH, _boogie_T__FAST_MUTEX, _boogie_T__FILE_BASIC_INFORMATION, _boogie_T__FILE_GET_QUOTA_INFORMATION, _boogie_T__FILE_INFORMATION_CLASS, _boogie_T__FILE_NETWORK_OPEN_INFORMATION, _boogie_T__FILE_OBJECT, _boogie_T__FILE_STANDARD_INFORMATION, _boogie_T__FSINFOCLASS, _boogie_T__GLOBALS, _boogie_T__GUID, _boogie_T__INITIAL_PRIVILEGE_SET, _boogie_T__INTERFACE, _boogie_T__INTERFACE_TYPE, _boogie_T__IO_ALLOCATION_ACTION, _boogie_T__IO_COMPLETION_CONTEXT, _boogie_T__IO_REMOVE_LOCK, _boogie_T__IO_REMOVE_LOCK_COMMON_BLOCK, _boogie_T__IO_REMOVE_LOCK_DBG_BLOCK, _boogie_T__IO_REMOVE_LOCK_TRACKING_BLOCK, _boogie_T__IO_RESOURCE_DESCRIPTOR, _boogie_T__IO_RESOURCE_LIST, _boogie_T__IO_RESOURCE_REQUIREMENTS_LIST, _boogie_T__IO_SECURITY_CONTEXT, _boogie_T__IO_STACK_LOCATION, _boogie_T__IO_STATUS_BLOCK, _boogie_T__IO_TIMER, _boogie_T__IRP, _boogie_T__IRQ_DEVICE_POLICY, _boogie_T__IRQ_PRIORITY, _boogie_T__KAPC, _boogie_T__KDEVICE_QUEUE, _boogie_T__KDEVICE_QUEUE_ENTRY, _boogie_T__KDPC, _boogie_T__KEVENT, _boogie_T__KEYBOARD_ATTRIBUTES, _boogie_T__KEYBOARD_ID, _boogie_T__KEYBOARD_INDICATOR_PARAMETERS, _boogie_T__KEYBOARD_INPUT_DATA, _boogie_T__KEYBOARD_TYPEMATIC_PARAMETERS, _boogie_T__KSEMAPHORE, _boogie_T__KTHREAD, _boogie_T__LARGE_INTEGER, _boogie_T__LIST_ENTRY, _boogie_T__LUID, _boogie_T__LUID_AND_ATTRIBUTES, _boogie_T__MDL, _boogie_T__OWNER_ENTRY, _boogie_T__PORT, _boogie_T__POWER_SEQUENCE, _boogie_T__POWER_STATE, _boogie_T__POWER_STATE_TYPE, _boogie_T__PRIVILEGE_SET, _boogie_T__SCSI_REQUEST_BLOCK, _boogie_T__SECTION_OBJECT_POINTERS, _boogie_T__SECURITY_IMPERSONATION_LEVEL, _boogie_T__SECURITY_QUALITY_OF_SERVICE, _boogie_T__SECURITY_SUBJECT_CONTEXT, _boogie_T__SYSTEM_POWER_STATE, _boogie_T__SYSTEM_POWER_STATE_CONTEXT, _boogie_T__UNICODE_STRING, _boogie_T__VPB, _boogie_T__WAIT_CONTEXT_BLOCK, _boogie_T__WMILIB_CONTEXT, _boogie_T___unnamed_12_0d6a30de, _boogie_T___unnamed_12_17f5c211, _boogie_T___unnamed_12_1fb42e39, _boogie_T___unnamed_12_2a1563c6, _boogie_T___unnamed_12_31347272, _boogie_T___unnamed_12_429aadc0, _boogie_T___unnamed_12_4719de1a, _boogie_T___unnamed_12_4be56faa, _boogie_T___unnamed_12_5ce25b92, _boogie_T___unnamed_12_7a698b72, _boogie_T___unnamed_12_87c0de8d, _boogie_T___unnamed_12_98bfc55a, _boogie_T___unnamed_12_ab1bd9d7, _boogie_T___unnamed_12_b0429be9, _boogie_T___unnamed_12_b43e8de8, _boogie_T___unnamed_12_bfdb39ee, _boogie_T___unnamed_12_cd42b3c3, _boogie_T___unnamed_12_e668effc, _boogie_T___unnamed_12_e80d029e, _boogie_T___unnamed_16_07c0bcc5, _boogie_T___unnamed_16_29cb9f2f, _boogie_T___unnamed_16_30f11dbf, _boogie_T___unnamed_16_35034f68, _boogie_T___unnamed_16_487a9498, _boogie_T___unnamed_16_5f6a8844, _boogie_T___unnamed_16_7177b9f3, _boogie_T___unnamed_16_88e91ef6, _boogie_T___unnamed_16_8c506c98, _boogie_T___unnamed_16_9ac2e5f8, _boogie_T___unnamed_16_b93842ad, _boogie_T___unnamed_16_b9c62eab, _boogie_T___unnamed_16_bb584060, _boogie_T___unnamed_16_dba55c7c, _boogie_T___unnamed_16_e70c268b, _boogie_T___unnamed_16_e734d694, _boogie_T___unnamed_16_eac6dbea, _boogie_T___unnamed_16_f6cae4c2, _boogie_T___unnamed_16_fe36e4f4, _boogie_T___unnamed_1_29794256, _boogie_T___unnamed_1_2dc63b48, _boogie_T___unnamed_1_2ef8da39, _boogie_T___unnamed_1_faa7dc71, _boogie_T___unnamed_20_f4d2e6d8, _boogie_T___unnamed_24_41cbc8c0, _boogie_T___unnamed_24_5419c914, _boogie_T___unnamed_24_67a5ff10, _boogie_T___unnamed_24_72c3976e, _boogie_T___unnamed_24_a26050bb, _boogie_T___unnamed_24_b8f476db, _boogie_T___unnamed_24_d09044b4, _boogie_T___unnamed_2_46cc4597, _boogie_T___unnamed_40_7218f704, _boogie_T___unnamed_40_c55c9377, _boogie_T___unnamed_44_5584090d, _boogie_T___unnamed_48_cf99b13f, _boogie_T___unnamed_4_069846fb, _boogie_T___unnamed_4_224c32f4, _boogie_T___unnamed_4_2de698da, _boogie_T___unnamed_4_3a2fdc5e, _boogie_T___unnamed_4_3a4c1a13, _boogie_T___unnamed_4_43913aa5, _boogie_T___unnamed_4_4e8dd2ba, _boogie_T___unnamed_4_52603077, _boogie_T___unnamed_4_52c594f7, _boogie_T___unnamed_4_5ca00198, _boogie_T___unnamed_4_6ac6463c, _boogie_T___unnamed_4_6f9ac8e1, _boogie_T___unnamed_4_7a02167b, _boogie_T___unnamed_4_7d9d0c7e, _boogie_T___unnamed_4_82f7a864, _boogie_T___unnamed_4_9aec220b, _boogie_T___unnamed_4_a97c65a1, _boogie_T___unnamed_4_c3479730, _boogie_T___unnamed_4_d99b6e2b, _boogie_T___unnamed_4_f19b65c1, _boogie_T___unnamed_4_fa10fc16, _boogie_T___unnamed_8_01efa60d, _boogie_T___unnamed_8_08d4cef8, _boogie_T___unnamed_8_0a898c0c, _boogie_T___unnamed_8_1330f93a, _boogie_T___unnamed_8_181d0de9, _boogie_T___unnamed_8_4812764d, _boogie_T___unnamed_8_559a91e6, _boogie_T___unnamed_8_5845b309, _boogie_T___unnamed_8_58ee4a31, _boogie_T___unnamed_8_61acf4ce, _boogie_T___unnamed_8_6acfee04, _boogie_T___unnamed_8_7f26a9dd, _boogie_T___unnamed_8_87add0bd, _boogie_T___unnamed_8_b2773e4c, _boogie_T___unnamed_8_de890d4e, _boogie_T___unnamed_8_ef9ba0d3]
axiom unique1: distinct [_boogie_Globals]

-- Variables
variable (_boogie_Mem_BYTE : (SMTArray1 Int _boogie_byte))
variable (_boogie_alloc : (SMTArray1 Int _boogie_name))
variable (_boogie_Mem : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
variable (_boogie_Res_DEVICE_STACK : (SMTArray1 Int Int))
variable (_boogie_Res_DEV_EXTN : (SMTArray1 Int Int))
variable (_boogie_Res_DEV_OBJ_INIT : (SMTArray1 Int Int))
variable (_boogie_Res_SPIN_LOCK : (SMTArray1 Int Int))

-- Functions
axiom _boogie_OneByteToInt : _boogie_byte → Int
axiom _boogie_TwoBytesToInt : _boogie_byte → _boogie_byte → Int
axiom _boogie_FourBytesToInt : _boogie_byte → _boogie_byte → _boogie_byte → _boogie_byte → Int
axiom _boogie_Field : Int → _boogie_name
axiom _boogie_Base : Int → Int
axiom _boogie_Equal : (SMTArray1 Int Prop) → (SMTArray1 Int Prop) → Prop
axiom _boogie_Subset : (SMTArray1 Int Prop) → (SMTArray1 Int Prop) → Prop
axiom _boogie_Disjoint : (SMTArray1 Int Prop) → (SMTArray1 Int Prop) → Prop
axiom _boogie_Empty : (SMTArray1 Int Prop)
axiom _boogie_SetTrue : (SMTArray1 Int Prop)
axiom _boogie_Singleton : Int → (SMTArray1 Int Prop)
axiom _boogie_Reachable : (SMTArray2 Int Int Prop) → Int → (SMTArray1 Int Prop)
axiom _boogie_Union : (SMTArray1 Int Prop) → (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Intersection : (SMTArray1 Int Prop) → (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Difference : (SMTArray1 Int Prop) → (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Dereference : (SMTArray1 Int Prop) → (SMTArray1 Int Int) → (SMTArray1 Int Prop)
axiom _boogie_Inverse : (SMTArray1 Int Int) → Int → (SMTArray1 Int Prop)
axiom _boogie_AtLeast : Int → Int → (SMTArray1 Int Prop)
axiom _boogie_Rep : Int → Int → Int
axiom _boogie_Array : Int → Int → Int → (SMTArray1 Int Prop)
axiom _boogie_Unified : (SMTArray1 _boogie_name (SMTArray1 Int Int)) → (SMTArray1 Int Int)
axiom _boogie_Match : Int → _boogie_name → Prop
axiom _boogie_HasType : Int → _boogie_name → (SMTArray1 _boogie_name (SMTArray1 Int Int)) → Prop
axiom _boogie_Values : _boogie_name → (SMTArray1 _boogie_name (SMTArray1 Int Int)) → (SMTArray1 Int Prop)
axiom _boogie_T_Ptr : _boogie_name → _boogie_name
axiom _boogie_AssocClassList__GLOBALS : Int → Int
axiom _boogie_AssocClassList__GLOBALSInv : Int → Int
axiom _boogie__S_AssocClassList__GLOBALS : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_AssocClassList__GLOBALSInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Buffer__UNICODE_STRING : Int → Int
axiom _boogie_Buffer__UNICODE_STRINGInv : Int → Int
axiom _boogie__S_Buffer__UNICODE_STRING : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Buffer__UNICODE_STRINGInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_DataIn__DEVICE_EXTENSION : Int → Int
axiom _boogie_DataIn__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_DataIn__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_DataIn__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_DataOut__DEVICE_EXTENSION : Int → Int
axiom _boogie_DataOut__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_DataOut__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_DataOut__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_DeviceExtension__DEVICE_OBJECT : Int → Int
axiom _boogie_DeviceExtension__DEVICE_OBJECTInv : Int → Int
axiom _boogie__S_DeviceExtension__DEVICE_OBJECT : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_DeviceExtension__DEVICE_OBJECTInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Enabled__DEVICE_EXTENSION : Int → Int
axiom _boogie_Enabled__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_Enabled__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Enabled__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Enabled__PORT : Int → Int
axiom _boogie_Enabled__PORTInv : Int → Int
axiom _boogie__S_Enabled__PORT : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Enabled__PORTInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_File__DEVICE_EXTENSION : Int → Int
axiom _boogie_File__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_File__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_File__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_File__PORT : Int → Int
axiom _boogie_File__PORTInv : Int → Int
axiom _boogie__S_File__PORT : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_File__PORTInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Flink__LIST_ENTRY : Int → Int
axiom _boogie_Flink__LIST_ENTRYInv : Int → Int
axiom _boogie__S_Flink__LIST_ENTRY : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Flink__LIST_ENTRYInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Free__PORT : Int → Int
axiom _boogie_Free__PORTInv : Int → Int
axiom _boogie__S_Free__PORT : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Free__PORTInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_GrandMaster__GLOBALS : Int → Int
axiom _boogie_GrandMaster__GLOBALSInv : Int → Int
axiom _boogie__S_GrandMaster__GLOBALS : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_GrandMaster__GLOBALSInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_InputData__DEVICE_EXTENSION : Int → Int
axiom _boogie_InputData__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_InputData__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_InputData__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_LegacyDeviceList__GLOBALS : Int → Int
axiom _boogie_LegacyDeviceList__GLOBALSInv : Int → Int
axiom _boogie__S_LegacyDeviceList__GLOBALS : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_LegacyDeviceList__GLOBALSInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Link__DEVICE_EXTENSION : Int → Int
axiom _boogie_Link__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_Link__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Link__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_NumAssocClass__GLOBALS : Int → Int
axiom _boogie_NumAssocClass__GLOBALSInv : Int → Int
axiom _boogie__S_NumAssocClass__GLOBALS : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_NumAssocClass__GLOBALSInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_PnP__DEVICE_EXTENSION : Int → Int
axiom _boogie_PnP__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_PnP__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_PnP__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Port__PORT : Int → Int
axiom _boogie_Port__PORTInv : Int → Int
axiom _boogie__S_Port__PORT : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Port__PORTInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_RegistryPath__GLOBALS : Int → Int
axiom _boogie_RegistryPath__GLOBALSInv : Int → Int
axiom _boogie__S_RegistryPath__GLOBALS : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_RegistryPath__GLOBALSInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Self__DEVICE_EXTENSION : Int → Int
axiom _boogie_Self__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_Self__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Self__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_StackSize__DEVICE_OBJECT : Int → Int
axiom _boogie_StackSize__DEVICE_OBJECTInv : Int → Int
axiom _boogie__S_StackSize__DEVICE_OBJECT : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_StackSize__DEVICE_OBJECTInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_Started__DEVICE_EXTENSION : Int → Int
axiom _boogie_Started__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_Started__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_Started__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_TopPort__DEVICE_EXTENSION : Int → Int
axiom _boogie_TopPort__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_TopPort__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_TopPort__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_UnitId__DEVICE_EXTENSION : Int → Int
axiom _boogie_UnitId__DEVICE_EXTENSIONInv : Int → Int
axiom _boogie__S_UnitId__DEVICE_EXTENSION : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie__S_UnitId__DEVICE_EXTENSIONInv : (SMTArray1 Int Prop) → (SMTArray1 Int Prop)
axiom _boogie_MINUS_BOTH_PTR_OR_BOTH_INT : Int → Int → Int → Int
axiom _boogie_MINUS_LEFT_PTR : Int → Int → Int → Int
axiom _boogie_PLUS : Int → Int → Int → Int
axiom _boogie_MULT : Int → Int → Int
axiom _boogie_DIV : Int → Int → Int
axiom _boogie_BINARY_BOTH_INT : Int → Int → Int
axiom _boogie_POW2 : Int → Prop
axiom _boogie_choose : Prop → Int → Int → Int
axiom _boogie_BIT_BAND : Int → Int → Int
axiom _boogie_BIT_BOR : Int → Int → Int
axiom _boogie_BIT_BXOR : Int → Int → Int
axiom _boogie_BIT_BNOT : Int → Int
axiom _boogie_LIFT : Prop → Int
axiom _boogie_NOT : Int → Int
axiom _boogie_NULL_CHECK : Int → Int
axiom _boogie_ReachBetween : (SMTArray1 Int Int) → Int → Int → Int → Prop
axiom _boogie_ReachAvoiding : (SMTArray1 Int Int) → Int → Int → Int → Prop
axiom _boogie_ReachBetweenSet : (SMTArray1 Int Int) → Int → Int → (SMTArray1 Int Prop)
axiom _boogie_Shift_Flink__LIST_ENTRY : (SMTArray1 Int Int) → (SMTArray1 Int Int)

-- Axioms
axiom ax_l7c1: (forall (_boogie_b0 : _boogie_byte) (_boogie_c0 : _boogie_byte), (((_boogie_OneByteToInt _boogie_b0) = (_boogie_OneByteToInt _boogie_c0)) → (_boogie_b0 = _boogie_c0)))
axiom ax_l8c1: (forall (_boogie_b0 : _boogie_byte) (_boogie_b1 : _boogie_byte) (_boogie_c0 : _boogie_byte) (_boogie_c1 : _boogie_byte), (((_boogie_TwoBytesToInt _boogie_b0 _boogie_b1) = (_boogie_TwoBytesToInt _boogie_c0 _boogie_c1)) → ((_boogie_b0 = _boogie_c0) ∧ (_boogie_b1 = _boogie_c1))))
axiom ax_l9c1: (forall (_boogie_b0 : _boogie_byte) (_boogie_b1 : _boogie_byte) (_boogie_b2 : _boogie_byte) (_boogie_b3 : _boogie_byte) (_boogie_c0 : _boogie_byte) (_boogie_c1 : _boogie_byte) (_boogie_c2 : _boogie_byte) (_boogie_c3 : _boogie_byte), (((_boogie_FourBytesToInt _boogie_b0 _boogie_b1 _boogie_b2 _boogie_b3) = (_boogie_FourBytesToInt _boogie_c0 _boogie_c1 _boogie_c2 _boogie_c3)) → ((((_boogie_b0 = _boogie_c0) ∧ (_boogie_b1 = _boogie_c1)) ∧ (_boogie_b2 = _boogie_c2)) ∧ (_boogie_b3 = _boogie_c3))))
axiom ax_l42c1: (forall (_boogie_n : Int) (_boogie_x : Int) (_boogie_y : Int), ((select1 (_boogie_AtLeast _boogie_n _boogie_x) _boogie_y) → ((_boogie_x <= _boogie_y) ∧ ((_boogie_Rep _boogie_n _boogie_x) = (_boogie_Rep _boogie_n _boogie_y)))))
axiom ax_l43c1: (forall (_boogie_n : Int) (_boogie_x : Int) (_boogie_y : Int), (((_boogie_x <= _boogie_y) ∧ ((_boogie_Rep _boogie_n _boogie_x) = (_boogie_Rep _boogie_n _boogie_y))) → (select1 (_boogie_AtLeast _boogie_n _boogie_x) _boogie_y)))
axiom ax_l44c1: (forall (_boogie_n : Int) (_boogie_x : Int), (select1 (_boogie_AtLeast _boogie_n _boogie_x) _boogie_x))
axiom ax_l45c1: (forall (_boogie_n : Int) (_boogie_x : Int) (_boogie_z : Int), ((_boogie_Rep _boogie_n _boogie_x) = (_boogie_Rep _boogie_n (_boogie_PLUS _boogie_x _boogie_n _boogie_z))))
axiom ax_l46c1: (forall (_boogie_n : Int) (_boogie_x : Int), (exists (_boogie_k : Int), (((_boogie_Rep _boogie_n _boogie_x) - _boogie_x) = (_boogie_n * _boogie_k))))
axiom ax_l61c1: (forall (_boogie_x : Int) (_boogie_n : Int) (_boogie_z : Int), ((_boogie_z <= 0) → (_boogie_Equal (_boogie_Array _boogie_x _boogie_n _boogie_z) (_boogie_Empty))))
axiom ax_l62c1: (forall (_boogie_x : Int) (_boogie_n : Int) (_boogie_z : Int), ((_boogie_z > 0) → (_boogie_Equal (_boogie_Array _boogie_x _boogie_n _boogie_z) (_boogie_Difference (_boogie_AtLeast _boogie_n _boogie_x) (_boogie_AtLeast _boogie_n (_boogie_PLUS _boogie_x _boogie_n _boogie_z))))))
axiom ax_l65c1: (forall (_boogie_x : Int), (Not (select1 (_boogie_Empty) _boogie_x)))
axiom ax_l67c1: (forall (_boogie_x : Int), (select1 (_boogie_SetTrue) _boogie_x))
axiom ax_l69c1: (forall (_boogie_x : Int) (_boogie_y : Int), ((select1 (_boogie_Singleton _boogie_y) _boogie_x) = (_boogie_x = _boogie_y)))
axiom ax_l70c1: (forall (_boogie_y : Int), (select1 (_boogie_Singleton _boogie_y) _boogie_y))
axiom ax_l74c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), ((select1 (_boogie_Union _boogie_S _boogie_T) _boogie_x) = ((select1 _boogie_S _boogie_x) ∨ (select1 _boogie_T _boogie_x))))
axiom ax_l75c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), ((select1 (_boogie_Intersection _boogie_S _boogie_T) _boogie_x) = ((select1 _boogie_S _boogie_x) ∧ (select1 _boogie_T _boogie_x))))
axiom ax_l76c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), ((select1 (_boogie_Difference _boogie_S _boogie_T) _boogie_x) = ((select1 _boogie_S _boogie_x) ∧ (Not (select1 _boogie_T _boogie_x)))))
axiom ax_l78c1: (forall (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), ((_boogie_Equal _boogie_S _boogie_T) = ((_boogie_Subset _boogie_S _boogie_T) ∧ (_boogie_Subset _boogie_T _boogie_S))))
axiom ax_l79c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), (((select1 _boogie_S _boogie_x) ∧ (_boogie_Subset _boogie_S _boogie_T)) → (select1 _boogie_T _boogie_x)))
axiom ax_l80c1: (forall (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), ((_boogie_Subset _boogie_S _boogie_T) ∨ (exists (_boogie_x : Int), ((select1 _boogie_S _boogie_x) ∧ (Not (select1 _boogie_T _boogie_x))))))
axiom ax_l81c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), (Not (((select1 _boogie_S _boogie_x) ∧ (_boogie_Disjoint _boogie_S _boogie_T)) ∧ (select1 _boogie_T _boogie_x))))
axiom ax_l82c1: (forall (_boogie_S : (SMTArray1 Int Prop)) (_boogie_T : (SMTArray1 Int Prop)), ((_boogie_Disjoint _boogie_S _boogie_T) ∨ (exists (_boogie_x : Int), ((select1 _boogie_S _boogie_x) ∧ (select1 _boogie_T _boogie_x)))))
axiom ax_l84c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int), (select1 (_boogie_Inverse _boogie_f (select1 _boogie_f _boogie_x)) _boogie_x))
axiom ax_l85c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int), ((select1 (_boogie_Inverse _boogie_f _boogie_y) _boogie_x) → ((select1 _boogie_f _boogie_x) = _boogie_y)))
axiom ax_l86c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int), (_boogie_Equal (_boogie_Inverse (store1 _boogie_f _boogie_x _boogie_y) _boogie_y) (_boogie_Union (_boogie_Inverse _boogie_f _boogie_y) (_boogie_Singleton _boogie_x))))
axiom ax_l87c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int), ((_boogie_y = _boogie_z) ∨ (_boogie_Equal (_boogie_Inverse (store1 _boogie_f _boogie_x _boogie_y) _boogie_z) (_boogie_Difference (_boogie_Inverse _boogie_f _boogie_z) (_boogie_Singleton _boogie_x)))))
axiom ax_l90c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_M : (SMTArray1 Int Int)), ((select1 (_boogie_Dereference _boogie_S _boogie_M) _boogie_x) → (exists (_boogie_y : Int), ((_boogie_x = (select1 _boogie_M _boogie_y)) ∧ (select1 _boogie_S _boogie_y)))))
axiom ax_l91c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_M : (SMTArray1 Int Int)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie_Dereference _boogie_S _boogie_M) (select1 _boogie_M _boogie_x))))
axiom ax_l92c1: (forall (_boogie_x : Int) (_boogie_y : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_M : (SMTArray1 Int Int)), ((Not (select1 _boogie_S _boogie_x)) → (_boogie_Equal (_boogie_Dereference _boogie_S (store1 _boogie_M _boogie_x _boogie_y)) (_boogie_Dereference _boogie_S _boogie_M))))
axiom ax_l93c1: (forall (_boogie_x : Int) (_boogie_y : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_M : (SMTArray1 Int Int)), (((select1 _boogie_S _boogie_x) ∧ (_boogie_Equal (_boogie_Intersection (_boogie_Inverse _boogie_M (select1 _boogie_M _boogie_x)) _boogie_S) (_boogie_Singleton _boogie_x))) → (_boogie_Equal (_boogie_Dereference _boogie_S (store1 _boogie_M _boogie_x _boogie_y)) (_boogie_Union (_boogie_Difference (_boogie_Dereference _boogie_S _boogie_M) (_boogie_Singleton (select1 _boogie_M _boogie_x))) (_boogie_Singleton _boogie_y)))))
axiom ax_l95c1: (forall (_boogie_x : Int) (_boogie_y : Int) (_boogie_S : (SMTArray1 Int Prop)) (_boogie_M : (SMTArray1 Int Int)), (((select1 _boogie_S _boogie_x) ∧ (Not (_boogie_Equal (_boogie_Intersection (_boogie_Inverse _boogie_M (select1 _boogie_M _boogie_x)) _boogie_S) (_boogie_Singleton _boogie_x)))) → (_boogie_Equal (_boogie_Dereference _boogie_S (store1 _boogie_M _boogie_x _boogie_y)) (_boogie_Union (_boogie_Dereference _boogie_S _boogie_M) (_boogie_Singleton _boogie_y)))))
axiom ax_l99c1: (forall (_boogie_M : (SMTArray1 _boogie_name (SMTArray1 Int Int))) (_boogie_x : Int), ((select1 (_boogie_Unified _boogie_M) _boogie_x) = (select1 (select1 _boogie_M (_boogie_Field _boogie_x)) _boogie_x)))
axiom ax_l100c1: (forall (_boogie_M : (SMTArray1 _boogie_name (SMTArray1 Int Int))) (_boogie_x : Int) (_boogie_y : Int), ((_boogie_Unified (store1 _boogie_M (_boogie_Field _boogie_x) (store1 (select1 _boogie_M (_boogie_Field _boogie_x)) _boogie_x _boogie_y))) = (store1 (_boogie_Unified _boogie_M) _boogie_x _boogie_y)))
axiom ax_l110c1: (forall (_boogie_v : Int) (_boogie_t : _boogie_name) (_boogie_m : (SMTArray1 _boogie_name (SMTArray1 Int Int))), ((select1 (_boogie_Values _boogie_t _boogie_m) _boogie_v) → (_boogie_HasType _boogie_v _boogie_t _boogie_m)))
axiom ax_l111c1: (forall (_boogie_v : Int) (_boogie_t : _boogie_name) (_boogie_m : (SMTArray1 _boogie_name (SMTArray1 Int Int))), ((_boogie_HasType _boogie_v _boogie_t _boogie_m) → (select1 (_boogie_Values _boogie_t _boogie_m) _boogie_v)))
axiom ax_l113c1: (forall (_boogie_a : Int) (_boogie_t : _boogie_name), ((_boogie_Match _boogie_a (_boogie_T_Ptr _boogie_t)) = ((_boogie_Field _boogie_a) = (_boogie_T_Ptr _boogie_t))))
axiom ax_l114c1: (forall (_boogie_v : Int) (_boogie_t : _boogie_name) (_boogie_m : (SMTArray1 _boogie_name (SMTArray1 Int Int))), ((_boogie_HasType _boogie_v (_boogie_T_Ptr _boogie_t) _boogie_m) = ((_boogie_v = 0) ∨ ((_boogie_v > 0) ∧ (_boogie_Match _boogie_v _boogie_t)))))
axiom ax_l116c1: (forall (_boogie_v : Int) (_boogie_t : _boogie_name) (_boogie_m1 : (SMTArray1 _boogie_name (SMTArray1 Int Int))) (_boogie_m2 : (SMTArray1 _boogie_name (SMTArray1 Int Int))), ((_boogie_HasType _boogie_v _boogie_t _boogie_m1) = (_boogie_HasType _boogie_v _boogie_t _boogie_m2)))
axiom ax_l1298c1: (forall (_boogie_x : Int), ((_boogie_AssocClassList__GLOBALSInv (_boogie_AssocClassList__GLOBALS _boogie_x)) = _boogie_x))
axiom ax_l1299c1: (forall (_boogie_x : Int), ((_boogie_AssocClassList__GLOBALS (_boogie_AssocClassList__GLOBALSInv _boogie_x)) = _boogie_x))
axiom ax_l1301c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_AssocClassList__GLOBALS _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_AssocClassList__GLOBALSInv _boogie_x))))
axiom ax_l1302c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_AssocClassList__GLOBALSInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_AssocClassList__GLOBALS _boogie_x))))
axiom ax_l1303c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_AssocClassList__GLOBALS _boogie_S) (_boogie_AssocClassList__GLOBALS _boogie_x))))
axiom ax_l1304c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_AssocClassList__GLOBALSInv _boogie_S) (_boogie_AssocClassList__GLOBALSInv _boogie_x))))
axiom ax_l1306c1: (forall (_boogie_x : Int), ((_boogie_AssocClassList__GLOBALS _boogie_x) = (_boogie_x + 8)))
axiom ax_l1307c1: (forall (_boogie_x : Int), ((_boogie_AssocClassList__GLOBALSInv _boogie_x) = (_boogie_x - 8)))
axiom ax_l1308c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 8 1) = (_boogie_AssocClassList__GLOBALSInv _boogie_x)))
axiom ax_l1309c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 8) = (_boogie_AssocClassList__GLOBALSInv _boogie_x)))
axiom ax_l1315c1: (forall (_boogie_x : Int), ((_boogie_Buffer__UNICODE_STRINGInv (_boogie_Buffer__UNICODE_STRING _boogie_x)) = _boogie_x))
axiom ax_l1316c1: (forall (_boogie_x : Int), ((_boogie_Buffer__UNICODE_STRING (_boogie_Buffer__UNICODE_STRINGInv _boogie_x)) = _boogie_x))
axiom ax_l1318c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Buffer__UNICODE_STRING _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Buffer__UNICODE_STRINGInv _boogie_x))))
axiom ax_l1319c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Buffer__UNICODE_STRINGInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Buffer__UNICODE_STRING _boogie_x))))
axiom ax_l1320c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Buffer__UNICODE_STRING _boogie_S) (_boogie_Buffer__UNICODE_STRING _boogie_x))))
axiom ax_l1321c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Buffer__UNICODE_STRINGInv _boogie_S) (_boogie_Buffer__UNICODE_STRINGInv _boogie_x))))
axiom ax_l1323c1: (forall (_boogie_x : Int), ((_boogie_Buffer__UNICODE_STRING _boogie_x) = (_boogie_x + 4)))
axiom ax_l1324c1: (forall (_boogie_x : Int), ((_boogie_Buffer__UNICODE_STRINGInv _boogie_x) = (_boogie_x - 4)))
axiom ax_l1325c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 4 1) = (_boogie_Buffer__UNICODE_STRINGInv _boogie_x)))
axiom ax_l1326c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 4) = (_boogie_Buffer__UNICODE_STRINGInv _boogie_x)))
axiom ax_l1332c1: (forall (_boogie_x : Int), ((_boogie_DataIn__DEVICE_EXTENSIONInv (_boogie_DataIn__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1333c1: (forall (_boogie_x : Int), ((_boogie_DataIn__DEVICE_EXTENSION (_boogie_DataIn__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1335c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_DataIn__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_DataIn__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1336c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_DataIn__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_DataIn__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1337c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_DataIn__DEVICE_EXTENSION _boogie_S) (_boogie_DataIn__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1338c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_DataIn__DEVICE_EXTENSIONInv _boogie_S) (_boogie_DataIn__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1340c1: (forall (_boogie_x : Int), ((_boogie_DataIn__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 132)))
axiom ax_l1341c1: (forall (_boogie_x : Int), ((_boogie_DataIn__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 132)))
axiom ax_l1342c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 132 1) = (_boogie_DataIn__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1343c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 132) = (_boogie_DataIn__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1349c1: (forall (_boogie_x : Int), ((_boogie_DataOut__DEVICE_EXTENSIONInv (_boogie_DataOut__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1350c1: (forall (_boogie_x : Int), ((_boogie_DataOut__DEVICE_EXTENSION (_boogie_DataOut__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1352c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_DataOut__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_DataOut__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1353c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_DataOut__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_DataOut__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1354c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_DataOut__DEVICE_EXTENSION _boogie_S) (_boogie_DataOut__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1355c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_DataOut__DEVICE_EXTENSIONInv _boogie_S) (_boogie_DataOut__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1357c1: (forall (_boogie_x : Int), ((_boogie_DataOut__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 136)))
axiom ax_l1358c1: (forall (_boogie_x : Int), ((_boogie_DataOut__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 136)))
axiom ax_l1359c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 136 1) = (_boogie_DataOut__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1360c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 136) = (_boogie_DataOut__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1366c1: (forall (_boogie_x : Int), ((_boogie_DeviceExtension__DEVICE_OBJECTInv (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_x)) = _boogie_x))
axiom ax_l1367c1: (forall (_boogie_x : Int), ((_boogie_DeviceExtension__DEVICE_OBJECT (_boogie_DeviceExtension__DEVICE_OBJECTInv _boogie_x)) = _boogie_x))
axiom ax_l1369c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_DeviceExtension__DEVICE_OBJECT _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_DeviceExtension__DEVICE_OBJECTInv _boogie_x))))
axiom ax_l1370c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_DeviceExtension__DEVICE_OBJECTInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_x))))
axiom ax_l1371c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_DeviceExtension__DEVICE_OBJECT _boogie_S) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_x))))
axiom ax_l1372c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_DeviceExtension__DEVICE_OBJECTInv _boogie_S) (_boogie_DeviceExtension__DEVICE_OBJECTInv _boogie_x))))
axiom ax_l1374c1: (forall (_boogie_x : Int), ((_boogie_DeviceExtension__DEVICE_OBJECT _boogie_x) = (_boogie_x + 40)))
axiom ax_l1375c1: (forall (_boogie_x : Int), ((_boogie_DeviceExtension__DEVICE_OBJECTInv _boogie_x) = (_boogie_x - 40)))
axiom ax_l1376c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 40 1) = (_boogie_DeviceExtension__DEVICE_OBJECTInv _boogie_x)))
axiom ax_l1377c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 40) = (_boogie_DeviceExtension__DEVICE_OBJECTInv _boogie_x)))
axiom ax_l1383c1: (forall (_boogie_x : Int), ((_boogie_Enabled__DEVICE_EXTENSIONInv (_boogie_Enabled__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1384c1: (forall (_boogie_x : Int), ((_boogie_Enabled__DEVICE_EXTENSION (_boogie_Enabled__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1386c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Enabled__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Enabled__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1387c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Enabled__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Enabled__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1388c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Enabled__DEVICE_EXTENSION _boogie_S) (_boogie_Enabled__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1389c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Enabled__DEVICE_EXTENSIONInv _boogie_S) (_boogie_Enabled__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1391c1: (forall (_boogie_x : Int), ((_boogie_Enabled__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 284)))
axiom ax_l1392c1: (forall (_boogie_x : Int), ((_boogie_Enabled__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 284)))
axiom ax_l1393c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 284 1) = (_boogie_Enabled__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1394c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 284) = (_boogie_Enabled__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1400c1: (forall (_boogie_x : Int), ((_boogie_Enabled__PORTInv (_boogie_Enabled__PORT _boogie_x)) = _boogie_x))
axiom ax_l1401c1: (forall (_boogie_x : Int), ((_boogie_Enabled__PORT (_boogie_Enabled__PORTInv _boogie_x)) = _boogie_x))
axiom ax_l1403c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Enabled__PORT _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Enabled__PORTInv _boogie_x))))
axiom ax_l1404c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Enabled__PORTInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Enabled__PORT _boogie_x))))
axiom ax_l1405c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Enabled__PORT _boogie_S) (_boogie_Enabled__PORT _boogie_x))))
axiom ax_l1406c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Enabled__PORTInv _boogie_S) (_boogie_Enabled__PORTInv _boogie_x))))
axiom ax_l1408c1: (forall (_boogie_x : Int), ((_boogie_Enabled__PORT _boogie_x) = (_boogie_x + 8)))
axiom ax_l1409c1: (forall (_boogie_x : Int), ((_boogie_Enabled__PORTInv _boogie_x) = (_boogie_x - 8)))
axiom ax_l1410c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 8 1) = (_boogie_Enabled__PORTInv _boogie_x)))
axiom ax_l1411c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 8) = (_boogie_Enabled__PORTInv _boogie_x)))
axiom ax_l1417c1: (forall (_boogie_x : Int), ((_boogie_File__DEVICE_EXTENSIONInv (_boogie_File__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1418c1: (forall (_boogie_x : Int), ((_boogie_File__DEVICE_EXTENSION (_boogie_File__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1420c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_File__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_File__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1421c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_File__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_File__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1422c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_File__DEVICE_EXTENSION _boogie_S) (_boogie_File__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1423c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_File__DEVICE_EXTENSIONInv _boogie_S) (_boogie_File__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1425c1: (forall (_boogie_x : Int), ((_boogie_File__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 280)))
axiom ax_l1426c1: (forall (_boogie_x : Int), ((_boogie_File__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 280)))
axiom ax_l1427c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 280 1) = (_boogie_File__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1428c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 280) = (_boogie_File__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1434c1: (forall (_boogie_x : Int), ((_boogie_File__PORTInv (_boogie_File__PORT _boogie_x)) = _boogie_x))
axiom ax_l1435c1: (forall (_boogie_x : Int), ((_boogie_File__PORT (_boogie_File__PORTInv _boogie_x)) = _boogie_x))
axiom ax_l1437c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_File__PORT _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_File__PORTInv _boogie_x))))
axiom ax_l1438c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_File__PORTInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_File__PORT _boogie_x))))
axiom ax_l1439c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_File__PORT _boogie_S) (_boogie_File__PORT _boogie_x))))
axiom ax_l1440c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_File__PORTInv _boogie_S) (_boogie_File__PORTInv _boogie_x))))
axiom ax_l1442c1: (forall (_boogie_x : Int), ((_boogie_File__PORT _boogie_x) = (_boogie_x + 0)))
axiom ax_l1443c1: (forall (_boogie_x : Int), ((_boogie_File__PORTInv _boogie_x) = (_boogie_x - 0)))
axiom ax_l1444c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 0 1) = (_boogie_File__PORTInv _boogie_x)))
axiom ax_l1445c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 0) = (_boogie_File__PORTInv _boogie_x)))
axiom ax_l1451c1: (forall (_boogie_x : Int), ((_boogie_Flink__LIST_ENTRYInv (_boogie_Flink__LIST_ENTRY _boogie_x)) = _boogie_x))
axiom ax_l1452c1: (forall (_boogie_x : Int), ((_boogie_Flink__LIST_ENTRY (_boogie_Flink__LIST_ENTRYInv _boogie_x)) = _boogie_x))
axiom ax_l1454c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Flink__LIST_ENTRY _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Flink__LIST_ENTRYInv _boogie_x))))
axiom ax_l1455c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Flink__LIST_ENTRYInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Flink__LIST_ENTRY _boogie_x))))
axiom ax_l1456c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Flink__LIST_ENTRY _boogie_S) (_boogie_Flink__LIST_ENTRY _boogie_x))))
axiom ax_l1457c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Flink__LIST_ENTRYInv _boogie_S) (_boogie_Flink__LIST_ENTRYInv _boogie_x))))
axiom ax_l1459c1: (forall (_boogie_x : Int), ((_boogie_Flink__LIST_ENTRY _boogie_x) = (_boogie_x + 0)))
axiom ax_l1460c1: (forall (_boogie_x : Int), ((_boogie_Flink__LIST_ENTRYInv _boogie_x) = (_boogie_x - 0)))
axiom ax_l1461c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 0 1) = (_boogie_Flink__LIST_ENTRYInv _boogie_x)))
axiom ax_l1462c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 0) = (_boogie_Flink__LIST_ENTRYInv _boogie_x)))
axiom ax_l1468c1: (forall (_boogie_x : Int), ((_boogie_Free__PORTInv (_boogie_Free__PORT _boogie_x)) = _boogie_x))
axiom ax_l1469c1: (forall (_boogie_x : Int), ((_boogie_Free__PORT (_boogie_Free__PORTInv _boogie_x)) = _boogie_x))
axiom ax_l1471c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Free__PORT _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Free__PORTInv _boogie_x))))
axiom ax_l1472c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Free__PORTInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Free__PORT _boogie_x))))
axiom ax_l1473c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Free__PORT _boogie_S) (_boogie_Free__PORT _boogie_x))))
axiom ax_l1474c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Free__PORTInv _boogie_S) (_boogie_Free__PORTInv _boogie_x))))
axiom ax_l1476c1: (forall (_boogie_x : Int), ((_boogie_Free__PORT _boogie_x) = (_boogie_x + 11)))
axiom ax_l1477c1: (forall (_boogie_x : Int), ((_boogie_Free__PORTInv _boogie_x) = (_boogie_x - 11)))
axiom ax_l1478c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 11 1) = (_boogie_Free__PORTInv _boogie_x)))
axiom ax_l1479c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 11) = (_boogie_Free__PORTInv _boogie_x)))
axiom ax_l1485c1: (forall (_boogie_x : Int), ((_boogie_GrandMaster__GLOBALSInv (_boogie_GrandMaster__GLOBALS _boogie_x)) = _boogie_x))
axiom ax_l1486c1: (forall (_boogie_x : Int), ((_boogie_GrandMaster__GLOBALS (_boogie_GrandMaster__GLOBALSInv _boogie_x)) = _boogie_x))
axiom ax_l1488c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_GrandMaster__GLOBALS _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_GrandMaster__GLOBALSInv _boogie_x))))
axiom ax_l1489c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_GrandMaster__GLOBALSInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_GrandMaster__GLOBALS _boogie_x))))
axiom ax_l1490c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_GrandMaster__GLOBALS _boogie_S) (_boogie_GrandMaster__GLOBALS _boogie_x))))
axiom ax_l1491c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_GrandMaster__GLOBALSInv _boogie_S) (_boogie_GrandMaster__GLOBALSInv _boogie_x))))
axiom ax_l1493c1: (forall (_boogie_x : Int), ((_boogie_GrandMaster__GLOBALS _boogie_x) = (_boogie_x + 4)))
axiom ax_l1494c1: (forall (_boogie_x : Int), ((_boogie_GrandMaster__GLOBALSInv _boogie_x) = (_boogie_x - 4)))
axiom ax_l1495c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 4 1) = (_boogie_GrandMaster__GLOBALSInv _boogie_x)))
axiom ax_l1496c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 4) = (_boogie_GrandMaster__GLOBALSInv _boogie_x)))
axiom ax_l1502c1: (forall (_boogie_x : Int), ((_boogie_InputData__DEVICE_EXTENSIONInv (_boogie_InputData__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1503c1: (forall (_boogie_x : Int), ((_boogie_InputData__DEVICE_EXTENSION (_boogie_InputData__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1505c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_InputData__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_InputData__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1506c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_InputData__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_InputData__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1507c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_InputData__DEVICE_EXTENSION _boogie_S) (_boogie_InputData__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1508c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_InputData__DEVICE_EXTENSIONInv _boogie_S) (_boogie_InputData__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1510c1: (forall (_boogie_x : Int), ((_boogie_InputData__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 128)))
axiom ax_l1511c1: (forall (_boogie_x : Int), ((_boogie_InputData__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 128)))
axiom ax_l1512c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 128 1) = (_boogie_InputData__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1513c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 128) = (_boogie_InputData__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1519c1: (forall (_boogie_x : Int), ((_boogie_LegacyDeviceList__GLOBALSInv (_boogie_LegacyDeviceList__GLOBALS _boogie_x)) = _boogie_x))
axiom ax_l1520c1: (forall (_boogie_x : Int), ((_boogie_LegacyDeviceList__GLOBALS (_boogie_LegacyDeviceList__GLOBALSInv _boogie_x)) = _boogie_x))
axiom ax_l1522c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_LegacyDeviceList__GLOBALS _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_LegacyDeviceList__GLOBALSInv _boogie_x))))
axiom ax_l1523c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_LegacyDeviceList__GLOBALSInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_LegacyDeviceList__GLOBALS _boogie_x))))
axiom ax_l1524c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_LegacyDeviceList__GLOBALS _boogie_S) (_boogie_LegacyDeviceList__GLOBALS _boogie_x))))
axiom ax_l1525c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_LegacyDeviceList__GLOBALSInv _boogie_S) (_boogie_LegacyDeviceList__GLOBALSInv _boogie_x))))
axiom ax_l1527c1: (forall (_boogie_x : Int), ((_boogie_LegacyDeviceList__GLOBALS _boogie_x) = (_boogie_x + 888)))
axiom ax_l1528c1: (forall (_boogie_x : Int), ((_boogie_LegacyDeviceList__GLOBALSInv _boogie_x) = (_boogie_x - 888)))
axiom ax_l1529c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 888 1) = (_boogie_LegacyDeviceList__GLOBALSInv _boogie_x)))
axiom ax_l1530c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 888) = (_boogie_LegacyDeviceList__GLOBALSInv _boogie_x)))
axiom ax_l1536c1: (forall (_boogie_x : Int), ((_boogie_Link__DEVICE_EXTENSIONInv (_boogie_Link__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1537c1: (forall (_boogie_x : Int), ((_boogie_Link__DEVICE_EXTENSION (_boogie_Link__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1539c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Link__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Link__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1540c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Link__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Link__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1541c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Link__DEVICE_EXTENSION _boogie_S) (_boogie_Link__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1542c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Link__DEVICE_EXTENSIONInv _boogie_S) (_boogie_Link__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1544c1: (forall (_boogie_x : Int), ((_boogie_Link__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 272)))
axiom ax_l1545c1: (forall (_boogie_x : Int), ((_boogie_Link__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 272)))
axiom ax_l1546c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 272 1) = (_boogie_Link__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1547c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 272) = (_boogie_Link__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1553c1: (forall (_boogie_x : Int), ((_boogie_NumAssocClass__GLOBALSInv (_boogie_NumAssocClass__GLOBALS _boogie_x)) = _boogie_x))
axiom ax_l1554c1: (forall (_boogie_x : Int), ((_boogie_NumAssocClass__GLOBALS (_boogie_NumAssocClass__GLOBALSInv _boogie_x)) = _boogie_x))
axiom ax_l1556c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_NumAssocClass__GLOBALS _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_NumAssocClass__GLOBALSInv _boogie_x))))
axiom ax_l1557c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_NumAssocClass__GLOBALSInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_NumAssocClass__GLOBALS _boogie_x))))
axiom ax_l1558c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_NumAssocClass__GLOBALS _boogie_S) (_boogie_NumAssocClass__GLOBALS _boogie_x))))
axiom ax_l1559c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_NumAssocClass__GLOBALSInv _boogie_S) (_boogie_NumAssocClass__GLOBALSInv _boogie_x))))
axiom ax_l1561c1: (forall (_boogie_x : Int), ((_boogie_NumAssocClass__GLOBALS _boogie_x) = (_boogie_x + 12)))
axiom ax_l1562c1: (forall (_boogie_x : Int), ((_boogie_NumAssocClass__GLOBALSInv _boogie_x) = (_boogie_x - 12)))
axiom ax_l1563c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 12 1) = (_boogie_NumAssocClass__GLOBALSInv _boogie_x)))
axiom ax_l1564c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 12) = (_boogie_NumAssocClass__GLOBALSInv _boogie_x)))
axiom ax_l1570c1: (forall (_boogie_x : Int), ((_boogie_PnP__DEVICE_EXTENSIONInv (_boogie_PnP__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1571c1: (forall (_boogie_x : Int), ((_boogie_PnP__DEVICE_EXTENSION (_boogie_PnP__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1573c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_PnP__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_PnP__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1574c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_PnP__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_PnP__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1575c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_PnP__DEVICE_EXTENSION _boogie_S) (_boogie_PnP__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1576c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_PnP__DEVICE_EXTENSIONInv _boogie_S) (_boogie_PnP__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1578c1: (forall (_boogie_x : Int), ((_boogie_PnP__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 104)))
axiom ax_l1579c1: (forall (_boogie_x : Int), ((_boogie_PnP__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 104)))
axiom ax_l1580c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 104 1) = (_boogie_PnP__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1581c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 104) = (_boogie_PnP__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1587c1: (forall (_boogie_x : Int), ((_boogie_Port__PORTInv (_boogie_Port__PORT _boogie_x)) = _boogie_x))
axiom ax_l1588c1: (forall (_boogie_x : Int), ((_boogie_Port__PORT (_boogie_Port__PORTInv _boogie_x)) = _boogie_x))
axiom ax_l1590c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Port__PORT _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Port__PORTInv _boogie_x))))
axiom ax_l1591c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Port__PORTInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Port__PORT _boogie_x))))
axiom ax_l1592c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Port__PORT _boogie_S) (_boogie_Port__PORT _boogie_x))))
axiom ax_l1593c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Port__PORTInv _boogie_S) (_boogie_Port__PORTInv _boogie_x))))
axiom ax_l1595c1: (forall (_boogie_x : Int), ((_boogie_Port__PORT _boogie_x) = (_boogie_x + 4)))
axiom ax_l1596c1: (forall (_boogie_x : Int), ((_boogie_Port__PORTInv _boogie_x) = (_boogie_x - 4)))
axiom ax_l1597c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 4 1) = (_boogie_Port__PORTInv _boogie_x)))
axiom ax_l1598c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 4) = (_boogie_Port__PORTInv _boogie_x)))
axiom ax_l1604c1: (forall (_boogie_x : Int), ((_boogie_RegistryPath__GLOBALSInv (_boogie_RegistryPath__GLOBALS _boogie_x)) = _boogie_x))
axiom ax_l1605c1: (forall (_boogie_x : Int), ((_boogie_RegistryPath__GLOBALS (_boogie_RegistryPath__GLOBALSInv _boogie_x)) = _boogie_x))
axiom ax_l1607c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_RegistryPath__GLOBALS _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_RegistryPath__GLOBALSInv _boogie_x))))
axiom ax_l1608c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_RegistryPath__GLOBALSInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_RegistryPath__GLOBALS _boogie_x))))
axiom ax_l1609c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_RegistryPath__GLOBALS _boogie_S) (_boogie_RegistryPath__GLOBALS _boogie_x))))
axiom ax_l1610c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_RegistryPath__GLOBALSInv _boogie_S) (_boogie_RegistryPath__GLOBALSInv _boogie_x))))
axiom ax_l1612c1: (forall (_boogie_x : Int), ((_boogie_RegistryPath__GLOBALS _boogie_x) = (_boogie_x + 360)))
axiom ax_l1613c1: (forall (_boogie_x : Int), ((_boogie_RegistryPath__GLOBALSInv _boogie_x) = (_boogie_x - 360)))
axiom ax_l1614c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 360 1) = (_boogie_RegistryPath__GLOBALSInv _boogie_x)))
axiom ax_l1615c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 360) = (_boogie_RegistryPath__GLOBALSInv _boogie_x)))
axiom ax_l1621c1: (forall (_boogie_x : Int), ((_boogie_Self__DEVICE_EXTENSIONInv (_boogie_Self__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1622c1: (forall (_boogie_x : Int), ((_boogie_Self__DEVICE_EXTENSION (_boogie_Self__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1624c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Self__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Self__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1625c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Self__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Self__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1626c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Self__DEVICE_EXTENSION _boogie_S) (_boogie_Self__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1627c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Self__DEVICE_EXTENSIONInv _boogie_S) (_boogie_Self__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1629c1: (forall (_boogie_x : Int), ((_boogie_Self__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 0)))
axiom ax_l1630c1: (forall (_boogie_x : Int), ((_boogie_Self__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 0)))
axiom ax_l1631c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 0 1) = (_boogie_Self__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1632c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 0) = (_boogie_Self__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1638c1: (forall (_boogie_x : Int), ((_boogie_StackSize__DEVICE_OBJECTInv (_boogie_StackSize__DEVICE_OBJECT _boogie_x)) = _boogie_x))
axiom ax_l1639c1: (forall (_boogie_x : Int), ((_boogie_StackSize__DEVICE_OBJECT (_boogie_StackSize__DEVICE_OBJECTInv _boogie_x)) = _boogie_x))
axiom ax_l1641c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_StackSize__DEVICE_OBJECT _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_StackSize__DEVICE_OBJECTInv _boogie_x))))
axiom ax_l1642c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_StackSize__DEVICE_OBJECTInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_StackSize__DEVICE_OBJECT _boogie_x))))
axiom ax_l1643c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_StackSize__DEVICE_OBJECT _boogie_S) (_boogie_StackSize__DEVICE_OBJECT _boogie_x))))
axiom ax_l1644c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_StackSize__DEVICE_OBJECTInv _boogie_S) (_boogie_StackSize__DEVICE_OBJECTInv _boogie_x))))
axiom ax_l1646c1: (forall (_boogie_x : Int), ((_boogie_StackSize__DEVICE_OBJECT _boogie_x) = (_boogie_x + 48)))
axiom ax_l1647c1: (forall (_boogie_x : Int), ((_boogie_StackSize__DEVICE_OBJECTInv _boogie_x) = (_boogie_x - 48)))
axiom ax_l1648c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 48 1) = (_boogie_StackSize__DEVICE_OBJECTInv _boogie_x)))
axiom ax_l1649c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 48) = (_boogie_StackSize__DEVICE_OBJECTInv _boogie_x)))
axiom ax_l1655c1: (forall (_boogie_x : Int), ((_boogie_Started__DEVICE_EXTENSIONInv (_boogie_Started__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1656c1: (forall (_boogie_x : Int), ((_boogie_Started__DEVICE_EXTENSION (_boogie_Started__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1658c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Started__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Started__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1659c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_Started__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_Started__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1660c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Started__DEVICE_EXTENSION _boogie_S) (_boogie_Started__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1661c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_Started__DEVICE_EXTENSIONInv _boogie_S) (_boogie_Started__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1663c1: (forall (_boogie_x : Int), ((_boogie_Started__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 105)))
axiom ax_l1664c1: (forall (_boogie_x : Int), ((_boogie_Started__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 105)))
axiom ax_l1665c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 105 1) = (_boogie_Started__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1666c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 105) = (_boogie_Started__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1672c1: (forall (_boogie_x : Int), ((_boogie_TopPort__DEVICE_EXTENSIONInv (_boogie_TopPort__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1673c1: (forall (_boogie_x : Int), ((_boogie_TopPort__DEVICE_EXTENSION (_boogie_TopPort__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1675c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_TopPort__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_TopPort__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1676c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_TopPort__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_TopPort__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1677c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_TopPort__DEVICE_EXTENSION _boogie_S) (_boogie_TopPort__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1678c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_TopPort__DEVICE_EXTENSIONInv _boogie_S) (_boogie_TopPort__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1680c1: (forall (_boogie_x : Int), ((_boogie_TopPort__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 8)))
axiom ax_l1681c1: (forall (_boogie_x : Int), ((_boogie_TopPort__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 8)))
axiom ax_l1682c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 8 1) = (_boogie_TopPort__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1683c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 8) = (_boogie_TopPort__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1689c1: (forall (_boogie_x : Int), ((_boogie_UnitId__DEVICE_EXTENSIONInv (_boogie_UnitId__DEVICE_EXTENSION _boogie_x)) = _boogie_x))
axiom ax_l1690c1: (forall (_boogie_x : Int), ((_boogie_UnitId__DEVICE_EXTENSION (_boogie_UnitId__DEVICE_EXTENSIONInv _boogie_x)) = _boogie_x))
axiom ax_l1692c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_UnitId__DEVICE_EXTENSION _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_UnitId__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1693c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 (_boogie__S_UnitId__DEVICE_EXTENSIONInv _boogie_S) _boogie_x) = (select1 _boogie_S (_boogie_UnitId__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1694c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_UnitId__DEVICE_EXTENSION _boogie_S) (_boogie_UnitId__DEVICE_EXTENSION _boogie_x))))
axiom ax_l1695c1: (forall (_boogie_x : Int) (_boogie_S : (SMTArray1 Int Prop)), ((select1 _boogie_S _boogie_x) → (select1 (_boogie__S_UnitId__DEVICE_EXTENSIONInv _boogie_S) (_boogie_UnitId__DEVICE_EXTENSIONInv _boogie_x))))
axiom ax_l1697c1: (forall (_boogie_x : Int), ((_boogie_UnitId__DEVICE_EXTENSION _boogie_x) = (_boogie_x + 196)))
axiom ax_l1698c1: (forall (_boogie_x : Int), ((_boogie_UnitId__DEVICE_EXTENSIONInv _boogie_x) = (_boogie_x - 196)))
axiom ax_l1699c1: (forall (_boogie_x : Int), ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_x 196 1) = (_boogie_UnitId__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1700c1: (forall (_boogie_x : Int), ((_boogie_MINUS_LEFT_PTR _boogie_x 1 196) = (_boogie_UnitId__DEVICE_EXTENSIONInv _boogie_x)))
axiom ax_l1702c1: (forall (_boogie_a : Int) (_boogie_b : Int) (_boogie_size : Int), (((_boogie_size * (_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_a _boogie_b _boogie_size)) <= (_boogie_a - _boogie_b)) ∧ ((_boogie_a - _boogie_b) < (_boogie_size * ((_boogie_MINUS_BOTH_PTR_OR_BOTH_INT _boogie_a _boogie_b _boogie_size) + 1)))))
axiom ax_l1706c1: (forall (_boogie_a : Int) (_boogie_a_size : Int) (_boogie_b : Int), ((_boogie_MINUS_LEFT_PTR _boogie_a _boogie_a_size _boogie_b) = (_boogie_a - (_boogie_a_size * _boogie_b))))
axiom ax_l1709c1: (forall (_boogie_a : Int) (_boogie_a_size : Int) (_boogie_b : Int), ((_boogie_PLUS _boogie_a _boogie_a_size _boogie_b) = (_boogie_a + (_boogie_a_size * _boogie_b))))
axiom ax_l1712c1: (forall (_boogie_a : Int) (_boogie_b : Int), ((_boogie_MULT _boogie_a _boogie_b) = (_boogie_a * _boogie_b)))
axiom ax_l1716c1: (forall (_boogie_a : Int) (_boogie_b : Int), (((_boogie_a >= 0) ∧ (_boogie_b > 0)) → (((_boogie_b * (_boogie_DIV _boogie_a _boogie_b)) <= _boogie_a) ∧ (_boogie_a < (_boogie_b * ((_boogie_DIV _boogie_a _boogie_b) + 1))))))
axiom ax_l1720c1: (forall (_boogie_a : Int) (_boogie_b : Int), (((_boogie_a >= 0) ∧ (_boogie_b < 0)) → (((_boogie_b * (_boogie_DIV _boogie_a _boogie_b)) <= _boogie_a) ∧ (_boogie_a < (_boogie_b * ((_boogie_DIV _boogie_a _boogie_b) - 1))))))
axiom ax_l1724c1: (forall (_boogie_a : Int) (_boogie_b : Int), (((_boogie_a < 0) ∧ (_boogie_b > 0)) → (((_boogie_b * (_boogie_DIV _boogie_a _boogie_b)) >= _boogie_a) ∧ (_boogie_a > (_boogie_b * ((_boogie_DIV _boogie_a _boogie_b) - 1))))))
axiom ax_l1728c1: (forall (_boogie_a : Int) (_boogie_b : Int), (((_boogie_a < 0) ∧ (_boogie_b < 0)) → (((_boogie_b * (_boogie_DIV _boogie_a _boogie_b)) >= _boogie_a) ∧ (_boogie_a > (_boogie_b * ((_boogie_DIV _boogie_a _boogie_b) + 1))))))
axiom ax_l1735c1: (_boogie_POW2 1)
axiom ax_l1736c1: (_boogie_POW2 2)
axiom ax_l1737c1: (_boogie_POW2 4)
axiom ax_l1738c1: (_boogie_POW2 8)
axiom ax_l1739c1: (_boogie_POW2 16)
axiom ax_l1740c1: (_boogie_POW2 32)
axiom ax_l1741c1: (_boogie_POW2 64)
axiom ax_l1742c1: (_boogie_POW2 128)
axiom ax_l1743c1: (_boogie_POW2 256)
axiom ax_l1744c1: (_boogie_POW2 512)
axiom ax_l1745c1: (_boogie_POW2 1024)
axiom ax_l1746c1: (_boogie_POW2 2048)
axiom ax_l1747c1: (_boogie_POW2 4096)
axiom ax_l1748c1: (_boogie_POW2 8192)
axiom ax_l1749c1: (_boogie_POW2 16384)
axiom ax_l1750c1: (_boogie_POW2 32768)
axiom ax_l1751c1: (_boogie_POW2 65536)
axiom ax_l1752c1: (_boogie_POW2 131072)
axiom ax_l1753c1: (_boogie_POW2 262144)
axiom ax_l1754c1: (_boogie_POW2 524288)
axiom ax_l1755c1: (_boogie_POW2 1048576)
axiom ax_l1756c1: (_boogie_POW2 2097152)
axiom ax_l1757c1: (_boogie_POW2 4194304)
axiom ax_l1758c1: (_boogie_POW2 8388608)
axiom ax_l1759c1: (_boogie_POW2 16777216)
axiom ax_l1760c1: (_boogie_POW2 33554432)
axiom ax_l1763c1: (forall (_boogie_a : Prop) (_boogie_b : Int) (_boogie_c : Int), (_boogie_a → ((_boogie_choose _boogie_a _boogie_b _boogie_c) = _boogie_b)))
axiom ax_l1764c1: (forall (_boogie_a : Prop) (_boogie_b : Int) (_boogie_c : Int), ((Not _boogie_a) → ((_boogie_choose _boogie_a _boogie_b _boogie_c) = _boogie_c)))
axiom ax_l1767c1: (forall (_boogie_a : Int) (_boogie_b : Int), ((_boogie_a = _boogie_b) → ((_boogie_BIT_BAND _boogie_a _boogie_b) = _boogie_a)))
axiom ax_l1768c1: (forall (_boogie_a : Int) (_boogie_b : Int), ((((_boogie_POW2 _boogie_a) ∧ (_boogie_POW2 _boogie_b)) ∧ (_boogie_a ≠ _boogie_b)) → ((_boogie_BIT_BAND _boogie_a _boogie_b) = 0)))
axiom ax_l1769c1: (forall (_boogie_a : Int) (_boogie_b : Int), (((_boogie_a = 0) ∨ (_boogie_b = 0)) → ((_boogie_BIT_BAND _boogie_a _boogie_b) = 0)))
axiom ax_l1778c1: (forall (_boogie_a : Prop), (_boogie_a = ((_boogie_LIFT _boogie_a) ≠ 0)))
axiom ax_l1781c1: (forall (_boogie_a : Int), ((_boogie_a = 0) → ((_boogie_NOT _boogie_a) ≠ 0)))
axiom ax_l1782c1: (forall (_boogie_a : Int), ((_boogie_a ≠ 0) → ((_boogie_NOT _boogie_a) = 0)))
axiom ax_l1785c1: (forall (_boogie_a : Int), ((_boogie_a = 0) → ((_boogie_NULL_CHECK _boogie_a) ≠ 0)))
axiom ax_l1786c1: (forall (_boogie_a : Int), ((_boogie_a ≠ 0) → ((_boogie_NULL_CHECK _boogie_a) = 0)))
axiom ax_l1843c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int), ((select1 (_boogie_ReachBetweenSet _boogie_f _boogie_x _boogie_z) _boogie_y) = (_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_z)))
axiom ax_l1844c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int), ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_z) → (select1 (_boogie_ReachBetweenSet _boogie_f _boogie_x _boogie_z) _boogie_y)))
axiom ax_l1845c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_z : Int), (_boogie_ReachBetween _boogie_f _boogie_x _boogie_x _boogie_x))
axiom ax_l1853c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int), (_boogie_ReachBetween _boogie_f _boogie_x _boogie_x _boogie_x))
axiom ax_l1857c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int) (_boogie_w : Int), (_boogie_ReachBetween _boogie_f _boogie_x (select1 _boogie_f _boogie_x) (select1 _boogie_f _boogie_x)))
axiom ax_l1860c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int), ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_y) → ((_boogie_x = _boogie_y) ∨ (_boogie_ReachBetween _boogie_f _boogie_x (select1 _boogie_f _boogie_x) _boogie_y))))
axiom ax_l1863c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int), ((((select1 _boogie_f _boogie_x) = _boogie_x) ∧ (_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_y)) → (_boogie_x = _boogie_y)))
axiom ax_l1866c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int), ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_x) → (_boogie_x = _boogie_y)))
axiom ax_l1869c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int), (((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_y) ∧ (_boogie_ReachBetween _boogie_f _boogie_x _boogie_z _boogie_z)) → ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_z) ∨ (_boogie_ReachBetween _boogie_f _boogie_x _boogie_z _boogie_y))))
axiom ax_l1872c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int), ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_z) → ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_y) ∧ (_boogie_ReachBetween _boogie_f _boogie_y _boogie_z _boogie_z))))
axiom ax_l1875c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int), (((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_y) ∧ (_boogie_ReachBetween _boogie_f _boogie_y _boogie_z _boogie_z)) → (_boogie_ReachBetween _boogie_f _boogie_x _boogie_z _boogie_z)))
axiom ax_l1878c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int) (_boogie_w : Int), (((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_z) ∧ (_boogie_ReachBetween _boogie_f _boogie_y _boogie_w _boogie_z)) → ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_w) ∧ (_boogie_ReachBetween _boogie_f _boogie_x _boogie_w _boogie_z))))
axiom ax_l1881c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int) (_boogie_w : Int), (((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_z) ∧ (_boogie_ReachBetween _boogie_f _boogie_x _boogie_w _boogie_y)) → ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_w _boogie_z) ∧ (_boogie_ReachBetween _boogie_f _boogie_w _boogie_y _boogie_z))))
axiom ax_l1885c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_u : Int) (_boogie_x : Int), ((_boogie_ReachBetween _boogie_f _boogie_u _boogie_x _boogie_x) → (_boogie_ReachBetween _boogie_f _boogie_u _boogie_u _boogie_x)))
axiom ax_l1888c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_x : Int) (_boogie_y : Int) (_boogie_z : Int), ((_boogie_ReachAvoiding _boogie_f _boogie_x _boogie_y _boogie_z) = ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_z) ∨ ((_boogie_ReachBetween _boogie_f _boogie_x _boogie_y _boogie_y) ∧ (Not (_boogie_ReachBetween _boogie_f _boogie_x _boogie_z _boogie_z))))))
axiom ax_l1891c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie_u : Int) (_boogie_v : Int) (_boogie_x : Int) (_boogie_p : Int) (_boogie_q : Int), ((_boogie_ReachAvoiding (store1 _boogie_f _boogie_p _boogie_q) _boogie_u _boogie_v _boogie_x) = (((_boogie_ReachAvoiding _boogie_f _boogie_u _boogie_v _boogie_p) ∧ (_boogie_ReachAvoiding _boogie_f _boogie_u _boogie_v _boogie_x)) ∨ ((((_boogie_ReachAvoiding _boogie_f _boogie_u _boogie_p _boogie_x) ∧ (_boogie_p ≠ _boogie_x)) ∧ (_boogie_ReachAvoiding _boogie_f _boogie_q _boogie_v _boogie_p)) ∧ (_boogie_ReachAvoiding _boogie_f _boogie_q _boogie_v _boogie_x)))))
axiom ax_l1896c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie___x : Int), ((select1 (_boogie_Shift_Flink__LIST_ENTRY _boogie_f) _boogie___x) = (select1 _boogie_f (_boogie_Flink__LIST_ENTRY _boogie___x))))
axiom ax_l1897c1: (forall (_boogie_f : (SMTArray1 Int Int)) (_boogie___x : Int) (_boogie___v : Int), ((_boogie_Shift_Flink__LIST_ENTRY (store1 _boogie_f (_boogie_Flink__LIST_ENTRY _boogie___x) _boogie___v)) = (store1 (_boogie_Shift_Flink__LIST_ENTRY _boogie_f) _boogie___x _boogie___v)))
axiom ax_l1900c1: (_boogie_Globals ≠ 0)

-- Implementations

namespace impl__boogie_KeyboardClassUnload

@[simp]
def _boogie_KeyboardClassUnload
  (_boogie__dollar_DriverObject_dollar_1_dollar_2966_24_dollar_KeyboardClassUnload_dollar_41 : Int)
  (_boogie_havoc_stringTemp : Int)
  (_boogie__dollar_DriverObject_dollar_1_dollar_2966_24_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar_ : Int)
  (_boogie__dollar_KbdDebugPrint_arg_2_dollar_1_dollar_ : Int)
  (_boogie__dollar_KbdDebugPrint_arg_2_dollar_19_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_14_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_16_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_18_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_3_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_5_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_7_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_13_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_15_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_17_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_2_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_4_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_6_dollar_ : Int)
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_file_dollar_7_dollar_3007_21_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_irp_dollar_5_dollar_2991_9_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_result_IoAllocateIrp_dollar_3031_31_dollar_8_dollar_ : Int)
  (_boogie__dollar_result_KbdEnableDisablePort_dollar_3033_37_dollar_10_dollar_ : Int)
  (_boogie__dollar_result_ObfDereferenceObject_dollar_3044_12_dollar_11_dollar_ : Int)
  (_boogie__dollar_result_RemoveEntryList_dollar_3055_24_dollar_12_dollar_ : Int)
  (_boogie_LOOP_15_alloc : (SMTArray1 Int _boogie_name))
  (_boogie_LOOP_15_Mem : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_LOOP_15_Res_DEVICE_STACK : (SMTArray1 Int Int))
  (_boogie_LOOP_15_Res_DEV_EXTN : (SMTArray1 Int Int))
  (_boogie_LOOP_15_Res_DEV_OBJ_INIT : (SMTArray1 Int Int))
  (_boogie_LOOP_15_Res_SPIN_LOCK : (SMTArray1 Int Int))
  (_boogie_LOOP_108_alloc : (SMTArray1 Int _boogie_name))
  (_boogie_LOOP_108_Mem : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_LOOP_108_Res_DEVICE_STACK : (SMTArray1 Int Int))
  (_boogie_LOOP_108_Res_DEV_EXTN : (SMTArray1 Int Int))
  (_boogie_LOOP_108_Res_DEV_OBJ_INIT : (SMTArray1 Int Int))
  (_boogie_LOOP_108_Res_SPIN_LOCK : (SMTArray1 Int Int))
  (_boogie_alloc_0 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_Res_DEVICE_STACK_0 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_0 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_0 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_0 : (SMTArray1 Int Int))
  (_boogie_Mem_0 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_1 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie_Res_DEVICE_STACK_1 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_1 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_1 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_1 : (SMTArray1 Int Int))
  (_boogie_Mem_1 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie__dollar_result_RemoveEntryList_dollar_3055_24_dollar_12_dollar__0 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie__dollar_result_ObfDereferenceObject_dollar_3044_12_dollar_11_dollar__0 : Int)
  (_boogie__dollar_result_KbdEnableDisablePort_dollar_3033_37_dollar_10_dollar__0 : Int)
  (_boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar__0 : Int)
  (_boogie__dollar_result_IoAllocateIrp_dollar_3031_31_dollar_8_dollar__0 : Int)
  (_boogie__dollar_irp_dollar_5_dollar_2991_9_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie_havoc_stringTemp_0 : Int)
  (_boogie_alloc_2 : (SMTArray1 Int _boogie_name))
  (_boogie__dollar_RtlAssert_arg_2_dollar_4_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_5_dollar__0 : Int)
  (_boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_2_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_3_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_6_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_7_dollar__0 : Int)
  (_boogie_Mem_2 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2 : Int)
  (_boogie_Mem_3 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 : Int)
  (_boogie_Res_DEVICE_STACK_2 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_2 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_2 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_2 : (SMTArray1 Int Int))
  (_boogie_Mem_4 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_3 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_3 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_3 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_3 : (SMTArray1 Int Int))
  (_boogie_Mem_5 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_6 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_7 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_8 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_4 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_4 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_4 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_4 : (SMTArray1 Int Int))
  (_boogie_Mem_9 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_5 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_5 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_5 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_5 : (SMTArray1 Int Int))
  (_boogie_Mem_10 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_11 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_SPIN_LOCK_6 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_6 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_6 : (SMTArray1 Int Int))
  (_boogie_Res_DEVICE_STACK_6 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_7 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_7 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_7 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_7 : (SMTArray1 Int Int))
  (_boogie_Mem_12 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie_havoc_stringTemp_1 : Int)
  (_boogie_alloc_3 : (SMTArray1 Int _boogie_name))
  (_boogie__dollar_RtlAssert_arg_2_dollar_17_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_18_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_15_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_16_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_13_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_14_dollar__0 : Int)
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_8 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_8 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_8 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_8 : (SMTArray1 Int Int))
  (_boogie_Mem_13 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_4 : (SMTArray1 Int _boogie_name))
  (_boogie_Res_SPIN_LOCK_9 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_9 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_9 : (SMTArray1 Int Int))
  (_boogie_Res_DEVICE_STACK_9 : (SMTArray1 Int Int))
  (_boogie_Mem_14 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_5 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_6 : (SMTArray1 Int _boogie_name))
  (_boogie_alloc_7 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_8 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_9 : (SMTArray1 Int _boogie_name))
  (_boogie_alloc_10 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_11 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_12 : (SMTArray1 Int _boogie_name))
  (_boogie_alloc_13 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_14 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie_alloc_15 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_16 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_17 : (SMTArray1 Int _boogie_name))
  (_boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie_Mem_15 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_18 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_19 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_Mem_16 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_20 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_21 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_2 : Int)
  (_boogie_Mem_17 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_18 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_19 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_20 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_21 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_3 : Int)
  (_boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar__1 : Int)
  (_boogie_Res_DEVICE_STACK_10 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_10 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_10 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_10 : (SMTArray1 Int Int))
  (_boogie_Mem_22 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call7formal__dollar_result_IoAllocateIrp_dollar_20452_0_dollar_1_dollar__0 : Int)
  (_boogie_Res_DEVICE_STACK_11 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_11 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_11 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_11 : (SMTArray1 Int Int))
  (_boogie_Mem_23 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call9formal__dollar_result_KbdEnableDisablePort_dollar_542_0_dollar_1_dollar__0 : Int)
  (_boogie_Res_DEVICE_STACK_12 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_12 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_12 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_12 : (SMTArray1 Int Int))
  (_boogie_Mem_24 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_13 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_13 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_13 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_13 : (SMTArray1 Int Int))
  (_boogie_Mem_25 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_Object_dollar_1_dollar_24931_15_dollar_ObfDereferenceObject_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_14 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_14 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_14 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_14 : (SMTArray1 Int Int))
  (_boogie_Mem_26 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call6formal__dollar_result_ObfDereferenceObject_dollar_24930_0_dollar_1_dollar__0 : Int)
  (_boogie_Res_DEVICE_STACK_15 : (SMTArray1 Int Int))
  (_boogie_Mem_27 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_SPIN_LOCK_15 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_15 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_15 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 : Int)
  (_boogie_Res_DEVICE_STACK_16 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_16 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_16 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_16 : (SMTArray1 Int Int))
  (_boogie_Mem_28 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEV_EXTN_17 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_17 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_17 : (SMTArray1 Int Int))
  (_boogie_Mem_29 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_17 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_18 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_18 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_18 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_18 : (SMTArray1 Int Int))
  (_boogie_Mem_30 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call6formal__dollar_result_RemoveEntryList_dollar_6928_0_dollar_1_dollar__0 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_2 : Int)
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_19 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_19 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_19 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_19 : (SMTArray1 Int Int))
  (_boogie_Mem_31 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_32 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_33 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_34 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_20 : (SMTArray1 Int Int))
  (_boogie_Mem_35 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_SPIN_LOCK_20 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_20 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_20 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_21 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_21 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_21 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_21 : (SMTArray1 Int Int))
  (_boogie_Mem_36 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEV_OBJ_INIT_22 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_22 : (SMTArray1 Int Int))
  (_boogie_Mem_37 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  : Prop := β__boogie_PreconditionGeneratedEntry
  where
  @[simp]
  β__boogie_PreconditionGeneratedEntry :=
    assume (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN (select1 (select1 _boogie_Mem _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assume ((forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT (select1 (select1 _boogie_Mem _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) ∧ ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN 1) _boogie__H_z) → true)))) $
    assume (true → (((select1 (select1 _boogie_Mem _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN (select1 (select1 _boogie_Mem _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assume (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assume (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assume (true → (Not (select1 (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_Link__DEVICE_EXTENSION (select1 (select1 _boogie_Mem _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)))))) $
    goto β__boogie_start
  @[simp]
  β__boogie_start :=
    assume ((select1 _boogie_alloc _boogie__dollar_DriverObject_dollar_1_dollar_2966_24_dollar_KeyboardClassUnload_dollar_41) ≠ _boogie_UNALLOCATED) $
    assert (4 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 4))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc _boogie_x) = (select1 _boogie_alloc_0 _boogie_x)))) $
    assume (((select1 _boogie_alloc _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_0 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assume (_boogie_Mem_0 = _boogie_Mem) $
    assume ((_boogie_Res_DEV_OBJ_INIT_0 = _boogie_Res_DEV_OBJ_INIT) ∧ (_boogie_Res_DEV_EXTN_0 = _boogie_Res_DEV_EXTN)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_0 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN _boogie_r) = (select1 _boogie_Res_DEV_EXTN_0 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_0 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_0 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_0 _boogie_x) = (select1 _boogie_alloc_1 _boogie_x)))) $
    assume (((select1 _boogie_alloc_0 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_1 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assume (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_0 = (select1 (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)))) $
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_0 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_0 (select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_0 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_0 (select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_0 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_0 1) _boogie__H_z) → true))) $
    assert (true → (((select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_0 (select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assert (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assert (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_0 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assert (true → (Not (select1 (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_Link__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)))))) $
    assert (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_0 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_0) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_0 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_0 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_SetTrue))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_SetTrue) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_0 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_0 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_SetTrue))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_SetTrue) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_0 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_0 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_0 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_0 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_0 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    goto β__boogie_label_15_head
  @[simp]
  β__boogie_label_15_head :=
    assume (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_1 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_1 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_1 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_1 (select1 (select1 _boogie_Mem_1 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assume (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_1 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_1 (select1 (select1 _boogie_Mem_1 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_1 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_1 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_1 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_1 1) _boogie__H_z) → true))) $
    assume (true → (((select1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_1 (select1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assume (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assume (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_1 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assume (true → (Not (select1 (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_Link__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)))))) $
    assume (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_1 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1) $
    assume (forall (_boogie_f : Int), (((select1 _boogie_alloc_1 (_boogie_Base _boogie_f)) = _boogie_UNALLOCATED) ∨ ((select1 _boogie_alloc_1 (_boogie_Base _boogie_f)) = (select1 _boogie_alloc_2 (_boogie_Base _boogie_f))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_0 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_1 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_SetTrue))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_SetTrue) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_0 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_1 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_SetTrue))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_SetTrue) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_0 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_1 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_0 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_1 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_1 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_1 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_1 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_1 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_1 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_1 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    goto β__boogie_label_15_true ∧ goto β__boogie_label_15_false
  @[simp]
  β__boogie_label_15_false :=
    assume (Not (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1 ≠ (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    goto β__boogie_label_85_true ∧ goto β__boogie_label_85_false
  @[simp]
  β__boogie_label_85_false :=
    assume ((select1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) = 0) $
    assume (_boogie_Mem_11 = _boogie_Mem_1) $
    assume (_boogie_Res_SPIN_LOCK_6 = _boogie_Res_SPIN_LOCK_1) $
    assume (_boogie_Res_DEV_OBJ_INIT_6 = _boogie_Res_DEV_OBJ_INIT_1) $
    assume (_boogie_Res_DEV_EXTN_6 = _boogie_Res_DEV_EXTN_1) $
    assume (_boogie_Res_DEVICE_STACK_6 = _boogie_Res_DEVICE_STACK_1) $
    goto β__boogie_label_102
  @[simp]
  β__boogie_label_102 :=
    assume (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 = (select1 (select1 _boogie_Mem_11 _boogie_T_Buffer__UNICODE_STRING) (_boogie_Buffer__UNICODE_STRING (_boogie_RegistryPath__GLOBALS _boogie_Globals)))) $
    assume (_boogie_Mem_12 = _boogie_Mem_11) $
    assume ((_boogie_Res_DEV_OBJ_INIT_7 = _boogie_Res_DEV_OBJ_INIT_6) ∧ (_boogie_Res_DEV_EXTN_7 = _boogie_Res_DEV_EXTN_6)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_6 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_6 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_6 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_6 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_11 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_11 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_11 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_11 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_11 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_11 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_11 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    goto β__boogie_label_105_true ∧ goto β__boogie_label_105_false
  @[simp]
  β__boogie_label_105_false :=
    assume ((select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) = 0) $
    assume (_boogie_alloc_4 = _boogie_alloc_2) $
    assume (_boogie_Res_SPIN_LOCK_9 = _boogie_Res_SPIN_LOCK_7) $
    assume (_boogie_Res_DEV_OBJ_INIT_9 = _boogie_Res_DEV_OBJ_INIT_7) $
    assume (_boogie_Res_DEV_EXTN_9 = _boogie_Res_DEV_EXTN_7) $
    assume (_boogie_Res_DEVICE_STACK_9 = _boogie_Res_DEVICE_STACK_7) $
    assume (_boogie_Mem_14 = _boogie_Mem_12) $
    goto β__boogie_label_134
  @[simp]
  β__boogie_label_134 :=
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_4 _boogie_x) = (select1 _boogie_alloc_5 _boogie_x)))) $
    assume (((select1 _boogie_alloc_4 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_5 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_5 _boogie_x) = (select1 _boogie_alloc_6 _boogie_x)))) $
    assume ((select1 _boogie_alloc_6 _boogie_call2formal_new_0) = _boogie_FREED) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 _boogie_Res_DEVICE_STACK_9 _boogie_m) = (select1 _boogie_Res_DEVICE_STACK _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 _boogie_Res_DEV_EXTN_9 _boogie_m) = (select1 _boogie_Res_DEV_EXTN _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 _boogie_Res_DEV_OBJ_INIT_9 _boogie_m) = (select1 _boogie_Res_DEV_OBJ_INIT _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 _boogie_Res_SPIN_LOCK_9 _boogie_m) = (select1 _boogie_Res_SPIN_LOCK _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_A11CHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_A11CHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_A19CHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_A19CHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_A36CHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_A36CHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_A37CHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_A37CHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_A39CHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_A39CHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_A43CHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_A43CHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_A74CHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_A74CHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_AssocClassList__GLOBALS) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_AssocClassList__GLOBALS) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Buffer__UNICODE_STRING) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Buffer__UNICODE_STRING) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_DataIn__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_DataIn__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_DataOut__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_DataOut__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Enabled__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Enabled__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Enabled__PORT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Enabled__PORT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_File__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_File__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_File__PORT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_File__PORT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Flink__LIST_ENTRY) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Flink__LIST_ENTRY) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Free__PORT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Free__PORT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_GrandMaster__GLOBALS) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_GrandMaster__GLOBALS) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_INT4) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_INT4) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_InputData__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_InputData__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_LegacyDeviceList__GLOBALS) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_LegacyDeviceList__GLOBALS) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Link__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Link__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_NumAssocClass__GLOBALS) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_NumAssocClass__GLOBALS) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_PCHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_PCHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_PP_FILE_OBJECT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_PP_FILE_OBJECT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_PVOID) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_PVOID) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_P_DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_P_DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_P_DEVICE_OBJECT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_P_DEVICE_OBJECT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_P_FILE_OBJECT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_P_FILE_OBJECT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_P_IRP) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_P_IRP) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_P_KEYBOARD_INPUT_DATA) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_P_KEYBOARD_INPUT_DATA) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_P_LIST_ENTRY) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_P_LIST_ENTRY) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_P_PORT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_P_PORT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_PnP__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_PnP__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Port__PORT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Port__PORT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_RegistryPath__GLOBALS) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_RegistryPath__GLOBALS) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Self__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Self__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_StackSize__DEVICE_OBJECT) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_StackSize__DEVICE_OBJECT) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_Started__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_Started__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_TopPort__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_TopPort__DEVICE_EXTENSION) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_UCHAR) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_UCHAR) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_UINT4) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_UINT4) _boogie_m)))) $
    assume (forall (_boogie_m : Int), ((((select1 _boogie_alloc_6 (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED) ∧ ((select1 _boogie_alloc (_boogie_Base _boogie_m)) ≠ _boogie_ALLOCATED)) → ((select1 (select1 _boogie_Mem_14 _boogie_T_UnitId__DEVICE_EXTENSION) _boogie_m) = (select1 (select1 _boogie_Mem _boogie_T_UnitId__DEVICE_EXTENSION) _boogie_m)))) $
    assume (_boogie_Res_DEV_OBJ_INIT_22 = _boogie_Res_DEV_OBJ_INIT_9) $
    assume (_boogie_Res_DEV_EXTN_22 = _boogie_Res_DEV_EXTN_9) $
    assume (_boogie_Mem_37 = _boogie_Mem_14) $
    goto β__boogie_GeneratedUnifiedExit
  @[simp]
  β__boogie_GeneratedUnifiedExit :=
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_22 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_37 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_37 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_22 (select1 (select1 _boogie_Mem_37 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert ((forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_22 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_22 (select1 (select1 _boogie_Mem_37 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_37 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_37 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) ∧ ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_22 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_22 1) _boogie__H_z) → true)))) $
    ret
  @[simp]
  β__boogie_label_105_true :=
    assume ((select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) ≠ 0) $
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_7 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_7 (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_7 (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1) _boogie__H_z) → true))) $
    assert (true → (((select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_7 (select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assert (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assert (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_7 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assert (_boogie_Res_DEV_OBJ_INIT_7 = _boogie_Res_DEV_OBJ_INIT_7) $
    assert (_boogie_Res_DEV_EXTN_7 = _boogie_Res_DEV_EXTN_7) $
    assert ((select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) = (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_7 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_7 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_7 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    goto β__boogie_label_108_head
  @[simp]
  β__boogie_label_108_head :=
    assume (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_7 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_7 (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assume (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_7 (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1) _boogie__H_z) → true))) $
    assume (true → (((select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_7 (select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assume (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assume (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_7 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assume (_boogie_Res_DEV_OBJ_INIT_7 = _boogie_Res_DEV_OBJ_INIT_7) $
    assume (_boogie_Res_DEV_EXTN_7 = _boogie_Res_DEV_EXTN_7) $
    assume ((select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) = (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) $
    assume (forall (_boogie_f : Int), (((select1 _boogie_alloc_2 (_boogie_Base _boogie_f)) = _boogie_UNALLOCATED) ∨ ((select1 _boogie_alloc_2 (_boogie_Base _boogie_f)) = (select1 _boogie_alloc_3 (_boogie_Base _boogie_f))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_7 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_7 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_7 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_7 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    goto β__boogie_label_108_true ∧ goto β__boogie_label_108_false
  @[simp]
  β__boogie_label_108_false :=
    assume (Not (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0 < (select1 (select1 _boogie_Mem_12 _boogie_T_NumAssocClass__GLOBALS) (_boogie_NumAssocClass__GLOBALS _boogie_Globals)))) $
    assume (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 = (select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals))) $
    assume (_boogie_Mem_13 = _boogie_Mem_12) $
    assume ((_boogie_Res_DEV_OBJ_INIT_8 = _boogie_Res_DEV_OBJ_INIT_7) ∧ (_boogie_Res_DEV_EXTN_8 = _boogie_Res_DEV_EXTN_7)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_7 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_8 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_7 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_8 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_8 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_7 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_8 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_13 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_13 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_13 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_13 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_13 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_13 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_13 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_alloc_4 = _boogie_alloc_3) $
    assume (_boogie_Res_SPIN_LOCK_9 = _boogie_Res_SPIN_LOCK_8) $
    assume (_boogie_Res_DEV_OBJ_INIT_9 = _boogie_Res_DEV_OBJ_INIT_8) $
    assume (_boogie_Res_DEV_EXTN_9 = _boogie_Res_DEV_EXTN_8) $
    assume (_boogie_Res_DEVICE_STACK_9 = _boogie_Res_DEVICE_STACK_8) $
    assume (_boogie_Mem_14 = _boogie_Mem_13) $
    goto β__boogie_label_134
  @[simp]
  β__boogie_label_108_true :=
    assume (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0 < (select1 (select1 _boogie_Mem_12 _boogie_T_NumAssocClass__GLOBALS) (_boogie_NumAssocClass__GLOBALS _boogie_Globals))) $
    goto β__boogie_label_109_true ∧ goto β__boogie_label_109_false
  @[simp]
  β__boogie_label_109_false :=
    assume (Not ((select1 (select1 _boogie_Mem_12 _boogie_T_Free__PORT) (_boogie_Free__PORT (_boogie_PLUS (select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) 12 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0))) = 1)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_3 _boogie_x) = (select1 _boogie_alloc_7 _boogie_x)))) $
    assume (((select1 _boogie_alloc_3 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_7 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_7 _boogie_x) = (select1 _boogie_alloc_8 _boogie_x)))) $
    assume (((select1 _boogie_alloc_7 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_8 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assume (_boogie_alloc_9 = _boogie_alloc_8) $
    goto β__boogie_label_115_true ∧ goto β__boogie_label_115_false
  @[simp]
  β__boogie_label_115_false :=
    assume ((select1 (select1 _boogie_Mem_12 _boogie_T_Enabled__PORT) (_boogie_Enabled__PORT (_boogie_PLUS (select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) 12 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0))) = 0) $
    assume (_boogie_alloc_12 = _boogie_alloc_9) $
    goto β__boogie_label_121_true ∧ goto β__boogie_label_121_false
  @[simp]
  β__boogie_label_121_false :=
    assume ((select1 (select1 _boogie_Mem_12 _boogie_T_File__PORT) (_boogie_File__PORT (_boogie_PLUS (select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) 12 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0))) = 0) $
    goto β__boogie_label_127
  @[simp]
  β__boogie_label_127 :=
    assume (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_1 = (_boogie_PLUS _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0 1 1)) $
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_7 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_7 (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_7 (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_7 1) _boogie__H_z) → true))) $
    assert (true → (((select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_7 (select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assert (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assert (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_7 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assert (_boogie_Res_DEV_OBJ_INIT_7 = _boogie_Res_DEV_OBJ_INIT_7) $
    assert (_boogie_Res_DEV_EXTN_7 = _boogie_Res_DEV_EXTN_7) $
    assert ((select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY) = (select1 _boogie_Mem_12 _boogie_T_Flink__LIST_ENTRY)) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_7 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_7 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_7 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_7 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_12 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume false $
    assume (_boogie_Res_DEV_OBJ_INIT_22 = _boogie_Res_DEV_OBJ_INIT_7) $
    assume (_boogie_Res_DEV_EXTN_22 = _boogie_Res_DEV_EXTN_7) $
    assume (_boogie_Mem_37 = _boogie_Mem_12) $
    ret
  @[simp]
  β__boogie_label_121_true :=
    assume ((select1 (select1 _boogie_Mem_12 _boogie_T_File__PORT) (_boogie_File__PORT (_boogie_PLUS (select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) 12 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0))) ≠ 0) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_12 _boogie_x) = (select1 _boogie_alloc_13 _boogie_x)))) $
    assume (((select1 _boogie_alloc_12 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_13 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_13 _boogie_x) = (select1 _boogie_alloc_14 _boogie_x)))) $
    assume (((select1 _boogie_alloc_13 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_14 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    goto β__boogie_label_127
  @[simp]
  β__boogie_label_115_true :=
    assume ((select1 (select1 _boogie_Mem_12 _boogie_T_Enabled__PORT) (_boogie_Enabled__PORT (_boogie_PLUS (select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) 12 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0))) ≠ 0) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_9 _boogie_x) = (select1 _boogie_alloc_10 _boogie_x)))) $
    assume (((select1 _boogie_alloc_9 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_10 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_10 _boogie_x) = (select1 _boogie_alloc_11 _boogie_x)))) $
    assume (((select1 _boogie_alloc_10 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_11 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assume (_boogie_alloc_12 = _boogie_alloc_11) $
    goto β__boogie_label_121_true ∧ goto β__boogie_label_121_false
  @[simp]
  β__boogie_label_109_true :=
    assume ((select1 (select1 _boogie_Mem_12 _boogie_T_Free__PORT) (_boogie_Free__PORT (_boogie_PLUS (select1 (select1 _boogie_Mem_12 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) 12 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0))) = 1) $
    assume (_boogie_alloc_9 = _boogie_alloc_3) $
    goto β__boogie_label_115_true ∧ goto β__boogie_label_115_false
  @[simp]
  β__boogie_label_85_true :=
    assume ((select1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) $
    assume (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2 = (select1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) $
    assume (_boogie_Mem_3 = (store1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS (store1 (select1 _boogie_Mem_1 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals) 0))) $
    assume (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 = (select1 (select1 _boogie_Mem_3 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2))) $
    assert ((select1 _boogie_Res_DEV_EXTN_1 _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2) = 1) $
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_1 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_3 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_3 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_1 (select1 (select1 _boogie_Mem_3 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_1 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_1 (select1 (select1 _boogie_Mem_3 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_3 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_3 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_1 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_1 1) _boogie__H_z) → true))) $
    assert (true → (((select1 (select1 _boogie_Mem_3 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_1 (select1 (select1 _boogie_Mem_3 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assert (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_3 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_3 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assert (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_3 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_3 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_3 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_3 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_1 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assert ((select1 _boogie_Res_DEV_OBJ_INIT_1 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0) = 1) $
    assume ((select1 _boogie_Res_DEV_EXTN_2 _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2) = 1) $
    assume (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_2 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_4 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_4 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_2 (select1 (select1 _boogie_Mem_4 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assume (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_2 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_2 (select1 (select1 _boogie_Mem_4 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_4 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_4 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_2 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_2 1) _boogie__H_z) → true))) $
    assume (true → (((select1 (select1 _boogie_Mem_4 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_2 (select1 (select1 _boogie_Mem_4 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assume (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_4 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_4 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assume (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_4 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_4 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_4 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_4 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_2 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assume ((select1 _boogie_Mem_4 _boogie_T_Flink__LIST_ENTRY) = (select1 _boogie_Mem_3 _boogie_T_Flink__LIST_ENTRY)) $
    assume (_boogie_Res_DEV_OBJ_INIT_2 = _boogie_Res_DEV_OBJ_INIT_1) $
    assume (_boogie_Res_DEV_EXTN_2 = _boogie_Res_DEV_EXTN_1) $
    assume ((select1 _boogie_Res_DEV_OBJ_INIT_2 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0) = 1) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_1 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_2 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_1 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_2 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_1 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_2 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_1 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_2 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_4 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_3 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_4 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_3 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_4 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_3 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_4 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_3 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_4 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_3 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_4 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_3 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_4 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_3 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    goto β__boogie_label_91_true ∧ goto β__boogie_label_91_false
  @[simp]
  β__boogie_label_91_false :=
    assume ((select1 (select1 _boogie_Mem_4 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2)) = 0) $
    assume (_boogie_Res_DEVICE_STACK_4 = _boogie_Res_DEVICE_STACK_2) $
    assume (_boogie_Res_DEV_EXTN_4 = _boogie_Res_DEV_EXTN_2) $
    assume (_boogie_Res_DEV_OBJ_INIT_4 = _boogie_Res_DEV_OBJ_INIT_2) $
    assume (_boogie_Res_SPIN_LOCK_4 = _boogie_Res_SPIN_LOCK_2) $
    assume (_boogie_Mem_9 = _boogie_Mem_4) $
    goto β__boogie_label_98
  @[simp]
  β__boogie_label_98 :=
    assume (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 = (select1 (select1 _boogie_Mem_9 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2))) $
    assert (true → (((select1 _boogie_Res_DEV_OBJ_INIT_4 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0) = 1) ∧ ((select1 _boogie_Res_DEV_EXTN_4 (select1 (select1 _boogie_Mem_9 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) = 1))) $
    assume (_boogie_Mem_10 = _boogie_Mem_9) $
    assume (true → (((select1 _boogie_Res_DEV_OBJ_INIT_5 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0) = 0) ∧ ((select1 _boogie_Res_DEV_EXTN_5 (select1 (select1 _boogie_Mem_10 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) = 0))) $
    assume (true → ((_boogie_Res_DEV_OBJ_INIT_5 = (store1 _boogie_Res_DEV_OBJ_INIT_4 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 0)) ∧ (_boogie_Res_DEV_EXTN_5 = (store1 _boogie_Res_DEV_EXTN_4 (select1 (select1 _boogie_Mem_10 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)) 0)))) $
    assume ((Not true) → (((select1 _boogie_Res_DEV_OBJ_INIT_5 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0) = (select1 _boogie_Res_DEV_OBJ_INIT_4 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)) ∧ ((select1 _boogie_Res_DEV_EXTN_5 (select1 (select1 _boogie_Mem_10 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) = (select1 _boogie_Res_DEV_EXTN_4 (select1 (select1 _boogie_Mem_10 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)))))) $
    assume ((Not true) → ((_boogie_Res_DEV_OBJ_INIT_5 = _boogie_Res_DEV_OBJ_INIT_4) ∧ (_boogie_Res_DEV_EXTN_5 = _boogie_Res_DEV_EXTN_4))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_4 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_5 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Singleton (select1 (select1 _boogie_Mem_10 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)) = _boogie_r)) ∨ ((select1 _boogie_Res_DEV_EXTN_4 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_5 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Singleton _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 = _boogie_r)) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_4 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_5 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_4 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_5 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_9 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_9 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_9 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_9 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_9 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_9 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_10 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_9 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_Mem_11 = _boogie_Mem_10) $
    assume (_boogie_Res_SPIN_LOCK_6 = _boogie_Res_SPIN_LOCK_5) $
    assume (_boogie_Res_DEV_OBJ_INIT_6 = _boogie_Res_DEV_OBJ_INIT_5) $
    assume (_boogie_Res_DEV_EXTN_6 = _boogie_Res_DEV_EXTN_5) $
    assume (_boogie_Res_DEVICE_STACK_6 = _boogie_Res_DEVICE_STACK_5) $
    goto β__boogie_label_102
  @[simp]
  β__boogie_label_91_true :=
    assume ((select1 (select1 _boogie_Mem_4 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2)) ≠ 0) $
    assume (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 = (select1 (select1 _boogie_Mem_4 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2))) $
    assume (_boogie_Mem_5 = _boogie_Mem_4) $
    assume ((_boogie_Res_DEV_OBJ_INIT_3 = _boogie_Res_DEV_OBJ_INIT_2) ∧ (_boogie_Res_DEV_EXTN_3 = _boogie_Res_DEV_EXTN_2)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_2 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_3 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_2 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_3 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_2 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_3 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_2 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_3 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_5 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_4 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_5 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_4 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_5 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_4 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_5 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_4 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_5 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_4 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_5 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_4 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_5 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_4 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_Mem_6 = (store1 _boogie_Mem_5 _boogie_T_DataOut__DEVICE_EXTENSION (store1 (select1 _boogie_Mem_5 _boogie_T_DataOut__DEVICE_EXTENSION) (_boogie_DataOut__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2) 0))) $
    assume (_boogie_Mem_7 = (store1 _boogie_Mem_6 _boogie_T_DataIn__DEVICE_EXTENSION (store1 (select1 _boogie_Mem_6 _boogie_T_DataIn__DEVICE_EXTENSION) (_boogie_DataIn__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2) (select1 (select1 _boogie_Mem_6 _boogie_T_DataOut__DEVICE_EXTENSION) (_boogie_DataOut__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2))))) $
    assume (_boogie_Mem_8 = (store1 _boogie_Mem_7 _boogie_T_InputData__DEVICE_EXTENSION (store1 (select1 _boogie_Mem_7 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2) (select1 (select1 _boogie_Mem_7 _boogie_T_DataIn__DEVICE_EXTENSION) (_boogie_DataIn__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2))))) $
    assume (_boogie_Res_DEVICE_STACK_4 = _boogie_Res_DEVICE_STACK_3) $
    assume (_boogie_Res_DEV_EXTN_4 = _boogie_Res_DEV_EXTN_3) $
    assume (_boogie_Res_DEV_OBJ_INIT_4 = _boogie_Res_DEV_OBJ_INIT_3) $
    assume (_boogie_Res_SPIN_LOCK_4 = _boogie_Res_SPIN_LOCK_3) $
    assume (_boogie_Mem_9 = _boogie_Mem_8) $
    goto β__boogie_label_98
  @[simp]
  β__boogie_label_15_true :=
    assume (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1 ≠ (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) $
    assume (_boogie_Mem_2 = (store1 _boogie_Mem_1 _boogie_T_P_FILE_OBJECT (store1 (select1 _boogie_Mem_1 _boogie_T_P_FILE_OBJECT) _boogie_call2formal_new_0 0))) $
    assume (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1 = (_boogie_MINUS_LEFT_PTR _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1 1 272)) $
    goto β__boogie_label_21_true ∧ goto β__boogie_label_21_false
  @[simp]
  β__boogie_label_21_false :=
    assume ((select1 (select1 _boogie_Mem_2 _boogie_T_PnP__DEVICE_EXTENSION) (_boogie_PnP__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) = 0) $
    assume (_boogie_alloc_17 = _boogie_alloc_2) $
    goto β__boogie_label_27_true ∧ goto β__boogie_label_27_false
  @[simp]
  β__boogie_label_27_false :=
    assume ((select1 (select1 _boogie_Mem_2 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) = 0) $
    assume (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_1 = (select1 (select1 _boogie_Mem_2 _boogie_T_Enabled__DEVICE_EXTENSION) (_boogie_Enabled__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1))) $
    assume (_boogie_Mem_15 = (store1 _boogie_Mem_2 _boogie_T_P_FILE_OBJECT (store1 (select1 _boogie_Mem_2 _boogie_T_P_FILE_OBJECT) _boogie_call2formal_new_0 (select1 (select1 _boogie_Mem_2 _boogie_T_File__DEVICE_EXTENSION) (_boogie_File__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1))))) $
    goto β__boogie_label_42_true ∧ goto β__boogie_label_42_false
  @[simp]
  β__boogie_label_42_false :=
    assume ((select1 (select1 _boogie_Mem_15 _boogie_T_File__DEVICE_EXTENSION) (_boogie_File__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) = 0) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_17 _boogie_x) = (select1 _boogie_alloc_18 _boogie_x)))) $
    assume (((select1 _boogie_alloc_17 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_18 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_18 _boogie_x) = (select1 _boogie_alloc_19 _boogie_x)))) $
    assume (((select1 _boogie_alloc_18 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_19 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    goto β__boogie_label_48
  @[simp]
  β__boogie_label_48 :=
    assume (_boogie_Mem_16 = (store1 _boogie_Mem_15 _boogie_T_Enabled__DEVICE_EXTENSION (store1 (select1 _boogie_Mem_15 _boogie_T_Enabled__DEVICE_EXTENSION) (_boogie_Enabled__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1) 0))) $
    assume (_boogie_Mem_21 = _boogie_Mem_16) $
    assume (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_3 = _boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_1) $
    goto β__boogie_label_49_true ∧ goto β__boogie_label_49_false
  @[simp]
  β__boogie_label_49_false :=
    assume (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_3 = 0) $
    assume (_boogie_Res_DEVICE_STACK_13 = _boogie_Res_DEVICE_STACK_1) $
    assume (_boogie_Res_DEV_EXTN_13 = _boogie_Res_DEV_EXTN_1) $
    assume (_boogie_Res_DEV_OBJ_INIT_13 = _boogie_Res_DEV_OBJ_INIT_1) $
    assume (_boogie_Res_SPIN_LOCK_13 = _boogie_Res_SPIN_LOCK_1) $
    assume (_boogie_Mem_25 = _boogie_Mem_21) $
    goto β__boogie_label_62_true ∧ goto β__boogie_label_62_false
  @[simp]
  β__boogie_label_62_false :=
    assume ((select1 (select1 _boogie_Mem_25 _boogie_T_P_FILE_OBJECT) _boogie_call2formal_new_0) = 0) $
    assume (_boogie_Res_DEVICE_STACK_15 = _boogie_Res_DEVICE_STACK_13) $
    assume (_boogie_Mem_27 = _boogie_Mem_25) $
    assume (_boogie_Res_SPIN_LOCK_15 = _boogie_Res_SPIN_LOCK_13) $
    assume (_boogie_Res_DEV_OBJ_INIT_15 = _boogie_Res_DEV_OBJ_INIT_13) $
    assume (_boogie_Res_DEV_EXTN_15 = _boogie_Res_DEV_EXTN_13) $
    goto β__boogie_label_66_true ∧ goto β__boogie_label_66_false
  @[simp]
  β__boogie_label_66_false :=
    assume ((select1 (select1 _boogie_Mem_27 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) = 0) $
    assume (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 = (select1 (select1 _boogie_Mem_27 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1))) $
    assert ((select1 _boogie_Res_DEV_EXTN_15 _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1) = 1) $
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_15 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_27 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_27 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_15 (select1 (select1 _boogie_Mem_27 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_15 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_15 (select1 (select1 _boogie_Mem_27 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_27 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_27 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_15 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_15 1) _boogie__H_z) → true))) $
    assert (true → (((select1 (select1 _boogie_Mem_27 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_15 (select1 (select1 _boogie_Mem_27 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assert (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_27 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_27 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assert (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_27 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_27 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_27 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_27 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_15 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assert ((select1 _boogie_Res_DEV_OBJ_INIT_15 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0) = 1) $
    assume ((select1 _boogie_Res_DEV_EXTN_16 _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1) = 1) $
    assume (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_16 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_28 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_28 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_16 (select1 (select1 _boogie_Mem_28 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assume (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_16 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_16 (select1 (select1 _boogie_Mem_28 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_28 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_28 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_16 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_16 1) _boogie__H_z) → true))) $
    assume (true → (((select1 (select1 _boogie_Mem_28 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_16 (select1 (select1 _boogie_Mem_28 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assume (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_28 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_28 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assume (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_28 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_28 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_28 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_28 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_16 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assume ((select1 _boogie_Mem_28 _boogie_T_Flink__LIST_ENTRY) = (select1 _boogie_Mem_27 _boogie_T_Flink__LIST_ENTRY)) $
    assume (_boogie_Res_DEV_OBJ_INIT_16 = _boogie_Res_DEV_OBJ_INIT_15) $
    assume (_boogie_Res_DEV_EXTN_16 = _boogie_Res_DEV_EXTN_15) $
    assume ((select1 _boogie_Res_DEV_OBJ_INIT_16 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0) = 1) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_15 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_16 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_15 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_16 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_15 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_16 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_15 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_16 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_28 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_27 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_28 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_27 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_28 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_27 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_28 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_27 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_28 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_27 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_28 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_27 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_28 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_27 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_Res_DEV_EXTN_17 = _boogie_Res_DEV_EXTN_16) $
    assume (_boogie_Res_DEV_OBJ_INIT_17 = _boogie_Res_DEV_OBJ_INIT_16) $
    assume (_boogie_Res_SPIN_LOCK_17 = _boogie_Res_SPIN_LOCK_16) $
    assume (_boogie_Mem_29 = _boogie_Mem_28) $
    assume (_boogie_Res_DEVICE_STACK_17 = _boogie_Res_DEVICE_STACK_16) $
    goto β__boogie_label_70
  @[simp]
  β__boogie_label_70 :=
    assume (_boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0 = (_boogie_Link__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) $
    assume ((_boogie_Res_DEV_OBJ_INIT_18 = _boogie_Res_DEV_OBJ_INIT_17) ∧ (_boogie_Res_DEV_EXTN_18 = _boogie_Res_DEV_EXTN_17)) $
    assume ((_boogie_Res_DEV_OBJ_INIT_18 = _boogie_Res_DEV_OBJ_INIT_17) ∧ (_boogie_Res_DEV_EXTN_18 = _boogie_Res_DEV_EXTN_17)) $
    assume ((_boogie_Subset (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_30 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_30 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_29 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_29 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton _boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0))) ∧ (_boogie_Subset (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_29 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_29 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton _boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0)) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_30 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_30 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)))) $
    assume ((select1 (select1 _boogie_Mem_30 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY _boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0)) = (select1 (select1 _boogie_Mem_29 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY _boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ (select1 (_boogie_Empty) _boogie_r)) ∨ ((select1 _boogie_Res_DEVICE_STACK_17 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_18 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ (select1 (_boogie_Empty) _boogie_r)) ∨ ((select1 _boogie_Res_DEV_EXTN_17 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_18 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ (select1 (_boogie_Empty) _boogie_r)) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_17 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_18 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ (select1 (_boogie_Empty) _boogie_r)) ∨ ((select1 _boogie_Res_SPIN_LOCK_17 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_18 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), (((select1 (_boogie_Empty) _boogie__m) ∨ (select1 (_boogie_Empty) _boogie__m)) ∨ ((select1 (select1 _boogie_Mem_30 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_29 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), (((select1 (_boogie_Empty) _boogie__m) ∨ (select1 (_boogie_Empty) _boogie__m)) ∨ ((select1 (select1 _boogie_Mem_30 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_29 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), (((select1 (_boogie_Empty) _boogie__m) ∨ (select1 (_boogie_Empty) _boogie__m)) ∨ ((select1 (select1 _boogie_Mem_30 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_29 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), (((select1 (_boogie_Empty) _boogie__m) ∨ (select1 (_boogie_Empty) _boogie__m)) ∨ ((select1 (select1 _boogie_Mem_30 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_29 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), (((select1 (_boogie_Empty) _boogie__m) ∨ (select1 (_boogie_Empty) _boogie__m)) ∨ ((select1 (select1 _boogie_Mem_30 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_29 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), (((select1 (_boogie_Empty) _boogie__m) ∨ (select1 (_boogie_Empty) _boogie__m)) ∨ ((select1 (select1 _boogie_Mem_30 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_29 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), (((select1 (_boogie_Empty) _boogie__m) ∨ (select1 (_boogie_Empty) _boogie__m)) ∨ ((select1 (select1 _boogie_Mem_30 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_29 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_2 = (select1 (select1 _boogie_Mem_30 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1))) $
    goto β__boogie_label_74_true ∧ goto β__boogie_label_74_false
  @[simp]
  β__boogie_label_74_false :=
    assume ((select1 (select1 _boogie_Mem_30 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) = 0) $
    assume (_boogie_Res_DEVICE_STACK_20 = _boogie_Res_DEVICE_STACK_18) $
    assume (_boogie_Mem_35 = _boogie_Mem_30) $
    assume (_boogie_Res_SPIN_LOCK_20 = _boogie_Res_SPIN_LOCK_18) $
    assume (_boogie_Res_DEV_OBJ_INIT_20 = _boogie_Res_DEV_OBJ_INIT_18) $
    assume (_boogie_Res_DEV_EXTN_20 = _boogie_Res_DEV_EXTN_18) $
    goto β__boogie_label_81
  @[simp]
  β__boogie_label_81 :=
    assume (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 = (select1 (select1 _boogie_Mem_35 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1))) $
    assert (true → (((select1 _boogie_Res_DEV_OBJ_INIT_20 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0) = 1) ∧ ((select1 _boogie_Res_DEV_EXTN_20 (select1 (select1 _boogie_Mem_35 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) = 1))) $
    assume (_boogie_Mem_36 = _boogie_Mem_35) $
    assume (true → (((select1 _boogie_Res_DEV_OBJ_INIT_21 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0) = 0) ∧ ((select1 _boogie_Res_DEV_EXTN_21 (select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) = 0))) $
    assume (true → ((_boogie_Res_DEV_OBJ_INIT_21 = (store1 _boogie_Res_DEV_OBJ_INIT_20 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 0)) ∧ (_boogie_Res_DEV_EXTN_21 = (store1 _boogie_Res_DEV_EXTN_20 (select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)) 0)))) $
    assume ((Not true) → (((select1 _boogie_Res_DEV_OBJ_INIT_21 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0) = (select1 _boogie_Res_DEV_OBJ_INIT_20 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)) ∧ ((select1 _boogie_Res_DEV_EXTN_21 (select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) = (select1 _boogie_Res_DEV_EXTN_20 (select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)))))) $
    assume ((Not true) → ((_boogie_Res_DEV_OBJ_INIT_21 = _boogie_Res_DEV_OBJ_INIT_20) ∧ (_boogie_Res_DEV_EXTN_21 = _boogie_Res_DEV_EXTN_20))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_20 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_21 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Singleton (select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0)) = _boogie_r)) ∨ ((select1 _boogie_Res_DEV_EXTN_20 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_21 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Union (_boogie_Empty) (_boogie_Empty)) (_boogie_Singleton _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0))) ∧ (forall (_boogie_r : Int), (((select1 (_boogie_Empty) _boogie_r) ∨ (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 = _boogie_r)) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_20 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_21 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_20 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_21 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_35 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_35 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_35 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_35 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_35 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_35 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_35 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_21 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_36 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_21 (select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_21 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_21 (select1 (select1 _boogie_Mem_36 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_36 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_21 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_21 1) _boogie__H_z) → true))) $
    assert (true → (((select1 (select1 _boogie_Mem_36 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_21 (select1 (select1 _boogie_Mem_36 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assert (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assert (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_21 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assert (true → (Not (select1 (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_Link__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_36 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)))))) $
    assert (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_36 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_2) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_0 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_21 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_SetTrue))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_SetTrue) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_0 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_21 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_SetTrue))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_SetTrue) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_0 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_21 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_0 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_21 _boogie_r))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_36 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_0 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume false $
    assume (_boogie_Res_DEV_OBJ_INIT_22 = _boogie_Res_DEV_OBJ_INIT_21) $
    assume (_boogie_Res_DEV_EXTN_22 = _boogie_Res_DEV_EXTN_21) $
    assume (_boogie_Mem_37 = _boogie_Mem_36) $
    ret
  @[simp]
  β__boogie_label_74_true :=
    assume ((select1 (select1 _boogie_Mem_30 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) ≠ 0) $
    assume (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 = (select1 (select1 _boogie_Mem_30 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1))) $
    assume (_boogie_Mem_31 = _boogie_Mem_30) $
    assume ((_boogie_Res_DEV_OBJ_INIT_19 = _boogie_Res_DEV_OBJ_INIT_18) ∧ (_boogie_Res_DEV_EXTN_19 = _boogie_Res_DEV_EXTN_18)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_18 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_19 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_18 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_19 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_18 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_19 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_18 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_19 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_31 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_30 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_31 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_30 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_31 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_30 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_31 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_30 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_31 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_30 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_31 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_30 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_31 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_30 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_Mem_32 = (store1 _boogie_Mem_31 _boogie_T_DataOut__DEVICE_EXTENSION (store1 (select1 _boogie_Mem_31 _boogie_T_DataOut__DEVICE_EXTENSION) (_boogie_DataOut__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1) 0))) $
    assume (_boogie_Mem_33 = (store1 _boogie_Mem_32 _boogie_T_DataIn__DEVICE_EXTENSION (store1 (select1 _boogie_Mem_32 _boogie_T_DataIn__DEVICE_EXTENSION) (_boogie_DataIn__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1) (select1 (select1 _boogie_Mem_32 _boogie_T_DataOut__DEVICE_EXTENSION) (_boogie_DataOut__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1))))) $
    assume (_boogie_Mem_34 = (store1 _boogie_Mem_33 _boogie_T_InputData__DEVICE_EXTENSION (store1 (select1 _boogie_Mem_33 _boogie_T_InputData__DEVICE_EXTENSION) (_boogie_InputData__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1) (select1 (select1 _boogie_Mem_33 _boogie_T_DataIn__DEVICE_EXTENSION) (_boogie_DataIn__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1))))) $
    assume (_boogie_Res_DEVICE_STACK_20 = _boogie_Res_DEVICE_STACK_19) $
    assume (_boogie_Mem_35 = _boogie_Mem_34) $
    assume (_boogie_Res_SPIN_LOCK_20 = _boogie_Res_SPIN_LOCK_19) $
    assume (_boogie_Res_DEV_OBJ_INIT_20 = _boogie_Res_DEV_OBJ_INIT_19) $
    assume (_boogie_Res_DEV_EXTN_20 = _boogie_Res_DEV_EXTN_19) $
    goto β__boogie_label_81
  @[simp]
  β__boogie_label_66_true :=
    assume ((select1 (select1 _boogie_Mem_27 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) $
    assume (_boogie_Res_DEV_EXTN_17 = _boogie_Res_DEV_EXTN_15) $
    assume (_boogie_Res_DEV_OBJ_INIT_17 = _boogie_Res_DEV_OBJ_INIT_15) $
    assume (_boogie_Res_SPIN_LOCK_17 = _boogie_Res_SPIN_LOCK_15) $
    assume (_boogie_Mem_29 = _boogie_Mem_27) $
    assume (_boogie_Res_DEVICE_STACK_17 = _boogie_Res_DEVICE_STACK_15) $
    goto β__boogie_label_70
  @[simp]
  β__boogie_label_62_true :=
    assume ((select1 (select1 _boogie_Mem_25 _boogie_T_P_FILE_OBJECT) _boogie_call2formal_new_0) ≠ 0) $
    assume (_boogie_call0formal__dollar_Object_dollar_1_dollar_24931_15_dollar_ObfDereferenceObject_dollar_41_0 = (select1 (select1 _boogie_Mem_25 _boogie_T_P_FILE_OBJECT) _boogie_call2formal_new_0)) $
    assume (_boogie_Mem_26 = _boogie_Mem_25) $
    assume ((_boogie_Res_DEV_OBJ_INIT_14 = _boogie_Res_DEV_OBJ_INIT_13) ∧ (_boogie_Res_DEV_EXTN_14 = _boogie_Res_DEV_EXTN_13)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_13 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_14 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_13 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_14 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_13 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_14 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_13 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_14 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_26 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_25 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_26 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_25 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_26 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_25 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_26 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_25 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_26 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_25 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_26 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_25 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_26 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_25 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_Res_DEVICE_STACK_15 = _boogie_Res_DEVICE_STACK_14) $
    assume (_boogie_Mem_27 = _boogie_Mem_26) $
    assume (_boogie_Res_SPIN_LOCK_15 = _boogie_Res_SPIN_LOCK_14) $
    assume (_boogie_Res_DEV_OBJ_INIT_15 = _boogie_Res_DEV_OBJ_INIT_14) $
    assume (_boogie_Res_DEV_EXTN_15 = _boogie_Res_DEV_EXTN_14) $
    goto β__boogie_label_66_true ∧ goto β__boogie_label_66_false
  @[simp]
  β__boogie_label_49_true :=
    assume (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_3 ≠ 0) $
    assume (_boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar__1 = (_boogie_PLUS (select1 (select1 _boogie_Mem_21 _boogie_T_StackSize__DEVICE_OBJECT) (_boogie_StackSize__DEVICE_OBJECT (select1 (select1 _boogie_Mem_21 _boogie_T_TopPort__DEVICE_EXTENSION) (_boogie_TopPort__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)))) 1 1)) $
    assume (_boogie_Mem_22 = _boogie_Mem_21) $
    assume ((_boogie_Res_DEV_OBJ_INIT_10 = _boogie_Res_DEV_OBJ_INIT_1) ∧ (_boogie_Res_DEV_EXTN_10 = _boogie_Res_DEV_EXTN_1)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_1 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_10 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_1 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_10 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_1 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_10 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_1 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_10 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_22 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_21 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_22 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_21 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_22 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_21 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_22 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_21 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_22 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_21 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_22 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_21 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_22 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_21 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    goto β__boogie_label_55_true ∧ goto β__boogie_label_55_false
  @[simp]
  β__boogie_label_55_false :=
    assume (_boogie_call7formal__dollar_result_IoAllocateIrp_dollar_20452_0_dollar_1_dollar__0 = 0) $
    assume (_boogie_Res_DEVICE_STACK_13 = _boogie_Res_DEVICE_STACK_10) $
    assume (_boogie_Res_DEV_EXTN_13 = _boogie_Res_DEV_EXTN_10) $
    assume (_boogie_Res_DEV_OBJ_INIT_13 = _boogie_Res_DEV_OBJ_INIT_10) $
    assume (_boogie_Res_SPIN_LOCK_13 = _boogie_Res_SPIN_LOCK_10) $
    assume (_boogie_Mem_25 = _boogie_Mem_22) $
    goto β__boogie_label_62_true ∧ goto β__boogie_label_62_false
  @[simp]
  β__boogie_label_55_true :=
    assume (_boogie_call7formal__dollar_result_IoAllocateIrp_dollar_20452_0_dollar_1_dollar__0 ≠ 0) $
    assert (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_10 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_22 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_22 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_10 (select1 (select1 _boogie_Mem_22 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assert (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_10 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_10 (select1 (select1 _boogie_Mem_22 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_22 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_22 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assert ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_10 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_10 1) _boogie__H_z) → true))) $
    assert (true → (((select1 (select1 _boogie_Mem_22 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_10 (select1 (select1 _boogie_Mem_22 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assert (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assert (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_10 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assert (true → (Not (select1 (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_Link__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_22 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)))))) $
    assume (forall (_boogie__H_x : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_OBJ_INIT_11 1) _boogie__H_x) → (((select1 (select1 _boogie_Mem_23 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_23 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x)))) = _boogie__H_x) ∧ ((select1 _boogie_Res_DEV_EXTN_11 (select1 (select1 _boogie_Mem_23 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT _boogie__H_x))) = 1)))) $
    assume (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_11 1) _boogie__H_z) → (((select1 _boogie_Res_DEV_OBJ_INIT_11 (select1 (select1 _boogie_Mem_23 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z))) = 1) ∧ ((select1 (select1 _boogie_Mem_23 _boogie_T_DeviceExtension__DEVICE_OBJECT) (_boogie_DeviceExtension__DEVICE_OBJECT (select1 (select1 _boogie_Mem_23 _boogie_T_Self__DEVICE_EXTENSION) (_boogie_Self__DEVICE_EXTENSION _boogie__H_z)))) = _boogie__H_z)))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Inverse _boogie_Res_DEV_EXTN_11 1)) ∧ (forall (_boogie__H_z : Int), ((select1 (_boogie_Inverse _boogie_Res_DEV_EXTN_11 1) _boogie__H_z) → true))) $
    assume (true → (((select1 (select1 _boogie_Mem_23 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) → ((select1 _boogie_Res_DEV_EXTN_11 (select1 (select1 _boogie_Mem_23 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals))) = 1))) $
    assume (true → (select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) $
    assume (true → ((_boogie_Subset (_boogie_Empty) (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) ∧ (forall (_boogie__H_y : Int), ((select1 (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) _boogie__H_y) → ((_boogie__H_y = (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) ∨ ((select1 _boogie_Res_DEV_EXTN_11 (_boogie_MINUS_LEFT_PTR _boogie__H_y 1 (_boogie_Link__DEVICE_EXTENSION 0))) = 1)))))) $
    assume (true → (Not (select1 (_boogie_Difference (_boogie_ReachBetweenSet (_boogie_Shift_Flink__LIST_ENTRY (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY)) (select1 (select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY) (_boogie_Flink__LIST_ENTRY (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals)) (_boogie_Singleton (_boogie_LegacyDeviceList__GLOBALS _boogie_Globals))) (_boogie_Link__DEVICE_EXTENSION (select1 (select1 _boogie_Mem_23 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)))))) $
    assume ((select1 _boogie_Mem_23 _boogie_T_Flink__LIST_ENTRY) = (select1 _boogie_Mem_22 _boogie_T_Flink__LIST_ENTRY)) $
    assume (_boogie_Res_DEV_OBJ_INIT_11 = _boogie_Res_DEV_OBJ_INIT_10) $
    assume (_boogie_Res_DEV_EXTN_11 = _boogie_Res_DEV_EXTN_10) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_10 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_11 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_10 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_11 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_10 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_11 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_10 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_11 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_23 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_22 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_23 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_22 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_23 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_22 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_23 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_22 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_23 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_22 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_23 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_22 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_23 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_22 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_Mem_24 = _boogie_Mem_23) $
    assume ((_boogie_Res_DEV_OBJ_INIT_12 = _boogie_Res_DEV_OBJ_INIT_11) ∧ (_boogie_Res_DEV_EXTN_12 = _boogie_Res_DEV_EXTN_11)) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEVICE_STACK_11 _boogie_r) = (select1 _boogie_Res_DEVICE_STACK_12 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_EXTN_11 _boogie_r) = (select1 _boogie_Res_DEV_EXTN_12 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_DEV_OBJ_INIT_11 _boogie_r) = (select1 _boogie_Res_DEV_OBJ_INIT_12 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie_r : Int), ((select1 (_boogie_Empty) _boogie_r) ∨ ((select1 _boogie_Res_SPIN_LOCK_11 _boogie_r) = (select1 _boogie_Res_SPIN_LOCK_12 _boogie_r))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_24 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m) = (select1 (select1 _boogie_Mem_23 _boogie_T_MinorFunction__IO_STACK_LOCATION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_24 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m) = (select1 (select1 _boogie_Mem_23 _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_24 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_23 _boogie_T_DeviceExtension__DEVICE_OBJECT) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_24 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_23 _boogie_T_Self__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_24 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m) = (select1 (select1 _boogie_Mem_23 _boogie_T_Started__DEVICE_EXTENSION) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_24 _boogie_T_GrandMaster__GLOBALS) _boogie__m) = (select1 (select1 _boogie_Mem_23 _boogie_T_GrandMaster__GLOBALS) _boogie__m))))) $
    assume ((_boogie_Subset (_boogie_Empty) (_boogie_Union (_boogie_Empty) (_boogie_Empty))) ∧ (forall (_boogie__m : Int), ((select1 (_boogie_Empty) _boogie__m) ∨ ((select1 (select1 _boogie_Mem_24 _boogie_T_P_DEVICE_OBJECT) _boogie__m) = (select1 (select1 _boogie_Mem_23 _boogie_T_P_DEVICE_OBJECT) _boogie__m))))) $
    assume (_boogie_Res_DEVICE_STACK_13 = _boogie_Res_DEVICE_STACK_12) $
    assume (_boogie_Res_DEV_EXTN_13 = _boogie_Res_DEV_EXTN_12) $
    assume (_boogie_Res_DEV_OBJ_INIT_13 = _boogie_Res_DEV_OBJ_INIT_12) $
    assume (_boogie_Res_SPIN_LOCK_13 = _boogie_Res_SPIN_LOCK_12) $
    assume (_boogie_Mem_25 = _boogie_Mem_24) $
    goto β__boogie_label_62_true ∧ goto β__boogie_label_62_false
  @[simp]
  β__boogie_label_42_true :=
    assume ((select1 (select1 _boogie_Mem_15 _boogie_T_File__DEVICE_EXTENSION) (_boogie_File__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) ≠ 0) $
    goto β__boogie_label_48
  @[simp]
  β__boogie_label_27_true :=
    assume ((select1 (select1 _boogie_Mem_2 _boogie_T_GrandMaster__GLOBALS) (_boogie_GrandMaster__GLOBALS _boogie_Globals)) ≠ 0) $
    assume (_boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1 = (_boogie_PLUS (select1 (select1 _boogie_Mem_2 _boogie_T_AssocClassList__GLOBALS) (_boogie_AssocClassList__GLOBALS _boogie_Globals)) 12 (select1 (select1 _boogie_Mem_2 _boogie_T_UnitId__DEVICE_EXTENSION) (_boogie_UnitId__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)))) $
    goto β__boogie_label_29_true ∧ goto β__boogie_label_29_false
  @[simp]
  β__boogie_label_29_false :=
    assume (Not ((select1 (select1 _boogie_Mem_2 _boogie_T_Port__PORT) (_boogie_Port__PORT _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1)) = _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_17 _boogie_x) = (select1 _boogie_alloc_20 _boogie_x)))) $
    assume (((select1 _boogie_alloc_17 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_20 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_20 _boogie_x) = (select1 _boogie_alloc_21 _boogie_x)))) $
    assume (((select1 _boogie_alloc_20 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_21 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    goto β__boogie_label_35
  @[simp]
  β__boogie_label_35 :=
    assume (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_2 = (select1 (select1 _boogie_Mem_2 _boogie_T_Enabled__PORT) (_boogie_Enabled__PORT _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1))) $
    assume (_boogie_Mem_17 = (store1 _boogie_Mem_2 _boogie_T_P_FILE_OBJECT (store1 (select1 _boogie_Mem_2 _boogie_T_P_FILE_OBJECT) _boogie_call2formal_new_0 (select1 (select1 _boogie_Mem_2 _boogie_T_File__PORT) (_boogie_File__PORT _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1))))) $
    assume (_boogie_Mem_18 = (store1 _boogie_Mem_17 _boogie_T_Enabled__PORT (store1 (select1 _boogie_Mem_17 _boogie_T_Enabled__PORT) (_boogie_Enabled__PORT _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1) 0))) $
    assume (_boogie_Mem_19 = (store1 _boogie_Mem_18 _boogie_T_File__PORT (store1 (select1 _boogie_Mem_18 _boogie_T_File__PORT) (_boogie_File__PORT _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1) 0))) $
    assume (_boogie_Mem_20 = (store1 _boogie_Mem_19 _boogie_T_Free__PORT (store1 (select1 _boogie_Mem_19 _boogie_T_Free__PORT) (_boogie_Free__PORT _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1) 1))) $
    assume (_boogie_Mem_21 = _boogie_Mem_20) $
    assume (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_3 = _boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_2) $
    goto β__boogie_label_49_true ∧ goto β__boogie_label_49_false
  @[simp]
  β__boogie_label_29_true :=
    assume ((select1 (select1 _boogie_Mem_2 _boogie_T_Port__PORT) (_boogie_Port__PORT _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1)) = _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1) $
    goto β__boogie_label_35
  @[simp]
  β__boogie_label_21_true :=
    assume ((select1 (select1 _boogie_Mem_2 _boogie_T_PnP__DEVICE_EXTENSION) (_boogie_PnP__DEVICE_EXTENSION _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1)) ≠ 0) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_2 _boogie_x) = (select1 _boogie_alloc_15 _boogie_x)))) $
    assume (((select1 _boogie_alloc_2 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_15 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assert (1 >= 0) $
    assume (_boogie_call2formal_new_0 > 0) $
    assume (forall (_boogie_x : Int), (((_boogie_call2formal_new_0 <= _boogie_x) ∧ (_boogie_x < (_boogie_call2formal_new_0 + 1))) → ((_boogie_Base _boogie_x) = _boogie_call2formal_new_0))) $
    assume (forall (_boogie_x : Int), ((_boogie_x = _boogie_call2formal_new_0) ∨ ((select1 _boogie_alloc_15 _boogie_x) = (select1 _boogie_alloc_16 _boogie_x)))) $
    assume (((select1 _boogie_alloc_15 _boogie_call2formal_new_0) = _boogie_UNALLOCATED) ∧ ((select1 _boogie_alloc_16 _boogie_call2formal_new_0) = _boogie_ALLOCATED)) $
    assume (_boogie_alloc_17 = _boogie_alloc_16) $
    goto β__boogie_label_27_true ∧ goto β__boogie_label_27_false

theorem _boogie_KeyboardClassUnload_correct
  (_boogie__dollar_DriverObject_dollar_1_dollar_2966_24_dollar_KeyboardClassUnload_dollar_41 : Int)
  (_boogie_havoc_stringTemp : Int)
  (_boogie__dollar_DriverObject_dollar_1_dollar_2966_24_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar_ : Int)
  (_boogie__dollar_KbdDebugPrint_arg_2_dollar_1_dollar_ : Int)
  (_boogie__dollar_KbdDebugPrint_arg_2_dollar_19_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_14_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_16_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_18_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_3_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_5_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_7_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_13_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_15_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_17_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_2_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_4_dollar_ : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_6_dollar_ : Int)
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_file_dollar_7_dollar_3007_21_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_irp_dollar_5_dollar_2991_9_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4 : Int)
  (_boogie__dollar_result_IoAllocateIrp_dollar_3031_31_dollar_8_dollar_ : Int)
  (_boogie__dollar_result_KbdEnableDisablePort_dollar_3033_37_dollar_10_dollar_ : Int)
  (_boogie__dollar_result_ObfDereferenceObject_dollar_3044_12_dollar_11_dollar_ : Int)
  (_boogie__dollar_result_RemoveEntryList_dollar_3055_24_dollar_12_dollar_ : Int)
  (_boogie_LOOP_15_alloc : (SMTArray1 Int _boogie_name))
  (_boogie_LOOP_15_Mem : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_LOOP_15_Res_DEVICE_STACK : (SMTArray1 Int Int))
  (_boogie_LOOP_15_Res_DEV_EXTN : (SMTArray1 Int Int))
  (_boogie_LOOP_15_Res_DEV_OBJ_INIT : (SMTArray1 Int Int))
  (_boogie_LOOP_15_Res_SPIN_LOCK : (SMTArray1 Int Int))
  (_boogie_LOOP_108_alloc : (SMTArray1 Int _boogie_name))
  (_boogie_LOOP_108_Mem : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_LOOP_108_Res_DEVICE_STACK : (SMTArray1 Int Int))
  (_boogie_LOOP_108_Res_DEV_EXTN : (SMTArray1 Int Int))
  (_boogie_LOOP_108_Res_DEV_OBJ_INIT : (SMTArray1 Int Int))
  (_boogie_LOOP_108_Res_SPIN_LOCK : (SMTArray1 Int Int))
  (_boogie_alloc_0 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_Res_DEVICE_STACK_0 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_0 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_0 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_0 : (SMTArray1 Int Int))
  (_boogie_Mem_0 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_1 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie_Res_DEVICE_STACK_1 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_1 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_1 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_1 : (SMTArray1 Int Int))
  (_boogie_Mem_1 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie__dollar_result_RemoveEntryList_dollar_3055_24_dollar_12_dollar__0 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie__dollar_result_ObfDereferenceObject_dollar_3044_12_dollar_11_dollar__0 : Int)
  (_boogie__dollar_result_KbdEnableDisablePort_dollar_3033_37_dollar_10_dollar__0 : Int)
  (_boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar__0 : Int)
  (_boogie__dollar_result_IoAllocateIrp_dollar_3031_31_dollar_8_dollar__0 : Int)
  (_boogie__dollar_irp_dollar_5_dollar_2991_9_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie_havoc_stringTemp_0 : Int)
  (_boogie_alloc_2 : (SMTArray1 Int _boogie_name))
  (_boogie__dollar_RtlAssert_arg_2_dollar_4_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_5_dollar__0 : Int)
  (_boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_2_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_3_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_6_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_7_dollar__0 : Int)
  (_boogie_Mem_2 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2 : Int)
  (_boogie_Mem_3 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 : Int)
  (_boogie_Res_DEVICE_STACK_2 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_2 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_2 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_2 : (SMTArray1 Int Int))
  (_boogie_Mem_4 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_3 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_3 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_3 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_3 : (SMTArray1 Int Int))
  (_boogie_Mem_5 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_6 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_7 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_8 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_4 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_4 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_4 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_4 : (SMTArray1 Int Int))
  (_boogie_Mem_9 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_5 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_5 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_5 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_5 : (SMTArray1 Int Int))
  (_boogie_Mem_10 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_11 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_SPIN_LOCK_6 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_6 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_6 : (SMTArray1 Int Int))
  (_boogie_Res_DEVICE_STACK_6 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_7 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_7 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_7 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_7 : (SMTArray1 Int Int))
  (_boogie_Mem_12 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0 : Int)
  (_boogie_havoc_stringTemp_1 : Int)
  (_boogie_alloc_3 : (SMTArray1 Int _boogie_name))
  (_boogie__dollar_RtlAssert_arg_2_dollar_17_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_18_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_15_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_16_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_2_dollar_13_dollar__0 : Int)
  (_boogie__dollar_RtlAssert_arg_1_dollar_14_dollar__0 : Int)
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_8 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_8 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_8 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_8 : (SMTArray1 Int Int))
  (_boogie_Mem_13 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_4 : (SMTArray1 Int _boogie_name))
  (_boogie_Res_SPIN_LOCK_9 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_9 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_9 : (SMTArray1 Int Int))
  (_boogie_Res_DEVICE_STACK_9 : (SMTArray1 Int Int))
  (_boogie_Mem_14 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_5 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_6 : (SMTArray1 Int _boogie_name))
  (_boogie_alloc_7 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_8 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_9 : (SMTArray1 Int _boogie_name))
  (_boogie_alloc_10 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_11 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_12 : (SMTArray1 Int _boogie_name))
  (_boogie_alloc_13 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_14 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie_alloc_15 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_16 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_17 : (SMTArray1 Int _boogie_name))
  (_boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_1 : Int)
  (_boogie_Mem_15 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_18 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_19 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_Mem_16 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_alloc_20 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie_alloc_21 : (SMTArray1 Int _boogie_name))
  (_boogie_call2formal_new_0 : Int)
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_2 : Int)
  (_boogie_Mem_17 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_18 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_19 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_20 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_21 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_3 : Int)
  (_boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar__1 : Int)
  (_boogie_Res_DEVICE_STACK_10 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_10 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_10 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_10 : (SMTArray1 Int Int))
  (_boogie_Mem_22 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call7formal__dollar_result_IoAllocateIrp_dollar_20452_0_dollar_1_dollar__0 : Int)
  (_boogie_Res_DEVICE_STACK_11 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_11 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_11 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_11 : (SMTArray1 Int Int))
  (_boogie_Mem_23 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call9formal__dollar_result_KbdEnableDisablePort_dollar_542_0_dollar_1_dollar__0 : Int)
  (_boogie_Res_DEVICE_STACK_12 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_12 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_12 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_12 : (SMTArray1 Int Int))
  (_boogie_Mem_24 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_13 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_13 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_13 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_13 : (SMTArray1 Int Int))
  (_boogie_Mem_25 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call0formal__dollar_Object_dollar_1_dollar_24931_15_dollar_ObfDereferenceObject_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_14 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_14 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_14 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_14 : (SMTArray1 Int Int))
  (_boogie_Mem_26 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call6formal__dollar_result_ObfDereferenceObject_dollar_24930_0_dollar_1_dollar__0 : Int)
  (_boogie_Res_DEVICE_STACK_15 : (SMTArray1 Int Int))
  (_boogie_Mem_27 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_SPIN_LOCK_15 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_15 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_15 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 : Int)
  (_boogie_Res_DEVICE_STACK_16 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_16 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_16 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_16 : (SMTArray1 Int Int))
  (_boogie_Mem_28 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEV_EXTN_17 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_17 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_17 : (SMTArray1 Int Int))
  (_boogie_Mem_29 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_17 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_18 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_18 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_18 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_18 : (SMTArray1 Int Int))
  (_boogie_Mem_30 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_call6formal__dollar_result_RemoveEntryList_dollar_6928_0_dollar_1_dollar__0 : Int)
  (_boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_2 : Int)
  (_boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 : Int)
  (_boogie_Res_DEVICE_STACK_19 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_19 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_19 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_19 : (SMTArray1 Int Int))
  (_boogie_Mem_31 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_32 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_33 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Mem_34 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEVICE_STACK_20 : (SMTArray1 Int Int))
  (_boogie_Mem_35 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_SPIN_LOCK_20 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_20 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_20 : (SMTArray1 Int Int))
  (_boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 : Int)
  (_boogie_Res_DEVICE_STACK_21 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_21 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_OBJ_INIT_21 : (SMTArray1 Int Int))
  (_boogie_Res_SPIN_LOCK_21 : (SMTArray1 Int Int))
  (_boogie_Mem_36 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  (_boogie_Res_DEV_OBJ_INIT_22 : (SMTArray1 Int Int))
  (_boogie_Res_DEV_EXTN_22 : (SMTArray1 Int Int))
  (_boogie_Mem_37 : (SMTArray1 _boogie_name (SMTArray1 Int Int)))
  : _boogie_KeyboardClassUnload _boogie_UNALLOCATED _boogie_ALLOCATED _boogie_FREED _boogie_T_Self__DEVICE_EXTENSION _boogie_T_TopPort__DEVICE_EXTENSION _boogie_T_PnP__DEVICE_EXTENSION _boogie_T_Started__DEVICE_EXTENSION _boogie_T_InputData__DEVICE_EXTENSION _boogie_T_DataIn__DEVICE_EXTENSION _boogie_T_DataOut__DEVICE_EXTENSION _boogie_T_UnitId__DEVICE_EXTENSION _boogie_T_Link__DEVICE_EXTENSION _boogie_T_File__DEVICE_EXTENSION _boogie_T_Enabled__DEVICE_EXTENSION _boogie_T_DeviceExtension__DEVICE_OBJECT _boogie_T_StackSize__DEVICE_OBJECT _boogie_T_GrandMaster__GLOBALS _boogie_T_AssocClassList__GLOBALS _boogie_T_NumAssocClass__GLOBALS _boogie_T_RegistryPath__GLOBALS _boogie_T_LegacyDeviceList__GLOBALS _boogie_T_MinorFunction__IO_STACK_LOCATION _boogie_T_Flink__LIST_ENTRY _boogie_T_File__PORT _boogie_T_Port__PORT _boogie_T_Enabled__PORT _boogie_T_Free__PORT _boogie_T_Buffer__UNICODE_STRING _boogie_T_CurrentStackLocation___unnamed_4_f19b65c1 _boogie_T_A11CHAR _boogie_T_A19CHAR _boogie_T_A36CHAR _boogie_T_A37CHAR _boogie_T_A39CHAR _boogie_T_A43CHAR _boogie_T_A74CHAR _boogie_T_INT4 _boogie_T_PCHAR _boogie_T_PP_FILE_OBJECT _boogie_T_PVOID _boogie_T_P_DEVICE_EXTENSION _boogie_T_P_DEVICE_OBJECT _boogie_T_P_FILE_OBJECT _boogie_T_P_IRP _boogie_T_P_KEYBOARD_INPUT_DATA _boogie_T_P_LIST_ENTRY _boogie_T_P_PORT _boogie_T_UCHAR _boogie_T_UINT4 _boogie_Globals _boogie_alloc _boogie_Mem _boogie_Res_DEVICE_STACK _boogie_Res_DEV_EXTN _boogie_Res_DEV_OBJ_INIT _boogie_Res_SPIN_LOCK _boogie__dollar_DriverObject_dollar_1_dollar_2966_24_dollar_KeyboardClassUnload_dollar_41 _boogie_havoc_stringTemp _boogie__dollar_DriverObject_dollar_1_dollar_2966_24_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar_ _boogie__dollar_KbdDebugPrint_arg_2_dollar_1_dollar_ _boogie__dollar_KbdDebugPrint_arg_2_dollar_19_dollar_ _boogie__dollar_RtlAssert_arg_1_dollar_14_dollar_ _boogie__dollar_RtlAssert_arg_1_dollar_16_dollar_ _boogie__dollar_RtlAssert_arg_1_dollar_18_dollar_ _boogie__dollar_RtlAssert_arg_1_dollar_3_dollar_ _boogie__dollar_RtlAssert_arg_1_dollar_5_dollar_ _boogie__dollar_RtlAssert_arg_1_dollar_7_dollar_ _boogie__dollar_RtlAssert_arg_2_dollar_13_dollar_ _boogie__dollar_RtlAssert_arg_2_dollar_15_dollar_ _boogie__dollar_RtlAssert_arg_2_dollar_17_dollar_ _boogie__dollar_RtlAssert_arg_2_dollar_2_dollar_ _boogie__dollar_RtlAssert_arg_2_dollar_4_dollar_ _boogie__dollar_RtlAssert_arg_2_dollar_6_dollar_ _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_file_dollar_7_dollar_3007_21_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_irp_dollar_5_dollar_2991_9_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4 _boogie__dollar_result_IoAllocateIrp_dollar_3031_31_dollar_8_dollar_ _boogie__dollar_result_KbdEnableDisablePort_dollar_3033_37_dollar_10_dollar_ _boogie__dollar_result_ObfDereferenceObject_dollar_3044_12_dollar_11_dollar_ _boogie__dollar_result_RemoveEntryList_dollar_3055_24_dollar_12_dollar_ _boogie_LOOP_15_alloc _boogie_LOOP_15_Mem _boogie_LOOP_15_Res_DEVICE_STACK _boogie_LOOP_15_Res_DEV_EXTN _boogie_LOOP_15_Res_DEV_OBJ_INIT _boogie_LOOP_15_Res_SPIN_LOCK _boogie_LOOP_108_alloc _boogie_LOOP_108_Mem _boogie_LOOP_108_Res_DEVICE_STACK _boogie_LOOP_108_Res_DEV_EXTN _boogie_LOOP_108_Res_DEV_OBJ_INIT _boogie_LOOP_108_Res_SPIN_LOCK _boogie_alloc_0 _boogie_call2formal_new_0 _boogie_Res_DEVICE_STACK_0 _boogie_Res_DEV_EXTN_0 _boogie_Res_DEV_OBJ_INIT_0 _boogie_Res_SPIN_LOCK_0 _boogie_Mem_0 _boogie_alloc_1 _boogie_call2formal_new_0 _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_0 _boogie_Res_DEVICE_STACK_1 _boogie_Res_DEV_EXTN_1 _boogie_Res_DEV_OBJ_INIT_1 _boogie_Res_SPIN_LOCK_1 _boogie_Mem_1 _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_0 _boogie__dollar_result_RemoveEntryList_dollar_3055_24_dollar_12_dollar__0 _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_1 _boogie__dollar_result_ObfDereferenceObject_dollar_3044_12_dollar_11_dollar__0 _boogie__dollar_result_KbdEnableDisablePort_dollar_3033_37_dollar_10_dollar__0 _boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar__0 _boogie__dollar_result_IoAllocateIrp_dollar_3031_31_dollar_8_dollar__0 _boogie__dollar_irp_dollar_5_dollar_2991_9_dollar_KeyboardClassUnload_dollar_4_0 _boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_0 _boogie_havoc_stringTemp_0 _boogie_alloc_2 _boogie__dollar_RtlAssert_arg_2_dollar_4_dollar__0 _boogie__dollar_RtlAssert_arg_1_dollar_5_dollar__0 _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_0 _boogie__dollar_RtlAssert_arg_2_dollar_2_dollar__0 _boogie__dollar_RtlAssert_arg_1_dollar_3_dollar__0 _boogie__dollar_RtlAssert_arg_2_dollar_6_dollar__0 _boogie__dollar_RtlAssert_arg_1_dollar_7_dollar__0 _boogie_Mem_2 _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_1 _boogie__dollar_data_dollar_3_dollar_2989_22_dollar_KeyboardClassUnload_dollar_4_2 _boogie_Mem_3 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 _boogie_Res_DEVICE_STACK_2 _boogie_Res_DEV_EXTN_2 _boogie_Res_DEV_OBJ_INIT_2 _boogie_Res_SPIN_LOCK_2 _boogie_Mem_4 _boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 _boogie_Res_DEVICE_STACK_3 _boogie_Res_DEV_EXTN_3 _boogie_Res_DEV_OBJ_INIT_3 _boogie_Res_SPIN_LOCK_3 _boogie_Mem_5 _boogie_Mem_6 _boogie_Mem_7 _boogie_Mem_8 _boogie_Res_DEVICE_STACK_4 _boogie_Res_DEV_EXTN_4 _boogie_Res_DEV_OBJ_INIT_4 _boogie_Res_SPIN_LOCK_4 _boogie_Mem_9 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 _boogie_Res_DEVICE_STACK_5 _boogie_Res_DEV_EXTN_5 _boogie_Res_DEV_OBJ_INIT_5 _boogie_Res_SPIN_LOCK_5 _boogie_Mem_10 _boogie_Mem_11 _boogie_Res_SPIN_LOCK_6 _boogie_Res_DEV_OBJ_INIT_6 _boogie_Res_DEV_EXTN_6 _boogie_Res_DEVICE_STACK_6 _boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 _boogie_Res_DEVICE_STACK_7 _boogie_Res_DEV_EXTN_7 _boogie_Res_DEV_OBJ_INIT_7 _boogie_Res_SPIN_LOCK_7 _boogie_Mem_12 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_0 _boogie_havoc_stringTemp_1 _boogie_alloc_3 _boogie__dollar_RtlAssert_arg_2_dollar_17_dollar__0 _boogie__dollar_RtlAssert_arg_1_dollar_18_dollar__0 _boogie__dollar_RtlAssert_arg_2_dollar_15_dollar__0 _boogie__dollar_RtlAssert_arg_1_dollar_16_dollar__0 _boogie__dollar_RtlAssert_arg_2_dollar_13_dollar__0 _boogie__dollar_RtlAssert_arg_1_dollar_14_dollar__0 _boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 _boogie_Res_DEVICE_STACK_8 _boogie_Res_DEV_EXTN_8 _boogie_Res_DEV_OBJ_INIT_8 _boogie_Res_SPIN_LOCK_8 _boogie_Mem_13 _boogie_alloc_4 _boogie_Res_SPIN_LOCK_9 _boogie_Res_DEV_OBJ_INIT_9 _boogie_Res_DEV_EXTN_9 _boogie_Res_DEVICE_STACK_9 _boogie_Mem_14 _boogie_alloc_5 _boogie_call2formal_new_0 _boogie_alloc_6 _boogie_alloc_7 _boogie_call2formal_new_0 _boogie_alloc_8 _boogie_call2formal_new_0 _boogie_alloc_9 _boogie_alloc_10 _boogie_call2formal_new_0 _boogie_alloc_11 _boogie_call2formal_new_0 _boogie_alloc_12 _boogie_alloc_13 _boogie_call2formal_new_0 _boogie_alloc_14 _boogie_call2formal_new_0 _boogie__dollar_i_dollar_8_dollar_3075_14_dollar_KeyboardClassUnload_dollar_4_1 _boogie_alloc_15 _boogie_call2formal_new_0 _boogie_alloc_16 _boogie_call2formal_new_0 _boogie_alloc_17 _boogie__dollar_port_dollar_4_dollar_2990_10_dollar_KeyboardClassUnload_dollar_4_1 _boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_1 _boogie_Mem_15 _boogie_alloc_18 _boogie_call2formal_new_0 _boogie_alloc_19 _boogie_call2formal_new_0 _boogie_Mem_16 _boogie_alloc_20 _boogie_call2formal_new_0 _boogie_alloc_21 _boogie_call2formal_new_0 _boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_2 _boogie_Mem_17 _boogie_Mem_18 _boogie_Mem_19 _boogie_Mem_20 _boogie_Mem_21 _boogie__dollar_enabled_dollar_6_dollar_3006_16_dollar_KeyboardClassUnload_dollar_4_3 _boogie__dollar_IoAllocateIrp_arg_1_dollar_9_dollar__1 _boogie_Res_DEVICE_STACK_10 _boogie_Res_DEV_EXTN_10 _boogie_Res_DEV_OBJ_INIT_10 _boogie_Res_SPIN_LOCK_10 _boogie_Mem_22 _boogie_call7formal__dollar_result_IoAllocateIrp_dollar_20452_0_dollar_1_dollar__0 _boogie_Res_DEVICE_STACK_11 _boogie_Res_DEV_EXTN_11 _boogie_Res_DEV_OBJ_INIT_11 _boogie_Res_SPIN_LOCK_11 _boogie_Mem_23 _boogie_call9formal__dollar_result_KbdEnableDisablePort_dollar_542_0_dollar_1_dollar__0 _boogie_Res_DEVICE_STACK_12 _boogie_Res_DEV_EXTN_12 _boogie_Res_DEV_OBJ_INIT_12 _boogie_Res_SPIN_LOCK_12 _boogie_Mem_24 _boogie_Res_DEVICE_STACK_13 _boogie_Res_DEV_EXTN_13 _boogie_Res_DEV_OBJ_INIT_13 _boogie_Res_SPIN_LOCK_13 _boogie_Mem_25 _boogie_call0formal__dollar_Object_dollar_1_dollar_24931_15_dollar_ObfDereferenceObject_dollar_41_0 _boogie_Res_DEVICE_STACK_14 _boogie_Res_DEV_EXTN_14 _boogie_Res_DEV_OBJ_INIT_14 _boogie_Res_SPIN_LOCK_14 _boogie_Mem_26 _boogie_call6formal__dollar_result_ObfDereferenceObject_dollar_24930_0_dollar_1_dollar__0 _boogie_Res_DEVICE_STACK_15 _boogie_Mem_27 _boogie_Res_SPIN_LOCK_15 _boogie_Res_DEV_OBJ_INIT_15 _boogie_Res_DEV_EXTN_15 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_1080_28_dollar_KeyboardClassCleanupQueue_dollar_121_0 _boogie_Res_DEVICE_STACK_16 _boogie_Res_DEV_EXTN_16 _boogie_Res_DEV_OBJ_INIT_16 _boogie_Res_SPIN_LOCK_16 _boogie_Mem_28 _boogie_Res_DEV_EXTN_17 _boogie_Res_DEV_OBJ_INIT_17 _boogie_Res_SPIN_LOCK_17 _boogie_Mem_29 _boogie_Res_DEVICE_STACK_17 _boogie_call0formal__dollar_Entry_dollar_1_dollar_6929_19_dollar_RemoveEntryList_dollar_41_0 _boogie_Res_DEVICE_STACK_18 _boogie_Res_DEV_EXTN_18 _boogie_Res_DEV_OBJ_INIT_18 _boogie_Res_SPIN_LOCK_18 _boogie_Mem_30 _boogie_call6formal__dollar_result_RemoveEntryList_dollar_6928_0_dollar_1_dollar__0 _boogie__dollar_entry_dollar_2_dollar_2988_16_dollar_KeyboardClassUnload_dollar_4_2 _boogie_call0formal__dollar_P_dollar_1_dollar_14901_35_dollar_ExFreePoolWithTag_dollar_81_0 _boogie_Res_DEVICE_STACK_19 _boogie_Res_DEV_EXTN_19 _boogie_Res_DEV_OBJ_INIT_19 _boogie_Res_SPIN_LOCK_19 _boogie_Mem_31 _boogie_Mem_32 _boogie_Mem_33 _boogie_Mem_34 _boogie_Res_DEVICE_STACK_20 _boogie_Mem_35 _boogie_Res_SPIN_LOCK_20 _boogie_Res_DEV_OBJ_INIT_20 _boogie_Res_DEV_EXTN_20 _boogie_call0formal__dollar_DeviceObject_dollar_1_dollar_21328_67_dollar_IoDeleteDevice_dollar_41_0 _boogie_Res_DEVICE_STACK_21 _boogie_Res_DEV_EXTN_21 _boogie_Res_DEV_OBJ_INIT_21 _boogie_Res_SPIN_LOCK_21 _boogie_Mem_36 _boogie_Res_DEV_OBJ_INIT_22 _boogie_Res_DEV_EXTN_22 _boogie_Mem_37 := by
    sorry

end impl__boogie_KeyboardClassUnload

end KeyboardClassUnload
