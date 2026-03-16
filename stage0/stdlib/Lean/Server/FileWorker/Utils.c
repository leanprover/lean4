// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: public import Lean.Language.Lean.Types public import Lean.Server.Snapshots public import Lean.Server.AsyncList
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_mono_ms_now();
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object*);
static const lean_closure_object l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
static lean_once_cell_t l_Lean_Server_FileWorker_RpcSession_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__0;
static lean_once_cell_t l_Lean_Server_FileWorker_RpcSession_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__1;
static lean_once_cell_t l_Lean_Server_FileWorker_RpcSession_new___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new();
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0(lean_object* v_stx_1_, lean_object* v_parserState_2_, lean_object* v_nextCmdSnap_x3f_3_, lean_object* v_result_4_){
_start:
{
lean_object* v_cmdState_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_28_; 
v_cmdState_5_ = lean_ctor_get(v_result_4_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_result_4_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; 
v_unused_29_ = lean_ctor_get(v_result_4_, 0);
lean_dec(v_unused_29_);
v___x_7_ = v_result_4_;
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_cmdState_5_);
lean_dec(v_result_4_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___y_11_; 
v___x_9_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_9_, 0, v_stx_1_);
lean_ctor_set(v___x_9_, 1, v_parserState_2_);
lean_ctor_set(v___x_9_, 2, v_cmdState_5_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3_) == 0)
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(2);
v___y_11_ = v___x_16_;
goto v___jp_10_;
}
else
{
lean_object* v_val_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_27_; 
v_val_17_ = lean_ctor_get(v_nextCmdSnap_x3f_3_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v_nextCmdSnap_x3f_3_);
if (v_isSharedCheck_27_ == 0)
{
v___x_19_ = v_nextCmdSnap_x3f_3_;
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_val_17_);
lean_dec(v_nextCmdSnap_x3f_3_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v_task_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
v_task_21_ = lean_ctor_get(v_val_17_, 3);
lean_inc_ref(v_task_21_);
lean_dec(v_val_17_);
v___x_22_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go), 1, 0);
v___x_23_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_21_, v___x_22_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_23_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
v___y_11_ = v___x_25_;
goto v___jp_10_;
}
}
}
v___jp_10_:
{
lean_object* v___x_13_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___y_11_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_13_ = v___x_7_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v___y_11_);
v___x_13_ = v_reuseFailAlloc_15_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object* v_cmdParsed_30_){
_start:
{
lean_object* v_elabSnap_31_; lean_object* v_resultSnap_32_; lean_object* v_stx_33_; lean_object* v_parserState_34_; lean_object* v_nextCmdSnap_x3f_35_; lean_object* v_task_36_; lean_object* v___f_37_; lean_object* v___x_38_; 
v_elabSnap_31_ = lean_ctor_get(v_cmdParsed_30_, 3);
v_resultSnap_32_ = lean_ctor_get(v_elabSnap_31_, 2);
lean_inc_ref(v_resultSnap_32_);
v_stx_33_ = lean_ctor_get(v_cmdParsed_30_, 1);
lean_inc(v_stx_33_);
v_parserState_34_ = lean_ctor_get(v_cmdParsed_30_, 2);
lean_inc_ref(v_parserState_34_);
v_nextCmdSnap_x3f_35_ = lean_ctor_get(v_cmdParsed_30_, 4);
lean_inc(v_nextCmdSnap_x3f_35_);
lean_dec_ref(v_cmdParsed_30_);
v_task_36_ = lean_ctor_get(v_resultSnap_32_, 3);
lean_inc_ref(v_task_36_);
lean_dec_ref(v_resultSnap_32_);
v___f_37_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0), 4, 3);
lean_closure_set(v___f_37_, 0, v_stx_33_);
lean_closure_set(v___f_37_, 1, v_parserState_34_);
lean_closure_set(v___f_37_, 2, v_nextCmdSnap_x3f_35_);
v___x_38_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_37_, v_task_36_);
return v___x_38_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1));
v___x_43_ = lean_task_pure(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(lean_object* v_stx_44_, lean_object* v_parserState_45_, lean_object* v_headerProcessed_46_){
_start:
{
lean_object* v_result_x3f_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_77_; 
v_result_x3f_47_ = lean_ctor_get(v_headerProcessed_46_, 2);
v_isSharedCheck_77_ = !lean_is_exclusive(v_headerProcessed_46_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; lean_object* v_unused_79_; 
v_unused_78_ = lean_ctor_get(v_headerProcessed_46_, 1);
lean_dec(v_unused_78_);
v_unused_79_ = lean_ctor_get(v_headerProcessed_46_, 0);
lean_dec(v_unused_79_);
v___x_49_ = v_headerProcessed_46_;
v_isShared_50_ = v_isSharedCheck_77_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_result_x3f_47_);
lean_dec(v_headerProcessed_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_77_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
if (lean_obj_tag(v_result_x3f_47_) == 1)
{
lean_object* v_val_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_75_; 
v_val_51_ = lean_ctor_get(v_result_x3f_47_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_result_x3f_47_);
if (v_isSharedCheck_75_ == 0)
{
v___x_53_ = v_result_x3f_47_;
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_val_51_);
lean_dec(v_result_x3f_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_firstCmdSnap_55_; lean_object* v_cmdState_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_74_; 
v_firstCmdSnap_55_ = lean_ctor_get(v_val_51_, 1);
v_cmdState_56_ = lean_ctor_get(v_val_51_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v_val_51_);
if (v_isSharedCheck_74_ == 0)
{
v___x_58_ = v_val_51_;
v_isShared_59_ = v_isSharedCheck_74_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_firstCmdSnap_55_);
lean_inc(v_cmdState_56_);
lean_dec(v_val_51_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_74_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v_task_60_; lean_object* v___x_62_; 
v_task_60_ = lean_ctor_get(v_firstCmdSnap_55_, 3);
lean_inc_ref(v_task_60_);
lean_dec_ref(v_firstCmdSnap_55_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v_cmdState_56_);
lean_ctor_set(v___x_49_, 1, v_parserState_45_);
lean_ctor_set(v___x_49_, 0, v_stx_44_);
v___x_62_ = v___x_49_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_stx_44_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_parserState_45_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v_cmdState_56_);
v___x_62_ = v_reuseFailAlloc_73_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0));
v___x_64_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_60_, v___x_63_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_64_);
v___x_66_ = v___x_53_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_72_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_68_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_66_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_68_ = v___x_58_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_71_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
v___x_70_ = lean_task_pure(v___x_69_);
return v___x_70_;
}
}
}
}
}
}
else
{
lean_object* v___x_76_; 
lean_del_object(v___x_49_);
lean_dec(v_result_x3f_47_);
lean_dec_ref(v_parserState_45_);
lean_dec(v_stx_44_);
v___x_76_ = lean_obj_once(&l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2, &l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2_once, _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object* v_initSnap_80_){
_start:
{
lean_object* v_result_x3f_81_; 
v_result_x3f_81_ = lean_ctor_get(v_initSnap_80_, 4);
lean_inc(v_result_x3f_81_);
if (lean_obj_tag(v_result_x3f_81_) == 1)
{
lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_95_; 
v_val_82_ = lean_ctor_get(v_result_x3f_81_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_result_x3f_81_);
if (v_isSharedCheck_95_ == 0)
{
v___x_84_ = v_result_x3f_81_;
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_dec(v_result_x3f_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_processedSnap_86_; lean_object* v_stx_87_; lean_object* v_parserState_88_; lean_object* v_task_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v_processedSnap_86_ = lean_ctor_get(v_val_82_, 1);
lean_inc_ref(v_processedSnap_86_);
v_stx_87_ = lean_ctor_get(v_initSnap_80_, 3);
lean_inc(v_stx_87_);
lean_dec_ref(v_initSnap_80_);
v_parserState_88_ = lean_ctor_get(v_val_82_, 0);
lean_inc_ref(v_parserState_88_);
lean_dec(v_val_82_);
v_task_89_ = lean_ctor_get(v_processedSnap_86_, 3);
lean_inc_ref(v_task_89_);
lean_dec_ref(v_processedSnap_86_);
v___f_90_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0), 3, 2);
lean_closure_set(v___f_90_, 0, v_stx_87_);
lean_closure_set(v___f_90_, 1, v_parserState_88_);
v___x_91_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_89_, v___f_90_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_91_);
v___x_93_ = v___x_84_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_result_x3f_81_);
lean_dec_ref(v_initSnap_80_);
v___x_96_ = lean_box(2);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore___private__1(lean_object* v_initSnap_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_initSnap_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object* v_ed_99_){
_start:
{
lean_object* v_toEditableDocumentCore_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_111_; 
v_toEditableDocumentCore_100_ = lean_ctor_get(v_ed_99_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v_ed_99_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v_ed_99_, 1);
lean_dec(v_unused_112_);
v___x_102_ = v_ed_99_;
v_isShared_103_ = v_isSharedCheck_111_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_toEditableDocumentCore_100_);
lean_dec(v_ed_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_111_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_meta_104_; lean_object* v_uri_105_; lean_object* v_version_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v_meta_104_ = lean_ctor_get(v_toEditableDocumentCore_100_, 0);
lean_inc_ref(v_meta_104_);
lean_dec_ref(v_toEditableDocumentCore_100_);
v_uri_105_ = lean_ctor_get(v_meta_104_, 0);
lean_inc_ref(v_uri_105_);
v_version_106_ = lean_ctor_get(v_meta_104_, 2);
lean_inc(v_version_106_);
lean_dec_ref(v_meta_104_);
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_version_106_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_107_);
lean_ctor_set(v___x_102_, 0, v_uri_105_);
v___x_109_ = v___x_102_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_uri_105_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_unsigned_to_nat(30000u);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__0, &l_Lean_Server_FileWorker_RpcSession_new___closed__0_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__2(void){
_start:
{
size_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = ((size_t)0ULL);
v___x_118_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__1, &l_Lean_Server_FileWorker_RpcSession_new___closed__1_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1);
v___x_119_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_ctor_set_usize(v___x_119_, 2, v___x_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(){
_start:
{
size_t v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((size_t)8ULL);
v___x_122_ = lean_io_get_random_bytes(v___x_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_138_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_138_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_138_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_138_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; uint64_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_127_ = lean_io_mono_ms_now();
v___x_128_ = l_ByteArray_toUInt64LE_x21(v_a_123_);
lean_dec(v_a_123_);
v___x_129_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__2, &l_Lean_Server_FileWorker_RpcSession_new___closed__2_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__2);
v___x_130_ = lean_unsigned_to_nat(30000u);
v___x_131_ = lean_nat_add(v___x_127_, v___x_130_);
lean_dec(v___x_127_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_129_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_box_uint64(v___x_128_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_134_);
v___x_136_ = v___x_125_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_122_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_122_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Server_FileWorker_RpcSession_new();
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object* v_monoMsNow_149_, lean_object* v_s_150_){
_start:
{
lean_object* v_objects_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_160_; 
v_objects_151_ = lean_ctor_get(v_s_150_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_s_150_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_s_150_, 1);
lean_dec(v_unused_161_);
v___x_153_ = v_s_150_;
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_objects_151_);
lean_dec(v_s_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_unsigned_to_nat(30000u);
v___x_156_ = lean_nat_add(v_monoMsNow_149_, v___x_155_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___x_156_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_objects_151_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object* v_monoMsNow_162_, lean_object* v_s_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Server_FileWorker_RpcSession_keptAlive(v_monoMsNow_162_, v_s_163_);
lean_dec(v_monoMsNow_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object* v_s_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_expireTime_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_167_ = lean_io_mono_ms_now();
v_expireTime_168_ = lean_ctor_get(v_s_165_, 1);
v___x_169_ = lean_nat_dec_le(v_expireTime_168_, v___x_167_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object* v_s_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_172_);
lean_dec_ref(v_s_172_);
return v_res_174_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Snapshots(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_AsyncList(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_Utils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Snapshots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_AsyncList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs = _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_Utils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin);
lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Snapshots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_AsyncList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_Utils(builtin);
}
#ifdef __cplusplus
}
#endif
