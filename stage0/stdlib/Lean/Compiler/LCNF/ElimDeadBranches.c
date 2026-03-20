// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDeadBranches
// Imports: public import Lean.Compiler.LCNF.InferType
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Format_join(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(uint8_t, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
uint8_t l_Prod_lexLtDec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_bot_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_bot_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_top_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_top_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_choice_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_choice_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_maxValueDepth;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instBEq___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instBEq = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊤"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__3_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " | "};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__10_value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.ElimDeadBranches"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Lean.Compiler.LCNF.UnreachableBranches.Value.inductValOfCtor"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "_private.Lean.Compiler.LCNF.ElimDeadBranches.0.Lean.Compiler.LCNF.UnreachableBranches.Value.merge.cleanup"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Lean.Compiler.LCNF.UnreachableBranches.Value.addChoice"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid addChoice "};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " into "};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2_value;
static const lean_array_object l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 117, .m_data = "_private.Lean.Compiler.LCNF.ElimDeadBranches.0.Lean.Compiler.LCNF.UnreachableBranches.Value.getLiteral.getNatConstant"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Not a well formed Nat constant Value"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___boxed(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "_private.Lean.Compiler.LCNF.ElimDeadBranches.0.Lean.Compiler.LCNF.UnreachableBranches.Value.getLiteral.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3;
static const lean_array_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "UnreachableBranches"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "functionSummariesExt"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 130, 135, 69, 155, 14, 96, 131)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 217, 249, 17, 195, 152, 212, 89)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Analyzing "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elimDeadBranches"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 80, 110, 205, 32, 43, 118, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Termination after "};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " steps"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Threw away cases "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " branch "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1;
static lean_once_cell_t l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2;
static const lean_ctor_object l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Eliminating "};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Analyzing block: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2;
static const lean_array_object l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_elimDeadBranches___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 204, 232, 255, 130, 130, 66, 205)}};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadBranches___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadBranches___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_elimDeadBranches___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_elimDeadBranches___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadBranches___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_elimDeadBranches___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadBranches___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadBranches___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadBranches___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadBranches___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_elimDeadBranches = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadBranches___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ElimDeadBranches"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 48, 204, 64, 9, 167, 133, 249)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(200, 150, 161, 93, 149, 239, 245, 119)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 115, 55, 70, 37, 185, 29, 189)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 112, 73, 71, 157, 233, 191, 127)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 232, 253, 11, 187, 111, 207, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 23, 231, 170, 231, 155, 87, 99)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 213, 22, 254, 230, 125, 90, 112)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 11, 80, 195, 104, 227, 74, 88)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 249, 148, 177, 5, 97, 125, 57)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 90, 29, 229, 248, 57, 61, 64)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 188, 228, 238, 115, 92, 75, 9)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
switch(lean_obj_tag(v_t_8_))
{
case 2:
{
lean_object* v_i_10_; lean_object* v_vs_11_; lean_object* v___x_12_; 
v_i_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_i_10_);
v_vs_11_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_vs_11_);
lean_dec_ref(v_t_8_);
v___x_12_ = lean_apply_2(v_k_9_, v_i_10_, v_vs_11_);
return v___x_12_;
}
case 3:
{
lean_object* v_vs_13_; lean_object* v___x_14_; 
v_vs_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_vs_13_);
lean_dec_ref(v_t_8_);
v___x_14_ = lean_apply_1(v_k_9_, v_vs_13_);
return v___x_14_;
}
default: 
{
lean_dec(v_t_8_);
return v_k_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim(lean_object* v_motive__1_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___boxed(lean_object* v_motive__1_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim(v_motive__1_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_bot_elim___redArg(lean_object* v_t_27_, lean_object* v_bot_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_27_, v_bot_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_bot_elim(lean_object* v_motive__1_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_bot_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_31_, v_bot_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_top_elim___redArg(lean_object* v_t_35_, lean_object* v_top_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_35_, v_top_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_top_elim(lean_object* v_motive__1_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_top_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_39_, v_top_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctor_elim___redArg(lean_object* v_t_43_, lean_object* v_ctor_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_43_, v_ctor_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctor_elim(lean_object* v_motive__1_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_ctor_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_47_, v_ctor_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_choice_elim___redArg(lean_object* v_t_51_, lean_object* v_choice_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_51_, v_choice_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_choice_elim(lean_object* v_motive__1_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_choice_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_55_, v_choice_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue_default(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue(void){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_box(0);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_maxValueDepth(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_unsigned_to_nat(8u);
return v___x_61_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___redArg(lean_object* v_xs_62_, lean_object* v_ys_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_zero_65_; uint8_t v_isZero_66_; 
v_zero_65_ = lean_unsigned_to_nat(0u);
v_isZero_66_ = lean_nat_dec_eq(v_x_64_, v_zero_65_);
if (v_isZero_66_ == 1)
{
lean_dec(v_x_64_);
return v_isZero_66_;
}
else
{
lean_object* v_one_67_; lean_object* v_n_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_one_67_ = lean_unsigned_to_nat(1u);
v_n_68_ = lean_nat_sub(v_x_64_, v_one_67_);
lean_dec(v_x_64_);
v___x_69_ = lean_array_fget_borrowed(v_xs_62_, v_n_68_);
v___x_70_ = lean_array_fget_borrowed(v_ys_63_, v_n_68_);
lean_inc(v___x_70_);
lean_inc(v___x_69_);
v___x_71_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_dec(v_n_68_);
return v___x_71_;
}
else
{
v_x_64_ = v_n_68_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__0___boxed(lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__0(v_a_73_, v_b_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__1(lean_object* v_bs_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___f_79_; uint8_t v___x_80_; 
v___f_79_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_79_, 0, v_a_78_);
v___x_80_ = l_List_any___redArg(v_bs_77_, v___f_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__1___boxed(lean_object* v_bs_81_, lean_object* v_a_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__1(v_bs_81_, v_a_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__2(lean_object* v_as_85_, lean_object* v_bs_86_){
_start:
{
lean_object* v___f_87_; uint8_t v___x_88_; 
v___f_87_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__1___boxed), 2, 1);
lean_closure_set(v___f_87_, 0, v_bs_86_);
v___x_88_ = l_List_all___redArg(v_as_85_, v___f_87_);
return v___x_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
if (lean_obj_tag(v_x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
lean_dec(v_x_90_);
v___x_92_ = 0;
return v___x_92_;
}
}
case 1:
{
if (lean_obj_tag(v_x_90_) == 1)
{
uint8_t v___x_93_; 
v___x_93_ = 1;
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
lean_dec(v_x_90_);
v___x_94_ = 0;
return v___x_94_;
}
}
case 2:
{
if (lean_obj_tag(v_x_90_) == 2)
{
lean_object* v_i_95_; lean_object* v_vs_96_; lean_object* v_i_97_; lean_object* v_vs_98_; uint8_t v___x_99_; 
v_i_95_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_i_95_);
v_vs_96_ = lean_ctor_get(v_x_89_, 1);
lean_inc_ref(v_vs_96_);
lean_dec_ref(v_x_89_);
v_i_97_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_i_97_);
v_vs_98_ = lean_ctor_get(v_x_90_, 1);
lean_inc_ref(v_vs_98_);
lean_dec_ref(v_x_90_);
v___x_99_ = lean_name_eq(v_i_95_, v_i_97_);
lean_dec(v_i_97_);
lean_dec(v_i_95_);
if (v___x_99_ == 0)
{
lean_dec_ref(v_vs_98_);
lean_dec_ref(v_vs_96_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_array_get_size(v_vs_96_);
v___x_101_ = lean_array_get_size(v_vs_98_);
v___x_102_ = lean_nat_dec_eq(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_dec_ref(v_vs_98_);
lean_dec_ref(v_vs_96_);
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___redArg(v_vs_96_, v_vs_98_, v___x_100_);
lean_dec_ref(v_vs_98_);
lean_dec_ref(v_vs_96_);
return v___x_103_;
}
}
}
else
{
uint8_t v___x_104_; 
lean_dec_ref(v_x_89_);
lean_dec(v_x_90_);
v___x_104_ = 0;
return v___x_104_;
}
}
default: 
{
if (lean_obj_tag(v_x_90_) == 3)
{
lean_object* v_vs_105_; lean_object* v_vs_106_; uint8_t v___x_107_; 
v_vs_105_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_vs_105_);
lean_dec_ref(v_x_89_);
v_vs_106_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_vs_106_);
lean_dec_ref(v_x_90_);
lean_inc(v_vs_106_);
lean_inc(v_vs_105_);
v___x_107_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__2(v_vs_105_, v_vs_106_);
if (v___x_107_ == 0)
{
lean_dec(v_vs_106_);
lean_dec(v_vs_105_);
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__2(v_vs_106_, v_vs_105_);
return v___x_108_;
}
}
else
{
uint8_t v___x_109_; 
lean_dec_ref(v_x_89_);
lean_dec(v_x_90_);
v___x_109_ = 0;
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__0(lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_110_, v_b_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__2___boxed(lean_object* v_as_113_, lean_object* v_bs_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___lam__2(v_as_113_, v_bs_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___redArg___boxed(lean_object* v_xs_117_, lean_object* v_ys_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___redArg(v_xs_117_, v_ys_118_, v_x_119_);
lean_dec_ref(v_ys_118_);
lean_dec_ref(v_xs_117_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___boxed(lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_x_122_, v_x_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(lean_object* v_xs_126_, lean_object* v_ys_127_, lean_object* v_hsz_128_, lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___redArg(v_xs_126_, v_ys_127_, v_x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___boxed(lean_object* v_xs_132_, lean_object* v_ys_133_, lean_object* v_hsz_134_, lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(v_xs_132_, v_ys_133_, v_hsz_134_, v_x_135_, v_x_136_);
lean_dec_ref(v_ys_133_);
lean_dec_ref(v_xs_132_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__1(lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_nat_to_int(v_a_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3_spec__3(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_dec(v_x_143_);
return v_x_144_;
}
else
{
lean_object* v_head_146_; lean_object* v_tail_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_156_; 
v_head_146_ = lean_ctor_get(v_x_145_, 0);
v_tail_147_ = lean_ctor_get(v_x_145_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_156_ == 0)
{
v___x_149_ = v_x_145_;
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_tail_147_);
lean_inc(v_head_146_);
lean_dec(v_x_145_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
lean_inc(v_x_143_);
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 5);
lean_ctor_set(v___x_149_, 1, v_x_143_);
lean_ctor_set(v___x_149_, 0, v_x_144_);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_x_144_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_x_143_);
v___x_152_ = v_reuseFailAlloc_155_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_head_146_);
v_x_144_ = v___x_153_;
v_x_145_ = v_tail_147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_x_158_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v_tail_160_; 
v_tail_160_ = lean_ctor_get(v_x_157_, 1);
if (lean_obj_tag(v_tail_160_) == 0)
{
lean_object* v_head_161_; 
lean_dec(v_x_158_);
v_head_161_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_head_161_);
lean_dec_ref(v_x_157_);
return v_head_161_;
}
else
{
lean_object* v_head_162_; lean_object* v___x_163_; 
lean_inc(v_tail_160_);
v_head_162_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_head_162_);
lean_dec_ref(v_x_157_);
v___x_163_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3_spec__3(v_x_158_, v_head_162_, v_tail_160_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0(lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
if (lean_obj_tag(v_a_173_) == 0)
{
lean_object* v___x_175_; 
v___x_175_ = l_List_reverse___redArg(v_a_174_);
return v___x_175_;
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_188_; 
v_head_176_ = lean_ctor_get(v_a_173_, 0);
v_tail_177_ = lean_ctor_get(v_a_173_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_a_173_);
if (v_isSharedCheck_188_ == 0)
{
v___x_179_ = v_a_173_;
v_isShared_180_ = v_isSharedCheck_188_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_tail_177_);
lean_inc(v_head_176_);
lean_dec(v_a_173_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_188_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_181_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__1));
v___x_182_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_176_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v_a_174_);
lean_ctor_set(v___x_179_, 0, v___x_183_);
v___x_185_ = v___x_179_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_a_174_);
v___x_185_ = v_reuseFailAlloc_187_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
v_a_173_ = v_tail_177_;
v_a_174_ = v___x_185_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__4));
v___x_191_ = lean_string_length(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6);
v___x_193_ = lean_nat_to_int(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(lean_object* v_x_202_){
_start:
{
switch(lean_obj_tag(v_x_202_))
{
case 0:
{
lean_object* v___x_203_; 
v___x_203_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__1));
return v___x_203_;
}
case 1:
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__3));
return v___x_204_;
}
case 2:
{
lean_object* v_i_205_; lean_object* v_vs_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_233_; 
v_i_205_ = lean_ctor_get(v_x_202_, 0);
v_vs_206_ = lean_ctor_get(v_x_202_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_233_ == 0)
{
v___x_208_ = v_x_202_;
v_isShared_209_ = v_isSharedCheck_233_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_vs_206_);
lean_inc(v_i_205_);
lean_dec(v_x_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_233_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_210_ = lean_array_get_size(v_vs_206_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_dec_eq(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_213_ = 1;
v___x_214_ = l_Lean_Name_toString(v_i_205_, v___x_213_);
v___x_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = lean_array_to_list(v_vs_206_);
v___x_217_ = lean_box(0);
v___x_218_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0(v___x_216_, v___x_217_);
v___x_219_ = l_Std_Format_join(v___x_218_);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 5);
lean_ctor_set(v___x_208_, 1, v___x_219_);
lean_ctor_set(v___x_208_, 0, v___x_215_);
v___x_221_ = v___x_208_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_230_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; 
v___x_222_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_223_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_221_);
v___x_225_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_222_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = 0;
v___x_229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_228_);
return v___x_229_;
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_del_object(v___x_208_);
lean_dec_ref(v_vs_206_);
v___x_231_ = l_Lean_Name_toString(v_i_205_, v___x_212_);
v___x_232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
default: 
{
lean_object* v_vs_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; 
v_vs_234_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_vs_234_);
lean_dec_ref(v_x_202_);
v___x_235_ = lean_box(0);
v___x_236_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__2(v_vs_234_, v___x_235_);
v___x_237_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__11));
v___x_238_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_236_, v___x_237_);
v___x_239_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_240_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_238_);
v___x_242_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_239_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_245_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__2(lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
if (lean_obj_tag(v_a_247_) == 0)
{
lean_object* v___x_249_; 
v___x_249_ = l_List_reverse___redArg(v_a_248_);
return v___x_249_;
}
else
{
lean_object* v_head_250_; lean_object* v_tail_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_260_; 
v_head_250_ = lean_ctor_get(v_a_247_, 0);
v_tail_251_ = lean_ctor_get(v_a_247_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_a_247_);
if (v_isSharedCheck_260_ == 0)
{
v___x_253_ = v_a_247_;
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_tail_251_);
lean_inc(v_head_250_);
lean_dec(v_a_247_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_250_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v_a_248_);
lean_ctor_set(v___x_253_, 0, v___x_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_a_248_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
v_a_247_ = v_tail_251_;
v_a_248_ = v___x_257_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0(lean_object* v_v_261_, lean_object* v_x_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0___boxed(lean_object* v_v_264_, lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0(v_v_264_, v_x_265_);
lean_dec(v_x_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(lean_object* v_msg_276_){
_start:
{
lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___f_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___f_277_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_278_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_279_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_280_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_281_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_282_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_283_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___f_277_);
lean_ctor_set(v___x_284_, 1, v___f_278_);
v___x_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___f_279_);
lean_ctor_set(v___x_285_, 2, v___f_280_);
lean_ctor_set(v___x_285_, 3, v___f_281_);
lean_ctor_set(v___x_285_, 4, v___f_282_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___f_283_);
v___x_287_ = l_Lean_instInhabitedInductiveVal_default;
v___x_288_ = l_instInhabitedOfMonad___redArg(v___x_286_, v___x_287_);
v___x_289_ = lean_panic_fn(v___x_288_, v_msg_276_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_293_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_294_ = lean_unsigned_to_nat(51u);
v___x_295_ = lean_unsigned_to_nat(72u);
v___x_296_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1));
v___x_297_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_298_ = l_mkPanicMessageWithDecl(v___x_297_, v___x_296_, v___x_295_, v___x_294_, v___x_293_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_300_ = lean_unsigned_to_nat(56u);
v___x_301_ = lean_unsigned_to_nat(73u);
v___x_302_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1));
v___x_303_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_304_ = l_mkPanicMessageWithDecl(v___x_303_, v___x_302_, v___x_301_, v___x_300_, v___x_299_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(lean_object* v_ctorName_305_, lean_object* v_env_306_){
_start:
{
uint8_t v___x_313_; lean_object* v___x_314_; 
v___x_313_ = 0;
lean_inc_ref(v_env_306_);
v___x_314_ = l_Lean_Environment_find_x3f(v_env_306_, v_ctorName_305_, v___x_313_);
if (lean_obj_tag(v___x_314_) == 1)
{
lean_object* v_val_315_; 
v_val_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_315_);
lean_dec_ref(v___x_314_);
if (lean_obj_tag(v_val_315_) == 6)
{
lean_object* v_val_316_; lean_object* v_induct_317_; lean_object* v___x_318_; 
v_val_316_ = lean_ctor_get(v_val_315_, 0);
lean_inc_ref(v_val_316_);
lean_dec_ref(v_val_315_);
v_induct_317_ = lean_ctor_get(v_val_316_, 1);
lean_inc(v_induct_317_);
lean_dec_ref(v_val_316_);
v___x_318_ = l_Lean_Environment_find_x3f(v_env_306_, v_induct_317_, v___x_313_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_319_);
lean_dec_ref(v___x_318_);
if (lean_obj_tag(v_val_319_) == 5)
{
lean_object* v_val_320_; 
v_val_320_ = lean_ctor_get(v_val_319_, 0);
lean_inc_ref(v_val_320_);
lean_dec_ref(v_val_319_);
return v_val_320_;
}
else
{
lean_dec(v_val_319_);
goto v___jp_310_;
}
}
else
{
lean_dec(v___x_318_);
goto v___jp_310_;
}
}
else
{
lean_dec(v_val_315_);
lean_dec_ref(v_env_306_);
goto v___jp_307_;
}
}
else
{
lean_dec(v___x_314_);
lean_dec_ref(v_env_306_);
goto v___jp_307_;
}
v___jp_307_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3);
v___x_309_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(v___x_308_);
return v___x_309_;
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4);
v___x_312_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(v___x_311_);
return v___x_312_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(lean_object* v_ctorName_321_, lean_object* v_env_322_, lean_object* v_n_323_){
_start:
{
lean_object* v_induct_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_induct_324_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_ctorName_321_, v_env_322_);
v___x_325_ = l_Lean_InductiveVal_numCtors(v_induct_324_);
lean_dec_ref(v_induct_324_);
v___x_326_ = lean_nat_dec_eq(v_n_323_, v___x_325_);
lean_dec(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___boxed(lean_object* v_ctorName_327_, lean_object* v_env_328_, lean_object* v_n_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_ctorName_327_, v_env_328_, v_n_329_);
lean_dec(v_n_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(uint8_t v___x_332_, lean_object* v_v_333_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_box(1);
v___x_335_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_v_333_, v___x_334_);
if (v___x_335_ == 0)
{
return v___x_332_;
}
else
{
uint8_t v___x_336_; 
v___x_336_ = 0;
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed(lean_object* v___x_337_, lean_object* v_v_338_){
_start:
{
uint8_t v___x_158__boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v___x_158__boxed_339_ = lean_unbox(v___x_337_);
v_res_340_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(v___x_158__boxed_339_, v_v_338_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(lean_object* v_value_342_){
_start:
{
if (lean_obj_tag(v_value_342_) == 2)
{
lean_object* v_vs_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_370_; 
v_vs_343_ = lean_ctor_get(v_value_342_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_value_342_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v_value_342_, 0);
lean_dec(v_unused_371_);
v___x_345_ = v_value_342_;
v_isShared_346_ = v_isSharedCheck_370_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_vs_343_);
lean_dec(v_value_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_370_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___f_353_; lean_object* v___f_354_; lean_object* v___f_355_; lean_object* v___x_357_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_array_get_size(v_vs_343_);
v___f_349_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_350_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_351_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_352_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_353_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_354_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_355_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 0);
lean_ctor_set(v___x_345_, 1, v___f_350_);
lean_ctor_set(v___x_345_, 0, v___f_349_);
v___x_357_ = v___x_345_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___f_349_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___f_350_);
v___x_357_ = v_reuseFailAlloc_369_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___f_351_);
lean_ctor_set(v___x_358_, 2, v___f_352_);
lean_ctor_set(v___x_358_, 3, v___f_353_);
lean_ctor_set(v___x_358_, 4, v___f_354_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___f_355_);
v___x_360_ = lean_nat_dec_lt(v___x_347_, v___x_348_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
lean_dec_ref(v___x_359_);
lean_dec_ref(v_vs_343_);
v___x_361_ = 1;
return v___x_361_;
}
else
{
if (v___x_360_ == 0)
{
lean_dec_ref(v___x_359_);
lean_dec_ref(v_vs_343_);
return v___x_360_;
}
else
{
lean_object* v___x_362_; lean_object* v___f_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_362_ = lean_box(v___x_360_);
v___f_363_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed), 2, 1);
lean_closure_set(v___f_363_, 0, v___x_362_);
v___x_364_ = ((size_t)0ULL);
v___x_365_ = lean_usize_of_nat(v___x_348_);
v___x_366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_359_, v___f_363_, v_vs_343_, v___x_364_, v___x_365_);
v___x_367_ = lean_unbox(v___x_366_);
lean_dec(v___x_366_);
if (v___x_367_ == 0)
{
return v___x_360_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = 0;
return v___x_368_;
}
}
}
}
}
}
else
{
uint8_t v___x_372_; 
lean_dec(v_value_342_);
v___x_372_ = 0;
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___boxed(lean_object* v_value_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(v_value_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(lean_object* v_msg_376_){
_start:
{
lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_379_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_380_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_381_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_382_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_383_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___f_377_);
lean_ctor_set(v___x_384_, 1, v___f_378_);
v___x_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___f_379_);
lean_ctor_set(v___x_385_, 2, v___f_380_);
lean_ctor_set(v___x_385_, 3, v___f_381_);
lean_ctor_set(v___x_385_, 4, v___f_382_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___f_383_);
v___x_387_ = lean_box(0);
v___x_388_ = l_instInhabitedOfMonad___redArg(v___x_386_, v___x_387_);
v___x_389_ = lean_panic_fn(v___x_388_, v_msg_376_);
return v___x_389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(lean_object* v_as_390_, size_t v_i_391_, size_t v_stop_392_){
_start:
{
uint8_t v___x_393_; 
v___x_393_ = lean_usize_dec_eq(v_i_391_, v_stop_392_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_394_ = 1;
v___x_395_ = lean_array_uget_borrowed(v_as_390_, v_i_391_);
v___x_396_ = lean_box(1);
lean_inc(v___x_395_);
v___x_397_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
return v___x_394_;
}
else
{
if (v___x_393_ == 0)
{
size_t v___x_398_; size_t v___x_399_; 
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_391_, v___x_398_);
v_i_391_ = v___x_399_;
goto _start;
}
else
{
return v___x_394_;
}
}
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0___boxed(lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; uint8_t v_res_407_; lean_object* v_r_408_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_as_402_, v_i_boxed_405_, v_stop_boxed_406_);
lean_dec_ref(v_as_402_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___lam__0(lean_object* v___y_409_){
_start:
{
if (lean_obj_tag(v___y_409_) == 2)
{
lean_object* v_vs_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_vs_410_ = lean_ctor_get(v___y_409_, 1);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_array_get_size(v_vs_410_);
v___x_413_ = lean_nat_dec_lt(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
else
{
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = ((size_t)0ULL);
v___x_416_ = lean_usize_of_nat(v___x_412_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_410_, v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
return v___x_413_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
}
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___lam__0___boxed(lean_object* v___y_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___lam__0(v___y_420_);
lean_dec(v___y_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__2(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_425_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_426_ = lean_unsigned_to_nat(42u);
v___x_427_ = lean_unsigned_to_nat(122u);
v___x_428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1));
v___x_429_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_430_ = l_mkPanicMessageWithDecl(v___x_429_, v___x_428_, v___x_427_, v___x_426_, v___x_425_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(lean_object* v_env_431_, lean_object* v_vs_432_){
_start:
{
lean_object* v___f_433_; uint8_t v___x_434_; 
v___f_433_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0));
lean_inc(v_vs_432_);
v___x_434_ = l_List_all___redArg(v_vs_432_, v___f_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec_ref(v_env_431_);
v___x_435_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_435_, 0, v_vs_432_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_box(0);
v___x_437_ = l_List_head_x21___redArg(v___x_436_, v_vs_432_);
if (lean_obj_tag(v___x_437_) == 2)
{
lean_object* v_i_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_i_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_i_438_);
lean_dec_ref(v___x_437_);
v___x_439_ = l_List_lengthTR___redArg(v_vs_432_);
v___x_440_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_i_438_, v_env_431_, v___x_439_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_441_, 0, v_vs_432_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; 
lean_dec(v_vs_432_);
v___x_442_ = lean_box(1);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v___x_437_);
lean_dec(v_vs_432_);
lean_dec_ref(v_env_431_);
v___x_443_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__2);
v___x_444_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v___x_443_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(lean_object* v_msg_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_panic_fn(v___x_446_, v_msg_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_dec(v_x_448_);
return v_x_449_;
}
else
{
lean_object* v_head_451_; lean_object* v_tail_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
v_head_451_ = lean_ctor_get(v_x_450_, 0);
v_tail_452_ = lean_ctor_get(v_x_450_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_462_ == 0)
{
v___x_454_ = v_x_450_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_tail_452_);
lean_inc(v_head_451_);
lean_dec(v_x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
lean_inc(v_x_448_);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 5);
lean_ctor_set(v___x_454_, 1, v_x_448_);
lean_ctor_set(v___x_454_, 0, v_x_449_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_x_449_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_x_448_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_451_);
v___x_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v_x_449_ = v___x_459_;
v_x_450_ = v_tail_452_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
lean_object* v___x_465_; 
lean_dec(v_x_464_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
lean_object* v_tail_466_; 
v_tail_466_ = lean_ctor_get(v_x_463_, 1);
if (lean_obj_tag(v_tail_466_) == 0)
{
lean_object* v_head_467_; lean_object* v___x_468_; 
lean_dec(v_x_464_);
v_head_467_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_head_467_);
lean_dec_ref(v_x_463_);
v___x_468_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_467_);
return v___x_468_;
}
else
{
lean_object* v_head_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc(v_tail_466_);
v_head_469_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_head_469_);
lean_dec_ref(v_x_463_);
v___x_470_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_469_);
v___x_471_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(v_x_464_, v___x_470_, v_tail_466_);
return v___x_471_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2));
v___x_484_ = lean_string_length(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7);
v___x_486_ = lean_nat_to_int(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(lean_object* v_a_491_){
_start:
{
if (lean_obj_tag(v_a_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1));
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; 
v___x_493_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_494_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(v_a_491_, v___x_493_);
v___x_495_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8);
v___x_496_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9));
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_494_);
v___x_498_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_495_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = 0;
v___x_502_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(lean_object* v_env_508_, lean_object* v_v1_509_, lean_object* v_v2_510_){
_start:
{
lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_518_; lean_object* v_i_519_; lean_object* v_vs_520_; 
switch(lean_obj_tag(v_v1_509_))
{
case 0:
{
switch(lean_obj_tag(v_v2_510_))
{
case 2:
{
lean_object* v_i_527_; lean_object* v_vs_528_; 
v_i_527_ = lean_ctor_get(v_v2_510_, 0);
lean_inc(v_i_527_);
v_vs_528_ = lean_ctor_get(v_v2_510_, 1);
lean_inc_ref(v_vs_528_);
v___y_518_ = v_v2_510_;
v_i_519_ = v_i_527_;
v_vs_520_ = v_vs_528_;
goto v___jp_517_;
}
case 3:
{
lean_object* v_vs_529_; lean_object* v___x_530_; 
v_vs_529_ = lean_ctor_get(v_v2_510_, 0);
lean_inc(v_vs_529_);
lean_dec_ref(v_v2_510_);
v___x_530_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_508_, v_vs_529_);
return v___x_530_;
}
default: 
{
lean_dec_ref(v_env_508_);
return v_v2_510_;
}
}
}
case 1:
{
lean_dec_ref(v_env_508_);
switch(lean_obj_tag(v_v2_510_))
{
case 0:
{
return v_v1_509_;
}
case 1:
{
return v_v2_510_;
}
case 3:
{
lean_dec_ref(v_v2_510_);
return v_v1_509_;
}
default: 
{
lean_dec(v_v2_510_);
return v_v1_509_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_v2_510_))
{
case 0:
{
lean_object* v_i_531_; lean_object* v_vs_532_; 
v_i_531_ = lean_ctor_get(v_v1_509_, 0);
lean_inc(v_i_531_);
v_vs_532_ = lean_ctor_get(v_v1_509_, 1);
lean_inc_ref(v_vs_532_);
v___y_518_ = v_v1_509_;
v_i_519_ = v_i_531_;
v_vs_520_ = v_vs_532_;
goto v___jp_517_;
}
case 1:
{
lean_dec_ref(v_v1_509_);
lean_dec_ref(v_env_508_);
return v_v2_510_;
}
case 2:
{
lean_object* v_i_533_; lean_object* v_vs_534_; lean_object* v_i_535_; lean_object* v_vs_536_; uint8_t v___x_537_; 
v_i_533_ = lean_ctor_get(v_v1_509_, 0);
v_vs_534_ = lean_ctor_get(v_v1_509_, 1);
v_i_535_ = lean_ctor_get(v_v2_510_, 0);
v_vs_536_ = lean_ctor_get(v_v2_510_, 1);
v___x_537_ = lean_name_eq(v_i_533_, v_i_535_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v_v2_510_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v_v1_509_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_508_, v___x_540_);
return v___x_541_;
}
else
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_551_; 
lean_inc_ref(v_vs_536_);
lean_inc_ref(v_vs_534_);
lean_inc(v_i_533_);
lean_dec_ref(v_v1_509_);
v_isSharedCheck_551_ = !lean_is_exclusive(v_v2_510_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; lean_object* v_unused_553_; 
v_unused_552_ = lean_ctor_get(v_v2_510_, 1);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_v2_510_, 0);
lean_dec(v_unused_553_);
v___x_543_ = v_v2_510_;
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
else
{
lean_dec(v_v2_510_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
lean_inc_ref(v_env_508_);
v___x_547_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_508_, v_vs_534_, v_vs_536_, v___x_545_, v___x_546_);
lean_dec_ref(v_vs_536_);
lean_dec_ref(v_vs_534_);
lean_inc_ref(v___x_547_);
lean_inc(v_i_533_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_547_);
lean_ctor_set(v___x_543_, 0, v_i_533_);
v___x_549_ = v___x_543_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_i_533_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
v___y_518_ = v___x_549_;
v_i_519_ = v_i_533_;
v_vs_520_ = v___x_547_;
goto v___jp_517_;
}
}
}
}
default: 
{
lean_object* v_vs_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_vs_554_ = lean_ctor_get(v_v2_510_, 0);
lean_inc(v_vs_554_);
lean_dec_ref(v_v2_510_);
lean_inc_ref(v_env_508_);
v___x_555_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_508_, v_vs_554_, v_v1_509_);
v___x_556_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_508_, v___x_555_);
return v___x_556_;
}
}
}
default: 
{
switch(lean_obj_tag(v_v2_510_))
{
case 0:
{
lean_object* v_vs_557_; lean_object* v___x_558_; 
v_vs_557_ = lean_ctor_get(v_v1_509_, 0);
lean_inc(v_vs_557_);
lean_dec_ref(v_v1_509_);
v___x_558_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_508_, v_vs_557_);
return v___x_558_;
}
case 1:
{
lean_dec_ref(v_v1_509_);
lean_dec_ref(v_env_508_);
return v_v2_510_;
}
case 3:
{
lean_object* v_vs_559_; lean_object* v_vs_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_vs_559_ = lean_ctor_get(v_v1_509_, 0);
lean_inc(v_vs_559_);
lean_dec_ref(v_v1_509_);
v_vs_560_ = lean_ctor_get(v_v2_510_, 0);
lean_inc(v_vs_560_);
lean_dec_ref(v_v2_510_);
lean_inc_ref(v_env_508_);
v___x_561_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(v_env_508_, v_vs_560_, v_vs_559_);
v___x_562_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_508_, v___x_561_);
return v___x_562_;
}
default: 
{
lean_object* v_vs_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_vs_563_ = lean_ctor_get(v_v1_509_, 0);
lean_inc(v_vs_563_);
lean_dec_ref(v_v1_509_);
lean_inc_ref(v_env_508_);
v___x_564_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_508_, v_vs_563_, v_v2_510_);
v___x_565_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_508_, v___x_564_);
return v___x_565_;
}
}
}
}
v___jp_511_:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v___y_512_, v_env_508_, v___x_514_);
if (v___x_515_ == 0)
{
return v___y_513_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v___y_513_);
v___x_516_ = lean_box(1);
return v___x_516_;
}
}
v___jp_517_:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = lean_array_get_size(v_vs_520_);
v___x_523_ = lean_nat_dec_lt(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_dec_ref(v_vs_520_);
v___y_512_ = v_i_519_;
v___y_513_ = v___y_518_;
goto v___jp_511_;
}
else
{
if (v___x_523_ == 0)
{
lean_dec_ref(v_vs_520_);
v___y_512_ = v_i_519_;
v___y_513_ = v___y_518_;
goto v___jp_511_;
}
else
{
size_t v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = ((size_t)0ULL);
v___x_525_ = lean_usize_of_nat(v___x_522_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_520_, v___x_524_, v___x_525_);
lean_dec_ref(v_vs_520_);
if (v___x_526_ == 0)
{
v___y_512_ = v_i_519_;
v___y_513_ = v___y_518_;
goto v___jp_511_;
}
else
{
lean_dec(v_i_519_);
lean_dec_ref(v_env_508_);
return v___y_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(lean_object* v_env_566_, lean_object* v_as_567_, lean_object* v_bs_568_, lean_object* v_i_569_, lean_object* v_cs_570_){
_start:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v_as_567_);
v___x_572_ = lean_nat_dec_lt(v_i_569_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec(v_i_569_);
lean_dec_ref(v_env_566_);
return v_cs_570_;
}
else
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_array_get_size(v_bs_568_);
v___x_574_ = lean_nat_dec_lt(v_i_569_, v___x_573_);
if (v___x_574_ == 0)
{
lean_dec(v_i_569_);
lean_dec_ref(v_env_566_);
return v_cs_570_;
}
else
{
lean_object* v_a_575_; lean_object* v_b_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_a_575_ = lean_array_fget_borrowed(v_as_567_, v_i_569_);
v_b_576_ = lean_array_fget_borrowed(v_bs_568_, v_i_569_);
lean_inc(v_b_576_);
lean_inc(v_a_575_);
lean_inc_ref(v_env_566_);
v___x_577_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_566_, v_a_575_, v_b_576_);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_i_569_, v___x_578_);
lean_dec(v_i_569_);
v___x_580_ = lean_array_push(v_cs_570_, v___x_577_);
v_i_569_ = v___x_579_;
v_cs_570_ = v___x_580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(lean_object* v_env_582_, lean_object* v_vs_583_, lean_object* v_v_584_){
_start:
{
if (lean_obj_tag(v_vs_583_) == 0)
{
lean_object* v___x_603_; 
lean_dec_ref(v_env_582_);
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v_v_584_);
lean_ctor_set(v___x_603_, 1, v_vs_583_);
return v___x_603_;
}
else
{
lean_object* v_head_604_; 
v_head_604_ = lean_ctor_get(v_vs_583_, 0);
if (lean_obj_tag(v_head_604_) == 2)
{
if (lean_obj_tag(v_v_584_) == 2)
{
lean_object* v_tail_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_633_; 
lean_inc_ref(v_head_604_);
v_tail_605_ = lean_ctor_get(v_vs_583_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_vs_583_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_vs_583_, 0);
lean_dec(v_unused_634_);
v___x_607_ = v_vs_583_;
v_isShared_608_ = v_isSharedCheck_633_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_tail_605_);
lean_dec(v_vs_583_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_633_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_i_609_; lean_object* v_vs_610_; lean_object* v_i_611_; lean_object* v_vs_612_; uint8_t v___x_613_; 
v_i_609_ = lean_ctor_get(v_head_604_, 0);
v_vs_610_ = lean_ctor_get(v_head_604_, 1);
v_i_611_ = lean_ctor_get(v_v_584_, 0);
v_vs_612_ = lean_ctor_get(v_v_584_, 1);
v___x_613_ = lean_name_eq(v_i_609_, v_i_611_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_582_, v_tail_605_, v_v_584_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_614_);
v___x_616_ = v___x_607_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_head_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_630_; 
lean_inc_ref(v_vs_612_);
lean_inc_ref(v_vs_610_);
lean_inc(v_i_609_);
lean_dec_ref(v_head_604_);
v_isSharedCheck_630_ = !lean_is_exclusive(v_v_584_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; lean_object* v_unused_632_; 
v_unused_631_ = lean_ctor_get(v_v_584_, 1);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_v_584_, 0);
lean_dec(v_unused_632_);
v___x_619_ = v_v_584_;
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
else
{
lean_dec(v_v_584_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
v___x_623_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_582_, v_vs_610_, v_vs_612_, v___x_621_, v___x_622_);
lean_dec_ref(v_vs_612_);
lean_dec_ref(v_vs_610_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_623_);
lean_ctor_set(v___x_619_, 0, v_i_609_);
v___x_625_ = v___x_619_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_i_609_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_623_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_625_);
v___x_627_ = v___x_607_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_tail_605_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_582_);
goto v___jp_585_;
}
}
else
{
lean_dec_ref(v_env_582_);
goto v___jp_585_;
}
}
v___jp_585_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_586_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_587_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0));
v___x_588_ = lean_unsigned_to_nat(92u);
v___x_589_ = lean_unsigned_to_nat(12u);
v___x_590_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1));
v___x_591_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_584_);
v___x_592_ = l_Std_Format_defWidth;
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = l_Std_Format_pretty(v___x_591_, v___x_592_, v___x_593_, v___x_593_);
v___x_595_ = lean_string_append(v___x_590_, v___x_594_);
lean_dec_ref(v___x_594_);
v___x_596_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2));
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
v___x_598_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_vs_583_);
v___x_599_ = l_Std_Format_pretty(v___x_598_, v___x_592_, v___x_593_, v___x_593_);
v___x_600_ = lean_string_append(v___x_597_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = l_mkPanicMessageWithDecl(v___x_586_, v___x_587_, v___x_588_, v___x_589_, v___x_600_);
lean_dec_ref(v___x_600_);
v___x_602_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(v___x_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(lean_object* v_env_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_dec_ref(v_env_635_);
return v_x_636_;
}
else
{
lean_object* v_head_638_; lean_object* v_tail_639_; lean_object* v___x_640_; 
v_head_638_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_head_638_);
v_tail_639_ = lean_ctor_get(v_x_637_, 1);
lean_inc(v_tail_639_);
lean_dec_ref(v_x_637_);
lean_inc_ref(v_env_635_);
v___x_640_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_635_, v_x_636_, v_head_638_);
v_x_636_ = v___x_640_;
v_x_637_ = v_tail_639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2___boxed(lean_object* v_env_642_, lean_object* v_as_643_, lean_object* v_bs_644_, lean_object* v_i_645_, lean_object* v_cs_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_642_, v_as_643_, v_bs_644_, v_i_645_, v_cs_646_);
lean_dec_ref(v_bs_644_);
lean_dec_ref(v_as_643_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(lean_object* v_a_648_, lean_object* v_n_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_a_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___boxed(lean_object* v_a_651_, lean_object* v_n_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(v_a_651_, v_n_652_);
lean_dec(v_n_652_);
return v_res_653_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(lean_object* v_a_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
uint8_t v___x_656_; 
lean_dec(v_a_654_);
v___x_656_ = 0;
return v___x_656_;
}
else
{
lean_object* v_head_657_; lean_object* v_tail_658_; uint8_t v___x_659_; 
v_head_657_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_head_657_);
v_tail_658_ = lean_ctor_get(v_x_655_, 1);
lean_inc(v_tail_658_);
lean_dec_ref(v_x_655_);
lean_inc(v_a_654_);
v___x_659_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_654_, v_head_657_);
if (v___x_659_ == 0)
{
v_x_655_ = v_tail_658_;
goto _start;
}
else
{
lean_dec(v_tail_658_);
lean_dec(v_a_654_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v_a_661_, v_x_662_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(lean_object* v_env_665_, lean_object* v_forbiddenTypes_x27_666_, lean_object* v_n_667_, size_t v_sz_668_, size_t v_i_669_, lean_object* v_bs_670_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = lean_usize_dec_lt(v_i_669_, v_sz_668_);
if (v___x_671_ == 0)
{
lean_dec(v_forbiddenTypes_x27_666_);
lean_dec_ref(v_env_665_);
return v_bs_670_;
}
else
{
lean_object* v_v_672_; lean_object* v___x_673_; lean_object* v_bs_x27_674_; lean_object* v___x_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v_v_672_ = lean_array_uget(v_bs_670_, v_i_669_);
v___x_673_ = lean_unsigned_to_nat(0u);
v_bs_x27_674_ = lean_array_uset(v_bs_670_, v_i_669_, v___x_673_);
lean_inc(v_forbiddenTypes_x27_666_);
lean_inc_ref(v_env_665_);
v___x_675_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_665_, v_v_672_, v_forbiddenTypes_x27_666_, v_n_667_);
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_669_, v___x_676_);
v___x_678_ = lean_array_uset(v_bs_x27_674_, v_i_669_, v___x_675_);
v_i_669_ = v___x_677_;
v_bs_670_ = v___x_678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(lean_object* v_env_680_, lean_object* v_v_681_, lean_object* v_forbiddenTypes_682_, lean_object* v_remainingDepth_683_){
_start:
{
lean_object* v_zero_684_; uint8_t v_isZero_685_; 
v_zero_684_ = lean_unsigned_to_nat(0u);
v_isZero_685_ = lean_nat_dec_eq(v_remainingDepth_683_, v_zero_684_);
if (v_isZero_685_ == 1)
{
lean_object* v___x_686_; 
lean_dec(v_forbiddenTypes_682_);
lean_dec(v_v_681_);
lean_dec_ref(v_env_680_);
v___x_686_ = lean_box(1);
return v___x_686_;
}
else
{
lean_object* v_one_687_; lean_object* v_n_688_; 
v_one_687_ = lean_unsigned_to_nat(1u);
v_n_688_ = lean_nat_sub(v_remainingDepth_683_, v_one_687_);
switch(lean_obj_tag(v_v_681_))
{
case 2:
{
lean_object* v_i_689_; lean_object* v_vs_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_709_; 
v_i_689_ = lean_ctor_get(v_v_681_, 0);
v_vs_690_ = lean_ctor_get(v_v_681_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_v_681_);
if (v_isSharedCheck_709_ == 0)
{
v___x_692_ = v_v_681_;
v_isShared_693_ = v_isSharedCheck_709_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_vs_690_);
lean_inc(v_i_689_);
lean_dec(v_v_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_709_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_forbiddenTypes_x27_695_; lean_object* v_induct_702_; lean_object* v_toConstantVal_703_; uint8_t v_isRec_704_; lean_object* v_name_705_; uint8_t v___x_706_; 
lean_inc_ref(v_env_680_);
lean_inc(v_i_689_);
v_induct_702_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_i_689_, v_env_680_);
v_toConstantVal_703_ = lean_ctor_get(v_induct_702_, 0);
lean_inc_ref(v_toConstantVal_703_);
v_isRec_704_ = lean_ctor_get_uint8(v_induct_702_, sizeof(void*)*6);
lean_dec_ref(v_induct_702_);
v_name_705_ = lean_ctor_get(v_toConstantVal_703_, 0);
lean_inc(v_name_705_);
lean_dec_ref(v_toConstantVal_703_);
v___x_706_ = l_Lean_NameSet_contains(v_forbiddenTypes_682_, v_name_705_);
if (v___x_706_ == 0)
{
if (v_isRec_704_ == 0)
{
lean_dec(v_name_705_);
v_forbiddenTypes_x27_695_ = v_forbiddenTypes_682_;
goto v___jp_694_;
}
else
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_NameSet_insert(v_forbiddenTypes_682_, v_name_705_);
v_forbiddenTypes_x27_695_ = v___x_707_;
goto v___jp_694_;
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v_name_705_);
lean_del_object(v___x_692_);
lean_dec_ref(v_vs_690_);
lean_dec(v_i_689_);
lean_dec(v_n_688_);
lean_dec(v_forbiddenTypes_682_);
lean_dec_ref(v_env_680_);
v___x_708_ = lean_box(1);
return v___x_708_;
}
v___jp_694_:
{
size_t v_sz_696_; size_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v_sz_696_ = lean_array_size(v_vs_690_);
v___x_697_ = ((size_t)0ULL);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_680_, v_forbiddenTypes_x27_695_, v_n_688_, v_sz_696_, v___x_697_, v_vs_690_);
lean_dec(v_n_688_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_698_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_i_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
case 3:
{
lean_object* v_vs_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_721_; 
v_vs_710_ = lean_ctor_get(v_v_681_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_v_681_);
if (v_isSharedCheck_721_ == 0)
{
v___x_712_ = v_v_681_;
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_vs_710_);
lean_dec(v_v_681_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v_vs_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_714_ = lean_box(0);
v_vs_715_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_680_, v_forbiddenTypes_682_, v_n_688_, v_vs_710_, v___x_714_);
lean_dec(v_n_688_);
v___x_716_ = lean_box(1);
lean_inc(v_vs_715_);
v___x_717_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v___x_716_, v_vs_715_);
if (v___x_717_ == 0)
{
lean_object* v___x_719_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v_vs_715_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_vs_715_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
else
{
lean_dec(v_vs_715_);
lean_del_object(v___x_712_);
return v___x_716_;
}
}
}
default: 
{
lean_dec(v_n_688_);
lean_dec(v_forbiddenTypes_682_);
lean_dec_ref(v_env_680_);
return v_v_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(lean_object* v_env_722_, lean_object* v_forbiddenTypes_723_, lean_object* v_n_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
if (lean_obj_tag(v_a_725_) == 0)
{
lean_object* v___x_727_; 
lean_dec(v_forbiddenTypes_723_);
lean_dec_ref(v_env_722_);
v___x_727_ = l_List_reverse___redArg(v_a_726_);
return v___x_727_;
}
else
{
lean_object* v_head_728_; lean_object* v_tail_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_738_; 
v_head_728_ = lean_ctor_get(v_a_725_, 0);
v_tail_729_ = lean_ctor_get(v_a_725_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_a_725_);
if (v_isSharedCheck_738_ == 0)
{
v___x_731_ = v_a_725_;
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_tail_729_);
lean_inc(v_head_728_);
lean_dec(v_a_725_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
lean_inc(v_forbiddenTypes_723_);
lean_inc_ref(v_env_722_);
v___x_733_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_722_, v_head_728_, v_forbiddenTypes_723_, v_n_724_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_a_726_);
lean_ctor_set(v___x_731_, 0, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_726_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v_a_725_ = v_tail_729_;
v_a_726_ = v___x_735_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object* v_env_739_, lean_object* v_forbiddenTypes_740_, lean_object* v_n_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_739_, v_forbiddenTypes_740_, v_n_741_, v_a_742_, v_a_743_);
lean_dec(v_n_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object* v_env_745_, lean_object* v_forbiddenTypes_x27_746_, lean_object* v_n_747_, lean_object* v_sz_748_, lean_object* v_i_749_, lean_object* v_bs_750_){
_start:
{
size_t v_sz_boxed_751_; size_t v_i_boxed_752_; lean_object* v_res_753_; 
v_sz_boxed_751_ = lean_unbox_usize(v_sz_748_);
lean_dec(v_sz_748_);
v_i_boxed_752_ = lean_unbox_usize(v_i_749_);
lean_dec(v_i_749_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_745_, v_forbiddenTypes_x27_746_, v_n_747_, v_sz_boxed_751_, v_i_boxed_752_, v_bs_750_);
lean_dec(v_n_747_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___boxed(lean_object* v_env_754_, lean_object* v_v_755_, lean_object* v_forbiddenTypes_756_, lean_object* v_remainingDepth_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_754_, v_v_755_, v_forbiddenTypes_756_, v_remainingDepth_757_);
lean_dec(v_remainingDepth_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(lean_object* v_env_759_, lean_object* v_v_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = l_Lean_NameSet_empty;
v___x_762_ = lean_unsigned_to_nat(8u);
v___x_763_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_759_, v_v_760_, v___x_761_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(lean_object* v_env_764_, lean_object* v_v1_765_, lean_object* v_v2_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_inc_ref(v_env_764_);
v___x_767_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_764_, v_v1_765_, v_v2_766_);
v___x_768_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(v_env_764_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___lam__0___boxed(lean_object* v_x_769_, lean_object* v_v_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___lam__0(v_x_769_, v_v_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
switch(lean_obj_tag(v_x_773_))
{
case 2:
{
lean_object* v_i_775_; uint8_t v___x_776_; 
v_i_775_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_i_775_);
lean_dec_ref(v_x_773_);
v___x_776_ = lean_name_eq(v_i_775_, v_x_774_);
lean_dec(v_x_774_);
lean_dec(v_i_775_);
return v___x_776_;
}
case 3:
{
lean_object* v_vs_777_; lean_object* v___f_778_; uint8_t v___x_779_; 
v_vs_777_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_vs_777_);
lean_dec_ref(v_x_773_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_778_, 0, v_x_774_);
v___x_779_ = l_List_any___redArg(v_vs_777_, v___f_778_);
return v___x_779_;
}
default: 
{
uint8_t v___x_780_; 
lean_dec(v_x_774_);
lean_dec(v_x_773_);
v___x_780_ = 1;
return v___x_780_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___lam__0(lean_object* v_x_781_, lean_object* v_v_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_v_782_, v_x_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_x_784_, v_x_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(lean_object* v_x_791_, lean_object* v_as_x27_792_, lean_object* v_b_793_){
_start:
{
if (lean_obj_tag(v_as_x27_792_) == 0)
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v_b_793_);
return v___x_794_;
}
else
{
lean_object* v_head_795_; lean_object* v_tail_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v_b_793_);
v_head_795_ = lean_ctor_get(v_as_x27_792_, 0);
lean_inc(v_head_795_);
v_tail_796_ = lean_ctor_get(v_as_x27_792_, 1);
lean_inc(v_tail_796_);
lean_dec_ref(v_as_x27_792_);
v___x_797_ = lean_box(0);
v___x_798_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_795_) == 2)
{
lean_object* v_i_799_; lean_object* v_vs_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_811_; 
v_i_799_ = lean_ctor_get(v_head_795_, 0);
v_vs_800_ = lean_ctor_get(v_head_795_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_head_795_);
if (v_isSharedCheck_811_ == 0)
{
v___x_802_ = v_head_795_;
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_vs_800_);
lean_inc(v_i_799_);
lean_dec(v_head_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
uint8_t v___x_804_; 
v___x_804_ = lean_name_eq(v_i_799_, v_x_791_);
lean_dec(v_i_799_);
if (v___x_804_ == 0)
{
lean_del_object(v___x_802_);
lean_dec_ref(v_vs_800_);
v_as_x27_792_ = v_tail_796_;
v_b_793_ = v___x_798_;
goto _start;
}
else
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_tail_796_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_vs_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 0);
lean_ctor_set(v___x_802_, 1, v___x_797_);
lean_ctor_set(v___x_802_, 0, v___x_806_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_797_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
}
else
{
lean_dec(v_head_795_);
v_as_x27_792_ = v_tail_796_;
v_b_793_ = v___x_798_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___boxed(lean_object* v_x_813_, lean_object* v_as_x27_814_, lean_object* v_b_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_813_, v_as_x27_814_, v_b_815_);
lean_dec(v_x_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
switch(lean_obj_tag(v_x_817_))
{
case 2:
{
lean_object* v_i_819_; lean_object* v_vs_820_; uint8_t v___x_821_; 
v_i_819_ = lean_ctor_get(v_x_817_, 0);
lean_inc(v_i_819_);
v_vs_820_ = lean_ctor_get(v_x_817_, 1);
lean_inc_ref(v_vs_820_);
lean_dec_ref(v_x_817_);
v___x_821_ = lean_name_eq(v_i_819_, v_x_818_);
lean_dec(v_i_819_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_dec_ref(v_vs_820_);
v___x_822_ = lean_box(0);
return v___x_822_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_vs_820_);
return v___x_823_;
}
}
case 3:
{
lean_object* v_vs_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_val_828_; lean_object* v_fst_829_; 
v_vs_824_ = lean_ctor_get(v_x_817_, 0);
lean_inc(v_vs_824_);
lean_dec_ref(v_x_817_);
v___x_825_ = lean_box(0);
v___x_826_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
v___x_827_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_818_, v_vs_824_, v___x_826_);
v_val_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_828_);
lean_dec(v___x_827_);
v_fst_829_ = lean_ctor_get(v_val_828_, 0);
lean_inc(v_fst_829_);
lean_dec(v_val_828_);
if (lean_obj_tag(v_fst_829_) == 0)
{
return v___x_825_;
}
else
{
return v_fst_829_;
}
}
default: 
{
lean_object* v___x_830_; 
lean_dec(v_x_817_);
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs___boxed(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_x_831_, v_x_832_);
lean_dec(v_x_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(lean_object* v_x_834_, lean_object* v_as_835_, lean_object* v_as_x27_836_, lean_object* v_b_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_834_, v_as_x27_836_, v_b_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___boxed(lean_object* v_x_840_, lean_object* v_as_841_, lean_object* v_as_x27_842_, lean_object* v_b_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(v_x_840_, v_as_841_, v_as_x27_842_, v_b_843_, v_a_844_);
lean_dec(v_as_841_);
lean_dec(v_x_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(lean_object* v_a_858_){
_start:
{
lean_object* v_zero_859_; uint8_t v_isZero_860_; 
v_zero_859_ = lean_unsigned_to_nat(0u);
v_isZero_860_ = lean_nat_dec_eq(v_a_858_, v_zero_859_);
if (v_isZero_860_ == 1)
{
lean_object* v___x_861_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3));
return v___x_861_;
}
else
{
lean_object* v_one_862_; lean_object* v_n_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_one_862_ = lean_unsigned_to_nat(1u);
v_n_863_ = lean_nat_sub(v_a_858_, v_one_862_);
v___x_864_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5));
v___x_865_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_863_);
lean_dec(v_n_863_);
v___x_866_ = lean_mk_empty_array_with_capacity(v_one_862_);
v___x_867_ = lean_array_push(v___x_866_, v___x_865_);
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_864_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___boxed(lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_a_869_);
lean_dec(v_a_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(lean_object* v_n_871_){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(8u);
v___x_873_ = lean_nat_dec_lt(v___x_872_, v_n_871_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_871_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; 
v___x_875_ = lean_box(1);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat___boxed(lean_object* v_n_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_n_876_);
lean_dec(v_n_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v_val_879_; lean_object* v___x_880_; 
v_val_879_ = lean_ctor_get(v_x_878_, 0);
v___x_880_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_val_879_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; 
v___x_881_ = lean_box(1);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit___boxed(lean_object* v_x_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_x_882_);
lean_dec_ref(v_x_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(lean_object* v_env_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
switch(lean_obj_tag(v_x_885_))
{
case 2:
{
lean_object* v_vs_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
lean_dec_ref(v_env_884_);
v_vs_887_ = lean_ctor_get(v_x_885_, 1);
v___x_888_ = lean_array_get_size(v_vs_887_);
v___x_889_ = lean_nat_dec_lt(v_x_886_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = lean_box(0);
return v___x_890_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = lean_array_fget_borrowed(v_vs_887_, v_x_886_);
lean_inc(v___x_891_);
return v___x_891_;
}
}
case 3:
{
lean_object* v_vs_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_vs_892_ = lean_ctor_get(v_x_885_, 0);
v___x_893_ = lean_box(0);
v___x_894_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_884_, v_x_886_, v___x_893_, v_vs_892_);
return v___x_894_;
}
default: 
{
lean_dec_ref(v_env_884_);
lean_inc(v_x_885_);
return v_x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(lean_object* v_env_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_dec_ref(v_env_895_);
return v_x_897_;
}
else
{
lean_object* v_head_899_; lean_object* v_tail_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_head_899_ = lean_ctor_get(v_x_898_, 0);
v_tail_900_ = lean_ctor_get(v_x_898_, 1);
lean_inc_ref(v_env_895_);
v___x_901_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_895_, v_head_899_, v_x_896_);
lean_inc_ref(v_env_895_);
v___x_902_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_895_, v_x_897_, v___x_901_);
v_x_897_ = v___x_902_;
v_x_898_ = v_tail_900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0___boxed(lean_object* v_env_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_904_, v_x_905_, v_x_906_, v_x_907_);
lean_dec(v_x_907_);
lean_dec(v_x_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj___boxed(lean_object* v_env_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_909_, v_x_910_, v_x_911_);
lean_dec(v_x_911_);
lean_dec(v_x_910_);
return v_res_912_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(lean_object* v_x_913_){
_start:
{
if (lean_obj_tag(v_x_913_) == 2)
{
lean_object* v_vs_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_vs_914_ = lean_ctor_get(v_x_913_, 1);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_array_get_size(v_vs_914_);
v___x_917_ = lean_nat_dec_lt(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; 
v___x_918_ = 1;
return v___x_918_;
}
else
{
if (v___x_917_ == 0)
{
return v___x_917_;
}
else
{
size_t v___x_919_; size_t v___x_920_; uint8_t v___x_921_; 
v___x_919_ = ((size_t)0ULL);
v___x_920_ = lean_usize_of_nat(v___x_916_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_vs_914_, v___x_919_, v___x_920_);
if (v___x_921_ == 0)
{
return v___x_917_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
}
}
else
{
uint8_t v___x_923_; 
v___x_923_ = 0;
return v___x_923_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(lean_object* v_as_924_, size_t v_i_925_, size_t v_stop_926_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = lean_usize_dec_eq(v_i_925_, v_stop_926_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = 1;
v___x_929_ = lean_array_uget_borrowed(v_as_924_, v_i_925_);
v___x_930_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v___x_929_);
if (v___x_930_ == 0)
{
return v___x_928_;
}
else
{
if (v___x_927_ == 0)
{
size_t v___x_931_; size_t v___x_932_; 
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_925_, v___x_931_);
v_i_925_ = v___x_932_;
goto _start;
}
else
{
return v___x_928_;
}
}
}
else
{
uint8_t v___x_934_; 
v___x_934_ = 0;
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0___boxed(lean_object* v_as_935_, lean_object* v_i_936_, lean_object* v_stop_937_){
_start:
{
size_t v_i_boxed_938_; size_t v_stop_boxed_939_; uint8_t v_res_940_; lean_object* v_r_941_; 
v_i_boxed_938_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_stop_boxed_939_ = lean_unbox_usize(v_stop_937_);
lean_dec(v_stop_937_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_as_935_, v_i_boxed_938_, v_stop_boxed_939_);
lean_dec_ref(v_as_935_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral___boxed(lean_object* v_x_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_x_942_);
lean_dec(v_x_942_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(lean_object* v_msg_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_panic_fn(v___x_946_, v_msg_945_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1));
v___x_951_ = lean_unsigned_to_nat(9u);
v___x_952_ = lean_unsigned_to_nat(271u);
v___x_953_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0));
v___x_954_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_955_ = l_mkPanicMessageWithDecl(v___x_954_, v___x_953_, v___x_952_, v___x_951_, v___x_950_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(lean_object* v_a_956_){
_start:
{
if (lean_obj_tag(v_a_956_) == 2)
{
lean_object* v_i_960_; 
v_i_960_ = lean_ctor_get(v_a_956_, 0);
if (lean_obj_tag(v_i_960_) == 1)
{
lean_object* v_pre_961_; 
v_pre_961_ = lean_ctor_get(v_i_960_, 0);
if (lean_obj_tag(v_pre_961_) == 1)
{
lean_object* v_pre_962_; 
v_pre_962_ = lean_ctor_get(v_pre_961_, 0);
if (lean_obj_tag(v_pre_962_) == 0)
{
lean_object* v_vs_963_; lean_object* v_str_964_; lean_object* v_str_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_vs_963_ = lean_ctor_get(v_a_956_, 1);
v_str_964_ = lean_ctor_get(v_i_960_, 1);
v_str_965_ = lean_ctor_get(v_pre_961_, 1);
v___x_966_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_967_ = lean_string_dec_eq(v_str_965_, v___x_966_);
if (v___x_967_ == 0)
{
goto v___jp_957_;
}
else
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_969_ = lean_string_dec_eq(v_str_964_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_971_ = lean_string_dec_eq(v_str_964_, v___x_970_);
if (v___x_971_ == 0)
{
goto v___jp_957_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_array_get_size(v_vs_963_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_dec_eq(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
goto v___jp_957_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_array_fget_borrowed(v_vs_963_, v___x_975_);
v___x_977_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_976_);
v___x_978_ = lean_nat_add(v___x_977_, v___x_973_);
lean_dec(v___x_977_);
return v___x_978_;
}
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = lean_array_get_size(v_vs_963_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_nat_dec_eq(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
goto v___jp_957_;
}
else
{
return v___x_980_;
}
}
}
}
else
{
goto v___jp_957_;
}
}
else
{
goto v___jp_957_;
}
}
else
{
goto v___jp_957_;
}
}
else
{
goto v___jp_957_;
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2);
v___x_959_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(v___x_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___boxed(lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v_a_982_);
lean_dec(v_a_982_);
return v_res_983_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_984_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Array_instInhabited(lean_box(0));
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(lean_object* v_msg_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_toApplicative_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1031_; 
v___x_994_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0);
v___x_995_ = l_ReaderT_instMonad___redArg(v___x_994_);
v_toApplicative_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v___x_995_, 1);
lean_dec(v_unused_1032_);
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1031_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_toApplicative_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1031_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_toFunctor_1000_; lean_object* v_toSeq_1001_; lean_object* v_toSeqLeft_1002_; lean_object* v_toSeqRight_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1029_; 
v_toFunctor_1000_ = lean_ctor_get(v_toApplicative_996_, 0);
v_toSeq_1001_ = lean_ctor_get(v_toApplicative_996_, 2);
v_toSeqLeft_1002_ = lean_ctor_get(v_toApplicative_996_, 3);
v_toSeqRight_1003_ = lean_ctor_get(v_toApplicative_996_, 4);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_toApplicative_996_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_toApplicative_996_, 1);
lean_dec(v_unused_1030_);
v___x_1005_ = v_toApplicative_996_;
v_isShared_1006_ = v_isSharedCheck_1029_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_toSeqRight_1003_);
lean_inc(v_toSeqLeft_1002_);
lean_inc(v_toSeq_1001_);
lean_inc(v_toFunctor_1000_);
lean_dec(v_toApplicative_996_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1029_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___x_1016_; 
v___f_1007_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1));
v___f_1008_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1000_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toFunctor_1000_);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toFunctor_1000_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___f_1009_);
lean_ctor_set(v___x_1011_, 1, v___f_1010_);
v___f_1012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1012_, 0, v_toSeqRight_1003_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toSeqLeft_1002_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toSeq_1001_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v___f_1012_);
lean_ctor_set(v___x_1005_, 3, v___f_1013_);
lean_ctor_set(v___x_1005_, 2, v___f_1014_);
lean_ctor_set(v___x_1005_, 1, v___f_1007_);
lean_ctor_set(v___x_1005_, 0, v___x_1011_);
v___x_1016_ = v___x_1005_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___f_1007_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v___f_1014_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v___f_1013_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v___f_1012_);
v___x_1016_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___f_1008_);
lean_ctor_set(v___x_998_, 0, v___x_1016_);
v___x_1018_ = v___x_998_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___f_1008_);
v___x_1018_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___x_2075__overap_1025_; lean_object* v___x_1026_; 
v___x_1019_ = l_ReaderT_instMonad___redArg(v___x_1018_);
v___x_1020_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_instInhabitedOfMonad___redArg(v___x_1019_, v___x_1022_);
v___f_1024_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1024_, 0, v___x_1023_);
v___x_2075__overap_1025_ = lean_panic_fn(v___f_1024_, v_msg_988_);
v___x_1026_ = lean_apply_5(v___x_2075__overap_1025_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, lean_box(0));
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object* v_msg_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v_msg_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object* v_as_1040_, size_t v_i_1041_, size_t v_stop_1042_, lean_object* v_b_1043_){
_start:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_usize_dec_eq(v_i_1041_, v_stop_1042_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1062_; 
v___x_1045_ = lean_array_uget_borrowed(v_as_1040_, v_i_1041_);
v_fst_1046_ = lean_ctor_get(v___x_1045_, 0);
v_snd_1047_ = lean_ctor_get(v___x_1045_, 1);
v_fst_1048_ = lean_ctor_get(v_b_1043_, 0);
v_snd_1049_ = lean_ctor_get(v_b_1043_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_b_1043_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1051_ = v_b_1043_;
v_isShared_1052_ = v_isSharedCheck_1062_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_inc(v_fst_1048_);
lean_dec(v_b_1043_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1062_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1053_ = l_Array_append___redArg(v_fst_1048_, v_fst_1046_);
lean_inc(v_snd_1047_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_snd_1047_);
v___x_1055_ = lean_array_push(v_snd_1049_, v___x_1054_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1055_);
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1057_ = v___x_1051_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
size_t v___x_1058_; size_t v___x_1059_; 
v___x_1058_ = ((size_t)1ULL);
v___x_1059_ = lean_usize_add(v_i_1041_, v___x_1058_);
v_i_1041_ = v___x_1059_;
v_b_1043_ = v___x_1057_;
goto _start;
}
}
}
else
{
return v_b_1043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object* v_as_1063_, lean_object* v_i_1064_, lean_object* v_stop_1065_, lean_object* v_b_1066_){
_start:
{
size_t v_i_boxed_1067_; size_t v_stop_boxed_1068_; lean_object* v_res_1069_; 
v_i_boxed_1067_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_stop_boxed_1068_ = lean_unbox_usize(v_stop_1065_);
lean_dec(v_stop_1065_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_as_1063_, v_i_boxed_1067_, v_stop_boxed_1068_, v_b_1066_);
lean_dec_ref(v_as_1063_);
return v_res_1069_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1074_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1075_ = lean_unsigned_to_nat(65u);
v___x_1076_ = lean_unsigned_to_nat(258u);
v___x_1077_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1078_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1079_ = l_mkPanicMessageWithDecl(v___x_1078_, v___x_1077_, v___x_1076_, v___x_1075_, v___x_1074_);
return v___x_1079_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1086_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1087_ = lean_unsigned_to_nat(9u);
v___x_1088_ = lean_unsigned_to_nat(266u);
v___x_1089_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1090_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1091_ = l_mkPanicMessageWithDecl(v___x_1090_, v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; 
if (lean_obj_tag(v_a_1092_) == 2)
{
lean_object* v_i_1147_; lean_object* v_vs_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1269_; 
v_i_1147_ = lean_ctor_get(v_a_1092_, 0);
v_vs_1148_ = lean_ctor_get(v_a_1092_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1150_ = v_a_1092_;
v_isShared_1151_ = v_isSharedCheck_1269_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_vs_1148_);
lean_inc(v_i_1147_);
lean_dec(v_a_1092_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1269_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_ctorName_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; 
if (lean_obj_tag(v_i_1147_) == 1)
{
lean_object* v_pre_1191_; 
v_pre_1191_ = lean_ctor_get(v_i_1147_, 0);
if (lean_obj_tag(v_pre_1191_) == 1)
{
lean_object* v_pre_1192_; 
v_pre_1192_ = lean_ctor_get(v_pre_1191_, 0);
if (lean_obj_tag(v_pre_1192_) == 0)
{
lean_object* v_str_1193_; lean_object* v_str_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v_str_1193_ = lean_ctor_get(v_i_1147_, 1);
v_str_1194_ = lean_ctor_get(v_pre_1191_, 1);
v___x_1195_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_1196_ = lean_string_dec_eq(v_str_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
v_ctorName_1153_ = v_i_1147_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
v___y_1157_ = v_a_1096_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
lean_inc(v_pre_1192_);
lean_inc_ref(v_str_1193_);
lean_dec_ref(v_i_1147_);
v___x_1197_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_1198_ = lean_string_dec_eq(v_str_1193_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_1200_ = lean_string_dec_eq(v_str_1193_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = l_Lean_Name_str___override(v_pre_1192_, v___x_1195_);
v___x_1202_ = l_Lean_Name_str___override(v___x_1201_, v_str_1193_);
v_ctorName_1153_ = v___x_1202_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
v___y_1157_ = v_a_1096_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
lean_dec_ref(v_str_1193_);
v___x_1203_ = lean_array_get_size(v_vs_1148_);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_dec_eq(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = l_Lean_Name_str___override(v_pre_1192_, v___x_1195_);
v___x_1207_ = l_Lean_Name_str___override(v___x_1206_, v___x_1199_);
v_ctorName_1153_ = v___x_1207_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
v___y_1157_ = v_a_1096_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_val_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_del_object(v___x_1150_);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_fget(v_vs_1148_, v___x_1208_);
lean_dec_ref(v_vs_1148_);
v___x_1210_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_1209_);
lean_dec(v___x_1209_);
v_val_1211_ = lean_nat_add(v___x_1210_, v___x_1204_);
lean_dec(v___x_1210_);
v___x_1212_ = 0;
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_val_1211_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1216_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1212_, v___x_1214_, v___x_1215_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1229_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_fvarId_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v_fvarId_1221_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_fvarId_1221_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_a_1217_);
v___x_1223_ = lean_mk_empty_array_with_capacity(v___x_1204_);
v___x_1224_ = lean_array_push(v___x_1223_, v___x_1222_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_fvarId_1221_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1225_);
v___x_1227_ = v___x_1219_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_a_1230_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1216_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1216_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
lean_dec_ref(v_str_1193_);
v___x_1238_ = lean_array_get_size(v_vs_1148_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_nat_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = l_Lean_Name_str___override(v_pre_1192_, v___x_1195_);
v___x_1242_ = l_Lean_Name_str___override(v___x_1241_, v___x_1197_);
v_ctorName_1153_ = v___x_1242_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
v___y_1157_ = v_a_1096_;
goto v___jp_1152_;
}
else
{
uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_del_object(v___x_1150_);
lean_dec_ref(v_vs_1148_);
v___x_1243_ = 0;
v___x_1244_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6));
v___x_1245_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1246_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1243_, v___x_1244_, v___x_1245_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1260_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1260_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1260_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_fvarId_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v_fvarId_1251_ = lean_ctor_get(v_a_1247_, 0);
lean_inc(v_fvarId_1251_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_a_1247_);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_mk_empty_array_with_capacity(v___x_1253_);
v___x_1255_ = lean_array_push(v___x_1254_, v___x_1252_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_fvarId_1251_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1256_);
v___x_1258_ = v___x_1249_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1246_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1246_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
}
else
{
v_ctorName_1153_ = v_i_1147_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
v___y_1157_ = v_a_1096_;
goto v___jp_1152_;
}
}
else
{
v_ctorName_1153_ = v_i_1147_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
v___y_1157_ = v_a_1096_;
goto v___jp_1152_;
}
}
else
{
v_ctorName_1153_ = v_i_1147_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
v___y_1157_ = v_a_1096_;
goto v___jp_1152_;
}
v___jp_1152_:
{
lean_object* v___x_1158_; lean_object* v_env_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = lean_st_ref_get(v___y_1157_);
v_env_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_ref(v_env_1159_);
lean_dec(v___x_1158_);
v___x_1160_ = 0;
lean_inc(v_ctorName_1153_);
v___x_1161_ = l_Lean_Environment_find_x3f(v_env_1159_, v_ctorName_1153_, v___x_1160_);
if (lean_obj_tag(v___x_1161_) == 1)
{
lean_object* v_val_1162_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v___x_1161_);
if (lean_obj_tag(v_val_1162_) == 6)
{
lean_object* v_val_1163_; size_t v_sz_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
v_val_1163_ = lean_ctor_get(v_val_1162_, 0);
lean_inc_ref(v_val_1163_);
lean_dec_ref(v_val_1162_);
v_sz_1164_ = lean_array_size(v_vs_1148_);
v___x_1165_ = ((size_t)0ULL);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_1164_, v___x_1165_, v_vs_1148_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_numParams_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v___x_1166_);
v_numParams_1168_ = lean_ctor_get(v_val_1163_, 3);
lean_inc(v_numParams_1168_);
lean_dec_ref(v_val_1163_);
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4));
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_mk_array(v_numParams_1168_, v___x_1171_);
v___x_1173_ = lean_array_get_size(v_a_1167_);
v___x_1174_ = lean_nat_dec_lt(v___x_1169_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_dec(v_a_1167_);
lean_del_object(v___x_1150_);
v___y_1099_ = v___y_1157_;
v___y_1100_ = v___y_1156_;
v___y_1101_ = v___y_1155_;
v___y_1102_ = v___y_1154_;
v___y_1103_ = v_ctorName_1153_;
v_fst_1104_ = v___x_1170_;
v_snd_1105_ = v___x_1172_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1176_; 
lean_inc_ref(v___x_1172_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 0);
lean_ctor_set(v___x_1150_, 1, v___x_1172_);
lean_ctor_set(v___x_1150_, 0, v___x_1170_);
v___x_1176_ = v___x_1150_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1172_);
v___x_1176_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_nat_dec_le(v___x_1173_, v___x_1173_);
if (v___x_1177_ == 0)
{
if (v___x_1174_ == 0)
{
lean_dec_ref(v___x_1176_);
lean_dec(v_a_1167_);
v___y_1099_ = v___y_1157_;
v___y_1100_ = v___y_1156_;
v___y_1101_ = v___y_1155_;
v___y_1102_ = v___y_1154_;
v___y_1103_ = v_ctorName_1153_;
v_fst_1104_ = v___x_1170_;
v_snd_1105_ = v___x_1172_;
goto v___jp_1098_;
}
else
{
size_t v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v___x_1172_);
v___x_1178_ = lean_usize_of_nat(v___x_1173_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1167_, v___x_1165_, v___x_1178_, v___x_1176_);
lean_dec(v_a_1167_);
v___y_1132_ = v___y_1157_;
v___y_1133_ = v___y_1156_;
v___y_1134_ = v_ctorName_1153_;
v___y_1135_ = v___y_1154_;
v___y_1136_ = v___y_1155_;
v___y_1137_ = v___x_1179_;
goto v___jp_1131_;
}
}
else
{
size_t v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref(v___x_1172_);
v___x_1180_ = lean_usize_of_nat(v___x_1173_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1167_, v___x_1165_, v___x_1180_, v___x_1176_);
lean_dec(v_a_1167_);
v___y_1132_ = v___y_1157_;
v___y_1133_ = v___y_1156_;
v___y_1134_ = v_ctorName_1153_;
v___y_1135_ = v___y_1154_;
v___y_1136_ = v___y_1155_;
v___y_1137_ = v___x_1181_;
goto v___jp_1131_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v_val_1163_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v_ctorName_1153_);
lean_del_object(v___x_1150_);
v_a_1183_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1166_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1166_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_dec(v_val_1162_);
lean_dec(v_ctorName_1153_);
lean_del_object(v___x_1150_);
lean_dec_ref(v_vs_1148_);
v___y_1141_ = v___y_1154_;
v___y_1142_ = v___y_1155_;
v___y_1143_ = v___y_1156_;
v___y_1144_ = v___y_1157_;
goto v___jp_1140_;
}
}
else
{
lean_dec(v___x_1161_);
lean_dec(v_ctorName_1153_);
lean_del_object(v___x_1150_);
lean_dec_ref(v_vs_1148_);
v___y_1141_ = v___y_1154_;
v___y_1142_ = v___y_1155_;
v___y_1143_ = v___y_1156_;
v___y_1144_ = v___y_1157_;
goto v___jp_1140_;
}
}
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_a_1092_);
v___x_1270_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7);
v___x_1271_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1270_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1271_;
}
v___jp_1098_:
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1106_ = 0;
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___y_1103_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
lean_ctor_set(v___x_1108_, 2, v_snd_1105_);
v___x_1109_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1110_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1106_, v___x_1108_, v___x_1109_, v___y_1102_, v___y_1101_, v___y_1100_, v___y_1099_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1122_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_fvarId_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_fvarId_1115_ = lean_ctor_get(v_a_1111_, 0);
lean_inc(v_fvarId_1115_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_a_1111_);
v___x_1117_ = lean_array_push(v_fst_1104_, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_fvarId_1115_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1118_);
v___x_1120_ = v___x_1113_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_fst_1104_);
v_a_1123_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1110_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1110_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
v___jp_1131_:
{
lean_object* v_fst_1138_; lean_object* v_snd_1139_; 
v_fst_1138_ = lean_ctor_get(v___y_1137_, 0);
lean_inc(v_fst_1138_);
v_snd_1139_ = lean_ctor_get(v___y_1137_, 1);
lean_inc(v_snd_1139_);
lean_dec_ref(v___y_1137_);
v___y_1099_ = v___y_1132_;
v___y_1100_ = v___y_1133_;
v___y_1101_ = v___y_1136_;
v___y_1102_ = v___y_1135_;
v___y_1103_ = v___y_1134_;
v_fst_1104_ = v_fst_1138_;
v_snd_1105_ = v_snd_1139_;
goto v___jp_1098_;
}
v___jp_1140_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3);
v___x_1146_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1145_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(size_t v_sz_1272_, size_t v_i_1273_, lean_object* v_bs_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_usize_dec_lt(v_i_1273_, v_sz_1272_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_bs_1274_);
return v___x_1281_;
}
else
{
lean_object* v_v_1282_; lean_object* v___x_1283_; 
v_v_1282_ = lean_array_uget_borrowed(v_bs_1274_, v_i_1273_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v_v_1282_);
v___x_1283_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1282_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v_bs_x27_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v_bs_x27_1286_ = lean_array_uset(v_bs_1274_, v_i_1273_, v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_add(v_i_1273_, v___x_1287_);
v___x_1289_ = lean_array_uset(v_bs_x27_1286_, v_i_1273_, v_a_1284_);
v_i_1273_ = v___x_1288_;
v_bs_1274_ = v___x_1289_;
goto _start;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec_ref(v_bs_1274_);
v_a_1291_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1283_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object* v_sz_1299_, lean_object* v_i_1300_, lean_object* v_bs_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_boxed_1307_, v_i_boxed_1308_, v_bs_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(lean_object* v_v_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_v_1317_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_v_1317_);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1326_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1326_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral___boxed(lean_object* v_v_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_v_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(lean_object* v_a_1351_, lean_object* v_b_1352_){
_start:
{
lean_object* v_fst_1353_; lean_object* v_fst_1354_; uint8_t v___x_1355_; 
v_fst_1353_ = lean_ctor_get(v_a_1351_, 0);
v_fst_1354_ = lean_ctor_get(v_b_1352_, 0);
v___x_1355_ = l_Lean_Name_quickLt(v_fst_1353_, v_fst_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed(lean_object* v_a_1356_, lean_object* v_b_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(v_a_1356_, v_b_1357_);
lean_dec_ref(v_b_1357_);
lean_dec_ref(v_a_1356_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(lean_object* v_entries_1362_, lean_object* v_fid_1363_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_array_get_size(v_entries_1362_);
v___x_1366_ = lean_nat_dec_lt(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec(v_fid_1363_);
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_sub(v___x_1365_, v___x_1368_);
v___x_1370_ = lean_nat_dec_le(v___x_1364_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v___x_1369_);
lean_dec(v_fid_1363_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_fid_1363_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0));
v___x_1375_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1));
v___x_1376_ = l_Array_binSearchAux___redArg(v___x_1374_, v___x_1375_, v_entries_1362_, v___x_1373_, v___x_1364_, v___x_1369_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_box(0);
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1386_; 
v_val_1378_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1380_ = v___x_1376_;
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_val_1378_);
lean_dec(v___x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_snd_1382_; lean_object* v___x_1384_; 
v_snd_1382_ = lean_ctor_get(v_val_1378_, 1);
lean_inc(v_snd_1382_);
lean_dec(v_val_1378_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v_snd_1382_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_snd_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___boxed(lean_object* v_entries_1387_, lean_object* v_fid_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(v_entries_1387_, v_fid_1388_);
lean_dec_ref(v_entries_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_es_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_array_mk(v_es_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1392_, lean_object* v_i_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_array_get_size(v_keys_1392_);
v___x_1396_ = lean_nat_dec_lt(v_i_1393_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec(v_i_1393_);
return v___x_1396_;
}
else
{
lean_object* v_k_x27_1397_; uint8_t v___x_1398_; 
v_k_x27_1397_ = lean_array_fget_borrowed(v_keys_1392_, v_i_1393_);
v___x_1398_ = lean_name_eq(v_k_1394_, v_k_x27_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = lean_nat_add(v_i_1393_, v___x_1399_);
lean_dec(v_i_1393_);
v_i_1393_ = v___x_1400_;
goto _start;
}
else
{
lean_dec(v_i_1393_);
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1402_, lean_object* v_i_1403_, lean_object* v_k_1404_){
_start:
{
uint8_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1402_, v_i_1403_, v_k_1404_);
lean_dec(v_k_1404_);
lean_dec_ref(v_keys_1402_);
v_r_1406_ = lean_box(v_res_1405_);
return v_r_1406_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; 
v___x_1407_ = ((size_t)5ULL);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_shift_left(v___x_1408_, v___x_1407_);
return v___x_1409_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; 
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_1412_ = lean_usize_sub(v___x_1411_, v___x_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1413_, size_t v_x_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v_es_1416_; lean_object* v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; size_t v___x_1420_; lean_object* v_j_1421_; lean_object* v___x_1422_; 
v_es_1416_ = lean_ctor_get(v_x_1413_, 0);
lean_inc_ref(v_es_1416_);
lean_dec_ref(v_x_1413_);
v___x_1417_ = lean_box(2);
v___x_1418_ = ((size_t)5ULL);
v___x_1419_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1420_ = lean_usize_land(v_x_1414_, v___x_1419_);
v_j_1421_ = lean_usize_to_nat(v___x_1420_);
v___x_1422_ = lean_array_get(v___x_1417_, v_es_1416_, v_j_1421_);
lean_dec(v_j_1421_);
lean_dec_ref(v_es_1416_);
switch(lean_obj_tag(v___x_1422_))
{
case 0:
{
lean_object* v_key_1423_; uint8_t v___x_1424_; 
v_key_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_key_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_name_eq(v_x_1415_, v_key_1423_);
lean_dec(v_key_1423_);
return v___x_1424_;
}
case 1:
{
lean_object* v_node_1425_; size_t v___x_1426_; 
v_node_1425_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_node_1425_);
lean_dec_ref(v___x_1422_);
v___x_1426_ = lean_usize_shift_right(v_x_1414_, v___x_1418_);
v_x_1413_ = v_node_1425_;
v_x_1414_ = v___x_1426_;
goto _start;
}
default: 
{
uint8_t v___x_1428_; 
v___x_1428_ = 0;
return v___x_1428_;
}
}
}
else
{
lean_object* v_ks_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_ks_1429_ = lean_ctor_get(v_x_1413_, 0);
lean_inc_ref(v_ks_1429_);
lean_dec_ref(v_x_1413_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1429_, v___x_1430_, v_x_1415_);
lean_dec_ref(v_ks_1429_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
size_t v_x_1122__boxed_1435_; uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_x_1122__boxed_1435_ = lean_unbox_usize(v_x_1433_);
lean_dec(v_x_1433_);
v_res_1436_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1432_, v_x_1122__boxed_1435_, v_x_1434_);
lean_dec(v_x_1434_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1438_; uint64_t v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1723u);
v___x_1439_ = lean_uint64_of_nat(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
uint64_t v___y_1443_; 
if (lean_obj_tag(v_x_1441_) == 0)
{
uint64_t v___x_1446_; 
v___x_1446_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1443_ = v___x_1446_;
goto v___jp_1442_;
}
else
{
uint64_t v_hash_1447_; 
v_hash_1447_ = lean_ctor_get_uint64(v_x_1441_, sizeof(void*)*2);
v___y_1443_ = v_hash_1447_;
goto v___jp_1442_;
}
v___jp_1442_:
{
size_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_uint64_to_usize(v___y_1443_);
v___x_1445_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1440_, v___x_1444_, v_x_1441_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(v_x_1448_, v_x_1449_);
lean_dec(v_x_1449_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_x1_1452_, lean_object* v_x2_1453_){
_start:
{
lean_object* v_fst_1454_; uint8_t v___x_1455_; 
v_fst_1454_ = lean_ctor_get(v_x2_1453_, 0);
v___x_1455_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(v_x1_1452_, v_fst_1454_);
if (v___x_1455_ == 0)
{
uint8_t v___x_1456_; 
v___x_1456_ = 1;
return v___x_1456_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = 0;
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_x1_1458_, lean_object* v_x2_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(v_x1_1458_, v_x2_1459_);
lean_dec_ref(v_x2_1459_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_fst_1464_; lean_object* v_fst_1465_; uint8_t v___x_1466_; 
v_fst_1464_ = lean_ctor_get(v___y_1462_, 0);
v_fst_1465_ = lean_ctor_get(v___y_1463_, 0);
v___x_1466_ = l_Lean_Name_quickLt(v_fst_1464_, v_fst_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1467_, v___y_1468_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v___y_1467_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_1472_, lean_object* v_lo_1473_, lean_object* v_hi_1474_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_nat_dec_lt(v_lo_1473_, v_hi_1474_);
if (v___x_1475_ == 0)
{
lean_dec(v_lo_1473_);
return v_as_1472_;
}
else
{
lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; uint8_t v___x_1480_; 
v___f_1476_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_1473_);
v___x_1477_ = l_Array_qpartition___redArg(v_as_1472_, v___f_1476_, v_lo_1473_, v_hi_1474_);
v_fst_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_fst_1478_);
v_snd_1479_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_snd_1479_);
lean_dec_ref(v___x_1477_);
v___x_1480_ = lean_nat_dec_le(v_hi_1474_, v_fst_1478_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v_snd_1479_, v_lo_1473_, v_fst_1478_);
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_nat_add(v_fst_1478_, v___x_1482_);
lean_dec(v_fst_1478_);
v_as_1472_ = v___x_1481_;
v_lo_1473_ = v___x_1483_;
goto _start;
}
else
{
lean_dec(v_fst_1478_);
lean_dec(v_lo_1473_);
return v_snd_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_1485_, lean_object* v_lo_1486_, lean_object* v_hi_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v_as_1485_, v_lo_1486_, v_hi_1487_);
lean_dec(v_hi_1487_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1489_, lean_object* v_keys_1490_, lean_object* v_vals_1491_, lean_object* v_i_1492_, lean_object* v_acc_1493_){
_start:
{
lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = lean_array_get_size(v_keys_1490_);
v___x_1495_ = lean_nat_dec_lt(v_i_1492_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_dec(v_i_1492_);
lean_dec(v_f_1489_);
return v_acc_1493_;
}
else
{
lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_k_1496_ = lean_array_fget_borrowed(v_keys_1490_, v_i_1492_);
v_v_1497_ = lean_array_fget_borrowed(v_vals_1491_, v_i_1492_);
lean_inc(v_f_1489_);
lean_inc(v_v_1497_);
lean_inc(v_k_1496_);
v___x_1498_ = lean_apply_3(v_f_1489_, v_acc_1493_, v_k_1496_, v_v_1497_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_i_1492_, v___x_1499_);
lean_dec(v_i_1492_);
v_i_1492_ = v___x_1500_;
v_acc_1493_ = v___x_1498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1502_, lean_object* v_keys_1503_, lean_object* v_vals_1504_, lean_object* v_i_1505_, lean_object* v_acc_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1502_, v_keys_1503_, v_vals_1504_, v_i_1505_, v_acc_1506_);
lean_dec_ref(v_vals_1504_);
lean_dec_ref(v_keys_1503_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v_es_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_es_1511_ = lean_ctor_get(v_x_1509_, 0);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_array_get_size(v_es_1511_);
v___x_1514_ = lean_nat_dec_lt(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_dec(v_f_1508_);
return v_x_1510_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_nat_dec_le(v___x_1513_, v___x_1513_);
if (v___x_1515_ == 0)
{
if (v___x_1514_ == 0)
{
lean_dec(v_f_1508_);
return v_x_1510_;
}
else
{
size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_of_nat(v___x_1513_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1508_, v_es_1511_, v___x_1516_, v___x_1517_, v_x_1510_);
return v___x_1518_;
}
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1513_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1508_, v_es_1511_, v___x_1519_, v___x_1520_, v_x_1510_);
return v___x_1521_;
}
}
}
else
{
lean_object* v_ks_1522_; lean_object* v_vs_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_ks_1522_ = lean_ctor_get(v_x_1509_, 0);
v_vs_1523_ = lean_ctor_get(v_x_1509_, 1);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1508_, v_ks_1522_, v_vs_1523_, v___x_1524_, v_x_1510_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(lean_object* v_f_1526_, lean_object* v_as_1527_, size_t v_i_1528_, size_t v_stop_1529_, lean_object* v_b_1530_){
_start:
{
lean_object* v___y_1532_; uint8_t v___x_1536_; 
v___x_1536_ = lean_usize_dec_eq(v_i_1528_, v_stop_1529_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_array_uget_borrowed(v_as_1527_, v_i_1528_);
switch(lean_obj_tag(v___x_1537_))
{
case 0:
{
lean_object* v_key_1538_; lean_object* v_val_1539_; lean_object* v___x_1540_; 
v_key_1538_ = lean_ctor_get(v___x_1537_, 0);
v_val_1539_ = lean_ctor_get(v___x_1537_, 1);
lean_inc(v_f_1526_);
lean_inc(v_val_1539_);
lean_inc(v_key_1538_);
v___x_1540_ = lean_apply_3(v_f_1526_, v_b_1530_, v_key_1538_, v_val_1539_);
v___y_1532_ = v___x_1540_;
goto v___jp_1531_;
}
case 1:
{
lean_object* v_node_1541_; lean_object* v___x_1542_; 
v_node_1541_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_f_1526_);
v___x_1542_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1526_, v_node_1541_, v_b_1530_);
v___y_1532_ = v___x_1542_;
goto v___jp_1531_;
}
default: 
{
v___y_1532_ = v_b_1530_;
goto v___jp_1531_;
}
}
}
else
{
lean_dec(v_f_1526_);
return v_b_1530_;
}
v___jp_1531_:
{
size_t v___x_1533_; size_t v___x_1534_; 
v___x_1533_ = ((size_t)1ULL);
v___x_1534_ = lean_usize_add(v_i_1528_, v___x_1533_);
v_i_1528_ = v___x_1534_;
v_b_1530_ = v___y_1532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_f_1543_, lean_object* v_as_1544_, lean_object* v_i_1545_, lean_object* v_stop_1546_, lean_object* v_b_1547_){
_start:
{
size_t v_i_boxed_1548_; size_t v_stop_boxed_1549_; lean_object* v_res_1550_; 
v_i_boxed_1548_ = lean_unbox_usize(v_i_1545_);
lean_dec(v_i_1545_);
v_stop_boxed_1549_ = lean_unbox_usize(v_stop_1546_);
lean_dec(v_stop_1546_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1543_, v_as_1544_, v_i_boxed_1548_, v_stop_boxed_1549_, v_b_1547_);
lean_dec_ref(v_as_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1551_, v_x_1552_, v_x_1553_);
lean_dec_ref(v_x_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1555_, lean_object* v_x1_1556_, lean_object* v_x2_1557_, lean_object* v_x3_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_apply_3(v_f_1555_, v_x1_1556_, v_x2_1557_, v_x3_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1560_, lean_object* v_f_1561_, lean_object* v_init_1562_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; 
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1563_, 0, v_f_1561_);
v___x_1564_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1563_, v_map_1560_, v_init_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1565_, lean_object* v_f_1566_, lean_object* v_init_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1565_, v_f_1566_, v_init_1567_);
lean_dec_ref(v_map_1565_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1569_, lean_object* v_k_1570_, lean_object* v_v_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_k_1570_);
lean_ctor_set(v___x_1572_, 1, v_v_1571_);
v___x_1573_ = lean_array_push(v_ps_1569_, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1577_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___f_1578_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1579_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1580_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1577_, v___f_1578_, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(v_m_1581_);
lean_dec_ref(v_m_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_x_1585_, lean_object* v_s_1586_, lean_object* v_x_1587_, uint8_t v_x_1588_){
_start:
{
if (v_x_1588_ == 2)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1589_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(v_s_1586_);
v___x_1590_ = lean_array_get_size(v___x_1589_);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_nat_dec_eq(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___y_1596_; uint8_t v___x_1600_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_sub(v___x_1590_, v___x_1593_);
v___x_1600_ = lean_nat_dec_le(v___x_1591_, v___x_1594_);
if (v___x_1600_ == 0)
{
lean_inc(v___x_1594_);
v___y_1596_ = v___x_1594_;
goto v___jp_1595_;
}
else
{
v___y_1596_ = v___x_1591_;
goto v___jp_1595_;
}
v___jp_1595_:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_nat_dec_le(v___y_1596_, v___x_1594_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec(v___x_1594_);
lean_inc(v___y_1596_);
v___x_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v___x_1589_, v___y_1596_, v___y_1596_);
lean_dec(v___y_1596_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v___x_1589_, v___y_1596_, v___x_1594_);
lean_dec(v___x_1594_);
return v___x_1599_;
}
}
}
else
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_));
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_x_1602_, lean_object* v_s_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
uint8_t v_x_1342__boxed_1606_; lean_object* v_res_1607_; 
v_x_1342__boxed_1606_ = lean_unbox(v_x_1605_);
v_res_1607_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(v_x_1602_, v_s_1603_, v_x_1604_, v_x_1342__boxed_1606_);
lean_dec(v_x_1604_);
lean_dec_ref(v_s_1603_);
lean_dec_ref(v_x_1602_);
return v_res_1607_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_x_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(v_x_1613_);
lean_dec_ref(v_x_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v_ks_1619_; lean_object* v_vs_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1644_; 
v_ks_1619_ = lean_ctor_get(v_x_1615_, 0);
v_vs_1620_ = lean_ctor_get(v_x_1615_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1622_ = v_x_1615_;
v_isShared_1623_ = v_isSharedCheck_1644_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_vs_1620_);
lean_inc(v_ks_1619_);
lean_dec(v_x_1615_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1644_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = lean_array_get_size(v_ks_1619_);
v___x_1625_ = lean_nat_dec_lt(v_x_1616_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_x_1616_);
v___x_1626_ = lean_array_push(v_ks_1619_, v_x_1617_);
v___x_1627_ = lean_array_push(v_vs_1620_, v_x_1618_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1627_);
lean_ctor_set(v___x_1622_, 0, v___x_1626_);
v___x_1629_ = v___x_1622_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v_k_x27_1631_; uint8_t v___x_1632_; 
v_k_x27_1631_ = lean_array_fget_borrowed(v_ks_1619_, v_x_1616_);
v___x_1632_ = lean_name_eq(v_x_1617_, v_k_x27_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1634_; 
if (v_isShared_1623_ == 0)
{
v___x_1634_ = v___x_1622_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_ks_1619_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_vs_1620_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_x_1616_, v___x_1635_);
lean_dec(v_x_1616_);
v_x_1615_ = v___x_1634_;
v_x_1616_ = v___x_1636_;
goto _start;
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1639_ = lean_array_fset(v_ks_1619_, v_x_1616_, v_x_1617_);
v___x_1640_ = lean_array_fset(v_vs_1620_, v_x_1616_, v_x_1618_);
lean_dec(v_x_1616_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1640_);
lean_ctor_set(v___x_1622_, 0, v___x_1639_);
v___x_1642_ = v___x_1622_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object* v_n_1645_, lean_object* v_k_1646_, lean_object* v_v_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(v_n_1645_, v___x_1648_, v_k_1646_, v_v_1647_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_1651_, size_t v_x_1652_, size_t v_x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 0)
{
lean_object* v_es_1656_; size_t v___x_1657_; size_t v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; lean_object* v_j_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_es_1656_ = lean_ctor_get(v_x_1651_, 0);
v___x_1657_ = ((size_t)5ULL);
v___x_1658_ = ((size_t)1ULL);
v___x_1659_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1660_ = lean_usize_land(v_x_1652_, v___x_1659_);
v_j_1661_ = lean_usize_to_nat(v___x_1660_);
v___x_1662_ = lean_array_get_size(v_es_1656_);
v___x_1663_ = lean_nat_dec_lt(v_j_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_dec(v_j_1661_);
lean_dec(v_x_1655_);
lean_dec(v_x_1654_);
return v_x_1651_;
}
else
{
lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1700_; 
lean_inc_ref(v_es_1656_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_x_1651_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v_x_1651_, 0);
lean_dec(v_unused_1701_);
v___x_1665_ = v_x_1651_;
v_isShared_1666_ = v_isSharedCheck_1700_;
goto v_resetjp_1664_;
}
else
{
lean_dec(v_x_1651_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1700_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_v_1667_; lean_object* v___x_1668_; lean_object* v_xs_x27_1669_; lean_object* v___y_1671_; 
v_v_1667_ = lean_array_fget(v_es_1656_, v_j_1661_);
v___x_1668_ = lean_box(0);
v_xs_x27_1669_ = lean_array_fset(v_es_1656_, v_j_1661_, v___x_1668_);
switch(lean_obj_tag(v_v_1667_))
{
case 0:
{
lean_object* v_key_1676_; lean_object* v_val_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1687_; 
v_key_1676_ = lean_ctor_get(v_v_1667_, 0);
v_val_1677_ = lean_ctor_get(v_v_1667_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_v_1667_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1679_ = v_v_1667_;
v_isShared_1680_ = v_isSharedCheck_1687_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_val_1677_);
lean_inc(v_key_1676_);
lean_dec(v_v_1667_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1687_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
uint8_t v___x_1681_; 
v___x_1681_ = lean_name_eq(v_x_1654_, v_key_1676_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_del_object(v___x_1679_);
v___x_1682_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1676_, v_val_1677_, v_x_1654_, v_x_1655_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
v___y_1671_ = v___x_1683_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1685_; 
lean_dec(v_val_1677_);
lean_dec(v_key_1676_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v_x_1655_);
lean_ctor_set(v___x_1679_, 0, v_x_1654_);
v___x_1685_ = v___x_1679_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_x_1654_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_x_1655_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v___y_1671_ = v___x_1685_;
goto v___jp_1670_;
}
}
}
}
case 1:
{
lean_object* v_node_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1698_; 
v_node_1688_ = lean_ctor_get(v_v_1667_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_v_1667_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1690_ = v_v_1667_;
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_node_1688_);
lean_dec(v_v_1667_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1692_ = lean_usize_shift_right(v_x_1652_, v___x_1657_);
v___x_1693_ = lean_usize_add(v_x_1653_, v___x_1658_);
v___x_1694_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_1688_, v___x_1692_, v___x_1693_, v_x_1654_, v_x_1655_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1694_);
v___x_1696_ = v___x_1690_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
v___y_1671_ = v___x_1696_;
goto v___jp_1670_;
}
}
}
default: 
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_x_1654_);
lean_ctor_set(v___x_1699_, 1, v_x_1655_);
v___y_1671_ = v___x_1699_;
goto v___jp_1670_;
}
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = lean_array_fset(v_xs_x27_1669_, v_j_1661_, v___y_1671_);
lean_dec(v_j_1661_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1672_);
v___x_1674_ = v___x_1665_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_object* v_ks_1702_; lean_object* v_vs_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1723_; 
v_ks_1702_ = lean_ctor_get(v_x_1651_, 0);
v_vs_1703_ = lean_ctor_get(v_x_1651_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_x_1651_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1705_ = v_x_1651_;
v_isShared_1706_ = v_isSharedCheck_1723_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_vs_1703_);
lean_inc(v_ks_1702_);
lean_dec(v_x_1651_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1723_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_ks_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_vs_1703_);
v___x_1708_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v_newNode_1709_; uint8_t v___y_1711_; size_t v___x_1717_; uint8_t v___x_1718_; 
v_newNode_1709_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v___x_1708_, v_x_1654_, v_x_1655_);
v___x_1717_ = ((size_t)7ULL);
v___x_1718_ = lean_usize_dec_le(v___x_1717_, v_x_1653_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1719_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1709_);
v___x_1720_ = lean_unsigned_to_nat(4u);
v___x_1721_ = lean_nat_dec_lt(v___x_1719_, v___x_1720_);
lean_dec(v___x_1719_);
v___y_1711_ = v___x_1721_;
goto v___jp_1710_;
}
else
{
v___y_1711_ = v___x_1718_;
goto v___jp_1710_;
}
v___jp_1710_:
{
if (v___y_1711_ == 0)
{
lean_object* v_ks_1712_; lean_object* v_vs_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_ks_1712_ = lean_ctor_get(v_newNode_1709_, 0);
lean_inc_ref(v_ks_1712_);
v_vs_1713_ = lean_ctor_get(v_newNode_1709_, 1);
lean_inc_ref(v_vs_1713_);
lean_dec_ref(v_newNode_1709_);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_1716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_x_1653_, v_ks_1712_, v_vs_1713_, v___x_1714_, v___x_1715_);
lean_dec_ref(v_vs_1713_);
lean_dec_ref(v_ks_1712_);
return v___x_1716_;
}
else
{
return v_newNode_1709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(size_t v_depth_1724_, lean_object* v_keys_1725_, lean_object* v_vals_1726_, lean_object* v_i_1727_, lean_object* v_entries_1728_){
_start:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = lean_array_get_size(v_keys_1725_);
v___x_1730_ = lean_nat_dec_lt(v_i_1727_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_dec(v_i_1727_);
return v_entries_1728_;
}
else
{
lean_object* v_k_1731_; lean_object* v_v_1732_; uint64_t v___y_1734_; 
v_k_1731_ = lean_array_fget_borrowed(v_keys_1725_, v_i_1727_);
v_v_1732_ = lean_array_fget_borrowed(v_vals_1726_, v_i_1727_);
if (lean_obj_tag(v_k_1731_) == 0)
{
uint64_t v___x_1745_; 
v___x_1745_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1734_ = v___x_1745_;
goto v___jp_1733_;
}
else
{
uint64_t v_hash_1746_; 
v_hash_1746_ = lean_ctor_get_uint64(v_k_1731_, sizeof(void*)*2);
v___y_1734_ = v_hash_1746_;
goto v___jp_1733_;
}
v___jp_1733_:
{
size_t v_h_1735_; size_t v___x_1736_; lean_object* v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v_h_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_h_1735_ = lean_uint64_to_usize(v___y_1734_);
v___x_1736_ = ((size_t)5ULL);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_sub(v_depth_1724_, v___x_1738_);
v___x_1740_ = lean_usize_mul(v___x_1736_, v___x_1739_);
v_h_1741_ = lean_usize_shift_right(v_h_1735_, v___x_1740_);
v___x_1742_ = lean_nat_add(v_i_1727_, v___x_1737_);
lean_dec(v_i_1727_);
lean_inc(v_v_1732_);
lean_inc(v_k_1731_);
v___x_1743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_1728_, v_h_1741_, v_depth_1724_, v_k_1731_, v_v_1732_);
v_i_1727_ = v___x_1742_;
v_entries_1728_ = v___x_1743_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_1747_, lean_object* v_keys_1748_, lean_object* v_vals_1749_, lean_object* v_i_1750_, lean_object* v_entries_1751_){
_start:
{
size_t v_depth_boxed_1752_; lean_object* v_res_1753_; 
v_depth_boxed_1752_ = lean_unbox_usize(v_depth_1747_);
lean_dec(v_depth_1747_);
v_res_1753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_depth_boxed_1752_, v_keys_1748_, v_vals_1749_, v_i_1750_, v_entries_1751_);
lean_dec_ref(v_vals_1749_);
lean_dec_ref(v_keys_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
size_t v_x_1479__boxed_1759_; size_t v_x_1480__boxed_1760_; lean_object* v_res_1761_; 
v_x_1479__boxed_1759_ = lean_unbox_usize(v_x_1755_);
lean_dec(v_x_1755_);
v_x_1480__boxed_1760_ = lean_unbox_usize(v_x_1756_);
lean_dec(v_x_1756_);
v_res_1761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1754_, v_x_1479__boxed_1759_, v_x_1480__boxed_1760_, v_x_1757_, v_x_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint64_t v___y_1766_; 
if (lean_obj_tag(v_x_1763_) == 0)
{
uint64_t v___x_1770_; 
v___x_1770_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1766_ = v___x_1770_;
goto v___jp_1765_;
}
else
{
uint64_t v_hash_1771_; 
v_hash_1771_ = lean_ctor_get_uint64(v_x_1763_, sizeof(void*)*2);
v___y_1766_ = v_hash_1771_;
goto v___jp_1765_;
}
v___jp_1765_:
{
size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_uint64_to_usize(v___y_1766_);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1762_, v___x_1767_, v___x_1768_, v_x_1763_, v_x_1764_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_s_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v_fst_1774_; lean_object* v_snd_1775_; lean_object* v___x_1776_; 
v_fst_1774_ = lean_ctor_get(v_x_1773_, 0);
lean_inc(v_fst_1774_);
v_snd_1775_ = lean_ctor_get(v_x_1773_, 1);
lean_inc(v_snd_1775_);
lean_dec_ref(v_x_1773_);
v___x_1776_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(v_s_1772_, v_fst_1774_, v_snd_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_));
v___x_1810_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_();
return v_res_1812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(v_x_1814_, v_x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_res_1820_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0(v_00_u03b2_1817_, v_x_1818_, v_x_1819_);
lean_dec(v_x_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1822_, lean_object* v_m_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(v_m_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1825_, lean_object* v_m_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1(v_00_u03b2_1825_, v_m_1826_);
lean_dec_ref(v_m_1826_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2(lean_object* v_n_1828_, lean_object* v_as_1829_, lean_object* v_lo_1830_, lean_object* v_hi_1831_, lean_object* v_w_1832_, lean_object* v_hlo_1833_, lean_object* v_hhi_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v_as_1829_, v_lo_1830_, v_hi_1831_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1836_, lean_object* v_as_1837_, lean_object* v_lo_1838_, lean_object* v_hi_1839_, lean_object* v_w_1840_, lean_object* v_hlo_1841_, lean_object* v_hhi_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2(v_n_1836_, v_as_1837_, v_lo_1838_, v_hi_1839_, v_w_1840_, v_hlo_1841_, v_hhi_1842_);
lean_dec(v_hi_1839_);
lean_dec(v_n_1836_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(v_x_1845_, v_x_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1849_, lean_object* v_x_1850_, size_t v_x_1851_, lean_object* v_x_1852_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1850_, v_x_1851_, v_x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
size_t v_x_1786__boxed_1858_; uint8_t v_res_1859_; lean_object* v_r_1860_; 
v_x_1786__boxed_1858_ = lean_unbox_usize(v_x_1856_);
lean_dec(v_x_1856_);
v_res_1859_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1854_, v_x_1855_, v_x_1786__boxed_1858_, v_x_1857_);
lean_dec(v_x_1857_);
v_r_1860_ = lean_box(v_res_1859_);
return v_r_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_map_1863_, lean_object* v_f_1864_, lean_object* v_init_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1863_, v_f_1864_, v_init_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_map_1869_, lean_object* v_f_1870_, lean_object* v_init_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1867_, v_00_u03b2_1868_, v_map_1869_, v_f_1870_, v_init_1871_);
lean_dec_ref(v_map_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_1873_, lean_object* v_x_1874_, size_t v_x_1875_, size_t v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1874_, v_x_1875_, v_x_1876_, v_x_1877_, v_x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
size_t v_x_1799__boxed_1886_; size_t v_x_1800__boxed_1887_; lean_object* v_res_1888_; 
v_x_1799__boxed_1886_ = lean_unbox_usize(v_x_1882_);
lean_dec(v_x_1882_);
v_x_1800__boxed_1887_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_res_1888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_1880_, v_x_1881_, v_x_1799__boxed_1886_, v_x_1800__boxed_1887_, v_x_1884_, v_x_1885_);
return v_res_1888_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1889_, lean_object* v_keys_1890_, lean_object* v_vals_1891_, lean_object* v_heq_1892_, lean_object* v_i_1893_, lean_object* v_k_1894_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1890_, v_i_1893_, v_k_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1896_, lean_object* v_keys_1897_, lean_object* v_vals_1898_, lean_object* v_heq_1899_, lean_object* v_i_1900_, lean_object* v_k_1901_){
_start:
{
uint8_t v_res_1902_; lean_object* v_r_1903_; 
v_res_1902_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1896_, v_keys_1897_, v_vals_1898_, v_heq_1899_, v_i_1900_, v_k_1901_);
lean_dec(v_k_1901_);
lean_dec_ref(v_vals_1898_);
lean_dec_ref(v_keys_1897_);
v_r_1903_ = lean_box(v_res_1902_);
return v_r_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1904_, lean_object* v_f_1905_, lean_object* v_init_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1905_, v_map_1904_, v_init_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1908_, lean_object* v_f_1909_, lean_object* v_init_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1908_, v_f_1909_, v_init_1910_);
lean_dec_ref(v_map_1908_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1912_, lean_object* v_00_u03b2_1913_, lean_object* v_map_1914_, lean_object* v_f_1915_, lean_object* v_init_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1915_, v_map_1914_, v_init_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_map_1920_, lean_object* v_f_1921_, lean_object* v_init_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1918_, v_00_u03b2_1919_, v_map_1920_, v_f_1921_, v_init_1922_);
lean_dec_ref(v_map_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1924_, lean_object* v_n_1925_, lean_object* v_k_1926_, lean_object* v_v_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_n_1925_, v_k_1926_, v_v_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1929_, size_t v_depth_1930_, lean_object* v_keys_1931_, lean_object* v_vals_1932_, lean_object* v_heq_1933_, lean_object* v_i_1934_, lean_object* v_entries_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_depth_1930_, v_keys_1931_, v_vals_1932_, v_i_1934_, v_entries_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1937_, lean_object* v_depth_1938_, lean_object* v_keys_1939_, lean_object* v_vals_1940_, lean_object* v_heq_1941_, lean_object* v_i_1942_, lean_object* v_entries_1943_){
_start:
{
size_t v_depth_boxed_1944_; lean_object* v_res_1945_; 
v_depth_boxed_1944_ = lean_unbox_usize(v_depth_1938_);
lean_dec(v_depth_1938_);
v_res_1945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9(v_00_u03b2_1937_, v_depth_boxed_1944_, v_keys_1939_, v_vals_1940_, v_heq_1941_, v_i_1942_, v_entries_1943_);
lean_dec_ref(v_vals_1940_);
lean_dec_ref(v_keys_1939_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_1946_, lean_object* v_00_u03b1_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_f_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1949_, v_x_1950_, v_x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_1953_, lean_object* v_00_u03b1_1954_, lean_object* v_00_u03b2_1955_, lean_object* v_f_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_1953_, v_00_u03b1_1954_, v_00_u03b2_1955_, v_f_1956_, v_x_1957_, v_x_1958_);
lean_dec_ref(v_x_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(v_x_1961_, v_x_1962_, v_x_1963_, v_x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_00_u03c3_1968_, lean_object* v_f_1969_, lean_object* v_as_1970_, size_t v_i_1971_, size_t v_stop_1972_, lean_object* v_b_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1969_, v_as_1970_, v_i_1971_, v_stop_1972_, v_b_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_00_u03c3_1977_, lean_object* v_f_1978_, lean_object* v_as_1979_, lean_object* v_i_1980_, lean_object* v_stop_1981_, lean_object* v_b_1982_){
_start:
{
size_t v_i_boxed_1983_; size_t v_stop_boxed_1984_; lean_object* v_res_1985_; 
v_i_boxed_1983_ = lean_unbox_usize(v_i_1980_);
lean_dec(v_i_1980_);
v_stop_boxed_1984_ = lean_unbox_usize(v_stop_1981_);
lean_dec(v_stop_1981_);
v_res_1985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(v_00_u03b1_1975_, v_00_u03b2_1976_, v_00_u03c3_1977_, v_f_1978_, v_as_1979_, v_i_boxed_1983_, v_stop_boxed_1984_, v_b_1982_);
lean_dec_ref(v_as_1979_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03c3_1986_, lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_f_1989_, lean_object* v_keys_1990_, lean_object* v_vals_1991_, lean_object* v_heq_1992_, lean_object* v_i_1993_, lean_object* v_acc_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1989_, v_keys_1990_, v_vals_1991_, v_i_1993_, v_acc_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03c3_1996_, lean_object* v_00_u03b1_1997_, lean_object* v_00_u03b2_1998_, lean_object* v_f_1999_, lean_object* v_keys_2000_, lean_object* v_vals_2001_, lean_object* v_heq_2002_, lean_object* v_i_2003_, lean_object* v_acc_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03c3_1996_, v_00_u03b1_1997_, v_00_u03b2_1998_, v_f_1999_, v_keys_2000_, v_vals_2001_, v_heq_2002_, v_i_2003_, v_acc_2004_);
lean_dec_ref(v_vals_2001_);
lean_dec_ref(v_keys_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2006_, lean_object* v_fid_2007_, lean_object* v_v_2008_){
_start:
{
lean_object* v___x_2009_; lean_object* v_toEnvExtension_2010_; lean_object* v_asyncMode_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2009_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc_ref(v_toEnvExtension_2010_);
v_asyncMode_2011_ = lean_ctor_get(v_toEnvExtension_2010_, 2);
lean_inc(v_asyncMode_2011_);
lean_dec_ref(v_toEnvExtension_2010_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_fid_2007_);
lean_ctor_set(v___x_2012_, 1, v_v_2008_);
v___x_2013_ = lean_box(0);
v___x_2014_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2009_, v_env_2006_, v___x_2012_, v_asyncMode_2011_, v___x_2013_);
lean_dec(v_asyncMode_2011_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2015_, lean_object* v_vals_2016_, lean_object* v_i_2017_, lean_object* v_k_2018_){
_start:
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = lean_array_get_size(v_keys_2015_);
v___x_2020_ = lean_nat_dec_lt(v_i_2017_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v_i_2017_);
v___x_2021_ = lean_box(0);
return v___x_2021_;
}
else
{
lean_object* v_k_x27_2022_; uint8_t v___x_2023_; 
v_k_x27_2022_ = lean_array_fget_borrowed(v_keys_2015_, v_i_2017_);
v___x_2023_ = lean_name_eq(v_k_2018_, v_k_x27_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_add(v_i_2017_, v___x_2024_);
lean_dec(v_i_2017_);
v_i_2017_ = v___x_2025_;
goto _start;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_array_fget_borrowed(v_vals_2016_, v_i_2017_);
lean_dec(v_i_2017_);
lean_inc(v___x_2027_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2029_, lean_object* v_vals_2030_, lean_object* v_i_2031_, lean_object* v_k_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2029_, v_vals_2030_, v_i_2031_, v_k_2032_);
lean_dec(v_k_2032_);
lean_dec_ref(v_vals_2030_);
lean_dec_ref(v_keys_2029_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2034_, size_t v_x_2035_, lean_object* v_x_2036_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v_es_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2058_; 
v_es_2037_ = lean_ctor_get(v_x_2034_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_2034_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2039_ = v_x_2034_;
v_isShared_2040_ = v_isSharedCheck_2058_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_es_2037_);
lean_dec(v_x_2034_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2058_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; size_t v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; lean_object* v_j_2045_; lean_object* v___x_2046_; 
v___x_2041_ = lean_box(2);
v___x_2042_ = ((size_t)5ULL);
v___x_2043_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_2044_ = lean_usize_land(v_x_2035_, v___x_2043_);
v_j_2045_ = lean_usize_to_nat(v___x_2044_);
v___x_2046_ = lean_array_get(v___x_2041_, v_es_2037_, v_j_2045_);
lean_dec(v_j_2045_);
lean_dec_ref(v_es_2037_);
switch(lean_obj_tag(v___x_2046_))
{
case 0:
{
lean_object* v_key_2047_; lean_object* v_val_2048_; uint8_t v___x_2049_; 
v_key_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_key_2047_);
v_val_2048_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_val_2048_);
lean_dec_ref(v___x_2046_);
v___x_2049_ = lean_name_eq(v_x_2036_, v_key_2047_);
lean_dec(v_key_2047_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec(v_val_2048_);
lean_del_object(v___x_2039_);
v___x_2050_ = lean_box(0);
return v___x_2050_;
}
else
{
lean_object* v___x_2052_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set_tag(v___x_2039_, 1);
lean_ctor_set(v___x_2039_, 0, v_val_2048_);
v___x_2052_ = v___x_2039_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_val_2048_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
case 1:
{
lean_object* v_node_2054_; size_t v___x_2055_; 
lean_del_object(v___x_2039_);
v_node_2054_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_node_2054_);
lean_dec_ref(v___x_2046_);
v___x_2055_ = lean_usize_shift_right(v_x_2035_, v___x_2042_);
v_x_2034_ = v_node_2054_;
v_x_2035_ = v___x_2055_;
goto _start;
}
default: 
{
lean_object* v___x_2057_; 
lean_del_object(v___x_2039_);
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_ks_2059_; lean_object* v_vs_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_ks_2059_ = lean_ctor_get(v_x_2034_, 0);
lean_inc_ref(v_ks_2059_);
v_vs_2060_ = lean_ctor_get(v_x_2034_, 1);
lean_inc_ref(v_vs_2060_);
lean_dec_ref(v_x_2034_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2059_, v_vs_2060_, v___x_2061_, v_x_2036_);
lean_dec_ref(v_vs_2060_);
lean_dec_ref(v_ks_2059_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
size_t v_x_340__boxed_2066_; lean_object* v_res_2067_; 
v_x_340__boxed_2066_ = lean_unbox_usize(v_x_2064_);
lean_dec(v_x_2064_);
v_res_2067_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2063_, v_x_340__boxed_2066_, v_x_2065_);
lean_dec(v_x_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
uint64_t v___y_2071_; 
if (lean_obj_tag(v_x_2069_) == 0)
{
uint64_t v___x_2074_; 
v___x_2074_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_2071_ = v___x_2074_;
goto v___jp_2070_;
}
else
{
uint64_t v_hash_2075_; 
v_hash_2075_ = lean_ctor_get_uint64(v_x_2069_, sizeof(void*)*2);
v___y_2071_ = v_hash_2075_;
goto v___jp_2070_;
}
v___jp_2070_:
{
size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_uint64_to_usize(v___y_2071_);
v___x_2073_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2068_, v___x_2072_, v_x_2069_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2076_, lean_object* v_x_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2076_, v_x_2077_);
lean_dec(v_x_2077_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2079_, lean_object* v_k_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_m_2085_; lean_object* v_a_2086_; uint8_t v___x_2087_; 
v___x_2083_ = lean_nat_add(v_x_2081_, v_x_2082_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v_m_2085_ = lean_nat_shiftr(v___x_2083_, v___x_2084_);
lean_dec(v___x_2083_);
v_a_2086_ = lean_array_fget_borrowed(v_as_2079_, v_m_2085_);
v___x_2087_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2086_, v_k_2080_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; 
lean_dec(v_x_2082_);
v___x_2088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2080_, v_a_2086_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v_m_2085_);
lean_dec(v_x_2081_);
lean_inc(v_a_2086_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_a_2086_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_nat_dec_eq(v_m_2085_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = lean_nat_sub(v_m_2085_, v___x_2084_);
lean_dec(v_m_2085_);
v___x_2093_ = lean_nat_dec_lt(v___x_2092_, v_x_2081_);
if (v___x_2093_ == 0)
{
v_x_2082_ = v___x_2092_;
goto _start;
}
else
{
lean_object* v___x_2095_; 
lean_dec(v___x_2092_);
lean_dec(v_x_2081_);
v___x_2095_ = lean_box(0);
return v___x_2095_;
}
}
else
{
lean_object* v___x_2096_; 
lean_dec(v_m_2085_);
lean_dec(v_x_2081_);
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
}
}
else
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
lean_dec(v_x_2081_);
v___x_2097_ = lean_nat_add(v_m_2085_, v___x_2084_);
lean_dec(v_m_2085_);
v___x_2098_ = lean_nat_dec_le(v___x_2097_, v_x_2082_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
lean_dec(v___x_2097_);
lean_dec(v_x_2082_);
v___x_2099_ = lean_box(0);
return v___x_2099_;
}
else
{
v_x_2081_ = v___x_2097_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2101_, lean_object* v_k_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2101_, v_k_2102_, v_x_2103_, v_x_2104_);
lean_dec_ref(v_k_2102_);
lean_dec_ref(v_as_2101_);
return v_res_2105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2109_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2110_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2109_, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2112_ = lean_box(0);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___x_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2114_, lean_object* v_fid_2115_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2117_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2114_, v_fid_2115_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; lean_object* v_toEnvExtension_2119_; lean_object* v_asyncMode_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2118_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_ref(v_toEnvExtension_2119_);
v_asyncMode_2120_ = lean_ctor_get(v_toEnvExtension_2119_, 2);
lean_inc(v_asyncMode_2120_);
lean_dec_ref(v_toEnvExtension_2119_);
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2116_, v___x_2118_, v_env_2114_, v_asyncMode_2120_, v___x_2121_);
lean_dec(v_asyncMode_2120_);
v___x_2123_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v___x_2122_, v_fid_2115_);
lean_dec(v_fid_2115_);
return v___x_2123_;
}
else
{
lean_object* v_val_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_val_2124_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_val_2124_);
lean_dec_ref(v___x_2117_);
v___x_2125_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2126_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2127_ = 0;
v___x_2128_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2125_, v___x_2126_, v_env_2114_, v_val_2124_, v___x_2127_);
lean_dec(v_val_2124_);
lean_dec_ref(v_env_2114_);
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_array_get_size(v___x_2128_);
v___x_2131_ = lean_nat_dec_lt(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; 
lean_dec_ref(v___x_2128_);
lean_dec(v_fid_2115_);
v___x_2132_ = lean_box(0);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_sub(v___x_2130_, v___x_2133_);
v___x_2135_ = lean_nat_dec_le(v___x_2129_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v___x_2134_);
lean_dec_ref(v___x_2128_);
lean_dec(v_fid_2115_);
v___x_2136_ = lean_box(0);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_fid_2115_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2128_, v___x_2138_, v___x_2129_, v___x_2134_);
lean_dec_ref(v___x_2138_);
lean_dec_ref(v___x_2128_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_box(0);
return v___x_2140_;
}
else
{
lean_object* v_val_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2149_; 
v_val_2141_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2143_ = v___x_2139_;
v_isShared_2144_ = v_isSharedCheck_2149_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_val_2141_);
lean_dec(v___x_2139_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2149_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_snd_2145_; lean_object* v___x_2147_; 
v_snd_2145_ = lean_ctor_get(v_val_2141_, 1);
lean_inc(v_snd_2145_);
lean_dec(v_val_2141_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v_snd_2145_);
v___x_2147_ = v___x_2143_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_snd_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2154_, v_x_2155_, v_x_2156_);
lean_dec(v_x_2156_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2158_, lean_object* v_k_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2158_, v_k_2159_, v_x_2160_, v_x_2161_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2164_, lean_object* v_k_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2164_, v_k_2165_, v_x_2166_, v_x_2167_, v_x_2168_);
lean_dec_ref(v_k_2165_);
lean_dec_ref(v_as_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2170_, lean_object* v_x_2171_, size_t v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2171_, v_x_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
size_t v_x_563__boxed_2179_; lean_object* v_res_2180_; 
v_x_563__boxed_2179_ = lean_unbox_usize(v_x_2177_);
lean_dec(v_x_2177_);
v_res_2180_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2175_, v_x_2176_, v_x_563__boxed_2179_, v_x_2178_);
lean_dec(v_x_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2181_, lean_object* v_keys_2182_, lean_object* v_vals_2183_, lean_object* v_heq_2184_, lean_object* v_i_2185_, lean_object* v_k_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2182_, v_vals_2183_, v_i_2185_, v_k_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2188_, lean_object* v_keys_2189_, lean_object* v_vals_2190_, lean_object* v_heq_2191_, lean_object* v_i_2192_, lean_object* v_k_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2188_, v_keys_2189_, v_vals_2190_, v_heq_2191_, v_i_2192_, v_k_2193_);
lean_dec(v_k_2193_);
lean_dec_ref(v_vals_2190_);
lean_dec_ref(v_keys_2189_);
return v_res_2194_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2198_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2199_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v_assignments_2204_; lean_object* v_currFnIdx_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2203_ = lean_st_ref_get(v_a_2201_);
v_assignments_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc_ref(v_assignments_2204_);
lean_dec(v___x_2203_);
v_currFnIdx_2205_ = lean_ctor_get(v_a_2200_, 1);
v___x_2206_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2207_ = lean_array_get(v___x_2206_, v_assignments_2204_, v_currFnIdx_2205_);
lean_dec_ref(v_assignments_2204_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2213_, v_a_2214_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v_funVals_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = lean_st_ref_get(v_a_2230_);
v_funVals_2233_ = lean_ctor_get(v___x_2232_, 1);
lean_inc_ref(v_funVals_2233_);
lean_dec(v___x_2232_);
v___x_2234_ = lean_box(0);
v___x_2235_ = lean_array_get(v___x_2234_, v_funVals_2233_, v_funIdx_2229_);
lean_dec_ref(v_funVals_2233_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2237_, v_a_2238_);
lean_dec(v_a_2238_);
lean_dec(v_funIdx_2237_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2241_, v_a_2243_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_funIdx_2250_);
return v_res_2258_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0(lean_object* v_declName_2259_, lean_object* v_x_2260_){
_start:
{
lean_object* v_toSignature_2261_; lean_object* v_name_2262_; uint8_t v___x_2263_; 
v_toSignature_2261_ = lean_ctor_get(v_x_2260_, 0);
v_name_2262_ = lean_ctor_get(v_toSignature_2261_, 0);
v___x_2263_ = lean_name_eq(v_name_2262_, v_declName_2259_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0___boxed(lean_object* v_declName_2264_, lean_object* v_x_2265_){
_start:
{
uint8_t v_res_2266_; lean_object* v_r_2267_; 
v_res_2266_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0(v_declName_2264_, v_x_2265_);
lean_dec_ref(v_x_2265_);
lean_dec(v_declName_2264_);
v_r_2267_ = lean_box(v_res_2266_);
return v_r_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_decls_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_decls_2272_ = lean_ctor_get(v_a_2269_, 0);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2273_, 0, v_declName_2268_);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = l_Array_findIdx_x3f_loop___redArg(v___f_2273_, v_decls_2272_, v___x_2274_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
else
{
lean_object* v_val_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2294_; 
v_val_2278_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2280_ = v___x_2275_;
v_isShared_2281_ = v_isSharedCheck_2294_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_val_2278_);
lean_dec(v___x_2275_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2294_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2293_; 
v___x_2282_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2278_, v_a_2270_);
lean_dec(v_val_2278_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2293_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2293_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v_a_2283_);
v___x_2288_ = v___x_2280_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2288_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2300_, v_a_2301_, v_a_2302_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v___x_2322_; lean_object* v_currFnIdx_2323_; lean_object* v_assignments_2324_; lean_object* v_funVals_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2343_; 
v___x_2322_ = lean_st_ref_take(v_a_2320_);
v_currFnIdx_2323_ = lean_ctor_get(v_a_2319_, 1);
v_assignments_2324_ = lean_ctor_get(v___x_2322_, 0);
v_funVals_2325_ = lean_ctor_get(v___x_2322_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2327_ = v___x_2322_;
v_isShared_2328_ = v_isSharedCheck_2343_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_funVals_2325_);
lean_inc(v_assignments_2324_);
lean_dec(v___x_2322_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2343_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___y_2331_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2329_ = lean_box(0);
v___x_2337_ = lean_array_get_size(v_assignments_2324_);
v___x_2338_ = lean_nat_dec_lt(v_currFnIdx_2323_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v_f_2318_);
v___y_2331_ = v_assignments_2324_;
goto v___jp_2330_;
}
else
{
lean_object* v_v_2339_; lean_object* v_xs_x27_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_v_2339_ = lean_array_fget(v_assignments_2324_, v_currFnIdx_2323_);
v_xs_x27_2340_ = lean_array_fset(v_assignments_2324_, v_currFnIdx_2323_, v___x_2329_);
v___x_2341_ = lean_apply_1(v_f_2318_, v_v_2339_);
v___x_2342_ = lean_array_fset(v_xs_x27_2340_, v_currFnIdx_2323_, v___x_2341_);
v___y_2331_ = v___x_2342_;
goto v___jp_2330_;
}
v___jp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___y_2331_);
v___x_2333_ = v___x_2327_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___y_2331_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_funVals_2325_);
v___x_2333_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_st_ref_set(v_a_2320_, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2329_);
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2344_, v_a_2345_, v_a_2346_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2349_, v_a_2350_, v_a_2351_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2367_, lean_object* v_fallback_2368_, lean_object* v_x_2369_){
_start:
{
if (lean_obj_tag(v_x_2369_) == 0)
{
lean_inc(v_fallback_2368_);
return v_fallback_2368_;
}
else
{
lean_object* v_key_2370_; lean_object* v_value_2371_; lean_object* v_tail_2372_; uint8_t v___x_2373_; 
v_key_2370_ = lean_ctor_get(v_x_2369_, 0);
v_value_2371_ = lean_ctor_get(v_x_2369_, 1);
v_tail_2372_ = lean_ctor_get(v_x_2369_, 2);
v___x_2373_ = l_Lean_instBEqFVarId_beq(v_key_2370_, v_a_2367_);
if (v___x_2373_ == 0)
{
v_x_2369_ = v_tail_2372_;
goto _start;
}
else
{
lean_inc(v_value_2371_);
return v_value_2371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2375_, lean_object* v_fallback_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2375_, v_fallback_2376_, v_x_2377_);
lean_dec(v_x_2377_);
lean_dec(v_fallback_2376_);
lean_dec(v_a_2375_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2379_, lean_object* v_a_2380_, lean_object* v_fallback_2381_){
_start:
{
lean_object* v_buckets_2382_; lean_object* v___x_2383_; uint64_t v___x_2384_; uint64_t v___x_2385_; uint64_t v___x_2386_; uint64_t v_fold_2387_; uint64_t v___x_2388_; uint64_t v___x_2389_; uint64_t v___x_2390_; size_t v___x_2391_; size_t v___x_2392_; size_t v___x_2393_; size_t v___x_2394_; size_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_buckets_2382_ = lean_ctor_get(v_m_2379_, 1);
v___x_2383_ = lean_array_get_size(v_buckets_2382_);
v___x_2384_ = l_Lean_instHashableFVarId_hash(v_a_2380_);
v___x_2385_ = 32ULL;
v___x_2386_ = lean_uint64_shift_right(v___x_2384_, v___x_2385_);
v_fold_2387_ = lean_uint64_xor(v___x_2384_, v___x_2386_);
v___x_2388_ = 16ULL;
v___x_2389_ = lean_uint64_shift_right(v_fold_2387_, v___x_2388_);
v___x_2390_ = lean_uint64_xor(v_fold_2387_, v___x_2389_);
v___x_2391_ = lean_uint64_to_usize(v___x_2390_);
v___x_2392_ = lean_usize_of_nat(v___x_2383_);
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_sub(v___x_2392_, v___x_2393_);
v___x_2395_ = lean_usize_land(v___x_2391_, v___x_2394_);
v___x_2396_ = lean_array_uget_borrowed(v_buckets_2382_, v___x_2395_);
v___x_2397_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2380_, v_fallback_2381_, v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2398_, lean_object* v_a_2399_, lean_object* v_fallback_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2398_, v_a_2399_, v_fallback_2400_);
lean_dec(v_fallback_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_m_2398_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2416_; 
v___x_2406_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2403_, v_a_2404_);
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2411_ = lean_box(0);
v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2407_, v_var_2402_, v___x_2411_);
lean_dec(v_a_2407_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2412_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_var_2417_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2422_, v_a_2423_, v_a_2424_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_var_2431_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2440_, lean_object* v_m_2441_, lean_object* v_a_2442_, lean_object* v_fallback_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2441_, v_a_2442_, v_fallback_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2445_, lean_object* v_m_2446_, lean_object* v_a_2447_, lean_object* v_fallback_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2445_, v_m_2446_, v_a_2447_, v_fallback_2448_);
lean_dec(v_fallback_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_m_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2450_, lean_object* v_a_2451_, lean_object* v_fallback_2452_, lean_object* v_x_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2451_, v_fallback_2452_, v_x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2455_, lean_object* v_a_2456_, lean_object* v_fallback_2457_, lean_object* v_x_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2455_, v_a_2456_, v_fallback_2457_, v_x_2458_);
lean_dec(v_x_2458_);
lean_dec(v_fallback_2457_);
lean_dec(v_a_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
if (lean_obj_tag(v_arg_2460_) == 1)
{
lean_object* v_fvarId_2464_; lean_object* v___x_2465_; 
v_fvarId_2464_ = lean_ctor_get(v_arg_2460_, 0);
v___x_2465_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2464_, v_a_2461_, v_a_2462_);
return v___x_2465_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_box(1);
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
return v___x_2467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2468_, v_a_2469_, v_a_2470_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_arg_2468_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2473_, v_a_2474_, v_a_2475_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_arg_2482_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2491_, lean_object* v_b_2492_, lean_object* v_x_2493_){
_start:
{
if (lean_obj_tag(v_x_2493_) == 0)
{
lean_dec(v_b_2492_);
lean_dec(v_a_2491_);
return v_x_2493_;
}
else
{
lean_object* v_key_2494_; lean_object* v_value_2495_; lean_object* v_tail_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2508_; 
v_key_2494_ = lean_ctor_get(v_x_2493_, 0);
v_value_2495_ = lean_ctor_get(v_x_2493_, 1);
v_tail_2496_ = lean_ctor_get(v_x_2493_, 2);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_x_2493_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2498_ = v_x_2493_;
v_isShared_2499_ = v_isSharedCheck_2508_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_tail_2496_);
lean_inc(v_value_2495_);
lean_inc(v_key_2494_);
lean_dec(v_x_2493_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2508_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
uint8_t v___x_2500_; 
v___x_2500_ = l_Lean_instBEqFVarId_beq(v_key_2494_, v_a_2491_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2501_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2491_, v_b_2492_, v_tail_2496_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 2, v___x_2501_);
v___x_2503_ = v___x_2498_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_key_2494_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_value_2495_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
else
{
lean_object* v___x_2506_; 
lean_dec(v_value_2495_);
lean_dec(v_key_2494_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v_b_2492_);
lean_ctor_set(v___x_2498_, 0, v_a_2491_);
v___x_2506_ = v___x_2498_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2491_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_b_2492_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_tail_2496_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
return v_x_2509_;
}
else
{
lean_object* v_key_2511_; lean_object* v_value_2512_; lean_object* v_tail_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2536_; 
v_key_2511_ = lean_ctor_get(v_x_2510_, 0);
v_value_2512_ = lean_ctor_get(v_x_2510_, 1);
v_tail_2513_ = lean_ctor_get(v_x_2510_, 2);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_x_2510_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2515_ = v_x_2510_;
v_isShared_2516_ = v_isSharedCheck_2536_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_tail_2513_);
lean_inc(v_value_2512_);
lean_inc(v_key_2511_);
lean_dec(v_x_2510_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2536_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; uint64_t v___x_2518_; uint64_t v___x_2519_; uint64_t v___x_2520_; uint64_t v_fold_2521_; uint64_t v___x_2522_; uint64_t v___x_2523_; uint64_t v___x_2524_; size_t v___x_2525_; size_t v___x_2526_; size_t v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2517_ = lean_array_get_size(v_x_2509_);
v___x_2518_ = l_Lean_instHashableFVarId_hash(v_key_2511_);
v___x_2519_ = 32ULL;
v___x_2520_ = lean_uint64_shift_right(v___x_2518_, v___x_2519_);
v_fold_2521_ = lean_uint64_xor(v___x_2518_, v___x_2520_);
v___x_2522_ = 16ULL;
v___x_2523_ = lean_uint64_shift_right(v_fold_2521_, v___x_2522_);
v___x_2524_ = lean_uint64_xor(v_fold_2521_, v___x_2523_);
v___x_2525_ = lean_uint64_to_usize(v___x_2524_);
v___x_2526_ = lean_usize_of_nat(v___x_2517_);
v___x_2527_ = ((size_t)1ULL);
v___x_2528_ = lean_usize_sub(v___x_2526_, v___x_2527_);
v___x_2529_ = lean_usize_land(v___x_2525_, v___x_2528_);
v___x_2530_ = lean_array_uget_borrowed(v_x_2509_, v___x_2529_);
lean_inc(v___x_2530_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 2, v___x_2530_);
v___x_2532_ = v___x_2515_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_key_2511_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_value_2512_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_array_uset(v_x_2509_, v___x_2529_, v___x_2532_);
v_x_2509_ = v___x_2533_;
v_x_2510_ = v_tail_2513_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2537_, lean_object* v_source_2538_, lean_object* v_target_2539_){
_start:
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = lean_array_get_size(v_source_2538_);
v___x_2541_ = lean_nat_dec_lt(v_i_2537_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_dec_ref(v_source_2538_);
lean_dec(v_i_2537_);
return v_target_2539_;
}
else
{
lean_object* v_es_2542_; lean_object* v___x_2543_; lean_object* v_source_2544_; lean_object* v_target_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_es_2542_ = lean_array_fget(v_source_2538_, v_i_2537_);
v___x_2543_ = lean_box(0);
v_source_2544_ = lean_array_fset(v_source_2538_, v_i_2537_, v___x_2543_);
v_target_2545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2539_, v_es_2542_);
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v_i_2537_, v___x_2546_);
lean_dec(v_i_2537_);
v_i_2537_ = v___x_2547_;
v_source_2538_ = v_source_2544_;
v_target_2539_ = v_target_2545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2549_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_nbuckets_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2550_ = lean_array_get_size(v_data_2549_);
v___x_2551_ = lean_unsigned_to_nat(2u);
v_nbuckets_2552_ = lean_nat_mul(v___x_2550_, v___x_2551_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_mk_array(v_nbuckets_2552_, v___x_2554_);
v___x_2556_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2553_, v_data_2549_, v___x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2557_, lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 0)
{
uint8_t v___x_2559_; 
v___x_2559_ = 0;
return v___x_2559_;
}
else
{
lean_object* v_key_2560_; lean_object* v_tail_2561_; uint8_t v___x_2562_; 
v_key_2560_ = lean_ctor_get(v_x_2558_, 0);
v_tail_2561_ = lean_ctor_get(v_x_2558_, 2);
v___x_2562_ = l_Lean_instBEqFVarId_beq(v_key_2560_, v_a_2557_);
if (v___x_2562_ == 0)
{
v_x_2558_ = v_tail_2561_;
goto _start;
}
else
{
return v___x_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2564_, lean_object* v_x_2565_){
_start:
{
uint8_t v_res_2566_; lean_object* v_r_2567_; 
v_res_2566_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2564_, v_x_2565_);
lean_dec(v_x_2565_);
lean_dec(v_a_2564_);
v_r_2567_ = lean_box(v_res_2566_);
return v_r_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2568_, lean_object* v_a_2569_, lean_object* v_b_2570_){
_start:
{
lean_object* v_size_2571_; lean_object* v_buckets_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2615_; 
v_size_2571_ = lean_ctor_get(v_m_2568_, 0);
v_buckets_2572_ = lean_ctor_get(v_m_2568_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_m_2568_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2574_ = v_m_2568_;
v_isShared_2575_ = v_isSharedCheck_2615_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_buckets_2572_);
lean_inc(v_size_2571_);
lean_dec(v_m_2568_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2615_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; uint64_t v___x_2577_; uint64_t v___x_2578_; uint64_t v___x_2579_; uint64_t v_fold_2580_; uint64_t v___x_2581_; uint64_t v___x_2582_; uint64_t v___x_2583_; size_t v___x_2584_; size_t v___x_2585_; size_t v___x_2586_; size_t v___x_2587_; size_t v___x_2588_; lean_object* v_bkt_2589_; uint8_t v___x_2590_; 
v___x_2576_ = lean_array_get_size(v_buckets_2572_);
v___x_2577_ = l_Lean_instHashableFVarId_hash(v_a_2569_);
v___x_2578_ = 32ULL;
v___x_2579_ = lean_uint64_shift_right(v___x_2577_, v___x_2578_);
v_fold_2580_ = lean_uint64_xor(v___x_2577_, v___x_2579_);
v___x_2581_ = 16ULL;
v___x_2582_ = lean_uint64_shift_right(v_fold_2580_, v___x_2581_);
v___x_2583_ = lean_uint64_xor(v_fold_2580_, v___x_2582_);
v___x_2584_ = lean_uint64_to_usize(v___x_2583_);
v___x_2585_ = lean_usize_of_nat(v___x_2576_);
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_sub(v___x_2585_, v___x_2586_);
v___x_2588_ = lean_usize_land(v___x_2584_, v___x_2587_);
v_bkt_2589_ = lean_array_uget_borrowed(v_buckets_2572_, v___x_2588_);
v___x_2590_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2569_, v_bkt_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v_size_x27_2592_; lean_object* v___x_2593_; lean_object* v_buckets_x27_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2591_ = lean_unsigned_to_nat(1u);
v_size_x27_2592_ = lean_nat_add(v_size_2571_, v___x_2591_);
lean_dec(v_size_2571_);
lean_inc(v_bkt_2589_);
v___x_2593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2593_, 0, v_a_2569_);
lean_ctor_set(v___x_2593_, 1, v_b_2570_);
lean_ctor_set(v___x_2593_, 2, v_bkt_2589_);
v_buckets_x27_2594_ = lean_array_uset(v_buckets_2572_, v___x_2588_, v___x_2593_);
v___x_2595_ = lean_unsigned_to_nat(4u);
v___x_2596_ = lean_nat_mul(v_size_x27_2592_, v___x_2595_);
v___x_2597_ = lean_unsigned_to_nat(3u);
v___x_2598_ = lean_nat_div(v___x_2596_, v___x_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_array_get_size(v_buckets_x27_2594_);
v___x_2600_ = lean_nat_dec_le(v___x_2598_, v___x_2599_);
lean_dec(v___x_2598_);
if (v___x_2600_ == 0)
{
lean_object* v_val_2601_; lean_object* v___x_2603_; 
v_val_2601_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2594_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v_val_2601_);
lean_ctor_set(v___x_2574_, 0, v_size_x27_2592_);
v___x_2603_ = v___x_2574_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_size_x27_2592_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_val_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
lean_object* v___x_2606_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v_buckets_x27_2594_);
lean_ctor_set(v___x_2574_, 0, v_size_x27_2592_);
v___x_2606_ = v___x_2574_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_size_x27_2592_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_buckets_x27_2594_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
else
{
lean_object* v___x_2608_; lean_object* v_buckets_x27_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_inc(v_bkt_2589_);
v___x_2608_ = lean_box(0);
v_buckets_x27_2609_ = lean_array_uset(v_buckets_2572_, v___x_2588_, v___x_2608_);
v___x_2610_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2569_, v_b_2570_, v_bkt_2589_);
v___x_2611_ = lean_array_uset(v_buckets_x27_2609_, v___x_2588_, v___x_2610_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v___x_2611_);
v___x_2613_ = v___x_2574_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_size_2571_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2616_, lean_object* v___x_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2618_, v_var_2616_, v___x_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2620_, lean_object* v_newVal_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_st_ref_get(v_a_2624_);
v___x_2627_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2620_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v_env_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v_env_2629_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_ref(v_env_2629_);
lean_dec(v___x_2626_);
v___x_2630_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2629_, v_a_2628_, v_newVal_2621_);
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2631_, 0, v_var_2620_);
lean_closure_set(v___f_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2631_, v_a_2622_, v_a_2623_);
return v___x_2632_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v___x_2626_);
lean_dec(v_newVal_2621_);
lean_dec(v_var_2620_);
v_a_2633_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2627_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2627_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2641_, lean_object* v_newVal_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2641_, v_newVal_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2648_, lean_object* v_newVal_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2648_, v_newVal_2649_, v_a_2650_, v_a_2651_, v_a_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2658_, lean_object* v_newVal_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2658_, v_newVal_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2668_, lean_object* v_m_2669_, lean_object* v_a_2670_, lean_object* v_b_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2669_, v_a_2670_, v_b_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2673_, lean_object* v_a_2674_, lean_object* v_x_2675_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2674_, v_x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2677_, lean_object* v_a_2678_, lean_object* v_x_2679_){
_start:
{
uint8_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2677_, v_a_2678_, v_x_2679_);
lean_dec(v_x_2679_);
lean_dec(v_a_2678_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2682_, lean_object* v_data_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2685_, lean_object* v_a_2686_, lean_object* v_b_2687_, lean_object* v_x_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2686_, v_b_2687_, v_x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2690_, lean_object* v_i_2691_, lean_object* v_source_2692_, lean_object* v_target_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2691_, v_source_2692_, v_target_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2696_, v_x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2699_, lean_object* v_x_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_box(0);
v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2700_, v_var_2699_, v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; 
v___f_2707_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2707_, 0, v_var_2703_);
v___x_2708_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2707_, v_a_2704_, v_a_2705_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2714_, v_a_2715_, v_a_2716_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v_fst_2740_; lean_object* v_snd_2741_; lean_object* v_currFnIdx_2744_; lean_object* v_assignments_2745_; lean_object* v_funVals_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2737_ = lean_st_ref_get(v_a_2735_);
v___x_2738_ = lean_st_ref_take(v_a_2734_);
v_currFnIdx_2744_ = lean_ctor_get(v_a_2733_, 1);
v_assignments_2745_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_ref(v_assignments_2745_);
v_funVals_2746_ = lean_ctor_get(v___x_2738_, 1);
lean_inc_ref(v_funVals_2746_);
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_array_get_size(v_funVals_2746_);
v___x_2749_ = lean_nat_dec_lt(v_currFnIdx_2744_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_dec_ref(v_funVals_2746_);
lean_dec_ref(v_assignments_2745_);
lean_dec(v___x_2737_);
lean_dec(v_v_2732_);
v_fst_2740_ = v___x_2747_;
v_snd_2741_ = v___x_2738_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2761_; 
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2761_ == 0)
{
lean_object* v_unused_2762_; lean_object* v_unused_2763_; 
v_unused_2762_ = lean_ctor_get(v___x_2738_, 1);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v___x_2738_, 0);
lean_dec(v_unused_2763_);
v___x_2751_ = v___x_2738_;
v_isShared_2752_ = v_isSharedCheck_2761_;
goto v_resetjp_2750_;
}
else
{
lean_dec(v___x_2738_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2761_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_env_2753_; lean_object* v_v_2754_; lean_object* v_xs_x27_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v_env_2753_ = lean_ctor_get(v___x_2737_, 0);
lean_inc_ref(v_env_2753_);
lean_dec(v___x_2737_);
v_v_2754_ = lean_array_fget(v_funVals_2746_, v_currFnIdx_2744_);
v_xs_x27_2755_ = lean_array_fset(v_funVals_2746_, v_currFnIdx_2744_, v___x_2747_);
v___x_2756_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2753_, v_v_2732_, v_v_2754_);
v___x_2757_ = lean_array_fset(v_xs_x27_2755_, v_currFnIdx_2744_, v___x_2756_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___x_2757_);
v___x_2759_ = v___x_2751_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_assignments_2745_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
v_fst_2740_ = v___x_2747_;
v_snd_2741_ = v___x_2759_;
goto v___jp_2739_;
}
}
}
v___jp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_st_ref_set(v_a_2734_, v_snd_2741_);
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v_fst_2740_);
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
lean_dec(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2770_, v_a_2771_, v_a_2772_, v_a_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2788_, uint8_t v_b_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_array_2794_; lean_object* v_start_2795_; lean_object* v_stop_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2833_; 
v_array_2794_ = lean_ctor_get(v_a_2788_, 0);
v_start_2795_ = lean_ctor_get(v_a_2788_, 1);
v_stop_2796_ = lean_ctor_get(v_a_2788_, 2);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_a_2788_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2798_ = v_a_2788_;
v_isShared_2799_ = v_isSharedCheck_2833_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_stop_2796_);
lean_inc(v_start_2795_);
lean_inc(v_array_2794_);
lean_dec(v_a_2788_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2833_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_nat_dec_lt(v_start_2795_, v_stop_2796_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2798_);
lean_dec(v_stop_2796_);
lean_dec(v_start_2795_);
lean_dec_ref(v_array_2794_);
v___x_2801_ = lean_box(v_b_2789_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; lean_object* v_fvarId_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_array_fget_borrowed(v_array_2794_, v_start_2795_);
v_fvarId_2804_ = lean_ctor_get(v___x_2803_, 0);
v___x_2805_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2804_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = lean_box(1);
lean_inc(v_fvarId_2804_);
v___x_2808_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2804_, v___x_2807_, v___y_2790_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
lean_dec_ref(v___x_2808_);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_nat_add(v_start_2795_, v___x_2809_);
lean_dec(v_start_2795_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 1, v___x_2810_);
v___x_2812_ = v___x_2798_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_array_2794_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_stop_2796_);
v___x_2812_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2813_ = lean_box(0);
v___x_2814_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2806_, v___x_2813_);
v_a_2788_ = v___x_2812_;
v_b_2789_ = v___x_2814_;
goto _start;
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v_a_2806_);
lean_del_object(v___x_2798_);
lean_dec(v_stop_2796_);
lean_dec(v_start_2795_);
lean_dec_ref(v_array_2794_);
v_a_2817_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2808_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2808_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_del_object(v___x_2798_);
lean_dec(v_stop_2796_);
lean_dec(v_start_2795_);
lean_dec_ref(v_array_2794_);
v_a_2825_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2805_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2805_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2834_, lean_object* v_b_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
uint8_t v_b_boxed_2840_; lean_object* v_res_2841_; 
v_b_boxed_2840_ = lean_unbox(v_b_2835_);
v_res_2841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2834_, v_b_boxed_2840_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2842_, lean_object* v___x_2843_, lean_object* v_x_2844_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2844_, v_fvarId_2842_, v___x_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2846_, lean_object* v_as_2847_, size_t v_sz_2848_, size_t v_i_2849_, lean_object* v_b_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_a_2855_; uint8_t v___x_2859_; 
v___x_2859_ = lean_usize_dec_lt(v_i_2849_, v_sz_2848_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v___x_2846_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_b_2850_);
return v___x_2860_;
}
else
{
lean_object* v_snd_2861_; lean_object* v_fst_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2928_; 
v_snd_2861_ = lean_ctor_get(v_b_2850_, 1);
v_fst_2862_ = lean_ctor_get(v_b_2850_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_b_2850_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2864_ = v_b_2850_;
v_isShared_2865_ = v_isSharedCheck_2928_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_snd_2861_);
lean_inc(v_fst_2862_);
lean_dec(v_b_2850_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2928_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_array_2866_; lean_object* v_start_2867_; lean_object* v_stop_2868_; uint8_t v___x_2869_; 
v_array_2866_ = lean_ctor_get(v_snd_2861_, 0);
v_start_2867_ = lean_ctor_get(v_snd_2861_, 1);
v_stop_2868_ = lean_ctor_get(v_snd_2861_, 2);
v___x_2869_ = lean_nat_dec_lt(v_start_2867_, v_stop_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2871_; 
lean_dec_ref(v___x_2846_);
if (v_isShared_2865_ == 0)
{
v___x_2871_ = v___x_2864_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_fst_2862_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_snd_2861_);
v___x_2871_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
else
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2924_; 
lean_inc(v_stop_2868_);
lean_inc(v_start_2867_);
lean_inc_ref(v_array_2866_);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_snd_2861_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; lean_object* v_unused_2926_; lean_object* v_unused_2927_; 
v_unused_2925_ = lean_ctor_get(v_snd_2861_, 2);
lean_dec(v_unused_2925_);
v_unused_2926_ = lean_ctor_get(v_snd_2861_, 1);
lean_dec(v_unused_2926_);
v_unused_2927_ = lean_ctor_get(v_snd_2861_, 0);
lean_dec(v_unused_2927_);
v___x_2875_ = v_snd_2861_;
v_isShared_2876_ = v_isSharedCheck_2924_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v_snd_2861_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2924_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_a_2877_; lean_object* v_fvarId_2878_; lean_object* v___x_2879_; 
v_a_2877_ = lean_array_uget_borrowed(v_as_2847_, v_i_2849_);
v_fvarId_2878_ = lean_ctor_get(v_a_2877_, 0);
v___x_2879_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2878_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = lean_array_fget_borrowed(v_array_2866_, v_start_2867_);
v___x_2882_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2881_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_add(v_start_2867_, v___x_2884_);
lean_dec(v_start_2867_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___x_2885_);
v___x_2887_ = v___x_2875_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_array_2866_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v_stop_2868_);
v___x_2887_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
lean_inc(v_a_2880_);
lean_inc_ref(v___x_2846_);
v___x_2888_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2846_, v_a_2880_, v_a_2883_);
lean_inc(v___x_2888_);
v___x_2889_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2888_, v_a_2880_);
if (v___x_2889_ == 0)
{
lean_object* v___f_2890_; lean_object* v___x_2891_; 
lean_dec(v_fst_2862_);
lean_inc(v_fvarId_2878_);
v___f_2890_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2890_, 0, v_fvarId_2878_);
lean_closure_set(v___f_2890_, 1, v___x_2888_);
v___x_2891_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2890_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_dec_ref(v___x_2891_);
v___x_2892_ = lean_box(v___x_2869_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 1, v___x_2887_);
lean_ctor_set(v___x_2864_, 0, v___x_2892_);
v___x_2894_ = v___x_2864_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2887_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v_a_2855_ = v___x_2894_;
goto v___jp_2854_;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2864_);
lean_dec_ref(v___x_2846_);
v_a_2896_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2891_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2891_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v___x_2905_; 
lean_dec(v___x_2888_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 1, v___x_2887_);
v___x_2905_ = v___x_2864_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_fst_2862_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v___x_2887_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
v_a_2855_ = v___x_2905_;
goto v___jp_2854_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_a_2880_);
lean_del_object(v___x_2875_);
lean_dec(v_stop_2868_);
lean_dec(v_start_2867_);
lean_dec_ref(v_array_2866_);
lean_del_object(v___x_2864_);
lean_dec(v_fst_2862_);
lean_dec_ref(v___x_2846_);
v_a_2908_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2882_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2882_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_del_object(v___x_2875_);
lean_dec(v_stop_2868_);
lean_dec(v_start_2867_);
lean_dec_ref(v_array_2866_);
lean_del_object(v___x_2864_);
lean_dec(v_fst_2862_);
lean_dec_ref(v___x_2846_);
v_a_2916_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2879_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2879_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
}
v___jp_2854_:
{
size_t v___x_2856_; size_t v___x_2857_; 
v___x_2856_ = ((size_t)1ULL);
v___x_2857_ = lean_usize_add(v_i_2849_, v___x_2856_);
v_i_2849_ = v___x_2857_;
v_b_2850_ = v_a_2855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_2929_, lean_object* v_as_2930_, lean_object* v_sz_2931_, lean_object* v_i_2932_, lean_object* v_b_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
size_t v_sz_boxed_2937_; size_t v_i_boxed_2938_; lean_object* v_res_2939_; 
v_sz_boxed_2937_ = lean_unbox_usize(v_sz_2931_);
lean_dec(v_sz_2931_);
v_i_boxed_2938_ = lean_unbox_usize(v_i_2932_);
lean_dec(v_i_2932_);
v_res_2939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_2929_, v_as_2930_, v_sz_boxed_2937_, v_i_boxed_2938_, v_b_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v_as_2930_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_2940_, lean_object* v_args_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v___x_2949_; lean_object* v_env_2950_; uint8_t v_ret_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; size_t v_sz_2957_; size_t v___x_2958_; lean_object* v___x_2959_; 
v___x_2949_ = lean_st_ref_get(v_a_2947_);
v_env_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc_ref(v_env_2950_);
lean_dec(v___x_2949_);
v_ret_2951_ = 0;
v___x_2952_ = lean_unsigned_to_nat(0u);
v___x_2953_ = lean_array_get_size(v_args_2941_);
v___x_2954_ = l_Array_toSubarray___redArg(v_args_2941_, v___x_2952_, v___x_2953_);
v___x_2955_ = lean_box(v_ret_2951_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v___x_2954_);
v_sz_2957_ = lean_array_size(v_params_2940_);
v___x_2958_ = ((size_t)0ULL);
v___x_2959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_2950_, v_params_2940_, v_sz_2957_, v___x_2958_, v___x_2956_, v_a_2942_, v_a_2943_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2977_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2977_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2977_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_fst_2964_; lean_object* v_lower_2966_; lean_object* v_upper_2967_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_fst_2964_ = lean_ctor_get(v_a_2960_, 0);
lean_inc(v_fst_2964_);
lean_dec(v_a_2960_);
v___x_2971_ = lean_array_get_size(v_params_2940_);
v___x_2972_ = lean_nat_dec_eq(v___x_2971_, v___x_2953_);
if (v___x_2972_ == 0)
{
uint8_t v___x_2973_; 
lean_del_object(v___x_2962_);
v___x_2973_ = lean_nat_dec_le(v___x_2953_, v___x_2952_);
if (v___x_2973_ == 0)
{
v_lower_2966_ = v___x_2953_;
v_upper_2967_ = v___x_2971_;
goto v___jp_2965_;
}
else
{
v_lower_2966_ = v___x_2952_;
v_upper_2967_ = v___x_2971_;
goto v___jp_2965_;
}
}
else
{
lean_object* v___x_2975_; 
lean_dec_ref(v_params_2940_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v_fst_2964_);
v___x_2975_ = v___x_2962_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_fst_2964_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
v___jp_2965_:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = l_Array_toSubarray___redArg(v_params_2940_, v_lower_2966_, v_upper_2967_);
v___x_2969_ = lean_unbox(v_fst_2964_);
lean_dec(v_fst_2964_);
v___x_2970_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_2968_, v___x_2969_, v_a_2942_, v_a_2943_, v_a_2947_);
return v___x_2970_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec_ref(v_params_2940_);
v_a_2978_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2959_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2959_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_2986_, lean_object* v_args_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_2986_, v_args_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_2996_, lean_object* v_as_2997_, size_t v_sz_2998_, size_t v_i_2999_, lean_object* v_b_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_2996_, v_as_2997_, v_sz_2998_, v_i_2999_, v_b_3000_, v___y_3001_, v___y_3002_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3009_, lean_object* v_as_3010_, lean_object* v_sz_3011_, lean_object* v_i_3012_, lean_object* v_b_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
size_t v_sz_boxed_3021_; size_t v_i_boxed_3022_; lean_object* v_res_3023_; 
v_sz_boxed_3021_ = lean_unbox_usize(v_sz_3011_);
lean_dec(v_sz_3011_);
v_i_boxed_3022_ = lean_unbox_usize(v_i_3012_);
lean_dec(v_i_3012_);
v_res_3023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3009_, v_as_3010_, v_sz_boxed_3021_, v_i_boxed_3022_, v_b_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec_ref(v_as_3010_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3024_, lean_object* v_R_3025_, lean_object* v_a_3026_, uint8_t v_b_3027_, lean_object* v_c_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3026_, v_b_3027_, v___y_3029_, v___y_3030_, v___y_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3037_, lean_object* v_R_3038_, lean_object* v_a_3039_, lean_object* v_b_3040_, lean_object* v_c_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
uint8_t v_b_boxed_3049_; lean_object* v_res_3050_; 
v_b_boxed_3049_ = lean_unbox(v_b_3040_);
v_res_3050_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3037_, v_R_3038_, v_a_3039_, v_b_boxed_3049_, v_c_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3051_, size_t v_sz_3052_, size_t v_i_3053_, uint8_t v_b_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v_a_3059_; uint8_t v___x_3063_; 
v___x_3063_ = lean_usize_dec_lt(v_i_3053_, v_sz_3052_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_box(v_b_3054_);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
else
{
lean_object* v_a_3066_; lean_object* v_fvarId_3067_; lean_object* v___x_3068_; 
v_a_3066_ = lean_array_uget_borrowed(v_as_3051_, v_i_3053_);
v_fvarId_3067_ = lean_ctor_get(v_a_3066_, 0);
v___x_3068_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3067_, v___y_3055_, v___y_3056_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref(v___x_3068_);
v___x_3070_ = lean_box(1);
v___x_3071_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3070_, v_a_3069_);
if (v___x_3071_ == 0)
{
lean_object* v___f_3072_; lean_object* v___x_3073_; 
lean_inc(v_fvarId_3067_);
v___f_3072_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3072_, 0, v_fvarId_3067_);
lean_closure_set(v___f_3072_, 1, v___x_3070_);
v___x_3073_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3072_, v___y_3055_, v___y_3056_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_dec_ref(v___x_3073_);
v_a_3059_ = v___x_3063_;
goto v___jp_3058_;
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
v_a_3059_ = v_b_3054_;
goto v___jp_3058_;
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
v_a_3082_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3068_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3068_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
v___jp_3058_:
{
size_t v___x_3060_; size_t v___x_3061_; 
v___x_3060_ = ((size_t)1ULL);
v___x_3061_ = lean_usize_add(v_i_3053_, v___x_3060_);
v_i_3053_ = v___x_3061_;
v_b_3054_ = v_a_3059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3090_, lean_object* v_sz_3091_, lean_object* v_i_3092_, lean_object* v_b_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
size_t v_sz_boxed_3097_; size_t v_i_boxed_3098_; uint8_t v_b_boxed_3099_; lean_object* v_res_3100_; 
v_sz_boxed_3097_ = lean_unbox_usize(v_sz_3091_);
lean_dec(v_sz_3091_);
v_i_boxed_3098_ = lean_unbox_usize(v_i_3092_);
lean_dec(v_i_3092_);
v_b_boxed_3099_ = lean_unbox(v_b_3093_);
v_res_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3090_, v_sz_boxed_3097_, v_i_boxed_3098_, v_b_boxed_3099_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec_ref(v_as_3090_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
uint8_t v_ret_3109_; size_t v_sz_3110_; size_t v___x_3111_; lean_object* v___x_3112_; 
v_ret_3109_ = 0;
v_sz_3110_ = lean_array_size(v_params_3101_);
v___x_3111_ = ((size_t)0ULL);
v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3101_, v_sz_3110_, v___x_3111_, v_ret_3109_, v_a_3102_, v_a_3103_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
lean_dec(v_a_3117_);
lean_dec_ref(v_a_3116_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec_ref(v_params_3113_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3122_, size_t v_sz_3123_, size_t v_i_3124_, uint8_t v_b_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3122_, v_sz_3123_, v_i_3124_, v_b_3125_, v___y_3126_, v___y_3127_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3134_, lean_object* v_sz_3135_, lean_object* v_i_3136_, lean_object* v_b_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
size_t v_sz_boxed_3145_; size_t v_i_boxed_3146_; uint8_t v_b_boxed_3147_; lean_object* v_res_3148_; 
v_sz_boxed_3145_ = lean_unbox_usize(v_sz_3135_);
lean_dec(v_sz_3135_);
v_i_boxed_3146_ = lean_unbox_usize(v_i_3136_);
lean_dec(v_i_3136_);
v_b_boxed_3147_ = lean_unbox(v_b_3137_);
v_res_3148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3134_, v_sz_boxed_3145_, v_i_boxed_3146_, v_b_boxed_3147_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec_ref(v_as_3134_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3149_, size_t v_i_3150_, size_t v_stop_3151_, lean_object* v_b_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
uint8_t v___x_3156_; 
v___x_3156_ = lean_usize_dec_eq(v_i_3150_, v_stop_3151_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v_fvarId_3158_; lean_object* v___x_3159_; 
v___x_3157_ = lean_array_uget_borrowed(v_as_3149_, v_i_3150_);
v_fvarId_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_fvarId_3158_);
v___x_3159_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3158_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; size_t v___x_3161_; size_t v___x_3162_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3150_, v___x_3161_);
v_i_3150_ = v___x_3162_;
v_b_3152_ = v_a_3160_;
goto _start;
}
else
{
return v___x_3159_;
}
}
else
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_b_3152_);
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3165_, lean_object* v_i_3166_, lean_object* v_stop_3167_, lean_object* v_b_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
size_t v_i_boxed_3172_; size_t v_stop_boxed_3173_; lean_object* v_res_3174_; 
v_i_boxed_3172_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_stop_boxed_3173_ = lean_unbox_usize(v_stop_3167_);
lean_dec(v_stop_3167_);
v_res_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3165_, v_i_boxed_3172_, v_stop_boxed_3173_, v_b_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v_as_3165_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v_decl_3194_; lean_object* v_k_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; 
switch(lean_obj_tag(v_x_3175_))
{
case 0:
{
lean_object* v_k_3216_; 
v_k_3216_ = lean_ctor_get(v_x_3175_, 1);
lean_inc_ref(v_k_3216_);
lean_dec_ref(v_x_3175_);
v_x_3175_ = v_k_3216_;
goto _start;
}
case 3:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec_ref(v_x_3175_);
v___x_3218_ = lean_box(0);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
case 4:
{
lean_object* v_cases_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3242_; 
v_cases_3220_ = lean_ctor_get(v_x_3175_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3222_ = v_x_3175_;
v_isShared_3223_ = v_isSharedCheck_3242_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_cases_3220_);
lean_dec(v_x_3175_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3242_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_alts_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v_alts_3224_ = lean_ctor_get(v_cases_3220_, 3);
lean_inc_ref(v_alts_3224_);
lean_dec_ref(v_cases_3220_);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = lean_array_get_size(v_alts_3224_);
v___x_3227_ = lean_box(0);
v___x_3228_ = lean_nat_dec_lt(v___x_3225_, v___x_3226_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3230_; 
lean_dec_ref(v_alts_3224_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3227_);
v___x_3230_ = v___x_3222_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3227_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = lean_nat_dec_le(v___x_3226_, v___x_3226_);
if (v___x_3232_ == 0)
{
if (v___x_3228_ == 0)
{
lean_object* v___x_3234_; 
lean_dec_ref(v_alts_3224_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3227_);
v___x_3234_ = v___x_3222_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3227_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
else
{
size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; 
lean_del_object(v___x_3222_);
v___x_3236_ = ((size_t)0ULL);
v___x_3237_ = lean_usize_of_nat(v___x_3226_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3224_, v___x_3236_, v___x_3237_, v___x_3227_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec_ref(v_alts_3224_);
return v___x_3238_;
}
}
else
{
size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
lean_del_object(v___x_3222_);
v___x_3239_ = ((size_t)0ULL);
v___x_3240_ = lean_usize_of_nat(v___x_3226_);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3224_, v___x_3239_, v___x_3240_, v___x_3227_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec_ref(v_alts_3224_);
return v___x_3241_;
}
}
}
}
case 5:
{
lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3250_; 
v_isSharedCheck_3250_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_x_3175_, 0);
lean_dec(v_unused_3251_);
v___x_3244_ = v_x_3175_;
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
else
{
lean_dec(v_x_3175_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3246_ = lean_box(0);
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3246_);
v___x_3248_ = v___x_3244_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
case 6:
{
lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3259_; 
v_isSharedCheck_3259_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v_x_3175_, 0);
lean_dec(v_unused_3260_);
v___x_3253_ = v_x_3175_;
v_isShared_3254_ = v_isSharedCheck_3259_;
goto v_resetjp_3252_;
}
else
{
lean_dec(v_x_3175_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3259_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = lean_box(0);
if (v_isShared_3254_ == 0)
{
lean_ctor_set_tag(v___x_3253_, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3255_);
v___x_3257_ = v___x_3253_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
default: 
{
lean_object* v_decl_3261_; lean_object* v_k_3262_; 
v_decl_3261_ = lean_ctor_get(v_x_3175_, 0);
lean_inc_ref(v_decl_3261_);
v_k_3262_ = lean_ctor_get(v_x_3175_, 1);
lean_inc_ref(v_k_3262_);
lean_dec_ref(v_x_3175_);
v_decl_3194_ = v_decl_3261_;
v_k_3195_ = v_k_3262_;
v___y_3196_ = v_a_3176_;
v___y_3197_ = v_a_3177_;
v___y_3198_ = v_a_3178_;
v___y_3199_ = v_a_3179_;
v___y_3200_ = v_a_3180_;
v___y_3201_ = v_a_3181_;
goto v___jp_3193_;
}
}
v___jp_3183_:
{
if (lean_obj_tag(v___y_3191_) == 0)
{
lean_dec_ref(v___y_3191_);
v_x_3175_ = v___y_3190_;
v_a_3176_ = v___y_3189_;
v_a_3177_ = v___y_3188_;
v_a_3178_ = v___y_3185_;
v_a_3179_ = v___y_3186_;
v_a_3180_ = v___y_3184_;
v_a_3181_ = v___y_3187_;
goto _start;
}
else
{
lean_dec_ref(v___y_3190_);
return v___y_3191_;
}
}
v___jp_3193_:
{
lean_object* v_params_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v_params_3202_ = lean_ctor_get(v_decl_3194_, 2);
lean_inc_ref(v_params_3202_);
lean_dec_ref(v_decl_3194_);
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = lean_array_get_size(v_params_3202_);
v___x_3205_ = lean_nat_dec_lt(v___x_3203_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_dec_ref(v_params_3202_);
v_x_3175_ = v_k_3195_;
v_a_3176_ = v___y_3196_;
v_a_3177_ = v___y_3197_;
v_a_3178_ = v___y_3198_;
v_a_3179_ = v___y_3199_;
v_a_3180_ = v___y_3200_;
v_a_3181_ = v___y_3201_;
goto _start;
}
else
{
lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3207_ = lean_box(0);
v___x_3208_ = lean_nat_dec_le(v___x_3204_, v___x_3204_);
if (v___x_3208_ == 0)
{
if (v___x_3205_ == 0)
{
lean_dec_ref(v_params_3202_);
v_x_3175_ = v_k_3195_;
v_a_3176_ = v___y_3196_;
v_a_3177_ = v___y_3197_;
v_a_3178_ = v___y_3198_;
v_a_3179_ = v___y_3199_;
v_a_3180_ = v___y_3200_;
v_a_3181_ = v___y_3201_;
goto _start;
}
else
{
size_t v___x_3210_; size_t v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = ((size_t)0ULL);
v___x_3211_ = lean_usize_of_nat(v___x_3204_);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3202_, v___x_3210_, v___x_3211_, v___x_3207_, v___y_3196_, v___y_3197_);
lean_dec_ref(v_params_3202_);
v___y_3184_ = v___y_3200_;
v___y_3185_ = v___y_3198_;
v___y_3186_ = v___y_3199_;
v___y_3187_ = v___y_3201_;
v___y_3188_ = v___y_3197_;
v___y_3189_ = v___y_3196_;
v___y_3190_ = v_k_3195_;
v___y_3191_ = v___x_3212_;
goto v___jp_3183_;
}
}
else
{
size_t v___x_3213_; size_t v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = ((size_t)0ULL);
v___x_3214_ = lean_usize_of_nat(v___x_3204_);
v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3202_, v___x_3213_, v___x_3214_, v___x_3207_, v___y_3196_, v___y_3197_);
lean_dec_ref(v_params_3202_);
v___y_3184_ = v___y_3200_;
v___y_3185_ = v___y_3198_;
v___y_3186_ = v___y_3199_;
v___y_3187_ = v___y_3201_;
v___y_3188_ = v___y_3197_;
v___y_3189_ = v___y_3196_;
v___y_3190_ = v_k_3195_;
v___y_3191_ = v___x_3215_;
goto v___jp_3183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3263_, size_t v_i_3264_, size_t v_stop_3265_, lean_object* v_b_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___y_3275_; uint8_t v___x_3281_; 
v___x_3281_ = lean_usize_dec_eq(v_i_3264_, v_stop_3265_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_array_uget_borrowed(v_as_3263_, v_i_3264_);
switch(lean_obj_tag(v___x_3282_))
{
case 0:
{
lean_object* v_code_3283_; 
v_code_3283_ = lean_ctor_get(v___x_3282_, 2);
lean_inc_ref(v_code_3283_);
v___y_3275_ = v_code_3283_;
goto v___jp_3274_;
}
case 1:
{
lean_object* v_code_3284_; 
v_code_3284_ = lean_ctor_get(v___x_3282_, 1);
lean_inc_ref(v_code_3284_);
v___y_3275_ = v_code_3284_;
goto v___jp_3274_;
}
default: 
{
lean_object* v_code_3285_; 
v_code_3285_ = lean_ctor_get(v___x_3282_, 0);
lean_inc_ref(v_code_3285_);
v___y_3275_ = v_code_3285_;
goto v___jp_3274_;
}
}
}
else
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_b_3266_);
return v___x_3286_;
}
v___jp_3274_:
{
lean_object* v___x_3276_; 
v___x_3276_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3275_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; size_t v___x_3278_; size_t v___x_3279_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
v___x_3278_ = ((size_t)1ULL);
v___x_3279_ = lean_usize_add(v_i_3264_, v___x_3278_);
v_i_3264_ = v___x_3279_;
v_b_3266_ = v_a_3277_;
goto _start;
}
else
{
return v___x_3276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3287_, lean_object* v_i_3288_, lean_object* v_stop_3289_, lean_object* v_b_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
size_t v_i_boxed_3298_; size_t v_stop_boxed_3299_; lean_object* v_res_3300_; 
v_i_boxed_3298_ = lean_unbox_usize(v_i_3288_);
lean_dec(v_i_3288_);
v_stop_boxed_3299_ = lean_unbox_usize(v_stop_3289_);
lean_dec(v_stop_3289_);
v_res_3300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3287_, v_i_boxed_3298_, v_stop_boxed_3299_, v_b_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec_ref(v_as_3287_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3310_, size_t v_i_3311_, size_t v_stop_3312_, lean_object* v_b_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3310_, v_i_3311_, v_stop_3312_, v_b_3313_, v___y_3314_, v___y_3315_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3322_, lean_object* v_i_3323_, lean_object* v_stop_3324_, lean_object* v_b_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
size_t v_i_boxed_3333_; size_t v_stop_boxed_3334_; lean_object* v_res_3335_; 
v_i_boxed_3333_ = lean_unbox_usize(v_i_3323_);
lean_dec(v_i_3323_);
v_stop_boxed_3334_ = lean_unbox_usize(v_stop_3324_);
lean_dec(v_stop_3324_);
v_res_3335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3322_, v_i_boxed_3333_, v_stop_boxed_3334_, v_b_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v_as_3322_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3336_, lean_object* v_b_3337_){
_start:
{
lean_object* v_array_3338_; lean_object* v_start_3339_; lean_object* v_stop_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3353_; 
v_array_3338_ = lean_ctor_get(v_a_3336_, 0);
v_start_3339_ = lean_ctor_get(v_a_3336_, 1);
v_stop_3340_ = lean_ctor_get(v_a_3336_, 2);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_a_3336_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3342_ = v_a_3336_;
v_isShared_3343_ = v_isSharedCheck_3353_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_stop_3340_);
lean_inc(v_start_3339_);
lean_inc(v_array_3338_);
lean_dec(v_a_3336_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3353_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
uint8_t v___x_3344_; 
v___x_3344_ = lean_nat_dec_lt(v_start_3339_, v_stop_3340_);
if (v___x_3344_ == 0)
{
lean_del_object(v___x_3342_);
lean_dec(v_stop_3340_);
lean_dec(v_start_3339_);
lean_dec_ref(v_array_3338_);
return v_b_3337_;
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = lean_nat_add(v_start_3339_, v___x_3345_);
lean_inc_ref(v_array_3338_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v___x_3346_);
v___x_3348_ = v___x_3342_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_array_3338_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_stop_3340_);
v___x_3348_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_array_fget(v_array_3338_, v_start_3339_);
lean_dec(v_start_3339_);
lean_dec_ref(v_array_3338_);
v___x_3350_ = lean_array_push(v_b_3337_, v___x_3349_);
v_a_3336_ = v___x_3348_;
v_b_3337_ = v___x_3350_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3354_, size_t v_i_3355_, lean_object* v_bs_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_usize_dec_lt(v_i_3355_, v_sz_3354_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_bs_3356_);
return v___x_3361_;
}
else
{
lean_object* v_v_3362_; lean_object* v___x_3363_; 
v_v_3362_ = lean_array_uget_borrowed(v_bs_3356_, v_i_3355_);
v___x_3363_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3362_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; lean_object* v_bs_x27_3366_; size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = lean_unsigned_to_nat(0u);
v_bs_x27_3366_ = lean_array_uset(v_bs_3356_, v_i_3355_, v___x_3365_);
v___x_3367_ = ((size_t)1ULL);
v___x_3368_ = lean_usize_add(v_i_3355_, v___x_3367_);
v___x_3369_ = lean_array_uset(v_bs_x27_3366_, v_i_3355_, v_a_3364_);
v_i_3355_ = v___x_3368_;
v_bs_3356_ = v___x_3369_;
goto _start;
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v_bs_3356_);
v_a_3371_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3363_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3363_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3379_, lean_object* v_i_3380_, lean_object* v_bs_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
size_t v_sz_boxed_3385_; size_t v_i_boxed_3386_; lean_object* v_res_3387_; 
v_sz_boxed_3385_ = lean_unbox_usize(v_sz_3379_);
lean_dec(v_sz_3379_);
v_i_boxed_3386_ = lean_unbox_usize(v_i_3380_);
lean_dec(v_i_3380_);
v_res_3387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3385_, v_i_boxed_3386_, v_bs_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3388_, size_t v_i_3389_, size_t v_stop_3390_, lean_object* v_b_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_usize_dec_eq(v_i_3389_, v_stop_3390_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v_fvarId_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3397_ = lean_array_uget_borrowed(v_as_3388_, v_i_3389_);
v_fvarId_3398_ = lean_ctor_get(v___x_3397_, 0);
v___x_3399_ = lean_box(1);
lean_inc(v_fvarId_3398_);
v___x_3400_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3398_, v___x_3399_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; size_t v___x_3402_; size_t v___x_3403_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref(v___x_3400_);
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3389_, v___x_3402_);
v_i_3389_ = v___x_3403_;
v_b_3391_ = v_a_3401_;
goto _start;
}
else
{
return v___x_3400_;
}
}
else
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_b_3391_);
return v___x_3405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3406_, lean_object* v_i_3407_, lean_object* v_stop_3408_, lean_object* v_b_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
size_t v_i_boxed_3414_; size_t v_stop_boxed_3415_; lean_object* v_res_3416_; 
v_i_boxed_3414_ = lean_unbox_usize(v_i_3407_);
lean_dec(v_i_3407_);
v_stop_boxed_3415_ = lean_unbox_usize(v_stop_3408_);
lean_dec(v_stop_3408_);
v_res_3416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3406_, v_i_boxed_3414_, v_stop_boxed_3415_, v_b_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v_as_3406_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3417_, size_t v_i_3418_, size_t v_stop_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_usize_dec_eq(v_i_3418_, v_stop_3419_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v_fvarId_3429_; lean_object* v___x_3430_; 
v___x_3426_ = lean_array_uget_borrowed(v_as_3417_, v_i_3418_);
v_fst_3427_ = lean_ctor_get(v___x_3426_, 0);
v_snd_3428_ = lean_ctor_get(v___x_3426_, 1);
v_fvarId_3429_ = lean_ctor_get(v_fst_3427_, 0);
lean_inc(v_snd_3428_);
lean_inc(v_fvarId_3429_);
v___x_3430_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3429_, v_snd_3428_, v___y_3421_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; size_t v___x_3432_; size_t v___x_3433_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___x_3430_);
v___x_3432_ = ((size_t)1ULL);
v___x_3433_ = lean_usize_add(v_i_3418_, v___x_3432_);
v_i_3418_ = v___x_3433_;
v_b_3420_ = v_a_3431_;
goto _start;
}
else
{
return v___x_3430_;
}
}
else
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v_b_3420_);
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3436_, lean_object* v_i_3437_, lean_object* v_stop_3438_, lean_object* v_b_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
size_t v_i_boxed_3444_; size_t v_stop_boxed_3445_; lean_object* v_res_3446_; 
v_i_boxed_3444_ = lean_unbox_usize(v_i_3437_);
lean_dec(v_i_3437_);
v_stop_boxed_3445_ = lean_unbox_usize(v_stop_3438_);
lean_dec(v_stop_3438_);
v_res_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3436_, v_i_boxed_3444_, v_stop_boxed_3445_, v_b_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec_ref(v_as_3436_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3449_, size_t v_i_3450_, size_t v_stop_3451_, lean_object* v_b_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_eq(v_i_3450_, v_stop_3451_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = lean_array_uget_borrowed(v_as_3449_, v_i_3450_);
v___x_3462_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3461_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; size_t v___x_3464_; size_t v___x_3465_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3462_);
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3450_, v___x_3464_);
v_i_3450_ = v___x_3465_;
v_b_3452_ = v_a_3463_;
goto _start;
}
else
{
return v___x_3462_;
}
}
else
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_b_3452_);
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v___y_3483_; 
switch(lean_obj_tag(v_letVal_3468_))
{
case 0:
{
lean_object* v_value_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3500_; 
v_value_3492_ = lean_ctor_get(v_letVal_3468_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_letVal_3468_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3494_ = v_letVal_3468_;
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_value_3492_);
lean_dec(v_letVal_3468_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3496_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3492_);
lean_dec_ref(v_value_3492_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3496_);
v___x_3498_ = v___x_3494_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
case 1:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_box(1);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
case 2:
{
lean_object* v_idx_3503_; lean_object* v_struct_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_idx_3503_ = lean_ctor_get(v_letVal_3468_, 1);
lean_inc(v_idx_3503_);
v_struct_3504_ = lean_ctor_get(v_letVal_3468_, 2);
lean_inc(v_struct_3504_);
lean_dec_ref(v_letVal_3468_);
v___x_3505_ = lean_st_ref_get(v_a_3474_);
v___x_3506_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3504_, v_a_3469_, v_a_3470_);
lean_dec(v_struct_3504_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3516_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3516_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3516_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v_env_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v_env_3511_ = lean_ctor_get(v___x_3505_, 0);
lean_inc_ref(v_env_3511_);
lean_dec(v___x_3505_);
v___x_3512_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3511_, v_a_3507_, v_idx_3503_);
lean_dec(v_idx_3503_);
lean_dec(v_a_3507_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3512_);
v___x_3514_ = v___x_3509_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
else
{
lean_dec(v___x_3505_);
lean_dec(v_idx_3503_);
return v___x_3506_;
}
}
case 3:
{
lean_object* v_declName_3517_; lean_object* v_args_3518_; lean_object* v___x_3519_; lean_object* v_env_3520_; lean_object* v___x_3521_; lean_object* v_numFields_3523_; lean_object* v_lower_3524_; lean_object* v_upper_3525_; lean_object* v___x_3553_; lean_object* v___y_3622_; uint8_t v___x_3631_; 
v_declName_3517_ = lean_ctor_get(v_letVal_3468_, 0);
lean_inc(v_declName_3517_);
v_args_3518_ = lean_ctor_get(v_letVal_3468_, 2);
lean_inc_ref(v_args_3518_);
lean_dec_ref(v_letVal_3468_);
v___x_3519_ = lean_st_ref_get(v_a_3474_);
v_env_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc_ref(v_env_3520_);
lean_dec(v___x_3519_);
v___x_3521_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_array_get_size(v_args_3518_);
v___x_3631_ = lean_nat_dec_lt(v___x_3521_, v___x_3553_);
if (v___x_3631_ == 0)
{
goto v___jp_3554_;
}
else
{
lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3632_ = lean_box(0);
v___x_3633_ = lean_nat_dec_le(v___x_3553_, v___x_3553_);
if (v___x_3633_ == 0)
{
if (v___x_3631_ == 0)
{
goto v___jp_3554_;
}
else
{
size_t v___x_3634_; size_t v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = ((size_t)0ULL);
v___x_3635_ = lean_usize_of_nat(v___x_3553_);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3518_, v___x_3634_, v___x_3635_, v___x_3632_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
v___y_3622_ = v___x_3636_;
goto v___jp_3621_;
}
}
else
{
size_t v___x_3637_; size_t v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = ((size_t)0ULL);
v___x_3638_ = lean_usize_of_nat(v___x_3553_);
v___x_3639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3518_, v___x_3637_, v___x_3638_, v___x_3632_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
v___y_3622_ = v___x_3639_;
goto v___jp_3621_;
}
}
v___jp_3522_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v___x_3526_ = l_Array_toSubarray___redArg(v_args_3518_, v_lower_3524_, v_upper_3525_);
v___x_3527_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3528_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3526_, v___x_3527_);
v___x_3529_ = lean_array_get_size(v___x_3528_);
v___x_3530_ = lean_nat_dec_eq(v_numFields_3523_, v___x_3529_);
lean_dec(v_numFields_3523_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_dec_ref(v___x_3528_);
lean_dec(v_declName_3517_);
v___x_3531_ = lean_box(1);
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
else
{
size_t v_sz_3533_; size_t v___x_3534_; lean_object* v___x_3535_; 
v_sz_3533_ = lean_array_size(v___x_3528_);
v___x_3534_ = ((size_t)0ULL);
v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3533_, v___x_3534_, v___x_3528_, v_a_3469_, v_a_3470_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3544_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3544_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3544_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3540_, 0, v_declName_3517_);
lean_ctor_set(v___x_3540_, 1, v_a_3536_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3540_);
v___x_3542_ = v___x_3538_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_declName_3517_);
v_a_3545_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3535_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3535_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
v___jp_3554_:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3471_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; uint8_t v___x_3557_; lean_object* v___x_3558_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = lean_unbox(v_a_3556_);
lean_dec(v_a_3556_);
lean_inc(v_declName_3517_);
v___x_3558_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3517_, v___x_3557_, v_a_3473_, v_a_3474_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3604_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3604_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3604_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
if (lean_obj_tag(v_a_3559_) == 1)
{
lean_object* v_val_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
lean_dec_ref(v_args_3518_);
v_val_3563_ = lean_ctor_get(v_a_3559_, 0);
lean_inc(v_val_3563_);
lean_dec_ref(v_a_3559_);
v___x_3564_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3563_);
lean_dec(v_val_3563_);
v___x_3565_ = lean_nat_dec_eq(v___x_3564_, v___x_3553_);
lean_dec(v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
lean_dec_ref(v_env_3520_);
lean_dec(v_declName_3517_);
v___x_3566_ = lean_box(1);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3566_);
v___x_3568_ = v___x_3561_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
else
{
lean_object* v___x_3570_; 
lean_inc(v_declName_3517_);
v___x_3570_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3520_, v_declName_3517_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v___x_3571_; 
lean_del_object(v___x_3561_);
v___x_3571_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3517_, v_a_3469_, v_a_3470_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3584_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3584_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3584_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
if (lean_obj_tag(v_a_3572_) == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3576_ = lean_box(1);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3578_ = v___x_3574_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
else
{
lean_object* v_val_3580_; lean_object* v___x_3582_; 
v_val_3580_ = lean_ctor_get(v_a_3572_, 0);
lean_inc(v_val_3580_);
lean_dec_ref(v_a_3572_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v_val_3580_);
v___x_3582_ = v___x_3574_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_val_3580_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
v_a_3585_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3571_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3571_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_object* v_val_3593_; lean_object* v___x_3595_; 
lean_dec(v_declName_3517_);
v_val_3593_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_val_3593_);
lean_dec_ref(v___x_3570_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v_val_3593_);
v___x_3595_ = v___x_3561_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_val_3593_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
uint8_t v___x_3597_; lean_object* v___x_3598_; 
lean_del_object(v___x_3561_);
lean_dec(v_a_3559_);
v___x_3597_ = 0;
lean_inc(v_declName_3517_);
v___x_3598_ = l_Lean_Environment_find_x3f(v_env_3520_, v_declName_3517_, v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 1)
{
lean_object* v_val_3599_; 
v_val_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_val_3599_);
lean_dec_ref(v___x_3598_);
if (lean_obj_tag(v_val_3599_) == 6)
{
lean_object* v_val_3600_; lean_object* v_numParams_3601_; lean_object* v_numFields_3602_; uint8_t v___x_3603_; 
v_val_3600_ = lean_ctor_get(v_val_3599_, 0);
lean_inc_ref(v_val_3600_);
lean_dec_ref(v_val_3599_);
v_numParams_3601_ = lean_ctor_get(v_val_3600_, 3);
lean_inc(v_numParams_3601_);
v_numFields_3602_ = lean_ctor_get(v_val_3600_, 4);
lean_inc(v_numFields_3602_);
lean_dec_ref(v_val_3600_);
v___x_3603_ = lean_nat_dec_le(v_numParams_3601_, v___x_3521_);
if (v___x_3603_ == 0)
{
v_numFields_3523_ = v_numFields_3602_;
v_lower_3524_ = v_numParams_3601_;
v_upper_3525_ = v___x_3553_;
goto v___jp_3522_;
}
else
{
lean_dec(v_numParams_3601_);
v_numFields_3523_ = v_numFields_3602_;
v_lower_3524_ = v___x_3521_;
v_upper_3525_ = v___x_3553_;
goto v___jp_3522_;
}
}
else
{
lean_dec(v_val_3599_);
lean_dec_ref(v_args_3518_);
lean_dec(v_declName_3517_);
goto v___jp_3476_;
}
}
else
{
lean_dec(v___x_3598_);
lean_dec_ref(v_args_3518_);
lean_dec(v_declName_3517_);
goto v___jp_3476_;
}
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec_ref(v_env_3520_);
lean_dec_ref(v_args_3518_);
lean_dec(v_declName_3517_);
v_a_3605_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3558_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3558_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec_ref(v_env_3520_);
lean_dec_ref(v_args_3518_);
lean_dec(v_declName_3517_);
v_a_3613_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3555_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3555_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
v___jp_3621_:
{
if (lean_obj_tag(v___y_3622_) == 0)
{
lean_dec_ref(v___y_3622_);
goto v___jp_3554_;
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref(v_env_3520_);
lean_dec_ref(v_args_3518_);
lean_dec(v_declName_3517_);
v_a_3623_ = lean_ctor_get(v___y_3622_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___y_3622_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___y_3622_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___y_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
default: 
{
lean_object* v_args_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v_args_3640_ = lean_ctor_get(v_letVal_3468_, 1);
lean_inc_ref(v_args_3640_);
lean_dec_ref(v_letVal_3468_);
v___x_3641_ = lean_unsigned_to_nat(0u);
v___x_3642_ = lean_array_get_size(v_args_3640_);
v___x_3643_ = lean_nat_dec_lt(v___x_3641_, v___x_3642_);
if (v___x_3643_ == 0)
{
lean_dec_ref(v_args_3640_);
goto v___jp_3479_;
}
else
{
lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3644_ = lean_box(0);
v___x_3645_ = lean_nat_dec_le(v___x_3642_, v___x_3642_);
if (v___x_3645_ == 0)
{
if (v___x_3643_ == 0)
{
lean_dec_ref(v_args_3640_);
goto v___jp_3479_;
}
else
{
size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v___x_3646_ = ((size_t)0ULL);
v___x_3647_ = lean_usize_of_nat(v___x_3642_);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3640_, v___x_3646_, v___x_3647_, v___x_3644_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
lean_dec_ref(v_args_3640_);
v___y_3483_ = v___x_3648_;
goto v___jp_3482_;
}
}
else
{
size_t v___x_3649_; size_t v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = ((size_t)0ULL);
v___x_3650_ = lean_usize_of_nat(v___x_3642_);
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3640_, v___x_3649_, v___x_3650_, v___x_3644_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
lean_dec_ref(v_args_3640_);
v___y_3483_ = v___x_3651_;
goto v___jp_3482_;
}
}
}
}
v___jp_3476_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_box(1);
v___x_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
return v___x_3478_;
}
v___jp_3479_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_box(1);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
v___jp_3482_:
{
if (lean_obj_tag(v___y_3483_) == 0)
{
lean_dec_ref(v___y_3483_);
goto v___jp_3479_;
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_a_3484_ = lean_ctor_get(v___y_3483_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___y_3483_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___y_3483_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___y_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3652_, lean_object* v_args_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v_params_3661_; lean_object* v_value_3662_; lean_object* v___x_3663_; 
v_params_3661_ = lean_ctor_get(v_funDecl_3652_, 2);
lean_inc_ref(v_params_3661_);
v_value_3662_ = lean_ctor_get(v_funDecl_3652_, 4);
lean_inc_ref(v_value_3662_);
lean_dec_ref(v_funDecl_3652_);
v___x_3663_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3661_, v_args_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3675_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3675_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3675_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
uint8_t v___x_3668_; 
v___x_3668_ = lean_unbox(v_a_3664_);
lean_dec(v_a_3664_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3671_; 
lean_dec_ref(v_value_3662_);
v___x_3669_ = lean_box(0);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3669_);
v___x_3671_ = v___x_3666_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
else
{
lean_object* v___x_3673_; 
lean_del_object(v___x_3666_);
lean_inc_ref(v_value_3662_);
v___x_3673_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3662_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v___x_3674_; 
lean_dec_ref(v___x_3673_);
v___x_3674_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3662_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
return v___x_3674_;
}
else
{
lean_dec_ref(v_value_3662_);
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec_ref(v_value_3662_);
v_a_3676_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3663_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3663_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3684_, lean_object* v_as_3685_, size_t v_sz_3686_, size_t v_i_3687_, lean_object* v_b_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_a_3697_; uint8_t v___x_3701_; 
v___x_3701_ = lean_usize_dec_lt(v_i_3687_, v_sz_3686_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; 
lean_dec(v_a_3684_);
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_b_3688_);
return v___x_3702_;
}
else
{
lean_object* v___x_3703_; lean_object* v_a_3704_; 
v___x_3703_ = lean_box(0);
v_a_3704_ = lean_array_uget_borrowed(v_as_3685_, v_i_3687_);
if (lean_obj_tag(v_a_3704_) == 0)
{
lean_object* v_ctorName_3705_; lean_object* v_params_3706_; lean_object* v_code_3707_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3717_; lean_object* v___y_3719_; lean_object* v___x_3720_; 
v_ctorName_3705_ = lean_ctor_get(v_a_3704_, 0);
v_params_3706_ = lean_ctor_get(v_a_3704_, 1);
v_code_3707_ = lean_ctor_get(v_a_3704_, 2);
lean_inc(v_a_3684_);
v___x_3720_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3684_, v_ctorName_3705_);
if (lean_obj_tag(v___x_3720_) == 1)
{
lean_object* v_val_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v_val_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_val_3721_);
lean_dec_ref(v___x_3720_);
v___x_3722_ = l_Array_zip___redArg(v_params_3706_, v_val_3721_);
lean_dec(v_val_3721_);
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = lean_array_get_size(v___x_3722_);
v___x_3725_ = lean_nat_dec_lt(v___x_3723_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_dec_ref(v___x_3722_);
v___y_3709_ = v___y_3689_;
v___y_3710_ = v___y_3690_;
v___y_3711_ = v___y_3691_;
v___y_3712_ = v___y_3692_;
v___y_3713_ = v___y_3693_;
v___y_3714_ = v___y_3694_;
goto v___jp_3708_;
}
else
{
uint8_t v___x_3726_; 
v___x_3726_ = lean_nat_dec_le(v___x_3724_, v___x_3724_);
if (v___x_3726_ == 0)
{
if (v___x_3725_ == 0)
{
lean_dec_ref(v___x_3722_);
v___y_3709_ = v___y_3689_;
v___y_3710_ = v___y_3690_;
v___y_3711_ = v___y_3691_;
v___y_3712_ = v___y_3692_;
v___y_3713_ = v___y_3693_;
v___y_3714_ = v___y_3694_;
goto v___jp_3708_;
}
else
{
size_t v___x_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3727_ = ((size_t)0ULL);
v___x_3728_ = lean_usize_of_nat(v___x_3724_);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3722_, v___x_3727_, v___x_3728_, v___x_3703_, v___y_3689_, v___y_3690_, v___y_3694_);
lean_dec_ref(v___x_3722_);
v___y_3717_ = v___x_3729_;
goto v___jp_3716_;
}
}
else
{
size_t v___x_3730_; size_t v___x_3731_; lean_object* v___x_3732_; 
v___x_3730_ = ((size_t)0ULL);
v___x_3731_ = lean_usize_of_nat(v___x_3724_);
v___x_3732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3722_, v___x_3730_, v___x_3731_, v___x_3703_, v___y_3689_, v___y_3690_, v___y_3694_);
lean_dec_ref(v___x_3722_);
v___y_3717_ = v___x_3732_;
goto v___jp_3716_;
}
}
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
lean_dec(v___x_3720_);
v___x_3733_ = lean_unsigned_to_nat(0u);
v___x_3734_ = lean_array_get_size(v_params_3706_);
v___x_3735_ = lean_nat_dec_lt(v___x_3733_, v___x_3734_);
if (v___x_3735_ == 0)
{
v___y_3709_ = v___y_3689_;
v___y_3710_ = v___y_3690_;
v___y_3711_ = v___y_3691_;
v___y_3712_ = v___y_3692_;
v___y_3713_ = v___y_3693_;
v___y_3714_ = v___y_3694_;
goto v___jp_3708_;
}
else
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_nat_dec_le(v___x_3734_, v___x_3734_);
if (v___x_3736_ == 0)
{
if (v___x_3735_ == 0)
{
v___y_3709_ = v___y_3689_;
v___y_3710_ = v___y_3690_;
v___y_3711_ = v___y_3691_;
v___y_3712_ = v___y_3692_;
v___y_3713_ = v___y_3693_;
v___y_3714_ = v___y_3694_;
goto v___jp_3708_;
}
else
{
size_t v___x_3737_; size_t v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = ((size_t)0ULL);
v___x_3738_ = lean_usize_of_nat(v___x_3734_);
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3706_, v___x_3737_, v___x_3738_, v___x_3703_, v___y_3689_, v___y_3690_, v___y_3694_);
v___y_3719_ = v___x_3739_;
goto v___jp_3718_;
}
}
else
{
size_t v___x_3740_; size_t v___x_3741_; lean_object* v___x_3742_; 
v___x_3740_ = ((size_t)0ULL);
v___x_3741_ = lean_usize_of_nat(v___x_3734_);
v___x_3742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3706_, v___x_3740_, v___x_3741_, v___x_3703_, v___y_3689_, v___y_3690_, v___y_3694_);
v___y_3719_ = v___x_3742_;
goto v___jp_3718_;
}
}
}
v___jp_3708_:
{
lean_object* v___x_3715_; 
lean_inc_ref(v_code_3707_);
v___x_3715_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3707_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_dec_ref(v___x_3715_);
v_a_3697_ = v___x_3703_;
goto v___jp_3696_;
}
else
{
lean_dec(v_a_3684_);
return v___x_3715_;
}
}
v___jp_3716_:
{
if (lean_obj_tag(v___y_3717_) == 0)
{
lean_dec_ref(v___y_3717_);
v___y_3709_ = v___y_3689_;
v___y_3710_ = v___y_3690_;
v___y_3711_ = v___y_3691_;
v___y_3712_ = v___y_3692_;
v___y_3713_ = v___y_3693_;
v___y_3714_ = v___y_3694_;
goto v___jp_3708_;
}
else
{
lean_dec(v_a_3684_);
return v___y_3717_;
}
}
v___jp_3718_:
{
if (lean_obj_tag(v___y_3719_) == 0)
{
lean_dec_ref(v___y_3719_);
v___y_3709_ = v___y_3689_;
v___y_3710_ = v___y_3690_;
v___y_3711_ = v___y_3691_;
v___y_3712_ = v___y_3692_;
v___y_3713_ = v___y_3693_;
v___y_3714_ = v___y_3694_;
goto v___jp_3708_;
}
else
{
lean_dec(v_a_3684_);
return v___y_3719_;
}
}
}
else
{
lean_object* v_code_3743_; lean_object* v___x_3744_; 
v_code_3743_ = lean_ctor_get(v_a_3704_, 0);
lean_inc_ref(v_code_3743_);
v___x_3744_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3743_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_dec_ref(v___x_3744_);
v_a_3697_ = v___x_3703_;
goto v___jp_3696_;
}
else
{
lean_dec(v_a_3684_);
return v___x_3744_;
}
}
}
v___jp_3696_:
{
size_t v___x_3698_; size_t v___x_3699_; 
v___x_3698_ = ((size_t)1ULL);
v___x_3699_ = lean_usize_add(v_i_3687_, v___x_3698_);
v_i_3687_ = v___x_3699_;
v_b_3688_ = v_a_3697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v_decl_3754_; lean_object* v_k_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; 
switch(lean_obj_tag(v_x_3745_))
{
case 0:
{
lean_object* v_decl_3765_; lean_object* v_k_3766_; lean_object* v_fvarId_3767_; lean_object* v_value_3768_; lean_object* v___x_3769_; 
v_decl_3765_ = lean_ctor_get(v_x_3745_, 0);
lean_inc_ref(v_decl_3765_);
v_k_3766_ = lean_ctor_get(v_x_3745_, 1);
lean_inc_ref(v_k_3766_);
lean_dec_ref(v_x_3745_);
v_fvarId_3767_ = lean_ctor_get(v_decl_3765_, 0);
lean_inc(v_fvarId_3767_);
v_value_3768_ = lean_ctor_get(v_decl_3765_, 3);
lean_inc(v_value_3768_);
lean_dec_ref(v_decl_3765_);
lean_inc(v_value_3768_);
v___x_3769_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3768_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3767_, v_a_3770_, v_a_3746_, v_a_3747_, v_a_3751_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_dec_ref(v___x_3771_);
if (lean_obj_tag(v_value_3768_) == 4)
{
lean_object* v_fvarId_3772_; lean_object* v_args_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; 
v_fvarId_3772_ = lean_ctor_get(v_value_3768_, 0);
lean_inc(v_fvarId_3772_);
v_args_3773_ = lean_ctor_get(v_value_3768_, 1);
lean_inc_ref(v_args_3773_);
lean_dec_ref(v_value_3768_);
v___x_3774_ = 0;
v___x_3775_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3774_, v_fvarId_3772_, v_a_3749_);
lean_dec(v_fvarId_3772_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3775_);
if (lean_obj_tag(v_a_3776_) == 1)
{
lean_object* v_val_3777_; lean_object* v___x_3778_; 
v_val_3777_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_val_3777_);
lean_dec_ref(v_a_3776_);
v___x_3778_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3777_, v_args_3773_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_dec_ref(v___x_3778_);
v_x_3745_ = v_k_3766_;
goto _start;
}
else
{
lean_dec_ref(v_k_3766_);
return v___x_3778_;
}
}
else
{
lean_dec(v_a_3776_);
lean_dec_ref(v_args_3773_);
v_x_3745_ = v_k_3766_;
goto _start;
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref(v_args_3773_);
lean_dec_ref(v_k_3766_);
v_a_3781_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3775_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3775_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_dec(v_value_3768_);
v_x_3745_ = v_k_3766_;
goto _start;
}
}
else
{
lean_dec(v_value_3768_);
lean_dec_ref(v_k_3766_);
return v___x_3771_;
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec(v_value_3768_);
lean_dec(v_fvarId_3767_);
lean_dec_ref(v_k_3766_);
v_a_3790_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3769_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3769_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3798_; lean_object* v_args_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; 
v_fvarId_3798_ = lean_ctor_get(v_x_3745_, 0);
lean_inc(v_fvarId_3798_);
v_args_3799_ = lean_ctor_get(v_x_3745_, 1);
lean_inc_ref(v_args_3799_);
lean_dec_ref(v_x_3745_);
v___x_3800_ = 0;
v___x_3801_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3800_, v_fvarId_3798_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___y_3804_; lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___x_3801_);
v___x_3806_ = lean_unsigned_to_nat(0u);
v___x_3807_ = lean_array_get_size(v_args_3799_);
v___x_3808_ = lean_nat_dec_lt(v___x_3806_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
v___x_3809_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3802_, v_args_3799_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
return v___x_3809_;
}
else
{
lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = lean_box(0);
v___x_3811_ = lean_nat_dec_le(v___x_3807_, v___x_3807_);
if (v___x_3811_ == 0)
{
if (v___x_3808_ == 0)
{
lean_object* v___x_3812_; 
v___x_3812_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3802_, v_args_3799_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
return v___x_3812_;
}
else
{
size_t v___x_3813_; size_t v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = ((size_t)0ULL);
v___x_3814_ = lean_usize_of_nat(v___x_3807_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3799_, v___x_3813_, v___x_3814_, v___x_3810_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
v___y_3804_ = v___x_3815_;
goto v___jp_3803_;
}
}
else
{
size_t v___x_3816_; size_t v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = ((size_t)0ULL);
v___x_3817_ = lean_usize_of_nat(v___x_3807_);
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3799_, v___x_3816_, v___x_3817_, v___x_3810_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
v___y_3804_ = v___x_3818_;
goto v___jp_3803_;
}
}
v___jp_3803_:
{
if (lean_obj_tag(v___y_3804_) == 0)
{
lean_object* v___x_3805_; 
lean_dec_ref(v___y_3804_);
v___x_3805_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3802_, v_args_3799_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
return v___x_3805_;
}
else
{
lean_dec(v_a_3802_);
lean_dec_ref(v_args_3799_);
return v___y_3804_;
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v_args_3799_);
v_a_3819_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3801_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3801_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
case 4:
{
lean_object* v_cases_3827_; lean_object* v_discr_3828_; lean_object* v_alts_3829_; lean_object* v___x_3830_; 
v_cases_3827_ = lean_ctor_get(v_x_3745_, 0);
lean_inc_ref(v_cases_3827_);
lean_dec_ref(v_x_3745_);
v_discr_3828_ = lean_ctor_get(v_cases_3827_, 2);
lean_inc(v_discr_3828_);
v_alts_3829_ = lean_ctor_get(v_cases_3827_, 3);
lean_inc_ref(v_alts_3829_);
lean_dec_ref(v_cases_3827_);
v___x_3830_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3828_, v_a_3746_, v_a_3747_);
lean_dec(v_discr_3828_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; size_t v_sz_3833_; size_t v___x_3834_; lean_object* v___x_3835_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3830_);
v___x_3832_ = lean_box(0);
v_sz_3833_ = lean_array_size(v_alts_3829_);
v___x_3834_ = ((size_t)0ULL);
v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3831_, v_alts_3829_, v_sz_3833_, v___x_3834_, v___x_3832_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
lean_dec_ref(v_alts_3829_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3842_ == 0)
{
lean_object* v_unused_3843_; 
v_unused_3843_ = lean_ctor_get(v___x_3835_, 0);
lean_dec(v_unused_3843_);
v___x_3837_ = v___x_3835_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_dec(v___x_3835_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3832_);
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3832_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
else
{
return v___x_3835_;
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v_alts_3829_);
v_a_3844_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3830_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3830_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3852_; lean_object* v___x_3853_; 
v_fvarId_3852_ = lean_ctor_get(v_x_3745_, 0);
lean_inc(v_fvarId_3852_);
lean_dec_ref(v_x_3745_);
v___x_3853_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3852_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; 
lean_dec_ref(v___x_3853_);
v___x_3854_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3852_, v_a_3746_, v_a_3747_);
lean_dec(v_fvarId_3852_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3855_, v_a_3746_, v_a_3747_, v_a_3751_);
return v___x_3856_;
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
v_a_3857_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3854_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3854_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
else
{
lean_dec(v_fvarId_3852_);
return v___x_3853_;
}
}
case 6:
{
lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3872_; 
v_isSharedCheck_3872_ = !lean_is_exclusive(v_x_3745_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; 
v_unused_3873_ = lean_ctor_get(v_x_3745_, 0);
lean_dec(v_unused_3873_);
v___x_3866_ = v_x_3745_;
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
else
{
lean_dec(v_x_3745_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = lean_box(0);
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3868_);
v___x_3870_ = v___x_3866_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
default: 
{
lean_object* v_decl_3874_; lean_object* v_k_3875_; 
v_decl_3874_ = lean_ctor_get(v_x_3745_, 0);
lean_inc_ref(v_decl_3874_);
v_k_3875_ = lean_ctor_get(v_x_3745_, 1);
lean_inc_ref(v_k_3875_);
lean_dec_ref(v_x_3745_);
v_decl_3754_ = v_decl_3874_;
v_k_3755_ = v_k_3875_;
v___y_3756_ = v_a_3746_;
v___y_3757_ = v_a_3747_;
v___y_3758_ = v_a_3748_;
v___y_3759_ = v_a_3749_;
v___y_3760_ = v_a_3750_;
v___y_3761_ = v_a_3751_;
goto v___jp_3753_;
}
}
v___jp_3753_:
{
lean_object* v_value_3762_; lean_object* v___x_3763_; 
v_value_3762_ = lean_ctor_get(v_decl_3754_, 4);
lean_inc_ref(v_value_3762_);
lean_dec_ref(v_decl_3754_);
v___x_3763_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3762_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_dec_ref(v___x_3763_);
v_x_3745_ = v_k_3755_;
v_a_3746_ = v___y_3756_;
v_a_3747_ = v___y_3757_;
v_a_3748_ = v___y_3758_;
v_a_3749_ = v___y_3759_;
v_a_3750_ = v___y_3760_;
v_a_3751_ = v___y_3761_;
goto _start;
}
else
{
lean_dec_ref(v_k_3755_);
return v___x_3763_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
uint8_t v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = 0;
v___x_3885_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3884_, v_var_3876_, v_a_3880_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3918_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3918_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3918_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
if (lean_obj_tag(v_a_3886_) == 1)
{
lean_object* v_val_3890_; lean_object* v_params_3891_; lean_object* v_value_3892_; lean_object* v___x_3893_; 
lean_del_object(v___x_3888_);
v_val_3890_ = lean_ctor_get(v_a_3886_, 0);
lean_inc(v_val_3890_);
lean_dec_ref(v_a_3886_);
v_params_3891_ = lean_ctor_get(v_val_3890_, 2);
lean_inc_ref(v_params_3891_);
v_value_3892_ = lean_ctor_get(v_val_3890_, 4);
lean_inc_ref(v_value_3892_);
lean_dec(v_val_3890_);
v___x_3893_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3891_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec_ref(v_params_3891_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3905_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3905_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3905_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
uint8_t v___x_3898_; 
v___x_3898_ = lean_unbox(v_a_3894_);
lean_dec(v_a_3894_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3901_; 
lean_dec_ref(v_value_3892_);
v___x_3899_ = lean_box(0);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3899_);
v___x_3901_ = v___x_3896_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
else
{
lean_object* v___x_3903_; 
lean_del_object(v___x_3896_);
lean_inc_ref(v_value_3892_);
v___x_3903_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3892_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v___x_3904_; 
lean_dec_ref(v___x_3903_);
v___x_3904_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3892_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
return v___x_3904_;
}
else
{
lean_dec_ref(v_value_3892_);
return v___x_3903_;
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v_value_3892_);
v_a_3906_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3893_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3893_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3916_; 
lean_dec(v_a_3886_);
v___x_3914_ = lean_box(0);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3914_);
v___x_3916_ = v___x_3888_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_a_3919_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3885_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3885_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_){
_start:
{
if (lean_obj_tag(v_arg_3927_) == 1)
{
lean_object* v_fvarId_3935_; lean_object* v___x_3936_; 
v_fvarId_3935_ = lean_ctor_get(v_arg_3927_, 0);
v___x_3936_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3935_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
return v___x_3936_;
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = lean_box(0);
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
return v___x_3938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_arg_3939_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_3948_, lean_object* v_i_3949_, lean_object* v_stop_3950_, lean_object* v_b_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
size_t v_i_boxed_3959_; size_t v_stop_boxed_3960_; lean_object* v_res_3961_; 
v_i_boxed_3959_ = lean_unbox_usize(v_i_3949_);
lean_dec(v_i_3949_);
v_stop_boxed_3960_ = lean_unbox_usize(v_stop_3950_);
lean_dec(v_stop_3950_);
v_res_3961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_3948_, v_i_boxed_3959_, v_stop_boxed_3960_, v_b_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec_ref(v_as_3948_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_3962_, lean_object* v_args_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_3962_, v_args_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
lean_dec(v_var_3972_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_3981_, lean_object* v_as_3982_, lean_object* v_sz_3983_, lean_object* v_i_3984_, lean_object* v_b_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
size_t v_sz_boxed_3993_; size_t v_i_boxed_3994_; lean_object* v_res_3995_; 
v_sz_boxed_3993_ = lean_unbox_usize(v_sz_3983_);
lean_dec(v_sz_3983_);
v_i_boxed_3994_ = lean_unbox_usize(v_i_3984_);
lean_dec(v_i_3984_);
v_res_3995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3981_, v_as_3982_, v_sz_boxed_3993_, v_i_boxed_3994_, v_b_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec_ref(v_as_3982_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4014_, lean_object* v_R_4015_, lean_object* v_a_4016_, lean_object* v_b_4017_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4016_, v_b_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4019_, size_t v_i_4020_, lean_object* v_bs_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4019_, v_i_4020_, v_bs_4021_, v___y_4022_, v___y_4023_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4030_, lean_object* v_i_4031_, lean_object* v_bs_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
size_t v_sz_boxed_4040_; size_t v_i_boxed_4041_; lean_object* v_res_4042_; 
v_sz_boxed_4040_ = lean_unbox_usize(v_sz_4030_);
lean_dec(v_sz_4030_);
v_i_boxed_4041_ = lean_unbox_usize(v_i_4031_);
lean_dec(v_i_4031_);
v_res_4042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4040_, v_i_boxed_4041_, v_bs_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4043_, size_t v_i_4044_, size_t v_stop_4045_, lean_object* v_b_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4043_, v_i_4044_, v_stop_4045_, v_b_4046_, v___y_4047_, v___y_4048_, v___y_4052_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4055_, lean_object* v_i_4056_, lean_object* v_stop_4057_, lean_object* v_b_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
size_t v_i_boxed_4066_; size_t v_stop_boxed_4067_; lean_object* v_res_4068_; 
v_i_boxed_4066_ = lean_unbox_usize(v_i_4056_);
lean_dec(v_i_4056_);
v_stop_boxed_4067_ = lean_unbox_usize(v_stop_4057_);
lean_dec(v_stop_4057_);
v_res_4068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4055_, v_i_boxed_4066_, v_stop_boxed_4067_, v_b_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec_ref(v_as_4055_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4069_, size_t v_i_4070_, size_t v_stop_4071_, lean_object* v_b_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4069_, v_i_4070_, v_stop_4071_, v_b_4072_, v___y_4073_, v___y_4074_, v___y_4078_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4081_, lean_object* v_i_4082_, lean_object* v_stop_4083_, lean_object* v_b_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
size_t v_i_boxed_4092_; size_t v_stop_boxed_4093_; lean_object* v_res_4094_; 
v_i_boxed_4092_ = lean_unbox_usize(v_i_4082_);
lean_dec(v_i_4082_);
v_stop_boxed_4093_ = lean_unbox_usize(v_stop_4083_);
lean_dec(v_stop_4083_);
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4081_, v_i_boxed_4092_, v_stop_boxed_4093_, v_b_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec_ref(v_as_4081_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v_cls_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_options_4101_; uint8_t v_hasTrace_4102_; 
v_options_4101_ = lean_ctor_get(v___y_4099_, 2);
v_hasTrace_4102_ = lean_ctor_get_uint8(v_options_4101_, sizeof(void*)*1);
if (v_hasTrace_4102_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
lean_dec(v_cls_4098_);
v___x_4103_ = lean_box(v_hasTrace_4102_);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
else
{
lean_object* v_inheritedTraceOptions_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v_inheritedTraceOptions_4105_ = lean_ctor_get(v___y_4099_, 13);
v___x_4106_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1));
v___x_4107_ = l_Lean_Name_append(v___x_4106_, v_cls_4098_);
v___x_4108_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4105_, v_options_4101_, v___x_4107_);
lean_dec(v___x_4107_);
v___x_4109_ = lean_box(v___x_4108_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
return v___x_4110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v_cls_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_cls_4111_, v___y_4112_);
lean_dec_ref(v___y_4112_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v_cls_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_cls_4115_, v___y_4120_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v_cls_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v_cls_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4132_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4133_ = lean_unsigned_to_nat(32u);
v___x_4134_ = lean_mk_empty_array_with_capacity(v___x_4133_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4136_ = ((size_t)5ULL);
v___x_4137_ = lean_unsigned_to_nat(0u);
v___x_4138_ = lean_unsigned_to_nat(32u);
v___x_4139_ = lean_mk_empty_array_with_capacity(v___x_4138_);
v___x_4140_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0);
v___x_4141_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
lean_ctor_set(v___x_4141_, 1, v___x_4139_);
lean_ctor_set(v___x_4141_, 2, v___x_4137_);
lean_ctor_set(v___x_4141_, 3, v___x_4137_);
lean_ctor_set_usize(v___x_4141_, 4, v___x_4136_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; lean_object* v_traceState_4145_; lean_object* v_traces_4146_; lean_object* v___x_4147_; lean_object* v_traceState_4148_; lean_object* v_env_4149_; lean_object* v_nextMacroScope_4150_; lean_object* v_ngen_4151_; lean_object* v_auxDeclNGen_4152_; lean_object* v_cache_4153_; lean_object* v_messages_4154_; lean_object* v_infoState_4155_; lean_object* v_snapshotTasks_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4175_; 
v___x_4144_ = lean_st_ref_get(v___y_4142_);
v_traceState_4145_ = lean_ctor_get(v___x_4144_, 4);
lean_inc_ref(v_traceState_4145_);
lean_dec(v___x_4144_);
v_traces_4146_ = lean_ctor_get(v_traceState_4145_, 0);
lean_inc_ref(v_traces_4146_);
lean_dec_ref(v_traceState_4145_);
v___x_4147_ = lean_st_ref_take(v___y_4142_);
v_traceState_4148_ = lean_ctor_get(v___x_4147_, 4);
v_env_4149_ = lean_ctor_get(v___x_4147_, 0);
v_nextMacroScope_4150_ = lean_ctor_get(v___x_4147_, 1);
v_ngen_4151_ = lean_ctor_get(v___x_4147_, 2);
v_auxDeclNGen_4152_ = lean_ctor_get(v___x_4147_, 3);
v_cache_4153_ = lean_ctor_get(v___x_4147_, 5);
v_messages_4154_ = lean_ctor_get(v___x_4147_, 6);
v_infoState_4155_ = lean_ctor_get(v___x_4147_, 7);
v_snapshotTasks_4156_ = lean_ctor_get(v___x_4147_, 8);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4158_ = v___x_4147_;
v_isShared_4159_ = v_isSharedCheck_4175_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_snapshotTasks_4156_);
lean_inc(v_infoState_4155_);
lean_inc(v_messages_4154_);
lean_inc(v_cache_4153_);
lean_inc(v_traceState_4148_);
lean_inc(v_auxDeclNGen_4152_);
lean_inc(v_ngen_4151_);
lean_inc(v_nextMacroScope_4150_);
lean_inc(v_env_4149_);
lean_dec(v___x_4147_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4175_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
uint64_t v_tid_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4173_; 
v_tid_4160_ = lean_ctor_get_uint64(v_traceState_4148_, sizeof(void*)*1);
v_isSharedCheck_4173_ = !lean_is_exclusive(v_traceState_4148_);
if (v_isSharedCheck_4173_ == 0)
{
lean_object* v_unused_4174_; 
v_unused_4174_ = lean_ctor_get(v_traceState_4148_, 0);
lean_dec(v_unused_4174_);
v___x_4162_ = v_traceState_4148_;
v_isShared_4163_ = v_isSharedCheck_4173_;
goto v_resetjp_4161_;
}
else
{
lean_dec(v_traceState_4148_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4173_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4164_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4164_);
v___x_4166_ = v___x_4162_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4164_);
lean_ctor_set_uint64(v_reuseFailAlloc_4172_, sizeof(void*)*1, v_tid_4160_);
v___x_4166_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4168_; 
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 4, v___x_4166_);
v___x_4168_ = v___x_4158_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_env_4149_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v_nextMacroScope_4150_);
lean_ctor_set(v_reuseFailAlloc_4171_, 2, v_ngen_4151_);
lean_ctor_set(v_reuseFailAlloc_4171_, 3, v_auxDeclNGen_4152_);
lean_ctor_set(v_reuseFailAlloc_4171_, 4, v___x_4166_);
lean_ctor_set(v_reuseFailAlloc_4171_, 5, v_cache_4153_);
lean_ctor_set(v_reuseFailAlloc_4171_, 6, v_messages_4154_);
lean_ctor_set(v_reuseFailAlloc_4171_, 7, v_infoState_4155_);
lean_ctor_set(v_reuseFailAlloc_4171_, 8, v_snapshotTasks_4156_);
v___x_4168_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = lean_st_ref_set(v___y_4142_, v___x_4168_);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v_traces_4146_);
return v___x_4170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___boxed(lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v___y_4176_);
lean_dec(v___y_4176_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v___y_4184_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4194_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_opts_4195_, lean_object* v_opt_4196_){
_start:
{
lean_object* v_name_4197_; lean_object* v_defValue_4198_; lean_object* v_map_4199_; lean_object* v___x_4200_; 
v_name_4197_ = lean_ctor_get(v_opt_4196_, 0);
v_defValue_4198_ = lean_ctor_get(v_opt_4196_, 1);
v_map_4199_ = lean_ctor_get(v_opts_4195_, 0);
v___x_4200_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4199_, v_name_4197_);
if (lean_obj_tag(v___x_4200_) == 0)
{
uint8_t v___x_4201_; 
v___x_4201_ = lean_unbox(v_defValue_4198_);
return v___x_4201_;
}
else
{
lean_object* v_val_4202_; 
v_val_4202_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_val_4202_);
lean_dec_ref(v___x_4200_);
if (lean_obj_tag(v_val_4202_) == 1)
{
uint8_t v_v_4203_; 
v_v_4203_ = lean_ctor_get_uint8(v_val_4202_, 0);
lean_dec_ref(v_val_4202_);
return v_v_4203_;
}
else
{
uint8_t v___x_4204_; 
lean_dec(v_val_4202_);
v___x_4204_ = lean_unbox(v_defValue_4198_);
return v___x_4204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_opts_4205_, lean_object* v_opt_4206_){
_start:
{
uint8_t v_res_4207_; lean_object* v_r_4208_; 
v_res_4207_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_opts_4205_, v_opt_4206_);
lean_dec_ref(v_opt_4206_);
lean_dec_ref(v_opts_4205_);
v_r_4208_ = lean_box(v_res_4207_);
return v_r_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(size_t v_sz_4209_, size_t v_i_4210_, lean_object* v_bs_4211_){
_start:
{
uint8_t v___x_4212_; 
v___x_4212_ = lean_usize_dec_lt(v_i_4210_, v_sz_4209_);
if (v___x_4212_ == 0)
{
return v_bs_4211_;
}
else
{
lean_object* v_v_4213_; lean_object* v_msg_4214_; lean_object* v___x_4215_; lean_object* v_bs_x27_4216_; size_t v___x_4217_; size_t v___x_4218_; lean_object* v___x_4219_; 
v_v_4213_ = lean_array_uget_borrowed(v_bs_4211_, v_i_4210_);
v_msg_4214_ = lean_ctor_get(v_v_4213_, 1);
lean_inc_ref(v_msg_4214_);
v___x_4215_ = lean_unsigned_to_nat(0u);
v_bs_x27_4216_ = lean_array_uset(v_bs_4211_, v_i_4210_, v___x_4215_);
v___x_4217_ = ((size_t)1ULL);
v___x_4218_ = lean_usize_add(v_i_4210_, v___x_4217_);
v___x_4219_ = lean_array_uset(v_bs_x27_4216_, v_i_4210_, v_msg_4214_);
v_i_4210_ = v___x_4218_;
v_bs_4211_ = v___x_4219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_4221_, lean_object* v_i_4222_, lean_object* v_bs_4223_){
_start:
{
size_t v_sz_boxed_4224_; size_t v_i_boxed_4225_; lean_object* v_res_4226_; 
v_sz_boxed_4224_ = lean_unbox_usize(v_sz_4221_);
lean_dec(v_sz_4221_);
v_i_boxed_4225_ = lean_unbox_usize(v_i_4222_);
lean_dec(v_i_4222_);
v_res_4226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(v_sz_boxed_4224_, v_i_boxed_4225_, v_bs_4223_);
return v_res_4226_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4227_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0);
v___x_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
return v___x_4229_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4230_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1);
v___x_4231_ = lean_unsigned_to_nat(0u);
v___x_4232_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
lean_ctor_set(v___x_4232_, 2, v___x_4231_);
lean_ctor_set(v___x_4232_, 3, v___x_4230_);
lean_ctor_set(v___x_4232_, 4, v___x_4230_);
lean_ctor_set(v___x_4232_, 5, v___x_4230_);
lean_ctor_set(v___x_4232_, 6, v___x_4230_);
lean_ctor_set(v___x_4232_, 7, v___x_4230_);
lean_ctor_set(v___x_4232_, 8, v___x_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(lean_object* v_oldTraces_4233_, lean_object* v_data_4234_, lean_object* v_ref_4235_, lean_object* v_msg_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_options_4242_; lean_object* v___x_4243_; lean_object* v_traceState_4244_; lean_object* v_traces_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_options_4242_ = lean_ctor_get(v___y_4239_, 2);
v___x_4243_ = lean_st_ref_get(v___y_4240_);
v_traceState_4244_ = lean_ctor_get(v___x_4243_, 4);
lean_inc_ref(v_traceState_4244_);
lean_dec(v___x_4243_);
v_traces_4245_ = lean_ctor_get(v_traceState_4244_, 0);
lean_inc_ref(v_traces_4245_);
lean_dec_ref(v_traceState_4244_);
v___x_4246_ = lean_st_ref_get(v___y_4240_);
v___x_4247_ = lean_st_ref_get(v___y_4238_);
v___x_4248_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4237_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4305_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4251_ = v___x_4248_;
v_isShared_4252_ = v_isSharedCheck_4305_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4305_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v_env_4253_; lean_object* v_lctx_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4303_; 
v_env_4253_ = lean_ctor_get(v___x_4246_, 0);
lean_inc_ref(v_env_4253_);
lean_dec(v___x_4246_);
v_lctx_4254_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4303_ == 0)
{
lean_object* v_unused_4304_; 
v_unused_4304_ = lean_ctor_get(v___x_4247_, 1);
lean_dec(v_unused_4304_);
v___x_4256_ = v___x_4247_;
v_isShared_4257_ = v_isSharedCheck_4303_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_lctx_4254_);
lean_dec(v___x_4247_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4303_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v_traceState_4260_; lean_object* v_env_4261_; lean_object* v_nextMacroScope_4262_; lean_object* v_ngen_4263_; lean_object* v_auxDeclNGen_4264_; lean_object* v_cache_4265_; lean_object* v_messages_4266_; lean_object* v_infoState_4267_; lean_object* v_snapshotTasks_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4302_; 
v___x_4258_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2);
v___x_4259_ = lean_st_ref_take(v___y_4240_);
v_traceState_4260_ = lean_ctor_get(v___x_4259_, 4);
v_env_4261_ = lean_ctor_get(v___x_4259_, 0);
v_nextMacroScope_4262_ = lean_ctor_get(v___x_4259_, 1);
v_ngen_4263_ = lean_ctor_get(v___x_4259_, 2);
v_auxDeclNGen_4264_ = lean_ctor_get(v___x_4259_, 3);
v_cache_4265_ = lean_ctor_get(v___x_4259_, 5);
v_messages_4266_ = lean_ctor_get(v___x_4259_, 6);
v_infoState_4267_ = lean_ctor_get(v___x_4259_, 7);
v_snapshotTasks_4268_ = lean_ctor_get(v___x_4259_, 8);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4270_ = v___x_4259_;
v_isShared_4271_ = v_isSharedCheck_4302_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_snapshotTasks_4268_);
lean_inc(v_infoState_4267_);
lean_inc(v_messages_4266_);
lean_inc(v_cache_4265_);
lean_inc(v_traceState_4260_);
lean_inc(v_auxDeclNGen_4264_);
lean_inc(v_ngen_4263_);
lean_inc(v_nextMacroScope_4262_);
lean_inc(v_env_4261_);
lean_dec(v___x_4259_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4302_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
uint64_t v_tid_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4300_; 
v_tid_4272_ = lean_ctor_get_uint64(v_traceState_4260_, sizeof(void*)*1);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_traceState_4260_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; 
v_unused_4301_ = lean_ctor_get(v_traceState_4260_, 0);
lean_dec(v_unused_4301_);
v___x_4274_ = v_traceState_4260_;
v_isShared_4275_ = v_isSharedCheck_4300_;
goto v_resetjp_4273_;
}
else
{
lean_dec(v_traceState_4260_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4300_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4276_; size_t v_sz_4277_; size_t v___x_4278_; lean_object* v___x_4279_; lean_object* v_msg_4280_; uint8_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4285_; 
v___x_4276_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4245_);
lean_dec_ref(v_traces_4245_);
v_sz_4277_ = lean_array_size(v___x_4276_);
v___x_4278_ = ((size_t)0ULL);
v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(v_sz_4277_, v___x_4278_, v___x_4276_);
v_msg_4280_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4280_, 0, v_data_4234_);
lean_ctor_set(v_msg_4280_, 1, v_msg_4236_);
lean_ctor_set(v_msg_4280_, 2, v___x_4279_);
v___x_4281_ = lean_unbox(v_a_4249_);
lean_dec(v_a_4249_);
v___x_4282_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4254_, v___x_4281_);
lean_dec_ref(v_lctx_4254_);
lean_inc_ref(v_options_4242_);
v___x_4283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4283_, 0, v_env_4253_);
lean_ctor_set(v___x_4283_, 1, v___x_4258_);
lean_ctor_set(v___x_4283_, 2, v___x_4282_);
lean_ctor_set(v___x_4283_, 3, v_options_4242_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set_tag(v___x_4256_, 3);
lean_ctor_set(v___x_4256_, 1, v_msg_4280_);
lean_ctor_set(v___x_4256_, 0, v___x_4283_);
v___x_4285_ = v___x_4256_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4283_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_msg_4280_);
v___x_4285_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4289_; 
v___x_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4286_, 0, v_ref_4235_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4233_, v___x_4286_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4287_);
v___x_4289_ = v___x_4274_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4287_);
lean_ctor_set_uint64(v_reuseFailAlloc_4298_, sizeof(void*)*1, v_tid_4272_);
v___x_4289_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
lean_object* v___x_4291_; 
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 4, v___x_4289_);
v___x_4291_ = v___x_4270_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_env_4261_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v_nextMacroScope_4262_);
lean_ctor_set(v_reuseFailAlloc_4297_, 2, v_ngen_4263_);
lean_ctor_set(v_reuseFailAlloc_4297_, 3, v_auxDeclNGen_4264_);
lean_ctor_set(v_reuseFailAlloc_4297_, 4, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4297_, 5, v_cache_4265_);
lean_ctor_set(v_reuseFailAlloc_4297_, 6, v_messages_4266_);
lean_ctor_set(v_reuseFailAlloc_4297_, 7, v_infoState_4267_);
lean_ctor_set(v_reuseFailAlloc_4297_, 8, v_snapshotTasks_4268_);
v___x_4291_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4292_ = lean_st_ref_set(v___y_4240_, v___x_4291_);
v___x_4293_ = lean_box(0);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4293_);
v___x_4295_ = v___x_4251_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec(v___x_4247_);
lean_dec(v___x_4246_);
lean_dec_ref(v_traces_4245_);
lean_dec_ref(v_msg_4236_);
lean_dec(v_ref_4235_);
lean_dec_ref(v_data_4234_);
lean_dec_ref(v_oldTraces_4233_);
v_a_4306_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4248_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4248_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_4314_, lean_object* v_data_4315_, lean_object* v_ref_4316_, lean_object* v_msg_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(v_oldTraces_4314_, v_data_4315_, v_ref_4316_, v_msg_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
return v_res_4323_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(lean_object* v_e_4324_){
_start:
{
if (lean_obj_tag(v_e_4324_) == 0)
{
uint8_t v___x_4325_; 
v___x_4325_ = 2;
return v___x_4325_;
}
else
{
uint8_t v___x_4326_; 
v___x_4326_ = 0;
return v___x_4326_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3___boxed(lean_object* v_e_4327_){
_start:
{
uint8_t v_res_4328_; lean_object* v_r_4329_; 
v_res_4328_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(v_e_4327_);
lean_dec_ref(v_e_4327_);
v_r_4329_ = lean_box(v_res_4328_);
return v_r_4329_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(lean_object* v_x_4330_){
_start:
{
if (lean_obj_tag(v_x_4330_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
v_a_4332_ = lean_ctor_get(v_x_4330_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_x_4330_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v_x_4330_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v_x_4330_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
lean_ctor_set_tag(v___x_4334_, 1);
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
v_a_4340_ = lean_ctor_get(v_x_4330_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_x_4330_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v_x_4330_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v_x_4330_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set_tag(v___x_4342_, 0);
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg___boxed(lean_object* v_x_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_x_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(lean_object* v_opts_4351_, lean_object* v_opt_4352_){
_start:
{
lean_object* v_name_4353_; lean_object* v_defValue_4354_; lean_object* v_map_4355_; lean_object* v___x_4356_; 
v_name_4353_ = lean_ctor_get(v_opt_4352_, 0);
v_defValue_4354_ = lean_ctor_get(v_opt_4352_, 1);
v_map_4355_ = lean_ctor_get(v_opts_4351_, 0);
v___x_4356_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4355_, v_name_4353_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_inc(v_defValue_4354_);
return v_defValue_4354_;
}
else
{
lean_object* v_val_4357_; 
v_val_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_val_4357_);
lean_dec_ref(v___x_4356_);
if (lean_obj_tag(v_val_4357_) == 3)
{
lean_object* v_v_4358_; 
v_v_4358_ = lean_ctor_get(v_val_4357_, 0);
lean_inc(v_v_4358_);
lean_dec_ref(v_val_4357_);
return v_v_4358_;
}
else
{
lean_dec(v_val_4357_);
lean_inc(v_defValue_4354_);
return v_defValue_4354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6___boxed(lean_object* v_opts_4359_, lean_object* v_opt_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(v_opts_4359_, v_opt_4360_);
lean_dec_ref(v_opt_4360_);
lean_dec_ref(v_opts_4359_);
return v_res_4361_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__0));
v___x_4363_ = l_Lean_stringToMessageData(v___x_4362_);
return v___x_4363_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4364_; double v___x_4365_; 
v___x_4364_ = lean_unsigned_to_nat(0u);
v___x_4365_ = lean_float_of_nat(v___x_4364_);
return v___x_4365_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2));
v___x_4368_ = l_Lean_stringToMessageData(v___x_4367_);
return v___x_4368_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4(void){
_start:
{
lean_object* v___x_4369_; double v___x_4370_; 
v___x_4369_ = lean_unsigned_to_nat(1000u);
v___x_4370_ = lean_float_of_nat(v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_cls_4371_, uint8_t v_collapsed_4372_, lean_object* v_tag_4373_, lean_object* v_opts_4374_, uint8_t v_clsEnabled_4375_, lean_object* v_oldTraces_4376_, lean_object* v_msg_4377_, lean_object* v_resStartStop_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v_fst_4386_; lean_object* v_snd_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4477_; 
v_fst_4386_ = lean_ctor_get(v_resStartStop_4378_, 0);
v_snd_4387_ = lean_ctor_get(v_resStartStop_4378_, 1);
v_isSharedCheck_4477_ = !lean_is_exclusive(v_resStartStop_4378_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4389_ = v_resStartStop_4378_;
v_isShared_4390_ = v_isSharedCheck_4477_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_snd_4387_);
lean_inc(v_fst_4386_);
lean_dec(v_resStartStop_4378_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4477_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v_data_4394_; lean_object* v_fst_4397_; lean_object* v_snd_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4476_; 
v_fst_4397_ = lean_ctor_get(v_snd_4387_, 0);
v_snd_4398_ = lean_ctor_get(v_snd_4387_, 1);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_snd_4387_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4400_ = v_snd_4387_;
v_isShared_4401_ = v_isSharedCheck_4476_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_snd_4398_);
lean_inc(v_fst_4397_);
lean_dec(v_snd_4387_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4476_;
goto v_resetjp_4399_;
}
v___jp_4391_:
{
lean_object* v___x_4395_; 
v___x_4395_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(v_oldTraces_4376_, v_data_4394_, v___y_4392_, v___y_4393_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v___x_4396_; 
lean_dec_ref(v___x_4395_);
v___x_4396_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_fst_4386_);
return v___x_4396_;
}
else
{
lean_dec(v_fst_4386_);
return v___x_4395_;
}
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; uint8_t v___x_4403_; lean_object* v___y_4405_; lean_object* v_a_4406_; uint8_t v___y_4430_; double v___y_4461_; 
v___x_4402_ = l_Lean_trace_profiler;
v___x_4403_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_opts_4374_, v___x_4402_);
if (v___x_4403_ == 0)
{
v___y_4430_ = v___x_4403_;
goto v___jp_4429_;
}
else
{
lean_object* v___x_4466_; uint8_t v___x_4467_; 
v___x_4466_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4467_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_opts_4374_, v___x_4466_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; double v___x_4470_; double v___x_4471_; double v___x_4472_; 
v___x_4468_ = l_Lean_trace_profiler_threshold;
v___x_4469_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(v_opts_4374_, v___x_4468_);
v___x_4470_ = lean_float_of_nat(v___x_4469_);
v___x_4471_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4);
v___x_4472_ = lean_float_div(v___x_4470_, v___x_4471_);
v___y_4461_ = v___x_4472_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; double v___x_4475_; 
v___x_4473_ = l_Lean_trace_profiler_threshold;
v___x_4474_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(v_opts_4374_, v___x_4473_);
v___x_4475_ = lean_float_of_nat(v___x_4474_);
v___y_4461_ = v___x_4475_;
goto v___jp_4460_;
}
}
v___jp_4404_:
{
uint8_t v_result_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4412_; 
v_result_4407_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(v_fst_4386_);
v___x_4408_ = l_Lean_TraceResult_toEmoji(v_result_4407_);
v___x_4409_ = l_Lean_stringToMessageData(v___x_4408_);
v___x_4410_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0);
if (v_isShared_4401_ == 0)
{
lean_ctor_set_tag(v___x_4400_, 7);
lean_ctor_set(v___x_4400_, 1, v___x_4410_);
lean_ctor_set(v___x_4400_, 0, v___x_4409_);
v___x_4412_ = v___x_4400_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4409_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v___x_4410_);
v___x_4412_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
lean_object* v_m_4414_; 
if (v_isShared_4390_ == 0)
{
lean_ctor_set_tag(v___x_4389_, 7);
lean_ctor_set(v___x_4389_, 1, v_a_4406_);
lean_ctor_set(v___x_4389_, 0, v___x_4412_);
v_m_4414_ = v___x_4389_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v_a_4406_);
v_m_4414_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; double v___x_4417_; lean_object* v_data_4418_; 
v___x_4415_ = lean_box(v_result_4407_);
v___x_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
v___x_4417_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1);
lean_inc_ref(v_tag_4373_);
lean_inc_ref(v___x_4416_);
lean_inc(v_cls_4371_);
v_data_4418_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4418_, 0, v_cls_4371_);
lean_ctor_set(v_data_4418_, 1, v___x_4416_);
lean_ctor_set(v_data_4418_, 2, v_tag_4373_);
lean_ctor_set_float(v_data_4418_, sizeof(void*)*3, v___x_4417_);
lean_ctor_set_float(v_data_4418_, sizeof(void*)*3 + 8, v___x_4417_);
lean_ctor_set_uint8(v_data_4418_, sizeof(void*)*3 + 16, v_collapsed_4372_);
if (v___x_4403_ == 0)
{
lean_dec_ref(v___x_4416_);
lean_dec(v_snd_4398_);
lean_dec(v_fst_4397_);
lean_dec_ref(v_tag_4373_);
lean_dec(v_cls_4371_);
v___y_4392_ = v___y_4405_;
v___y_4393_ = v_m_4414_;
v_data_4394_ = v_data_4418_;
goto v___jp_4391_;
}
else
{
lean_object* v_data_4419_; double v___x_4420_; double v___x_4421_; 
lean_dec_ref(v_data_4418_);
v_data_4419_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4419_, 0, v_cls_4371_);
lean_ctor_set(v_data_4419_, 1, v___x_4416_);
lean_ctor_set(v_data_4419_, 2, v_tag_4373_);
v___x_4420_ = lean_unbox_float(v_fst_4397_);
lean_dec(v_fst_4397_);
lean_ctor_set_float(v_data_4419_, sizeof(void*)*3, v___x_4420_);
v___x_4421_ = lean_unbox_float(v_snd_4398_);
lean_dec(v_snd_4398_);
lean_ctor_set_float(v_data_4419_, sizeof(void*)*3 + 8, v___x_4421_);
lean_ctor_set_uint8(v_data_4419_, sizeof(void*)*3 + 16, v_collapsed_4372_);
v___y_4392_ = v___y_4405_;
v___y_4393_ = v_m_4414_;
v_data_4394_ = v_data_4419_;
goto v___jp_4391_;
}
}
}
}
v___jp_4424_:
{
lean_object* v_ref_4425_; lean_object* v___x_4426_; 
v_ref_4425_ = lean_ctor_get(v___y_4383_, 5);
lean_inc(v___y_4384_);
lean_inc_ref(v___y_4383_);
lean_inc(v___y_4382_);
lean_inc_ref(v___y_4381_);
lean_inc(v_fst_4386_);
v___x_4426_ = lean_apply_8(v_msg_4377_, v_fst_4386_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, lean_box(0));
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref(v___x_4426_);
lean_inc(v_ref_4425_);
v___y_4405_ = v_ref_4425_;
v_a_4406_ = v_a_4427_;
goto v___jp_4404_;
}
else
{
lean_object* v___x_4428_; 
lean_dec_ref(v___x_4426_);
v___x_4428_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3);
lean_inc(v_ref_4425_);
v___y_4405_ = v_ref_4425_;
v_a_4406_ = v___x_4428_;
goto v___jp_4404_;
}
}
v___jp_4429_:
{
if (v_clsEnabled_4375_ == 0)
{
if (v___y_4430_ == 0)
{
lean_object* v___x_4431_; lean_object* v_traceState_4432_; lean_object* v_env_4433_; lean_object* v_nextMacroScope_4434_; lean_object* v_ngen_4435_; lean_object* v_auxDeclNGen_4436_; lean_object* v_cache_4437_; lean_object* v_messages_4438_; lean_object* v_infoState_4439_; lean_object* v_snapshotTasks_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4459_; 
lean_del_object(v___x_4400_);
lean_dec(v_snd_4398_);
lean_dec(v_fst_4397_);
lean_del_object(v___x_4389_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec_ref(v_msg_4377_);
lean_dec_ref(v_tag_4373_);
lean_dec(v_cls_4371_);
v___x_4431_ = lean_st_ref_take(v___y_4384_);
v_traceState_4432_ = lean_ctor_get(v___x_4431_, 4);
v_env_4433_ = lean_ctor_get(v___x_4431_, 0);
v_nextMacroScope_4434_ = lean_ctor_get(v___x_4431_, 1);
v_ngen_4435_ = lean_ctor_get(v___x_4431_, 2);
v_auxDeclNGen_4436_ = lean_ctor_get(v___x_4431_, 3);
v_cache_4437_ = lean_ctor_get(v___x_4431_, 5);
v_messages_4438_ = lean_ctor_get(v___x_4431_, 6);
v_infoState_4439_ = lean_ctor_get(v___x_4431_, 7);
v_snapshotTasks_4440_ = lean_ctor_get(v___x_4431_, 8);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4442_ = v___x_4431_;
v_isShared_4443_ = v_isSharedCheck_4459_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_snapshotTasks_4440_);
lean_inc(v_infoState_4439_);
lean_inc(v_messages_4438_);
lean_inc(v_cache_4437_);
lean_inc(v_traceState_4432_);
lean_inc(v_auxDeclNGen_4436_);
lean_inc(v_ngen_4435_);
lean_inc(v_nextMacroScope_4434_);
lean_inc(v_env_4433_);
lean_dec(v___x_4431_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4459_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
uint64_t v_tid_4444_; lean_object* v_traces_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4458_; 
v_tid_4444_ = lean_ctor_get_uint64(v_traceState_4432_, sizeof(void*)*1);
v_traces_4445_ = lean_ctor_get(v_traceState_4432_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_traceState_4432_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4447_ = v_traceState_4432_;
v_isShared_4448_ = v_isSharedCheck_4458_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_traces_4445_);
lean_dec(v_traceState_4432_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4458_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4449_; lean_object* v___x_4451_; 
v___x_4449_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4376_, v_traces_4445_);
lean_dec_ref(v_traces_4445_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 0, v___x_4449_);
v___x_4451_ = v___x_4447_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4449_);
lean_ctor_set_uint64(v_reuseFailAlloc_4457_, sizeof(void*)*1, v_tid_4444_);
v___x_4451_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
lean_object* v___x_4453_; 
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 4, v___x_4451_);
v___x_4453_ = v___x_4442_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_env_4433_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_nextMacroScope_4434_);
lean_ctor_set(v_reuseFailAlloc_4456_, 2, v_ngen_4435_);
lean_ctor_set(v_reuseFailAlloc_4456_, 3, v_auxDeclNGen_4436_);
lean_ctor_set(v_reuseFailAlloc_4456_, 4, v___x_4451_);
lean_ctor_set(v_reuseFailAlloc_4456_, 5, v_cache_4437_);
lean_ctor_set(v_reuseFailAlloc_4456_, 6, v_messages_4438_);
lean_ctor_set(v_reuseFailAlloc_4456_, 7, v_infoState_4439_);
lean_ctor_set(v_reuseFailAlloc_4456_, 8, v_snapshotTasks_4440_);
v___x_4453_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4454_ = lean_st_ref_set(v___y_4384_, v___x_4453_);
lean_dec(v___y_4384_);
v___x_4455_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_fst_4386_);
return v___x_4455_;
}
}
}
}
}
else
{
goto v___jp_4424_;
}
}
else
{
goto v___jp_4424_;
}
}
v___jp_4460_:
{
double v___x_4462_; double v___x_4463_; double v___x_4464_; uint8_t v___x_4465_; 
v___x_4462_ = lean_unbox_float(v_snd_4398_);
v___x_4463_ = lean_unbox_float(v_fst_4397_);
v___x_4464_ = lean_float_sub(v___x_4462_, v___x_4463_);
v___x_4465_ = lean_float_decLt(v___y_4461_, v___x_4464_);
v___y_4430_ = v___x_4465_;
goto v___jp_4429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_cls_4478_, lean_object* v_collapsed_4479_, lean_object* v_tag_4480_, lean_object* v_opts_4481_, lean_object* v_clsEnabled_4482_, lean_object* v_oldTraces_4483_, lean_object* v_msg_4484_, lean_object* v_resStartStop_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
uint8_t v_collapsed_boxed_4493_; uint8_t v_clsEnabled_boxed_4494_; lean_object* v_res_4495_; 
v_collapsed_boxed_4493_ = lean_unbox(v_collapsed_4479_);
v_clsEnabled_boxed_4494_ = lean_unbox(v_clsEnabled_4482_);
v_res_4495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_cls_4478_, v_collapsed_boxed_4493_, v_tag_4480_, v_opts_4481_, v_clsEnabled_boxed_4494_, v_oldTraces_4483_, v_msg_4484_, v_resStartStop_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec_ref(v_opts_4481_);
return v_res_4495_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0));
v___x_4498_ = l_Lean_stringToMessageData(v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0(lean_object* v_name_4499_, lean_object* v_x_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4508_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1);
v___x_4509_ = l_Lean_MessageData_ofName(v_name_4499_);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___boxed(lean_object* v_name_4512_, lean_object* v_x_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0(v_name_4512_, v_x_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec_ref(v_x_4513_);
return v_res_4521_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4525_; double v___x_4526_; 
v___x_4525_ = lean_unsigned_to_nat(1000000000u);
v___x_4526_ = lean_float_of_nat(v___x_4525_);
return v___x_4526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(lean_object* v_upperBound_4532_, lean_object* v___x_4533_, lean_object* v_a_4534_, lean_object* v_b_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_a_4544_; uint8_t v___x_4548_; 
v___x_4548_ = lean_nat_dec_lt(v_a_4534_, v_upperBound_4532_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; 
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v_b_4535_);
return v___x_4549_;
}
else
{
lean_object* v___x_4550_; lean_object* v_toSignature_4551_; lean_object* v_value_4552_; lean_object* v_name_4553_; lean_object* v_params_4554_; uint8_t v_safe_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
lean_dec_ref(v_b_4535_);
v___x_4550_ = lean_array_fget_borrowed(v___x_4533_, v_a_4534_);
v_toSignature_4551_ = lean_ctor_get(v___x_4550_, 0);
v_value_4552_ = lean_ctor_get(v___x_4550_, 1);
v_name_4553_ = lean_ctor_get(v_toSignature_4551_, 0);
v_params_4554_ = lean_ctor_get(v_toSignature_4551_, 3);
v_safe_4555_ = lean_ctor_get_uint8(v_toSignature_4551_, sizeof(void*)*4);
v___x_4556_ = lean_box(0);
v___x_4557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0));
if (v_safe_4555_ == 0)
{
v_a_4544_ = v___x_4557_;
goto v___jp_4543_;
}
else
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4534_, v___y_4537_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___y_4561_; lean_object* v_decls_4591_; lean_object* v___f_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___y_4597_; uint8_t v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v_a_4603_; lean_object* v___y_4616_; uint8_t v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v_a_4622_; uint8_t v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4712_; uint8_t v___x_4721_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref(v___x_4558_);
v_decls_4591_ = lean_ctor_get(v___y_4536_, 0);
lean_inc(v_name_4553_);
v___f_4592_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4592_, 0, v_name_4553_);
v___x_4593_ = lean_unsigned_to_nat(0u);
v___x_4594_ = lean_array_get_size(v_params_4554_);
lean_inc(v_a_4534_);
lean_inc_ref(v_decls_4591_);
v___x_4595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4595_, 0, v_decls_4591_);
lean_ctor_set(v___x_4595_, 1, v_a_4534_);
v___x_4721_ = lean_nat_dec_lt(v___x_4593_, v___x_4594_);
if (v___x_4721_ == 0)
{
goto v___jp_4685_;
}
else
{
uint8_t v___x_4722_; 
v___x_4722_ = lean_nat_dec_le(v___x_4594_, v___x_4594_);
if (v___x_4722_ == 0)
{
if (v___x_4721_ == 0)
{
goto v___jp_4685_;
}
else
{
size_t v___x_4723_; size_t v___x_4724_; lean_object* v___x_4725_; 
v___x_4723_ = ((size_t)0ULL);
v___x_4724_ = lean_usize_of_nat(v___x_4594_);
v___x_4725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4554_, v___x_4723_, v___x_4724_, v___x_4556_, v___x_4595_, v___y_4537_, v___y_4541_);
v___y_4712_ = v___x_4725_;
goto v___jp_4711_;
}
}
else
{
size_t v___x_4726_; size_t v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = ((size_t)0ULL);
v___x_4727_ = lean_usize_of_nat(v___x_4594_);
v___x_4728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4554_, v___x_4726_, v___x_4727_, v___x_4556_, v___x_4595_, v___y_4537_, v___y_4541_);
v___y_4712_ = v___x_4728_;
goto v___jp_4711_;
}
}
v___jp_4560_:
{
if (lean_obj_tag(v___y_4561_) == 0)
{
lean_object* v___x_4562_; 
lean_dec_ref(v___y_4561_);
v___x_4562_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4534_, v___y_4537_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4574_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4565_ = v___x_4562_;
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4562_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
uint8_t v___x_4567_; 
v___x_4567_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4559_, v_a_4563_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v___x_4568_ = lean_box(v_safe_4555_);
v___x_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
v___x_4570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
lean_ctor_set(v___x_4570_, 1, v___x_4556_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 0, v___x_4570_);
v___x_4572_ = v___x_4565_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
else
{
lean_del_object(v___x_4565_);
v_a_4544_ = v___x_4557_;
goto v___jp_4543_;
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_a_4559_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v_a_4575_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4562_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4562_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec(v_a_4559_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v_a_4583_ = lean_ctor_get(v___y_4561_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___y_4561_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___y_4561_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___y_4561_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
v___jp_4596_:
{
lean_object* v___x_4604_; double v___x_4605_; double v___x_4606_; double v___x_4607_; double v___x_4608_; double v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4604_ = lean_io_mono_nanos_now();
v___x_4605_ = lean_float_of_nat(v___y_4601_);
v___x_4606_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1);
v___x_4607_ = lean_float_div(v___x_4605_, v___x_4606_);
v___x_4608_ = lean_float_of_nat(v___x_4604_);
v___x_4609_ = lean_float_div(v___x_4608_, v___x_4606_);
v___x_4610_ = lean_box_float(v___x_4607_);
v___x_4611_ = lean_box_float(v___x_4609_);
v___x_4612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4610_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
v___x_4613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4613_, 0, v_a_4603_);
lean_ctor_set(v___x_4613_, 1, v___x_4612_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
lean_inc(v___y_4539_);
lean_inc_ref(v___y_4538_);
lean_inc(v___y_4537_);
v___x_4614_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_4600_, v_safe_4555_, v___y_4602_, v___y_4599_, v___y_4598_, v___y_4597_, v___f_4592_, v___x_4613_, v___x_4595_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
lean_dec_ref(v___y_4599_);
v___y_4561_ = v___x_4614_;
goto v___jp_4560_;
}
v___jp_4615_:
{
lean_object* v___x_4623_; double v___x_4624_; double v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4623_ = lean_io_get_num_heartbeats();
v___x_4624_ = lean_float_of_nat(v___y_4620_);
v___x_4625_ = lean_float_of_nat(v___x_4623_);
v___x_4626_ = lean_box_float(v___x_4624_);
v___x_4627_ = lean_box_float(v___x_4625_);
v___x_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4626_);
lean_ctor_set(v___x_4628_, 1, v___x_4627_);
v___x_4629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4629_, 0, v_a_4622_);
lean_ctor_set(v___x_4629_, 1, v___x_4628_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
lean_inc(v___y_4539_);
lean_inc_ref(v___y_4538_);
lean_inc(v___y_4537_);
v___x_4630_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_4619_, v_safe_4555_, v___y_4621_, v___y_4618_, v___y_4617_, v___y_4616_, v___f_4592_, v___x_4629_, v___x_4595_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
lean_dec_ref(v___y_4618_);
v___y_4561_ = v___x_4630_;
goto v___jp_4560_;
}
v___jp_4631_:
{
lean_object* v___x_4637_; 
v___x_4637_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v___y_4541_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4639_; uint8_t v___x_4640_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref(v___x_4637_);
v___x_4639_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4640_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4633_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = lean_io_mono_nanos_now();
v___x_4642_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4634_, v___x_4595_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4650_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4645_ = v___x_4642_;
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4642_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4646_ == 0)
{
lean_ctor_set_tag(v___x_4645_, 1);
v___x_4648_ = v___x_4645_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
v___y_4597_ = v_a_4638_;
v___y_4598_ = v___y_4632_;
v___y_4599_ = v___y_4633_;
v___y_4600_ = v___y_4635_;
v___y_4601_ = v___x_4641_;
v___y_4602_ = v___y_4636_;
v_a_4603_ = v___x_4648_;
goto v___jp_4596_;
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
v_a_4651_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4642_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4642_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
lean_ctor_set_tag(v___x_4653_, 0);
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
v___y_4597_ = v_a_4638_;
v___y_4598_ = v___y_4632_;
v___y_4599_ = v___y_4633_;
v___y_4600_ = v___y_4635_;
v___y_4601_ = v___x_4641_;
v___y_4602_ = v___y_4636_;
v_a_4603_ = v___x_4656_;
goto v___jp_4596_;
}
}
}
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = lean_io_get_num_heartbeats();
v___x_4660_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4634_, v___x_4595_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4668_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4663_ = v___x_4660_;
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4660_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4666_; 
if (v_isShared_4664_ == 0)
{
lean_ctor_set_tag(v___x_4663_, 1);
v___x_4666_ = v___x_4663_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4661_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
v___y_4616_ = v_a_4638_;
v___y_4617_ = v___y_4632_;
v___y_4618_ = v___y_4633_;
v___y_4619_ = v___y_4635_;
v___y_4620_ = v___x_4659_;
v___y_4621_ = v___y_4636_;
v_a_4622_ = v___x_4666_;
goto v___jp_4615_;
}
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
v_a_4669_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v___x_4660_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4660_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
lean_ctor_set_tag(v___x_4671_, 0);
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
v___y_4616_ = v_a_4638_;
v___y_4617_ = v___y_4632_;
v___y_4618_ = v___y_4633_;
v___y_4619_ = v___y_4635_;
v___y_4620_ = v___x_4659_;
v___y_4621_ = v___y_4636_;
v_a_4622_ = v___x_4674_;
goto v___jp_4615_;
}
}
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___f_4592_);
lean_dec(v_a_4559_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v_a_4677_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4637_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4637_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
v___jp_4685_:
{
if (lean_obj_tag(v_value_4552_) == 0)
{
lean_object* v_options_4686_; uint8_t v_hasTrace_4687_; 
v_options_4686_ = lean_ctor_get(v___y_4540_, 2);
v_hasTrace_4687_ = lean_ctor_get_uint8(v_options_4686_, sizeof(void*)*1);
if (v_hasTrace_4687_ == 0)
{
lean_object* v_code_4688_; lean_object* v___x_4689_; 
lean_dec_ref(v___f_4592_);
v_code_4688_ = lean_ctor_get(v_value_4552_, 0);
lean_inc_ref(v_code_4688_);
v___x_4689_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4688_, v___x_4595_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
lean_dec_ref(v___x_4595_);
v___y_4561_ = v___x_4689_;
goto v___jp_4560_;
}
else
{
lean_object* v_code_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v_code_4690_ = lean_ctor_get(v_value_4552_, 0);
v___x_4691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_4692_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___x_4691_, v___y_4540_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
lean_inc(v_a_4693_);
lean_dec_ref(v___x_4692_);
v___x_4694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
v___x_4695_ = lean_unbox(v_a_4693_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; uint8_t v___x_4697_; 
v___x_4696_ = l_Lean_trace_profiler;
v___x_4697_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_options_4686_, v___x_4696_);
if (v___x_4697_ == 0)
{
lean_object* v___x_4698_; 
lean_dec(v_a_4693_);
lean_dec_ref(v___f_4592_);
lean_inc_ref(v_code_4690_);
v___x_4698_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4690_, v___x_4595_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
lean_dec_ref(v___x_4595_);
v___y_4561_ = v___x_4698_;
goto v___jp_4560_;
}
else
{
uint8_t v___x_4699_; 
v___x_4699_ = lean_unbox(v_a_4693_);
lean_dec(v_a_4693_);
lean_inc_ref(v_code_4690_);
lean_inc_ref(v_options_4686_);
v___y_4632_ = v___x_4699_;
v___y_4633_ = v_options_4686_;
v___y_4634_ = v_code_4690_;
v___y_4635_ = v___x_4691_;
v___y_4636_ = v___x_4694_;
goto v___jp_4631_;
}
}
else
{
uint8_t v___x_4700_; 
v___x_4700_ = lean_unbox(v_a_4693_);
lean_dec(v_a_4693_);
lean_inc_ref(v_code_4690_);
lean_inc_ref(v_options_4686_);
v___y_4632_ = v___x_4700_;
v___y_4633_ = v_options_4686_;
v___y_4634_ = v_code_4690_;
v___y_4635_ = v___x_4691_;
v___y_4636_ = v___x_4694_;
goto v___jp_4631_;
}
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___f_4592_);
lean_dec(v_a_4559_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v_a_4701_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4692_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4692_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
}
else
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
lean_dec_ref(v___f_4592_);
v___x_4709_ = lean_box(1);
v___x_4710_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4709_, v___x_4595_, v___y_4537_, v___y_4541_);
lean_dec_ref(v___x_4595_);
v___y_4561_ = v___x_4710_;
goto v___jp_4560_;
}
}
v___jp_4711_:
{
if (lean_obj_tag(v___y_4712_) == 0)
{
lean_dec_ref(v___y_4712_);
goto v___jp_4685_;
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___f_4592_);
lean_dec(v_a_4559_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v_a_4713_ = lean_ctor_get(v___y_4712_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___y_4712_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___y_4712_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___y_4712_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec(v_a_4534_);
v_a_4729_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4558_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4558_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
}
v___jp_4543_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_unsigned_to_nat(1u);
v___x_4546_ = lean_nat_add(v_a_4534_, v___x_4545_);
lean_dec(v_a_4534_);
v_a_4534_ = v___x_4546_;
v_b_4535_ = v_a_4544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___boxed(lean_object* v_upperBound_4737_, lean_object* v___x_4738_, lean_object* v_a_4739_, lean_object* v_b_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(v_upperBound_4737_, v___x_4738_, v_a_4739_, v_b_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_);
lean_dec_ref(v___y_4741_);
lean_dec_ref(v___x_4738_);
lean_dec(v_upperBound_4737_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_decls_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v_decls_4756_ = lean_ctor_get(v_a_4749_, 0);
v___x_4757_ = lean_array_get_size(v_decls_4756_);
v___x_4758_ = lean_unsigned_to_nat(0u);
v___x_4759_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0));
v___x_4760_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(v___x_4757_, v_decls_4756_, v___x_4758_, v___x_4759_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4775_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4763_ = v___x_4760_;
v_isShared_4764_ = v_isSharedCheck_4775_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4760_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4775_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v_fst_4765_; 
v_fst_4765_ = lean_ctor_get(v_a_4761_, 0);
lean_inc(v_fst_4765_);
lean_dec(v_a_4761_);
if (lean_obj_tag(v_fst_4765_) == 0)
{
uint8_t v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4766_ = 0;
v___x_4767_ = lean_box(v___x_4766_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v___x_4767_);
v___x_4769_ = v___x_4763_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
else
{
lean_object* v_val_4771_; lean_object* v___x_4773_; 
v_val_4771_ = lean_ctor_get(v_fst_4765_, 0);
lean_inc(v_val_4771_);
lean_dec_ref(v_fst_4765_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v_val_4771_);
v___x_4773_ = v___x_4763_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_val_4771_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
else
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4783_; 
v_a_4776_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4778_ = v___x_4760_;
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v___x_4760_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4776_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
lean_dec_ref(v_a_4784_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5(lean_object* v_00_u03b1_4792_, lean_object* v_x_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v___x_4801_; 
v___x_4801_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_x_4793_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4802_, lean_object* v_x_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5(v_00_u03b1_4802_, v_x_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_);
lean_dec(v___y_4809_);
lean_dec_ref(v___y_4808_);
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4(lean_object* v_upperBound_4812_, lean_object* v___x_4813_, lean_object* v_inst_4814_, lean_object* v_R_4815_, lean_object* v_a_4816_, lean_object* v_b_4817_, lean_object* v_c_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(v_upperBound_4812_, v___x_4813_, v_a_4816_, v_b_4817_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___boxed(lean_object* v_upperBound_4827_, lean_object* v___x_4828_, lean_object* v_inst_4829_, lean_object* v_R_4830_, lean_object* v_a_4831_, lean_object* v_b_4832_, lean_object* v_c_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4(v_upperBound_4827_, v___x_4828_, v_inst_4829_, v_R_4830_, v_a_4831_, v_b_4832_, v_c_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec_ref(v___y_4834_);
lean_dec_ref(v___x_4828_);
lean_dec(v_upperBound_4827_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4(lean_object* v_oldTraces_4842_, lean_object* v_data_4843_, lean_object* v_ref_4844_, lean_object* v_msg_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(v_oldTraces_4842_, v_data_4843_, v_ref_4844_, v_msg_4845_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___boxed(lean_object* v_oldTraces_4854_, lean_object* v_data_4855_, lean_object* v_ref_4856_, lean_object* v_msg_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4(v_oldTraces_4854_, v_data_4855_, v_ref_4856_, v_msg_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4868_, lean_object* v_msg_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_options_4875_; lean_object* v_ref_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v_options_4875_ = lean_ctor_get(v___y_4872_, 2);
v_ref_4876_ = lean_ctor_get(v___y_4872_, 5);
v___x_4877_ = lean_st_ref_get(v___y_4873_);
v___x_4878_ = lean_st_ref_get(v___y_4871_);
v___x_4879_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4870_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4938_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4938_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4938_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v_env_4884_; lean_object* v_lctx_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4936_; 
v_env_4884_ = lean_ctor_get(v___x_4877_, 0);
lean_inc_ref(v_env_4884_);
lean_dec(v___x_4877_);
v_lctx_4885_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4936_ == 0)
{
lean_object* v_unused_4937_; 
v_unused_4937_ = lean_ctor_get(v___x_4878_, 1);
lean_dec(v_unused_4937_);
v___x_4887_ = v___x_4878_;
v_isShared_4888_ = v_isSharedCheck_4936_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_lctx_4885_);
lean_dec(v___x_4878_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4936_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v_traceState_4891_; lean_object* v_env_4892_; lean_object* v_nextMacroScope_4893_; lean_object* v_ngen_4894_; lean_object* v_auxDeclNGen_4895_; lean_object* v_cache_4896_; lean_object* v_messages_4897_; lean_object* v_infoState_4898_; lean_object* v_snapshotTasks_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4935_; 
v___x_4889_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2);
v___x_4890_ = lean_st_ref_take(v___y_4873_);
v_traceState_4891_ = lean_ctor_get(v___x_4890_, 4);
v_env_4892_ = lean_ctor_get(v___x_4890_, 0);
v_nextMacroScope_4893_ = lean_ctor_get(v___x_4890_, 1);
v_ngen_4894_ = lean_ctor_get(v___x_4890_, 2);
v_auxDeclNGen_4895_ = lean_ctor_get(v___x_4890_, 3);
v_cache_4896_ = lean_ctor_get(v___x_4890_, 5);
v_messages_4897_ = lean_ctor_get(v___x_4890_, 6);
v_infoState_4898_ = lean_ctor_get(v___x_4890_, 7);
v_snapshotTasks_4899_ = lean_ctor_get(v___x_4890_, 8);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4901_ = v___x_4890_;
v_isShared_4902_ = v_isSharedCheck_4935_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_snapshotTasks_4899_);
lean_inc(v_infoState_4898_);
lean_inc(v_messages_4897_);
lean_inc(v_cache_4896_);
lean_inc(v_traceState_4891_);
lean_inc(v_auxDeclNGen_4895_);
lean_inc(v_ngen_4894_);
lean_inc(v_nextMacroScope_4893_);
lean_inc(v_env_4892_);
lean_dec(v___x_4890_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4935_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
uint64_t v_tid_4903_; lean_object* v_traces_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4934_; 
v_tid_4903_ = lean_ctor_get_uint64(v_traceState_4891_, sizeof(void*)*1);
v_traces_4904_ = lean_ctor_get(v_traceState_4891_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v_traceState_4891_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4906_ = v_traceState_4891_;
v_isShared_4907_ = v_isSharedCheck_4934_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_traces_4904_);
lean_dec(v_traceState_4891_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4934_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
uint8_t v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4912_; 
v___x_4908_ = lean_unbox(v_a_4880_);
lean_dec(v_a_4880_);
v___x_4909_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4885_, v___x_4908_);
lean_dec_ref(v_lctx_4885_);
lean_inc_ref(v_options_4875_);
v___x_4910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4910_, 0, v_env_4884_);
lean_ctor_set(v___x_4910_, 1, v___x_4889_);
lean_ctor_set(v___x_4910_, 2, v___x_4909_);
lean_ctor_set(v___x_4910_, 3, v_options_4875_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set_tag(v___x_4887_, 3);
lean_ctor_set(v___x_4887_, 1, v_msg_4869_);
lean_ctor_set(v___x_4887_, 0, v___x_4910_);
v___x_4912_ = v___x_4887_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4933_, 1, v_msg_4869_);
v___x_4912_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4913_; double v___x_4914_; uint8_t v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4913_ = lean_box(0);
v___x_4914_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1);
v___x_4915_ = 0;
v___x_4916_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
v___x_4917_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4917_, 0, v_cls_4868_);
lean_ctor_set(v___x_4917_, 1, v___x_4913_);
lean_ctor_set(v___x_4917_, 2, v___x_4916_);
lean_ctor_set_float(v___x_4917_, sizeof(void*)*3, v___x_4914_);
lean_ctor_set_float(v___x_4917_, sizeof(void*)*3 + 8, v___x_4914_);
lean_ctor_set_uint8(v___x_4917_, sizeof(void*)*3 + 16, v___x_4915_);
v___x_4918_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4919_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4917_);
lean_ctor_set(v___x_4919_, 1, v___x_4912_);
lean_ctor_set(v___x_4919_, 2, v___x_4918_);
lean_inc(v_ref_4876_);
v___x_4920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4920_, 0, v_ref_4876_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
v___x_4921_ = l_Lean_PersistentArray_push___redArg(v_traces_4904_, v___x_4920_);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 0, v___x_4921_);
v___x_4923_ = v___x_4906_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v___x_4921_);
lean_ctor_set_uint64(v_reuseFailAlloc_4932_, sizeof(void*)*1, v_tid_4903_);
v___x_4923_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
lean_object* v___x_4925_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 4, v___x_4923_);
v___x_4925_ = v___x_4901_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_env_4892_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_nextMacroScope_4893_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_ngen_4894_);
lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_auxDeclNGen_4895_);
lean_ctor_set(v_reuseFailAlloc_4931_, 4, v___x_4923_);
lean_ctor_set(v_reuseFailAlloc_4931_, 5, v_cache_4896_);
lean_ctor_set(v_reuseFailAlloc_4931_, 6, v_messages_4897_);
lean_ctor_set(v_reuseFailAlloc_4931_, 7, v_infoState_4898_);
lean_ctor_set(v_reuseFailAlloc_4931_, 8, v_snapshotTasks_4899_);
v___x_4925_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4929_; 
v___x_4926_ = lean_st_ref_set(v___y_4873_, v___x_4925_);
v___x_4927_ = lean_box(0);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4927_);
v___x_4929_ = v___x_4882_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4927_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4946_; 
lean_dec(v___x_4878_);
lean_dec(v___x_4877_);
lean_dec_ref(v_msg_4869_);
lean_dec(v_cls_4868_);
v_a_4939_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4941_ = v___x_4879_;
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4879_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4942_ == 0)
{
v___x_4944_ = v___x_4941_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4939_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4947_, lean_object* v_msg_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4947_, v_msg_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4955_, lean_object* v_msg_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4955_, v_msg_4956_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4965_, lean_object* v_msg_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4965_, v_msg_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
lean_dec(v___y_4970_);
lean_dec_ref(v___y_4969_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
return v_res_4974_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4975_ = lean_box(0);
v___x_4976_ = lean_unsigned_to_nat(16u);
v___x_4977_ = lean_mk_array(v___x_4976_, v___x_4975_);
return v___x_4977_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4978_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_4979_ = lean_unsigned_to_nat(0u);
v___x_4980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
lean_ctor_set(v___x_4980_, 1, v___x_4978_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_4981_, size_t v_i_4982_, lean_object* v_bs_4983_){
_start:
{
uint8_t v___x_4984_; 
v___x_4984_ = lean_usize_dec_lt(v_i_4982_, v_sz_4981_);
if (v___x_4984_ == 0)
{
return v_bs_4983_;
}
else
{
lean_object* v___x_4985_; lean_object* v_bs_x27_4986_; lean_object* v___x_4987_; size_t v___x_4988_; size_t v___x_4989_; lean_object* v___x_4990_; 
v___x_4985_ = lean_unsigned_to_nat(0u);
v_bs_x27_4986_ = lean_array_uset(v_bs_4983_, v_i_4982_, v___x_4985_);
v___x_4987_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_4988_ = ((size_t)1ULL);
v___x_4989_ = lean_usize_add(v_i_4982_, v___x_4988_);
v___x_4990_ = lean_array_uset(v_bs_x27_4986_, v_i_4982_, v___x_4987_);
v_i_4982_ = v___x_4989_;
v_bs_4983_ = v___x_4990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_4992_, lean_object* v_i_4993_, lean_object* v_bs_4994_){
_start:
{
size_t v_sz_boxed_4995_; size_t v_i_boxed_4996_; lean_object* v_res_4997_; 
v_sz_boxed_4995_ = lean_unbox_usize(v_sz_4992_);
lean_dec(v_sz_4992_);
v_i_boxed_4996_ = lean_unbox_usize(v_i_4993_);
lean_dec(v_i_4993_);
v_res_4997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_4995_, v_i_boxed_4996_, v_bs_4994_);
return v_res_4997_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5000_ = l_Lean_stringToMessageData(v___x_4999_);
return v___x_5000_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5002_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5003_ = l_Lean_stringToMessageData(v___x_5002_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v___x_5015_; lean_object* v_decls_5016_; lean_object* v_funVals_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5070_; 
v___x_5015_ = lean_st_ref_take(v_a_5006_);
v_decls_5016_ = lean_ctor_get(v_a_5005_, 0);
v_funVals_5017_ = lean_ctor_get(v___x_5015_, 1);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5070_ == 0)
{
lean_object* v_unused_5071_; 
v_unused_5071_ = lean_ctor_get(v___x_5015_, 0);
lean_dec(v_unused_5071_);
v___x_5019_ = v___x_5015_;
v_isShared_5020_ = v_isSharedCheck_5070_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_funVals_5017_);
lean_dec(v___x_5015_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5070_;
goto v_resetjp_5018_;
}
v___jp_5012_:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5013_ = lean_box(0);
v___x_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5013_);
return v___x_5014_;
}
v_resetjp_5018_:
{
size_t v_sz_5021_; size_t v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5025_; 
v_sz_5021_ = lean_array_size(v_decls_5016_);
v___x_5022_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5016_);
v___x_5023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5021_, v___x_5022_, v_decls_5016_);
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 0, v___x_5023_);
v___x_5025_ = v___x_5019_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5023_);
lean_ctor_set(v_reuseFailAlloc_5069_, 1, v_funVals_5017_);
v___x_5025_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5026_ = lean_st_ref_set(v_a_5006_, v___x_5025_);
lean_inc(v_a_5010_);
lean_inc_ref(v_a_5009_);
lean_inc(v_a_5008_);
lean_inc_ref(v_a_5007_);
lean_inc(v_a_5006_);
v___x_5027_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; uint8_t v___x_5029_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref(v___x_5027_);
v___x_5029_ = lean_unbox(v_a_5028_);
lean_dec(v_a_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5055_; 
lean_dec(v_a_5006_);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_a_5005_);
if (v_isSharedCheck_5055_ == 0)
{
lean_object* v_unused_5056_; lean_object* v_unused_5057_; 
v_unused_5056_ = lean_ctor_get(v_a_5005_, 1);
lean_dec(v_unused_5056_);
v_unused_5057_ = lean_ctor_get(v_a_5005_, 0);
lean_dec(v_unused_5057_);
v___x_5031_ = v_a_5005_;
v_isShared_5032_ = v_isSharedCheck_5055_;
goto v_resetjp_5030_;
}
else
{
lean_dec(v_a_5005_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5055_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_5034_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___x_5033_, v_a_5009_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; uint8_t v___x_5036_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref(v___x_5034_);
v___x_5036_ = lean_unbox(v_a_5035_);
lean_dec(v_a_5035_);
if (v___x_5036_ == 0)
{
lean_del_object(v___x_5031_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
lean_dec(v_n_5004_);
goto v___jp_5012_;
}
else
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5042_; 
v___x_5037_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5038_ = l_Nat_reprFast(v_n_5004_);
v___x_5039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5038_);
v___x_5040_ = l_Lean_MessageData_ofFormat(v___x_5039_);
if (v_isShared_5032_ == 0)
{
lean_ctor_set_tag(v___x_5031_, 7);
lean_ctor_set(v___x_5031_, 1, v___x_5040_);
lean_ctor_set(v___x_5031_, 0, v___x_5037_);
v___x_5042_ = v___x_5031_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5043_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5042_);
lean_ctor_set(v___x_5044_, 1, v___x_5043_);
v___x_5045_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5033_, v___x_5044_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_dec_ref(v___x_5045_);
goto v___jp_5012_;
}
else
{
return v___x_5045_;
}
}
}
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_del_object(v___x_5031_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
lean_dec(v_n_5004_);
v_a_5047_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5034_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5034_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
else
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = lean_unsigned_to_nat(1u);
v___x_5059_ = lean_nat_add(v_n_5004_, v___x_5058_);
lean_dec(v_n_5004_);
v_n_5004_ = v___x_5059_;
goto _start;
}
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
lean_dec(v_a_5006_);
lean_dec_ref(v_a_5005_);
lean_dec(v_n_5004_);
v_a_5061_ = lean_ctor_get(v___x_5027_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5027_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5027_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_);
return v_res_5080_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5081_; lean_object* v___x_5082_; 
v___x_5081_ = 0;
v___x_5082_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5081_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5083_){
_start:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5085_ = lean_panic_fn(v___x_5084_, v_msg_5083_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(lean_object* v_cls_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v_options_5089_; uint8_t v_hasTrace_5090_; 
v_options_5089_ = lean_ctor_get(v___y_5087_, 2);
v_hasTrace_5090_ = lean_ctor_get_uint8(v_options_5089_, sizeof(void*)*1);
if (v_hasTrace_5090_ == 0)
{
lean_object* v___x_5091_; lean_object* v___x_5092_; 
lean_dec(v_cls_5086_);
v___x_5091_ = lean_box(v_hasTrace_5090_);
v___x_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5091_);
return v___x_5092_;
}
else
{
lean_object* v_inheritedTraceOptions_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; uint8_t v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
v_inheritedTraceOptions_5093_ = lean_ctor_get(v___y_5087_, 13);
v___x_5094_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1));
v___x_5095_ = l_Lean_Name_append(v___x_5094_, v_cls_5086_);
v___x_5096_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5093_, v_options_5089_, v___x_5095_);
lean_dec(v___x_5095_);
v___x_5097_ = lean_box(v___x_5096_);
v___x_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5098_, 0, v___x_5097_);
return v___x_5098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg___boxed(lean_object* v_cls_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_5099_, v___y_5100_);
lean_dec_ref(v___y_5100_);
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v___x_5109_; 
v___x_5109_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_5103_, v___y_5106_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_cls_5117_, lean_object* v_msg_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v_options_5124_; lean_object* v_ref_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_options_5124_ = lean_ctor_get(v___y_5121_, 2);
v_ref_5125_ = lean_ctor_get(v___y_5121_, 5);
v___x_5126_ = lean_st_ref_get(v___y_5122_);
v___x_5127_ = lean_st_ref_get(v___y_5120_);
v___x_5128_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5119_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5187_; 
v_a_5129_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5187_ == 0)
{
v___x_5131_ = v___x_5128_;
v_isShared_5132_ = v_isSharedCheck_5187_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v___x_5128_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5187_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v_env_5133_; lean_object* v_lctx_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5185_; 
v_env_5133_ = lean_ctor_get(v___x_5126_, 0);
lean_inc_ref(v_env_5133_);
lean_dec(v___x_5126_);
v_lctx_5134_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5185_ == 0)
{
lean_object* v_unused_5186_; 
v_unused_5186_ = lean_ctor_get(v___x_5127_, 1);
lean_dec(v_unused_5186_);
v___x_5136_ = v___x_5127_;
v_isShared_5137_ = v_isSharedCheck_5185_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_lctx_5134_);
lean_dec(v___x_5127_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5185_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v_traceState_5140_; lean_object* v_env_5141_; lean_object* v_nextMacroScope_5142_; lean_object* v_ngen_5143_; lean_object* v_auxDeclNGen_5144_; lean_object* v_cache_5145_; lean_object* v_messages_5146_; lean_object* v_infoState_5147_; lean_object* v_snapshotTasks_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5184_; 
v___x_5138_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2);
v___x_5139_ = lean_st_ref_take(v___y_5122_);
v_traceState_5140_ = lean_ctor_get(v___x_5139_, 4);
v_env_5141_ = lean_ctor_get(v___x_5139_, 0);
v_nextMacroScope_5142_ = lean_ctor_get(v___x_5139_, 1);
v_ngen_5143_ = lean_ctor_get(v___x_5139_, 2);
v_auxDeclNGen_5144_ = lean_ctor_get(v___x_5139_, 3);
v_cache_5145_ = lean_ctor_get(v___x_5139_, 5);
v_messages_5146_ = lean_ctor_get(v___x_5139_, 6);
v_infoState_5147_ = lean_ctor_get(v___x_5139_, 7);
v_snapshotTasks_5148_ = lean_ctor_get(v___x_5139_, 8);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5150_ = v___x_5139_;
v_isShared_5151_ = v_isSharedCheck_5184_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_snapshotTasks_5148_);
lean_inc(v_infoState_5147_);
lean_inc(v_messages_5146_);
lean_inc(v_cache_5145_);
lean_inc(v_traceState_5140_);
lean_inc(v_auxDeclNGen_5144_);
lean_inc(v_ngen_5143_);
lean_inc(v_nextMacroScope_5142_);
lean_inc(v_env_5141_);
lean_dec(v___x_5139_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5184_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
uint64_t v_tid_5152_; lean_object* v_traces_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5183_; 
v_tid_5152_ = lean_ctor_get_uint64(v_traceState_5140_, sizeof(void*)*1);
v_traces_5153_ = lean_ctor_get(v_traceState_5140_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v_traceState_5140_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5155_ = v_traceState_5140_;
v_isShared_5156_ = v_isSharedCheck_5183_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_traces_5153_);
lean_dec(v_traceState_5140_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5183_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
uint8_t v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5161_; 
v___x_5157_ = lean_unbox(v_a_5129_);
lean_dec(v_a_5129_);
v___x_5158_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5134_, v___x_5157_);
lean_dec_ref(v_lctx_5134_);
lean_inc_ref(v_options_5124_);
v___x_5159_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5159_, 0, v_env_5133_);
lean_ctor_set(v___x_5159_, 1, v___x_5138_);
lean_ctor_set(v___x_5159_, 2, v___x_5158_);
lean_ctor_set(v___x_5159_, 3, v_options_5124_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set_tag(v___x_5136_, 3);
lean_ctor_set(v___x_5136_, 1, v_msg_5118_);
lean_ctor_set(v___x_5136_, 0, v___x_5159_);
v___x_5161_ = v___x_5136_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5159_);
lean_ctor_set(v_reuseFailAlloc_5182_, 1, v_msg_5118_);
v___x_5161_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
lean_object* v___x_5162_; double v___x_5163_; uint8_t v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5172_; 
v___x_5162_ = lean_box(0);
v___x_5163_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1);
v___x_5164_ = 0;
v___x_5165_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
v___x_5166_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5166_, 0, v_cls_5117_);
lean_ctor_set(v___x_5166_, 1, v___x_5162_);
lean_ctor_set(v___x_5166_, 2, v___x_5165_);
lean_ctor_set_float(v___x_5166_, sizeof(void*)*3, v___x_5163_);
lean_ctor_set_float(v___x_5166_, sizeof(void*)*3 + 8, v___x_5163_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*3 + 16, v___x_5164_);
v___x_5167_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5168_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set(v___x_5168_, 1, v___x_5161_);
lean_ctor_set(v___x_5168_, 2, v___x_5167_);
lean_inc(v_ref_5125_);
v___x_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5169_, 0, v_ref_5125_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
v___x_5170_ = l_Lean_PersistentArray_push___redArg(v_traces_5153_, v___x_5169_);
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 0, v___x_5170_);
v___x_5172_ = v___x_5155_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5170_);
lean_ctor_set_uint64(v_reuseFailAlloc_5181_, sizeof(void*)*1, v_tid_5152_);
v___x_5172_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
lean_object* v___x_5174_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 4, v___x_5172_);
v___x_5174_ = v___x_5150_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_env_5141_);
lean_ctor_set(v_reuseFailAlloc_5180_, 1, v_nextMacroScope_5142_);
lean_ctor_set(v_reuseFailAlloc_5180_, 2, v_ngen_5143_);
lean_ctor_set(v_reuseFailAlloc_5180_, 3, v_auxDeclNGen_5144_);
lean_ctor_set(v_reuseFailAlloc_5180_, 4, v___x_5172_);
lean_ctor_set(v_reuseFailAlloc_5180_, 5, v_cache_5145_);
lean_ctor_set(v_reuseFailAlloc_5180_, 6, v_messages_5146_);
lean_ctor_set(v_reuseFailAlloc_5180_, 7, v_infoState_5147_);
lean_ctor_set(v_reuseFailAlloc_5180_, 8, v_snapshotTasks_5148_);
v___x_5174_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5178_; 
v___x_5175_ = lean_st_ref_set(v___y_5122_, v___x_5174_);
v___x_5176_ = lean_box(0);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 0, v___x_5176_);
v___x_5178_ = v___x_5131_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5176_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
lean_dec(v___x_5127_);
lean_dec(v___x_5126_);
lean_dec_ref(v_msg_5118_);
lean_dec(v_cls_5117_);
v_a_5188_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5128_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5128_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_cls_5196_, lean_object* v_msg_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_cls_5196_, v_msg_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
lean_dec(v___y_5199_);
lean_dec_ref(v___y_5198_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(lean_object* v_as_5204_, size_t v_i_5205_, size_t v_stop_5206_, lean_object* v_b_5207_){
_start:
{
uint8_t v___x_5209_; 
v___x_5209_ = lean_usize_dec_eq(v_i_5205_, v_stop_5206_);
if (v___x_5209_ == 0)
{
lean_object* v_fst_5210_; lean_object* v_snd_5211_; lean_object* v___x_5212_; lean_object* v_snd_5213_; lean_object* v_fst_5214_; lean_object* v_fst_5215_; lean_object* v_snd_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5231_; 
v_fst_5210_ = lean_ctor_get(v_b_5207_, 0);
lean_inc(v_fst_5210_);
v_snd_5211_ = lean_ctor_get(v_b_5207_, 1);
lean_inc(v_snd_5211_);
lean_dec_ref(v_b_5207_);
v___x_5212_ = lean_array_uget_borrowed(v_as_5204_, v_i_5205_);
v_snd_5213_ = lean_ctor_get(v___x_5212_, 1);
lean_inc(v_snd_5213_);
v_fst_5214_ = lean_ctor_get(v___x_5212_, 0);
v_fst_5215_ = lean_ctor_get(v_snd_5213_, 0);
v_snd_5216_ = lean_ctor_get(v_snd_5213_, 1);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_snd_5213_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5218_ = v_snd_5213_;
v_isShared_5219_ = v_isSharedCheck_5231_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_snd_5216_);
lean_inc(v_fst_5215_);
lean_dec(v_snd_5213_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5231_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v_fvarId_5220_; uint8_t v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5226_; 
v_fvarId_5220_ = lean_ctor_get(v_fst_5214_, 0);
v___x_5221_ = 0;
v___x_5222_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5221_, v_fst_5215_, v_fst_5210_);
lean_dec(v_fst_5215_);
v___x_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5223_, 0, v_snd_5216_);
lean_inc(v_fvarId_5220_);
v___x_5224_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5211_, v_fvarId_5220_, v___x_5223_);
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 1, v___x_5224_);
lean_ctor_set(v___x_5218_, 0, v___x_5222_);
v___x_5226_ = v___x_5218_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5222_);
lean_ctor_set(v_reuseFailAlloc_5230_, 1, v___x_5224_);
v___x_5226_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
size_t v___x_5227_; size_t v___x_5228_; 
v___x_5227_ = ((size_t)1ULL);
v___x_5228_ = lean_usize_add(v_i_5205_, v___x_5227_);
v_i_5205_ = v___x_5228_;
v_b_5207_ = v___x_5226_;
goto _start;
}
}
}
else
{
lean_object* v___x_5232_; 
v___x_5232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5232_, 0, v_b_5207_);
return v___x_5232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg___boxed(lean_object* v_as_5233_, lean_object* v_i_5234_, lean_object* v_stop_5235_, lean_object* v_b_5236_, lean_object* v___y_5237_){
_start:
{
size_t v_i_boxed_5238_; size_t v_stop_boxed_5239_; lean_object* v_res_5240_; 
v_i_boxed_5238_ = lean_unbox_usize(v_i_5234_);
lean_dec(v_i_5234_);
v_stop_boxed_5239_ = lean_unbox_usize(v_stop_5235_);
lean_dec(v_stop_5235_);
v_res_5240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_as_5233_, v_i_boxed_5238_, v_stop_boxed_5239_, v_b_5236_);
lean_dec_ref(v_as_5233_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5241_, lean_object* v_x_5242_){
_start:
{
if (lean_obj_tag(v_x_5242_) == 0)
{
lean_object* v___x_5243_; 
v___x_5243_ = lean_box(0);
return v___x_5243_;
}
else
{
lean_object* v_key_5244_; lean_object* v_value_5245_; lean_object* v_tail_5246_; uint8_t v___x_5247_; 
v_key_5244_ = lean_ctor_get(v_x_5242_, 0);
v_value_5245_ = lean_ctor_get(v_x_5242_, 1);
v_tail_5246_ = lean_ctor_get(v_x_5242_, 2);
v___x_5247_ = l_Lean_instBEqFVarId_beq(v_key_5244_, v_a_5241_);
if (v___x_5247_ == 0)
{
v_x_5242_ = v_tail_5246_;
goto _start;
}
else
{
lean_object* v___x_5249_; 
lean_inc(v_value_5245_);
v___x_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5249_, 0, v_value_5245_);
return v___x_5249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5250_, lean_object* v_x_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5250_, v_x_5251_);
lean_dec(v_x_5251_);
lean_dec(v_a_5250_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5253_, lean_object* v_a_5254_){
_start:
{
lean_object* v_buckets_5255_; lean_object* v___x_5256_; uint64_t v___x_5257_; uint64_t v___x_5258_; uint64_t v___x_5259_; uint64_t v_fold_5260_; uint64_t v___x_5261_; uint64_t v___x_5262_; uint64_t v___x_5263_; size_t v___x_5264_; size_t v___x_5265_; size_t v___x_5266_; size_t v___x_5267_; size_t v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v_buckets_5255_ = lean_ctor_get(v_m_5253_, 1);
v___x_5256_ = lean_array_get_size(v_buckets_5255_);
v___x_5257_ = l_Lean_instHashableFVarId_hash(v_a_5254_);
v___x_5258_ = 32ULL;
v___x_5259_ = lean_uint64_shift_right(v___x_5257_, v___x_5258_);
v_fold_5260_ = lean_uint64_xor(v___x_5257_, v___x_5259_);
v___x_5261_ = 16ULL;
v___x_5262_ = lean_uint64_shift_right(v_fold_5260_, v___x_5261_);
v___x_5263_ = lean_uint64_xor(v_fold_5260_, v___x_5262_);
v___x_5264_ = lean_uint64_to_usize(v___x_5263_);
v___x_5265_ = lean_usize_of_nat(v___x_5256_);
v___x_5266_ = ((size_t)1ULL);
v___x_5267_ = lean_usize_sub(v___x_5265_, v___x_5266_);
v___x_5268_ = lean_usize_land(v___x_5264_, v___x_5267_);
v___x_5269_ = lean_array_uget_borrowed(v_buckets_5255_, v___x_5268_);
v___x_5270_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5254_, v___x_5269_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5271_, v_a_5272_);
lean_dec(v_a_5272_);
lean_dec_ref(v_m_5271_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(lean_object* v_assignment_5274_, lean_object* v_as_5275_, size_t v_i_5276_, size_t v_stop_5277_, lean_object* v_b_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v_a_5285_; uint8_t v___x_5289_; 
v___x_5289_ = lean_usize_dec_eq(v_i_5276_, v_stop_5277_);
if (v___x_5289_ == 0)
{
lean_object* v___x_5290_; lean_object* v_fvarId_5291_; lean_object* v___x_5292_; 
v___x_5290_ = lean_array_uget_borrowed(v_as_5275_, v_i_5276_);
v_fvarId_5291_ = lean_ctor_get(v___x_5290_, 0);
v___x_5292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5274_, v_fvarId_5291_);
if (lean_obj_tag(v___x_5292_) == 1)
{
lean_object* v_val_5293_; lean_object* v___x_5294_; 
v_val_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc(v_val_5293_);
lean_dec_ref(v___x_5292_);
lean_inc(v___y_5282_);
lean_inc_ref(v___y_5281_);
lean_inc(v___y_5280_);
lean_inc_ref(v___y_5279_);
v___x_5294_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5293_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref(v___x_5294_);
if (lean_obj_tag(v_a_5295_) == 1)
{
lean_object* v_val_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v_val_5296_ = lean_ctor_get(v_a_5295_, 0);
lean_inc(v_val_5296_);
lean_dec_ref(v_a_5295_);
lean_inc(v___x_5290_);
v___x_5297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5290_);
lean_ctor_set(v___x_5297_, 1, v_val_5296_);
v___x_5298_ = lean_array_push(v_b_5278_, v___x_5297_);
v_a_5285_ = v___x_5298_;
goto v___jp_5284_;
}
else
{
lean_dec(v_a_5295_);
v_a_5285_ = v_b_5278_;
goto v___jp_5284_;
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5306_; 
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec_ref(v_b_5278_);
v_a_5299_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5301_ = v___x_5294_;
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5294_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5304_; 
if (v_isShared_5302_ == 0)
{
v___x_5304_ = v___x_5301_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
return v___x_5304_;
}
}
}
}
else
{
lean_dec(v___x_5292_);
v_a_5285_ = v_b_5278_;
goto v___jp_5284_;
}
}
else
{
lean_object* v___x_5307_; 
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
v___x_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5307_, 0, v_b_5278_);
return v___x_5307_;
}
v___jp_5284_:
{
size_t v___x_5286_; size_t v___x_5287_; 
v___x_5286_ = ((size_t)1ULL);
v___x_5287_ = lean_usize_add(v_i_5276_, v___x_5286_);
v_i_5276_ = v___x_5287_;
v_b_5278_ = v_a_5285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5___boxed(lean_object* v_assignment_5308_, lean_object* v_as_5309_, lean_object* v_i_5310_, lean_object* v_stop_5311_, lean_object* v_b_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
size_t v_i_boxed_5318_; size_t v_stop_boxed_5319_; lean_object* v_res_5320_; 
v_i_boxed_5318_ = lean_unbox_usize(v_i_5310_);
lean_dec(v_i_5310_);
v_stop_boxed_5319_ = lean_unbox_usize(v_stop_5311_);
lean_dec(v_stop_5311_);
v_res_5320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(v_assignment_5308_, v_as_5309_, v_i_boxed_5318_, v_stop_boxed_5319_, v_b_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_);
lean_dec_ref(v_as_5309_);
lean_dec_ref(v_assignment_5308_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_assignment_5323_, lean_object* v_as_5324_, lean_object* v_start_5325_, lean_object* v_stop_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v___x_5332_; uint8_t v___x_5333_; 
v___x_5332_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0));
v___x_5333_ = lean_nat_dec_lt(v_start_5325_, v_stop_5326_);
if (v___x_5333_ == 0)
{
lean_object* v___x_5334_; 
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
v___x_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5332_);
return v___x_5334_;
}
else
{
lean_object* v___x_5335_; uint8_t v___x_5336_; 
v___x_5335_ = lean_array_get_size(v_as_5324_);
v___x_5336_ = lean_nat_dec_le(v_stop_5326_, v___x_5335_);
if (v___x_5336_ == 0)
{
uint8_t v___x_5337_; 
v___x_5337_ = lean_nat_dec_lt(v_start_5325_, v___x_5335_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5338_; 
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
v___x_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5332_);
return v___x_5338_;
}
else
{
size_t v___x_5339_; size_t v___x_5340_; lean_object* v___x_5341_; 
v___x_5339_ = lean_usize_of_nat(v_start_5325_);
v___x_5340_ = lean_usize_of_nat(v___x_5335_);
v___x_5341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(v_assignment_5323_, v_as_5324_, v___x_5339_, v___x_5340_, v___x_5332_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
return v___x_5341_;
}
}
else
{
size_t v___x_5342_; size_t v___x_5343_; lean_object* v___x_5344_; 
v___x_5342_ = lean_usize_of_nat(v_start_5325_);
v___x_5343_ = lean_usize_of_nat(v_stop_5326_);
v___x_5344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(v_assignment_5323_, v_as_5324_, v___x_5342_, v___x_5343_, v___x_5332_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
return v___x_5344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_assignment_5345_, lean_object* v_as_5346_, lean_object* v_start_5347_, lean_object* v_stop_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
lean_object* v_res_5354_; 
v_res_5354_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_assignment_5345_, v_as_5346_, v_start_5347_, v_stop_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
lean_dec(v_stop_5348_);
lean_dec(v_start_5347_);
lean_dec_ref(v_as_5346_);
lean_dec_ref(v_assignment_5345_);
return v_res_5354_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5357_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5358_ = lean_unsigned_to_nat(9u);
v___x_5359_ = lean_unsigned_to_nat(635u);
v___x_5360_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5361_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5362_ = l_mkPanicMessageWithDecl(v___x_5361_, v___x_5360_, v___x_5359_, v___x_5358_, v___x_5357_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(lean_object* v_resultType_5365_, lean_object* v_discrVal_5366_, lean_object* v_discr_5367_, lean_object* v_assignment_5368_, lean_object* v_i_5369_, lean_object* v_as_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
lean_object* v___x_5376_; uint8_t v___x_5377_; 
v___x_5376_ = lean_array_get_size(v_as_5370_);
v___x_5377_ = lean_nat_dec_lt(v_i_5369_, v___x_5376_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v___x_5378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5378_, 0, v_as_5370_);
return v___x_5378_;
}
else
{
lean_object* v_a_5379_; lean_object* v_a_5381_; 
v_a_5379_ = lean_array_fget_borrowed(v_as_5370_, v_i_5369_);
if (lean_obj_tag(v_a_5379_) == 0)
{
lean_object* v_ctorName_5392_; lean_object* v_params_5393_; lean_object* v_code_5394_; uint8_t v___x_5395_; lean_object* v___y_5397_; lean_object* v___y_5398_; lean_object* v___y_5411_; uint8_t v___x_5415_; 
v_ctorName_5392_ = lean_ctor_get(v_a_5379_, 0);
v_params_5393_ = lean_ctor_get(v_a_5379_, 1);
v_code_5394_ = lean_ctor_get(v_a_5379_, 2);
v___x_5395_ = 0;
lean_inc(v_ctorName_5392_);
lean_inc(v_discrVal_5366_);
v___x_5415_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5366_, v_ctorName_5392_);
if (v___x_5415_ == 0)
{
lean_object* v_cls_5416_; lean_object* v___x_5417_; 
v_cls_5416_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_5417_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_5416_, v___y_5373_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; uint8_t v___x_5419_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_a_5418_);
lean_dec_ref(v___x_5417_);
v___x_5419_ = lean_unbox(v_a_5418_);
if (v___x_5419_ == 0)
{
lean_dec(v_a_5418_);
lean_inc(v___y_5372_);
v___y_5411_ = v___y_5372_;
goto v___jp_5410_;
}
else
{
lean_object* v___x_5420_; 
lean_inc(v_discr_5367_);
v___x_5420_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5367_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; lean_object* v___x_5422_; uint8_t v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; uint8_t v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref(v___x_5420_);
v___x_5422_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0));
v___x_5423_ = lean_unbox(v_a_5418_);
v___x_5424_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5421_, v___x_5423_);
v___x_5425_ = lean_string_append(v___x_5422_, v___x_5424_);
lean_dec_ref(v___x_5424_);
v___x_5426_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1));
v___x_5427_ = lean_string_append(v___x_5425_, v___x_5426_);
v___x_5428_ = lean_unbox(v_a_5418_);
lean_dec(v_a_5418_);
lean_inc(v_ctorName_5392_);
v___x_5429_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5392_, v___x_5428_);
v___x_5430_ = lean_string_append(v___x_5427_, v___x_5429_);
lean_dec_ref(v___x_5429_);
v___x_5431_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5430_);
v___x_5432_ = l_Lean_MessageData_ofFormat(v___x_5431_);
v___x_5433_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_cls_5416_, v___x_5432_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_dec_ref(v___x_5433_);
lean_inc(v___y_5372_);
v___y_5411_ = v___y_5372_;
goto v___jp_5410_;
}
else
{
lean_object* v_a_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5441_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5436_ = v___x_5433_;
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_a_5434_);
lean_dec(v___x_5433_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5439_; 
if (v_isShared_5437_ == 0)
{
v___x_5439_ = v___x_5436_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_a_5434_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
}
}
else
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
lean_dec(v_a_5418_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5442_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5444_ = v___x_5420_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5420_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5447_; 
if (v_isShared_5445_ == 0)
{
v___x_5447_ = v___x_5444_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5442_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
}
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5450_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5417_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5417_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
else
{
lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5458_ = lean_unsigned_to_nat(0u);
v___x_5459_ = lean_array_get_size(v_params_5393_);
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5373_);
lean_inc(v___y_5372_);
lean_inc_ref(v___y_5371_);
v___x_5460_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_assignment_5368_, v_params_5393_, v___x_5458_, v___x_5459_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v___x_5474_; uint8_t v___x_5475_; lean_object* v_fst_5477_; lean_object* v_snd_5478_; lean_object* v___y_5491_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref(v___x_5460_);
v___x_5474_ = lean_array_get_size(v_a_5461_);
v___x_5475_ = lean_nat_dec_eq(v___x_5474_, v___x_5458_);
if (v___x_5475_ == 0)
{
if (v___x_5415_ == 0)
{
lean_dec(v_a_5461_);
goto v___jp_5462_;
}
else
{
lean_object* v___x_5503_; 
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5373_);
lean_inc(v___y_5372_);
lean_inc_ref(v___y_5371_);
lean_inc_ref(v_code_5394_);
v___x_5503_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5368_, v_code_5394_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
if (lean_obj_tag(v___x_5503_) == 0)
{
lean_object* v_a_5504_; lean_object* v___x_5505_; uint8_t v___x_5506_; 
v_a_5504_ = lean_ctor_get(v___x_5503_, 0);
lean_inc(v_a_5504_);
lean_dec_ref(v___x_5503_);
v___x_5505_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5506_ = lean_nat_dec_lt(v___x_5458_, v___x_5474_);
if (v___x_5506_ == 0)
{
lean_dec(v_a_5461_);
v_fst_5477_ = v_a_5504_;
v_snd_5478_ = v___x_5505_;
goto v___jp_5476_;
}
else
{
lean_object* v___x_5507_; uint8_t v___x_5508_; 
lean_inc(v_a_5504_);
v___x_5507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5507_, 0, v_a_5504_);
lean_ctor_set(v___x_5507_, 1, v___x_5505_);
v___x_5508_ = lean_nat_dec_le(v___x_5474_, v___x_5474_);
if (v___x_5508_ == 0)
{
if (v___x_5506_ == 0)
{
lean_dec_ref(v___x_5507_);
lean_dec(v_a_5461_);
v_fst_5477_ = v_a_5504_;
v_snd_5478_ = v___x_5505_;
goto v___jp_5476_;
}
else
{
size_t v___x_5509_; size_t v___x_5510_; lean_object* v___x_5511_; 
lean_dec(v_a_5504_);
v___x_5509_ = ((size_t)0ULL);
v___x_5510_ = lean_usize_of_nat(v___x_5474_);
v___x_5511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_a_5461_, v___x_5509_, v___x_5510_, v___x_5507_);
lean_dec(v_a_5461_);
v___y_5491_ = v___x_5511_;
goto v___jp_5490_;
}
}
else
{
size_t v___x_5512_; size_t v___x_5513_; lean_object* v___x_5514_; 
lean_dec(v_a_5504_);
v___x_5512_ = ((size_t)0ULL);
v___x_5513_ = lean_usize_of_nat(v___x_5474_);
v___x_5514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_a_5461_, v___x_5512_, v___x_5513_, v___x_5507_);
lean_dec(v_a_5461_);
v___y_5491_ = v___x_5514_;
goto v___jp_5490_;
}
}
}
else
{
lean_object* v_a_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5522_; 
lean_dec(v_a_5461_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5515_ = lean_ctor_get(v___x_5503_, 0);
v_isSharedCheck_5522_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5522_ == 0)
{
v___x_5517_ = v___x_5503_;
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_a_5515_);
lean_dec(v___x_5503_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5520_; 
if (v_isShared_5518_ == 0)
{
v___x_5520_ = v___x_5517_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
}
}
else
{
lean_dec(v_a_5461_);
goto v___jp_5462_;
}
v___jp_5462_:
{
lean_object* v___x_5463_; 
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5373_);
lean_inc(v___y_5372_);
lean_inc_ref(v___y_5371_);
lean_inc_ref(v_code_5394_);
v___x_5463_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5368_, v_code_5394_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___x_5465_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
lean_dec_ref(v___x_5463_);
lean_inc_ref(v_a_5379_);
v___x_5465_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5379_, v_a_5464_);
v_a_5381_ = v___x_5465_;
goto v___jp_5380_;
}
else
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5473_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5466_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5468_ = v___x_5463_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5463_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5471_; 
if (v_isShared_5469_ == 0)
{
v___x_5471_ = v___x_5468_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
}
v___jp_5476_:
{
lean_object* v___x_5479_; 
v___x_5479_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5395_, v_fst_5477_, v_snd_5478_, v___x_5475_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
lean_dec_ref(v_snd_5478_);
if (lean_obj_tag(v___x_5479_) == 0)
{
lean_object* v_a_5480_; lean_object* v___x_5481_; 
v_a_5480_ = lean_ctor_get(v___x_5479_, 0);
lean_inc(v_a_5480_);
lean_dec_ref(v___x_5479_);
lean_inc_ref(v_a_5379_);
v___x_5481_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5379_, v_a_5480_);
v_a_5381_ = v___x_5481_;
goto v___jp_5380_;
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5482_ = lean_ctor_get(v___x_5479_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5479_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___x_5479_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5479_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5487_; 
if (v_isShared_5485_ == 0)
{
v___x_5487_ = v___x_5484_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
v___x_5487_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
return v___x_5487_;
}
}
}
}
v___jp_5490_:
{
if (lean_obj_tag(v___y_5491_) == 0)
{
lean_object* v_a_5492_; lean_object* v_fst_5493_; lean_object* v_snd_5494_; 
v_a_5492_ = lean_ctor_get(v___y_5491_, 0);
lean_inc(v_a_5492_);
lean_dec_ref(v___y_5491_);
v_fst_5493_ = lean_ctor_get(v_a_5492_, 0);
lean_inc(v_fst_5493_);
v_snd_5494_ = lean_ctor_get(v_a_5492_, 1);
lean_inc(v_snd_5494_);
lean_dec(v_a_5492_);
v_fst_5477_ = v_fst_5493_;
v_snd_5478_ = v_snd_5494_;
goto v___jp_5476_;
}
else
{
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5502_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5495_ = lean_ctor_get(v___y_5491_, 0);
v_isSharedCheck_5502_ = !lean_is_exclusive(v___y_5491_);
if (v_isSharedCheck_5502_ == 0)
{
v___x_5497_ = v___y_5491_;
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v___y_5491_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5500_; 
if (v_isShared_5498_ == 0)
{
v___x_5500_ = v___x_5497_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
v___x_5500_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
return v___x_5500_;
}
}
}
}
}
else
{
lean_object* v_a_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5523_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5525_ = v___x_5460_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_a_5523_);
lean_dec(v___x_5460_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
v___jp_5396_:
{
lean_object* v___x_5399_; 
v___x_5399_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5395_, v___y_5398_, v___y_5397_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5398_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v___x_5400_; lean_object* v___x_5401_; 
lean_dec_ref(v___x_5399_);
lean_inc_ref(v_resultType_5365_);
v___x_5400_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5400_, 0, v_resultType_5365_);
lean_inc_ref(v_a_5379_);
v___x_5401_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5379_, v___x_5400_);
v_a_5381_ = v___x_5401_;
goto v___jp_5380_;
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5402_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5399_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5399_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
}
v___jp_5410_:
{
switch(lean_obj_tag(v_a_5379_))
{
case 0:
{
lean_object* v_code_5412_; 
v_code_5412_ = lean_ctor_get(v_a_5379_, 2);
lean_inc_ref(v_code_5412_);
v___y_5397_ = v___y_5411_;
v___y_5398_ = v_code_5412_;
goto v___jp_5396_;
}
case 1:
{
lean_object* v_code_5413_; 
v_code_5413_ = lean_ctor_get(v_a_5379_, 1);
lean_inc_ref(v_code_5413_);
v___y_5397_ = v___y_5411_;
v___y_5398_ = v_code_5413_;
goto v___jp_5396_;
}
default: 
{
lean_object* v_code_5414_; 
v_code_5414_ = lean_ctor_get(v_a_5379_, 0);
lean_inc_ref(v_code_5414_);
v___y_5397_ = v___y_5411_;
v___y_5398_ = v_code_5414_;
goto v___jp_5396_;
}
}
}
}
else
{
lean_object* v_code_5531_; lean_object* v___x_5532_; 
v_code_5531_ = lean_ctor_get(v_a_5379_, 0);
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5373_);
lean_inc(v___y_5372_);
lean_inc_ref(v___y_5371_);
lean_inc_ref(v_code_5531_);
v___x_5532_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5368_, v_code_5531_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v_a_5533_; lean_object* v___x_5534_; 
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
lean_inc(v_a_5533_);
lean_dec_ref(v___x_5532_);
lean_inc_ref(v_a_5379_);
v___x_5534_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5379_, v_a_5533_);
v_a_5381_ = v___x_5534_;
goto v___jp_5380_;
}
else
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5542_; 
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec_ref(v_as_5370_);
lean_dec(v_i_5369_);
lean_dec(v_discr_5367_);
lean_dec(v_discrVal_5366_);
lean_dec_ref(v_resultType_5365_);
v_a_5535_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5537_ = v___x_5532_;
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5532_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5540_; 
if (v_isShared_5538_ == 0)
{
v___x_5540_ = v___x_5537_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
v___jp_5380_:
{
size_t v___x_5382_; size_t v___x_5383_; uint8_t v___x_5384_; 
v___x_5382_ = lean_ptr_addr(v_a_5379_);
v___x_5383_ = lean_ptr_addr(v_a_5381_);
v___x_5384_ = lean_usize_dec_eq(v___x_5382_, v___x_5383_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5385_ = lean_unsigned_to_nat(1u);
v___x_5386_ = lean_nat_add(v_i_5369_, v___x_5385_);
v___x_5387_ = lean_array_fset(v_as_5370_, v_i_5369_, v_a_5381_);
lean_dec(v_i_5369_);
v_i_5369_ = v___x_5386_;
v_as_5370_ = v___x_5387_;
goto _start;
}
else
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
lean_dec_ref(v_a_5381_);
v___x_5389_ = lean_unsigned_to_nat(1u);
v___x_5390_ = lean_nat_add(v_i_5369_, v___x_5389_);
lean_dec(v_i_5369_);
v_i_5369_ = v___x_5390_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5543_, lean_object* v_code_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_){
_start:
{
lean_object* v___y_5551_; lean_object* v___y_5552_; uint8_t v___y_5553_; lean_object* v___y_5558_; lean_object* v___y_5559_; uint8_t v___y_5560_; lean_object* v_decl_5565_; lean_object* v_k_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; 
switch(lean_obj_tag(v_code_5544_))
{
case 0:
{
lean_object* v_decl_5616_; lean_object* v_k_5617_; lean_object* v___x_5618_; 
v_decl_5616_ = lean_ctor_get(v_code_5544_, 0);
v_k_5617_ = lean_ctor_get(v_code_5544_, 1);
lean_inc_ref(v_k_5617_);
v___x_5618_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5543_, v_k_5617_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_);
if (lean_obj_tag(v___x_5618_) == 0)
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5645_; 
v_a_5619_ = lean_ctor_get(v___x_5618_, 0);
v_isSharedCheck_5645_ = !lean_is_exclusive(v___x_5618_);
if (v_isSharedCheck_5645_ == 0)
{
v___x_5621_ = v___x_5618_;
v_isShared_5622_ = v_isSharedCheck_5645_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v___x_5618_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5645_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
uint8_t v___y_5624_; size_t v___x_5640_; size_t v___x_5641_; uint8_t v___x_5642_; 
v___x_5640_ = lean_ptr_addr(v_k_5617_);
v___x_5641_ = lean_ptr_addr(v_a_5619_);
v___x_5642_ = lean_usize_dec_eq(v___x_5640_, v___x_5641_);
if (v___x_5642_ == 0)
{
v___y_5624_ = v___x_5642_;
goto v___jp_5623_;
}
else
{
size_t v___x_5643_; uint8_t v___x_5644_; 
v___x_5643_ = lean_ptr_addr(v_decl_5616_);
v___x_5644_ = lean_usize_dec_eq(v___x_5643_, v___x_5643_);
v___y_5624_ = v___x_5644_;
goto v___jp_5623_;
}
v___jp_5623_:
{
if (v___y_5624_ == 0)
{
lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5634_; 
lean_inc_ref(v_decl_5616_);
v_isSharedCheck_5634_ = !lean_is_exclusive(v_code_5544_);
if (v_isSharedCheck_5634_ == 0)
{
lean_object* v_unused_5635_; lean_object* v_unused_5636_; 
v_unused_5635_ = lean_ctor_get(v_code_5544_, 1);
lean_dec(v_unused_5635_);
v_unused_5636_ = lean_ctor_get(v_code_5544_, 0);
lean_dec(v_unused_5636_);
v___x_5626_ = v_code_5544_;
v_isShared_5627_ = v_isSharedCheck_5634_;
goto v_resetjp_5625_;
}
else
{
lean_dec(v_code_5544_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5634_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
lean_ctor_set(v___x_5626_, 1, v_a_5619_);
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_decl_5616_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v_a_5619_);
v___x_5629_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
lean_object* v___x_5631_; 
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 0, v___x_5629_);
v___x_5631_ = v___x_5621_;
goto v_reusejp_5630_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v___x_5629_);
v___x_5631_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5630_;
}
v_reusejp_5630_:
{
return v___x_5631_;
}
}
}
}
else
{
lean_object* v___x_5638_; 
lean_dec(v_a_5619_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 0, v_code_5544_);
v___x_5638_ = v___x_5621_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_code_5544_);
v___x_5638_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
return v___x_5638_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_5544_);
return v___x_5618_;
}
}
case 1:
{
lean_object* v_decl_5646_; lean_object* v_k_5647_; 
v_decl_5646_ = lean_ctor_get(v_code_5544_, 0);
v_k_5647_ = lean_ctor_get(v_code_5544_, 1);
lean_inc_ref(v_k_5647_);
lean_inc_ref(v_decl_5646_);
v_decl_5565_ = v_decl_5646_;
v_k_5566_ = v_k_5647_;
v___y_5567_ = v_a_5545_;
v___y_5568_ = v_a_5546_;
v___y_5569_ = v_a_5547_;
v___y_5570_ = v_a_5548_;
goto v___jp_5564_;
}
case 2:
{
lean_object* v_decl_5648_; lean_object* v_k_5649_; 
v_decl_5648_ = lean_ctor_get(v_code_5544_, 0);
v_k_5649_ = lean_ctor_get(v_code_5544_, 1);
lean_inc_ref(v_k_5649_);
lean_inc_ref(v_decl_5648_);
v_decl_5565_ = v_decl_5648_;
v_k_5566_ = v_k_5649_;
v___y_5567_ = v_a_5545_;
v___y_5568_ = v_a_5546_;
v___y_5569_ = v_a_5547_;
v___y_5570_ = v_a_5548_;
goto v___jp_5564_;
}
case 4:
{
lean_object* v_cases_5650_; lean_object* v_typeName_5651_; lean_object* v_resultType_5652_; lean_object* v_discr_5653_; lean_object* v_alts_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5695_; 
v_cases_5650_ = lean_ctor_get(v_code_5544_, 0);
lean_inc_ref(v_cases_5650_);
v_typeName_5651_ = lean_ctor_get(v_cases_5650_, 0);
v_resultType_5652_ = lean_ctor_get(v_cases_5650_, 1);
v_discr_5653_ = lean_ctor_get(v_cases_5650_, 2);
v_alts_5654_ = lean_ctor_get(v_cases_5650_, 3);
v_isSharedCheck_5695_ = !lean_is_exclusive(v_cases_5650_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5656_ = v_cases_5650_;
v_isShared_5657_ = v_isSharedCheck_5695_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_alts_5654_);
lean_inc(v_discr_5653_);
lean_inc(v_resultType_5652_);
lean_inc(v_typeName_5651_);
lean_dec(v_cases_5650_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5695_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5658_; lean_object* v_discrVal_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; 
v___x_5658_ = lean_box(0);
v_discrVal_5659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5543_, v_discr_5653_, v___x_5658_);
v___x_5660_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5654_);
lean_inc(v_discr_5653_);
lean_inc_ref(v_resultType_5652_);
v___x_5661_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(v_resultType_5652_, v_discrVal_5659_, v_discr_5653_, v_assignment_5543_, v___x_5660_, v_alts_5654_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_);
if (lean_obj_tag(v___x_5661_) == 0)
{
lean_object* v_a_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5686_; 
v_a_5662_ = lean_ctor_get(v___x_5661_, 0);
v_isSharedCheck_5686_ = !lean_is_exclusive(v___x_5661_);
if (v_isSharedCheck_5686_ == 0)
{
v___x_5664_ = v___x_5661_;
v_isShared_5665_ = v_isSharedCheck_5686_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_a_5662_);
lean_dec(v___x_5661_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5686_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
size_t v___x_5666_; size_t v___x_5667_; uint8_t v___x_5668_; 
v___x_5666_ = lean_ptr_addr(v_alts_5654_);
lean_dec_ref(v_alts_5654_);
v___x_5667_ = lean_ptr_addr(v_a_5662_);
v___x_5668_ = lean_usize_dec_eq(v___x_5666_, v___x_5667_);
if (v___x_5668_ == 0)
{
lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5681_; 
v_isSharedCheck_5681_ = !lean_is_exclusive(v_code_5544_);
if (v_isSharedCheck_5681_ == 0)
{
lean_object* v_unused_5682_; 
v_unused_5682_ = lean_ctor_get(v_code_5544_, 0);
lean_dec(v_unused_5682_);
v___x_5670_ = v_code_5544_;
v_isShared_5671_ = v_isSharedCheck_5681_;
goto v_resetjp_5669_;
}
else
{
lean_dec(v_code_5544_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5681_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v___x_5673_; 
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 3, v_a_5662_);
v___x_5673_ = v___x_5656_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_typeName_5651_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v_resultType_5652_);
lean_ctor_set(v_reuseFailAlloc_5680_, 2, v_discr_5653_);
lean_ctor_set(v_reuseFailAlloc_5680_, 3, v_a_5662_);
v___x_5673_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
lean_object* v___x_5675_; 
if (v_isShared_5671_ == 0)
{
lean_ctor_set(v___x_5670_, 0, v___x_5673_);
v___x_5675_ = v___x_5670_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5673_);
v___x_5675_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
lean_object* v___x_5677_; 
if (v_isShared_5665_ == 0)
{
lean_ctor_set(v___x_5664_, 0, v___x_5675_);
v___x_5677_ = v___x_5664_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v___x_5675_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
}
}
}
else
{
lean_object* v___x_5684_; 
lean_dec(v_a_5662_);
lean_del_object(v___x_5656_);
lean_dec(v_discr_5653_);
lean_dec_ref(v_resultType_5652_);
lean_dec(v_typeName_5651_);
if (v_isShared_5665_ == 0)
{
lean_ctor_set(v___x_5664_, 0, v_code_5544_);
v___x_5684_ = v___x_5664_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5685_; 
v_reuseFailAlloc_5685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_code_5544_);
v___x_5684_ = v_reuseFailAlloc_5685_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
return v___x_5684_;
}
}
}
}
else
{
lean_object* v_a_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5694_; 
lean_del_object(v___x_5656_);
lean_dec_ref(v_alts_5654_);
lean_dec(v_discr_5653_);
lean_dec_ref(v_resultType_5652_);
lean_dec(v_typeName_5651_);
lean_dec_ref(v_code_5544_);
v_a_5687_ = lean_ctor_get(v___x_5661_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5661_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5689_ = v___x_5661_;
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_a_5687_);
lean_dec(v___x_5661_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5692_; 
if (v_isShared_5690_ == 0)
{
v___x_5692_ = v___x_5689_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_a_5687_);
v___x_5692_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
return v___x_5692_;
}
}
}
}
}
default: 
{
lean_object* v___x_5696_; 
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
v___x_5696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5696_, 0, v_code_5544_);
return v___x_5696_;
}
}
v___jp_5550_:
{
if (v___y_5553_ == 0)
{
lean_object* v___x_5554_; lean_object* v___x_5555_; 
lean_dec_ref(v_code_5544_);
v___x_5554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5554_, 0, v___y_5551_);
lean_ctor_set(v___x_5554_, 1, v___y_5552_);
v___x_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5554_);
return v___x_5555_;
}
else
{
lean_object* v___x_5556_; 
lean_dec_ref(v___y_5552_);
lean_dec_ref(v___y_5551_);
v___x_5556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5556_, 0, v_code_5544_);
return v___x_5556_;
}
}
v___jp_5557_:
{
if (v___y_5560_ == 0)
{
lean_object* v___x_5561_; lean_object* v___x_5562_; 
lean_dec_ref(v_code_5544_);
v___x_5561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5561_, 0, v___y_5558_);
lean_ctor_set(v___x_5561_, 1, v___y_5559_);
v___x_5562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5562_, 0, v___x_5561_);
return v___x_5562_;
}
else
{
lean_object* v___x_5563_; 
lean_dec_ref(v___y_5559_);
lean_dec_ref(v___y_5558_);
v___x_5563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5563_, 0, v_code_5544_);
return v___x_5563_;
}
}
v___jp_5564_:
{
lean_object* v_params_5571_; lean_object* v_type_5572_; lean_object* v_value_5573_; lean_object* v___x_5574_; 
v_params_5571_ = lean_ctor_get(v_decl_5565_, 2);
lean_inc_ref(v_params_5571_);
v_type_5572_ = lean_ctor_get(v_decl_5565_, 3);
lean_inc_ref(v_type_5572_);
v_value_5573_ = lean_ctor_get(v_decl_5565_, 4);
lean_inc(v___y_5570_);
lean_inc_ref(v___y_5569_);
lean_inc(v___y_5568_);
lean_inc_ref(v___y_5567_);
lean_inc_ref(v_value_5573_);
v___x_5574_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5543_, v_value_5573_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v_a_5575_; uint8_t v___x_5576_; lean_object* v___x_5577_; 
v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
lean_inc(v_a_5575_);
lean_dec_ref(v___x_5574_);
v___x_5576_ = 0;
v___x_5577_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5576_, v_decl_5565_, v_type_5572_, v_params_5571_, v_a_5575_, v___y_5568_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5579_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_a_5578_);
lean_dec_ref(v___x_5577_);
v___x_5579_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5543_, v_k_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5579_) == 0)
{
switch(lean_obj_tag(v_code_5544_))
{
case 1:
{
lean_object* v_a_5580_; lean_object* v_decl_5581_; lean_object* v_k_5582_; size_t v___x_5583_; size_t v___x_5584_; uint8_t v___x_5585_; 
v_a_5580_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_a_5580_);
lean_dec_ref(v___x_5579_);
v_decl_5581_ = lean_ctor_get(v_code_5544_, 0);
v_k_5582_ = lean_ctor_get(v_code_5544_, 1);
v___x_5583_ = lean_ptr_addr(v_k_5582_);
v___x_5584_ = lean_ptr_addr(v_a_5580_);
v___x_5585_ = lean_usize_dec_eq(v___x_5583_, v___x_5584_);
if (v___x_5585_ == 0)
{
v___y_5551_ = v_a_5578_;
v___y_5552_ = v_a_5580_;
v___y_5553_ = v___x_5585_;
goto v___jp_5550_;
}
else
{
size_t v___x_5586_; size_t v___x_5587_; uint8_t v___x_5588_; 
v___x_5586_ = lean_ptr_addr(v_decl_5581_);
v___x_5587_ = lean_ptr_addr(v_a_5578_);
v___x_5588_ = lean_usize_dec_eq(v___x_5586_, v___x_5587_);
v___y_5551_ = v_a_5578_;
v___y_5552_ = v_a_5580_;
v___y_5553_ = v___x_5588_;
goto v___jp_5550_;
}
}
case 2:
{
lean_object* v_a_5589_; lean_object* v_decl_5590_; lean_object* v_k_5591_; size_t v___x_5592_; size_t v___x_5593_; uint8_t v___x_5594_; 
v_a_5589_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_a_5589_);
lean_dec_ref(v___x_5579_);
v_decl_5590_ = lean_ctor_get(v_code_5544_, 0);
v_k_5591_ = lean_ctor_get(v_code_5544_, 1);
v___x_5592_ = lean_ptr_addr(v_k_5591_);
v___x_5593_ = lean_ptr_addr(v_a_5589_);
v___x_5594_ = lean_usize_dec_eq(v___x_5592_, v___x_5593_);
if (v___x_5594_ == 0)
{
v___y_5558_ = v_a_5578_;
v___y_5559_ = v_a_5589_;
v___y_5560_ = v___x_5594_;
goto v___jp_5557_;
}
else
{
size_t v___x_5595_; size_t v___x_5596_; uint8_t v___x_5597_; 
v___x_5595_ = lean_ptr_addr(v_decl_5590_);
v___x_5596_ = lean_ptr_addr(v_a_5578_);
v___x_5597_ = lean_usize_dec_eq(v___x_5595_, v___x_5596_);
v___y_5558_ = v_a_5578_;
v___y_5559_ = v_a_5589_;
v___y_5560_ = v___x_5597_;
goto v___jp_5557_;
}
}
default: 
{
lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5606_; 
lean_dec(v_a_5578_);
lean_dec_ref(v_code_5544_);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; 
v_unused_5607_ = lean_ctor_get(v___x_5579_, 0);
lean_dec(v_unused_5607_);
v___x_5599_ = v___x_5579_;
v_isShared_5600_ = v_isSharedCheck_5606_;
goto v_resetjp_5598_;
}
else
{
lean_dec(v___x_5579_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5606_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5601_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5602_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5601_);
if (v_isShared_5600_ == 0)
{
lean_ctor_set(v___x_5599_, 0, v___x_5602_);
v___x_5604_ = v___x_5599_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
}
}
else
{
lean_dec(v_a_5578_);
lean_dec_ref(v_code_5544_);
return v___x_5579_;
}
}
else
{
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5615_; 
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec_ref(v___y_5567_);
lean_dec_ref(v_k_5566_);
lean_dec_ref(v_code_5544_);
v_a_5608_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5610_ = v___x_5577_;
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5577_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v___x_5613_; 
if (v_isShared_5611_ == 0)
{
v___x_5613_ = v___x_5610_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_a_5608_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
}
else
{
lean_dec_ref(v_type_5572_);
lean_dec_ref(v_params_5571_);
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec_ref(v___y_5567_);
lean_dec_ref(v_k_5566_);
lean_dec_ref(v_decl_5565_);
lean_dec_ref(v_code_5544_);
return v___x_5574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5697_, lean_object* v_code_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_){
_start:
{
lean_object* v_res_5704_; 
v_res_5704_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5697_, v_code_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
lean_dec_ref(v_assignment_5697_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___boxed(lean_object* v_resultType_5705_, lean_object* v_discrVal_5706_, lean_object* v_discr_5707_, lean_object* v_assignment_5708_, lean_object* v_i_5709_, lean_object* v_as_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v_res_5716_; 
v_res_5716_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(v_resultType_5705_, v_discrVal_5706_, v_discr_5707_, v_assignment_5708_, v_i_5709_, v_as_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
lean_dec_ref(v_assignment_5708_);
return v_res_5716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5717_, lean_object* v_m_5718_, lean_object* v_a_5719_){
_start:
{
lean_object* v___x_5720_; 
v___x_5720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5718_, v_a_5719_);
return v___x_5720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5721_, lean_object* v_m_5722_, lean_object* v_a_5723_){
_start:
{
lean_object* v_res_5724_; 
v_res_5724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5721_, v_m_5722_, v_a_5723_);
lean_dec(v_a_5723_);
lean_dec_ref(v_m_5722_);
return v_res_5724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_as_5725_, size_t v_i_5726_, size_t v_stop_5727_, lean_object* v_b_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_){
_start:
{
lean_object* v___x_5734_; 
v___x_5734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_as_5725_, v_i_5726_, v_stop_5727_, v_b_5728_);
return v___x_5734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_as_5735_, lean_object* v_i_5736_, lean_object* v_stop_5737_, lean_object* v_b_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_){
_start:
{
size_t v_i_boxed_5744_; size_t v_stop_boxed_5745_; lean_object* v_res_5746_; 
v_i_boxed_5744_ = lean_unbox_usize(v_i_5736_);
lean_dec(v_i_5736_);
v_stop_boxed_5745_ = lean_unbox_usize(v_stop_5737_);
lean_dec(v_stop_5737_);
v_res_5746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_as_5735_, v_i_boxed_5744_, v_stop_boxed_5745_, v_b_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
lean_dec_ref(v_as_5735_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5747_, lean_object* v_a_5748_, lean_object* v_x_5749_){
_start:
{
lean_object* v___x_5750_; 
v___x_5750_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5748_, v_x_5749_);
return v___x_5750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5751_, lean_object* v_a_5752_, lean_object* v_x_5753_){
_start:
{
lean_object* v_res_5754_; 
v_res_5754_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5751_, v_a_5752_, v_x_5753_);
lean_dec(v_x_5753_);
lean_dec(v_a_5752_);
return v_res_5754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5755_, lean_object* v_v_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
if (lean_obj_tag(v_v_5756_) == 0)
{
lean_object* v_code_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5786_; 
v_code_5762_ = lean_ctor_get(v_v_5756_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v_v_5756_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5764_ = v_v_5756_;
v_isShared_5765_ = v_isSharedCheck_5786_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_code_5762_);
lean_dec(v_v_5756_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5786_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5766_; 
v___x_5766_ = lean_apply_6(v_f_5755_, v_code_5762_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, lean_box(0));
if (lean_obj_tag(v___x_5766_) == 0)
{
lean_object* v_a_5767_; lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5777_; 
v_a_5767_ = lean_ctor_get(v___x_5766_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5766_);
if (v_isSharedCheck_5777_ == 0)
{
v___x_5769_ = v___x_5766_;
v_isShared_5770_ = v_isSharedCheck_5777_;
goto v_resetjp_5768_;
}
else
{
lean_inc(v_a_5767_);
lean_dec(v___x_5766_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5777_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v___x_5772_; 
if (v_isShared_5765_ == 0)
{
lean_ctor_set(v___x_5764_, 0, v_a_5767_);
v___x_5772_ = v___x_5764_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_a_5767_);
v___x_5772_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
lean_object* v___x_5774_; 
if (v_isShared_5770_ == 0)
{
lean_ctor_set(v___x_5769_, 0, v___x_5772_);
v___x_5774_ = v___x_5769_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
}
else
{
lean_object* v_a_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5785_; 
lean_del_object(v___x_5764_);
v_a_5778_ = lean_ctor_get(v___x_5766_, 0);
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5766_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5780_ = v___x_5766_;
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_a_5778_);
lean_dec(v___x_5766_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5783_; 
if (v_isShared_5781_ == 0)
{
v___x_5783_ = v___x_5780_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
}
else
{
lean_object* v___x_5787_; 
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec_ref(v_f_5755_);
v___x_5787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5787_, 0, v_v_5756_);
return v___x_5787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5788_, lean_object* v_v_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_){
_start:
{
lean_object* v_res_5795_; 
v_res_5795_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5788_, v_v_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
return v_res_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5796_, lean_object* v_f_5797_, lean_object* v_v_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_){
_start:
{
lean_object* v___x_5804_; 
v___x_5804_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5797_, v_v_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
return v___x_5804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5805_, lean_object* v_f_5806_, lean_object* v_v_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_){
_start:
{
uint8_t v_pu_boxed_5813_; lean_object* v_res_5814_; 
v_pu_boxed_5813_ = lean_unbox(v_pu_5805_);
v_res_5814_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5813_, v_f_5806_, v_v_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5815_, lean_object* v_x_5816_){
_start:
{
if (lean_obj_tag(v_x_5816_) == 0)
{
return v_x_5815_;
}
else
{
lean_object* v_key_5817_; lean_object* v_value_5818_; lean_object* v_tail_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; 
v_key_5817_ = lean_ctor_get(v_x_5816_, 0);
v_value_5818_ = lean_ctor_get(v_x_5816_, 1);
v_tail_5819_ = lean_ctor_get(v_x_5816_, 2);
lean_inc(v_value_5818_);
lean_inc(v_key_5817_);
v___x_5820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5820_, 0, v_key_5817_);
lean_ctor_set(v___x_5820_, 1, v_value_5818_);
v___x_5821_ = lean_array_push(v_x_5815_, v___x_5820_);
v_x_5815_ = v___x_5821_;
v_x_5816_ = v_tail_5819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5823_, lean_object* v_x_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5823_, v_x_5824_);
lean_dec(v_x_5824_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5826_, size_t v_i_5827_, size_t v_stop_5828_, lean_object* v_b_5829_){
_start:
{
uint8_t v___x_5830_; 
v___x_5830_ = lean_usize_dec_eq(v_i_5827_, v_stop_5828_);
if (v___x_5830_ == 0)
{
lean_object* v___x_5831_; lean_object* v___x_5832_; size_t v___x_5833_; size_t v___x_5834_; 
v___x_5831_ = lean_array_uget_borrowed(v_as_5826_, v_i_5827_);
v___x_5832_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5829_, v___x_5831_);
v___x_5833_ = ((size_t)1ULL);
v___x_5834_ = lean_usize_add(v_i_5827_, v___x_5833_);
v_i_5827_ = v___x_5834_;
v_b_5829_ = v___x_5832_;
goto _start;
}
else
{
return v_b_5829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5836_, lean_object* v_i_5837_, lean_object* v_stop_5838_, lean_object* v_b_5839_){
_start:
{
size_t v_i_boxed_5840_; size_t v_stop_boxed_5841_; lean_object* v_res_5842_; 
v_i_boxed_5840_ = lean_unbox_usize(v_i_5837_);
lean_dec(v_i_5837_);
v_stop_boxed_5841_ = lean_unbox_usize(v_stop_5838_);
lean_dec(v_stop_5838_);
v_res_5842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5836_, v_i_boxed_5840_, v_stop_boxed_5841_, v_b_5839_);
lean_dec_ref(v_as_5836_);
return v_res_5842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5843_, size_t v_sz_5844_, size_t v_i_5845_, lean_object* v_bs_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_){
_start:
{
uint8_t v___x_5852_; 
v___x_5852_ = lean_usize_dec_lt(v_i_5845_, v_sz_5844_);
if (v___x_5852_ == 0)
{
lean_object* v___x_5853_; 
v___x_5853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5853_, 0, v_bs_5846_);
return v___x_5853_;
}
else
{
lean_object* v_v_5854_; lean_object* v_fst_5855_; lean_object* v_snd_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5880_; 
v_v_5854_ = lean_array_uget(v_bs_5846_, v_i_5845_);
v_fst_5855_ = lean_ctor_get(v_v_5854_, 0);
v_snd_5856_ = lean_ctor_get(v_v_5854_, 1);
v_isSharedCheck_5880_ = !lean_is_exclusive(v_v_5854_);
if (v_isSharedCheck_5880_ == 0)
{
v___x_5858_ = v_v_5854_;
v_isShared_5859_ = v_isSharedCheck_5880_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_snd_5856_);
lean_inc(v_fst_5855_);
lean_dec(v_v_5854_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5880_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v___x_5860_; 
v___x_5860_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5855_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_);
if (lean_obj_tag(v___x_5860_) == 0)
{
lean_object* v_a_5861_; lean_object* v___x_5862_; lean_object* v_bs_x27_5863_; lean_object* v___x_5864_; lean_object* v___x_5866_; 
v_a_5861_ = lean_ctor_get(v___x_5860_, 0);
lean_inc(v_a_5861_);
lean_dec_ref(v___x_5860_);
v___x_5862_ = lean_unsigned_to_nat(0u);
v_bs_x27_5863_ = lean_array_uset(v_bs_5846_, v_i_5845_, v___x_5862_);
v___x_5864_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5861_, v_a_5843_);
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 0, v___x_5864_);
v___x_5866_ = v___x_5858_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v___x_5864_);
lean_ctor_set(v_reuseFailAlloc_5871_, 1, v_snd_5856_);
v___x_5866_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
size_t v___x_5867_; size_t v___x_5868_; lean_object* v___x_5869_; 
v___x_5867_ = ((size_t)1ULL);
v___x_5868_ = lean_usize_add(v_i_5845_, v___x_5867_);
v___x_5869_ = lean_array_uset(v_bs_x27_5863_, v_i_5845_, v___x_5866_);
v_i_5845_ = v___x_5868_;
v_bs_5846_ = v___x_5869_;
goto _start;
}
}
else
{
lean_object* v_a_5872_; lean_object* v___x_5874_; uint8_t v_isShared_5875_; uint8_t v_isSharedCheck_5879_; 
lean_del_object(v___x_5858_);
lean_dec(v_snd_5856_);
lean_dec_ref(v_bs_5846_);
v_a_5872_ = lean_ctor_get(v___x_5860_, 0);
v_isSharedCheck_5879_ = !lean_is_exclusive(v___x_5860_);
if (v_isSharedCheck_5879_ == 0)
{
v___x_5874_ = v___x_5860_;
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
else
{
lean_inc(v_a_5872_);
lean_dec(v___x_5860_);
v___x_5874_ = lean_box(0);
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
v_resetjp_5873_:
{
lean_object* v___x_5877_; 
if (v_isShared_5875_ == 0)
{
v___x_5877_ = v___x_5874_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_a_5872_);
v___x_5877_ = v_reuseFailAlloc_5878_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
return v___x_5877_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5881_, lean_object* v_sz_5882_, lean_object* v_i_5883_, lean_object* v_bs_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_){
_start:
{
uint8_t v_a_2267__boxed_5890_; size_t v_sz_boxed_5891_; size_t v_i_boxed_5892_; lean_object* v_res_5893_; 
v_a_2267__boxed_5890_ = lean_unbox(v_a_5881_);
v_sz_boxed_5891_ = lean_unbox_usize(v_sz_5882_);
lean_dec(v_sz_5882_);
v_i_boxed_5892_ = lean_unbox_usize(v_i_5883_);
lean_dec(v_i_5883_);
v_res_5893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2267__boxed_5890_, v_sz_boxed_5891_, v_i_boxed_5892_, v_bs_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5894_){
_start:
{
lean_object* v_fst_5895_; lean_object* v_snd_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5919_; 
v_fst_5895_ = lean_ctor_get(v_x_5894_, 0);
v_snd_5896_ = lean_ctor_get(v_x_5894_, 1);
v_isSharedCheck_5919_ = !lean_is_exclusive(v_x_5894_);
if (v_isSharedCheck_5919_ == 0)
{
v___x_5898_ = v_x_5894_;
v_isShared_5899_ = v_isSharedCheck_5919_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_snd_5896_);
lean_inc(v_fst_5895_);
lean_dec(v_x_5894_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5919_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5904_; 
v___x_5900_ = l_String_quote(v_fst_5895_);
v___x_5901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5900_);
v___x_5902_ = lean_box(0);
if (v_isShared_5899_ == 0)
{
lean_ctor_set_tag(v___x_5898_, 1);
lean_ctor_set(v___x_5898_, 1, v___x_5902_);
lean_ctor_set(v___x_5898_, 0, v___x_5901_);
v___x_5904_ = v___x_5898_;
goto v_reusejp_5903_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v___x_5901_);
lean_ctor_set(v_reuseFailAlloc_5918_, 1, v___x_5902_);
v___x_5904_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5903_;
}
v_reusejp_5903_:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; uint8_t v___x_5916_; lean_object* v___x_5917_; 
v___x_5905_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5896_);
v___x_5906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5905_);
lean_ctor_set(v___x_5906_, 1, v___x_5904_);
v___x_5907_ = l_List_reverse___redArg(v___x_5906_);
v___x_5908_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5909_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5907_, v___x_5908_);
v___x_5910_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5911_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5911_);
lean_ctor_set(v___x_5912_, 1, v___x_5909_);
v___x_5913_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5912_);
lean_ctor_set(v___x_5914_, 1, v___x_5913_);
v___x_5915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5910_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = 0;
v___x_5917_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5917_, 0, v___x_5915_);
lean_ctor_set_uint8(v___x_5917_, sizeof(void*)*1, v___x_5916_);
return v___x_5917_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5920_, lean_object* v_x_5921_, lean_object* v_x_5922_){
_start:
{
if (lean_obj_tag(v_x_5922_) == 0)
{
lean_dec(v_x_5920_);
return v_x_5921_;
}
else
{
lean_object* v_head_5923_; lean_object* v_tail_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5934_; 
v_head_5923_ = lean_ctor_get(v_x_5922_, 0);
v_tail_5924_ = lean_ctor_get(v_x_5922_, 1);
v_isSharedCheck_5934_ = !lean_is_exclusive(v_x_5922_);
if (v_isSharedCheck_5934_ == 0)
{
v___x_5926_ = v_x_5922_;
v_isShared_5927_ = v_isSharedCheck_5934_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_tail_5924_);
lean_inc(v_head_5923_);
lean_dec(v_x_5922_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5934_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5929_; 
lean_inc(v_x_5920_);
if (v_isShared_5927_ == 0)
{
lean_ctor_set_tag(v___x_5926_, 5);
lean_ctor_set(v___x_5926_, 1, v_x_5920_);
lean_ctor_set(v___x_5926_, 0, v_x_5921_);
v___x_5929_ = v___x_5926_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5933_; 
v_reuseFailAlloc_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_x_5921_);
lean_ctor_set(v_reuseFailAlloc_5933_, 1, v_x_5920_);
v___x_5929_ = v_reuseFailAlloc_5933_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; 
v___x_5930_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5923_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5929_);
lean_ctor_set(v___x_5931_, 1, v___x_5930_);
v_x_5921_ = v___x_5931_;
v_x_5922_ = v_tail_5924_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5935_, lean_object* v_x_5936_, lean_object* v_x_5937_){
_start:
{
if (lean_obj_tag(v_x_5937_) == 0)
{
lean_dec(v_x_5935_);
return v_x_5936_;
}
else
{
lean_object* v_head_5938_; lean_object* v_tail_5939_; lean_object* v___x_5941_; uint8_t v_isShared_5942_; uint8_t v_isSharedCheck_5949_; 
v_head_5938_ = lean_ctor_get(v_x_5937_, 0);
v_tail_5939_ = lean_ctor_get(v_x_5937_, 1);
v_isSharedCheck_5949_ = !lean_is_exclusive(v_x_5937_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5941_ = v_x_5937_;
v_isShared_5942_ = v_isSharedCheck_5949_;
goto v_resetjp_5940_;
}
else
{
lean_inc(v_tail_5939_);
lean_inc(v_head_5938_);
lean_dec(v_x_5937_);
v___x_5941_ = lean_box(0);
v_isShared_5942_ = v_isSharedCheck_5949_;
goto v_resetjp_5940_;
}
v_resetjp_5940_:
{
lean_object* v___x_5944_; 
lean_inc(v_x_5935_);
if (v_isShared_5942_ == 0)
{
lean_ctor_set_tag(v___x_5941_, 5);
lean_ctor_set(v___x_5941_, 1, v_x_5935_);
lean_ctor_set(v___x_5941_, 0, v_x_5936_);
v___x_5944_ = v___x_5941_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_x_5936_);
lean_ctor_set(v_reuseFailAlloc_5948_, 1, v_x_5935_);
v___x_5944_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; 
v___x_5945_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5938_);
v___x_5946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5944_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
v___x_5947_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5935_, v___x_5946_, v_tail_5939_);
return v___x_5947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5950_, lean_object* v_x_5951_){
_start:
{
if (lean_obj_tag(v_x_5950_) == 0)
{
lean_object* v___x_5952_; 
lean_dec(v_x_5951_);
v___x_5952_ = lean_box(0);
return v___x_5952_;
}
else
{
lean_object* v_tail_5953_; 
v_tail_5953_ = lean_ctor_get(v_x_5950_, 1);
if (lean_obj_tag(v_tail_5953_) == 0)
{
lean_object* v_head_5954_; lean_object* v___x_5955_; 
lean_dec(v_x_5951_);
v_head_5954_ = lean_ctor_get(v_x_5950_, 0);
lean_inc(v_head_5954_);
lean_dec_ref(v_x_5950_);
v___x_5955_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5954_);
return v___x_5955_;
}
else
{
lean_object* v_head_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
lean_inc(v_tail_5953_);
v_head_5956_ = lean_ctor_get(v_x_5950_, 0);
lean_inc(v_head_5956_);
lean_dec_ref(v_x_5950_);
v___x_5957_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5956_);
v___x_5958_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5951_, v___x_5957_, v_tail_5953_);
return v___x_5958_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5960_; lean_object* v___x_5961_; 
v___x_5960_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5961_ = lean_string_length(v___x_5960_);
return v___x_5961_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5962_; lean_object* v___x_5963_; 
v___x_5962_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5963_ = lean_nat_to_int(v___x_5962_);
return v___x_5963_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5969_){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; uint8_t v___x_5972_; 
v___x_5970_ = lean_array_get_size(v_xs_5969_);
v___x_5971_ = lean_unsigned_to_nat(0u);
v___x_5972_ = lean_nat_dec_eq(v___x_5970_, v___x_5971_);
if (v___x_5972_ == 0)
{
lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; 
v___x_5973_ = lean_array_to_list(v_xs_5969_);
v___x_5974_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5975_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5973_, v___x_5974_);
v___x_5976_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5977_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5977_);
lean_ctor_set(v___x_5978_, 1, v___x_5975_);
v___x_5979_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5978_);
lean_ctor_set(v___x_5980_, 1, v___x_5979_);
v___x_5981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5976_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
v___x_5982_ = l_Std_Format_fill(v___x_5981_);
return v___x_5982_;
}
else
{
lean_object* v___x_5983_; 
lean_dec_ref(v_xs_5969_);
v___x_5983_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_5983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_5986_, lean_object* v_decl_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_){
_start:
{
lean_object* v___y_5994_; lean_object* v___y_5995_; lean_object* v___y_5996_; lean_object* v___y_5997_; lean_object* v_cls_6027_; lean_object* v___x_6028_; lean_object* v_a_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6088_; 
v_cls_6027_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_6028_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_6027_, v_a_5990_);
v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6088_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6088_ == 0)
{
v___x_6031_ = v___x_6028_;
v_isShared_6032_ = v_isSharedCheck_6088_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_a_6029_);
lean_dec(v___x_6028_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6088_;
goto v_resetjp_6030_;
}
v___jp_5993_:
{
lean_object* v_toSignature_5998_; lean_object* v_value_5999_; uint8_t v_recursive_6000_; lean_object* v_inlineAttr_x3f_6001_; lean_object* v___x_6003_; uint8_t v_isShared_6004_; uint8_t v_isSharedCheck_6026_; 
v_toSignature_5998_ = lean_ctor_get(v_decl_5987_, 0);
v_value_5999_ = lean_ctor_get(v_decl_5987_, 1);
v_recursive_6000_ = lean_ctor_get_uint8(v_decl_5987_, sizeof(void*)*3);
v_inlineAttr_x3f_6001_ = lean_ctor_get(v_decl_5987_, 2);
v_isSharedCheck_6026_ = !lean_is_exclusive(v_decl_5987_);
if (v_isSharedCheck_6026_ == 0)
{
v___x_6003_ = v_decl_5987_;
v_isShared_6004_ = v_isSharedCheck_6026_;
goto v_resetjp_6002_;
}
else
{
lean_inc(v_inlineAttr_x3f_6001_);
lean_inc(v_value_5999_);
lean_inc(v_toSignature_5998_);
lean_dec(v_decl_5987_);
v___x_6003_ = lean_box(0);
v_isShared_6004_ = v_isSharedCheck_6026_;
goto v_resetjp_6002_;
}
v_resetjp_6002_:
{
lean_object* v___x_6005_; lean_object* v___x_6006_; 
v___x_6005_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_6005_, 0, v_assignment_5986_);
v___x_6006_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_6005_, v_value_5999_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_);
if (lean_obj_tag(v___x_6006_) == 0)
{
lean_object* v_a_6007_; lean_object* v___x_6009_; uint8_t v_isShared_6010_; uint8_t v_isSharedCheck_6017_; 
v_a_6007_ = lean_ctor_get(v___x_6006_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_6006_);
if (v_isSharedCheck_6017_ == 0)
{
v___x_6009_ = v___x_6006_;
v_isShared_6010_ = v_isSharedCheck_6017_;
goto v_resetjp_6008_;
}
else
{
lean_inc(v_a_6007_);
lean_dec(v___x_6006_);
v___x_6009_ = lean_box(0);
v_isShared_6010_ = v_isSharedCheck_6017_;
goto v_resetjp_6008_;
}
v_resetjp_6008_:
{
lean_object* v___x_6012_; 
if (v_isShared_6004_ == 0)
{
lean_ctor_set(v___x_6003_, 1, v_a_6007_);
v___x_6012_ = v___x_6003_;
goto v_reusejp_6011_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_toSignature_5998_);
lean_ctor_set(v_reuseFailAlloc_6016_, 1, v_a_6007_);
lean_ctor_set(v_reuseFailAlloc_6016_, 2, v_inlineAttr_x3f_6001_);
lean_ctor_set_uint8(v_reuseFailAlloc_6016_, sizeof(void*)*3, v_recursive_6000_);
v___x_6012_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6011_;
}
v_reusejp_6011_:
{
lean_object* v___x_6014_; 
if (v_isShared_6010_ == 0)
{
lean_ctor_set(v___x_6009_, 0, v___x_6012_);
v___x_6014_ = v___x_6009_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v___x_6012_);
v___x_6014_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
return v___x_6014_;
}
}
}
}
else
{
lean_object* v_a_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6025_; 
lean_del_object(v___x_6003_);
lean_dec(v_inlineAttr_x3f_6001_);
lean_dec_ref(v_toSignature_5998_);
v_a_6018_ = lean_ctor_get(v___x_6006_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v___x_6006_);
if (v_isSharedCheck_6025_ == 0)
{
v___x_6020_ = v___x_6006_;
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_a_6018_);
lean_dec(v___x_6006_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_6021_ == 0)
{
v___x_6023_ = v___x_6020_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_a_6018_);
v___x_6023_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
return v___x_6023_;
}
}
}
}
}
v_resetjp_6030_:
{
lean_object* v___y_6034_; uint8_t v___x_6074_; 
v___x_6074_ = lean_unbox(v_a_6029_);
if (v___x_6074_ == 0)
{
lean_del_object(v___x_6031_);
lean_dec(v_a_6029_);
v___y_5994_ = v_a_5988_;
v___y_5995_ = v_a_5989_;
v___y_5996_ = v_a_5990_;
v___y_5997_ = v_a_5991_;
goto v___jp_5993_;
}
else
{
lean_object* v_size_6075_; lean_object* v_buckets_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; uint8_t v___x_6080_; 
v_size_6075_ = lean_ctor_get(v_assignment_5986_, 0);
v_buckets_6076_ = lean_ctor_get(v_assignment_5986_, 1);
v___x_6077_ = lean_mk_empty_array_with_capacity(v_size_6075_);
v___x_6078_ = lean_unsigned_to_nat(0u);
v___x_6079_ = lean_array_get_size(v_buckets_6076_);
v___x_6080_ = lean_nat_dec_lt(v___x_6078_, v___x_6079_);
if (v___x_6080_ == 0)
{
v___y_6034_ = v___x_6077_;
goto v___jp_6033_;
}
else
{
uint8_t v___x_6081_; 
v___x_6081_ = lean_nat_dec_le(v___x_6079_, v___x_6079_);
if (v___x_6081_ == 0)
{
if (v___x_6080_ == 0)
{
v___y_6034_ = v___x_6077_;
goto v___jp_6033_;
}
else
{
size_t v___x_6082_; size_t v___x_6083_; lean_object* v___x_6084_; 
v___x_6082_ = ((size_t)0ULL);
v___x_6083_ = lean_usize_of_nat(v___x_6079_);
v___x_6084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6076_, v___x_6082_, v___x_6083_, v___x_6077_);
v___y_6034_ = v___x_6084_;
goto v___jp_6033_;
}
}
else
{
size_t v___x_6085_; size_t v___x_6086_; lean_object* v___x_6087_; 
v___x_6085_ = ((size_t)0ULL);
v___x_6086_ = lean_usize_of_nat(v___x_6079_);
v___x_6087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6076_, v___x_6085_, v___x_6086_, v___x_6077_);
v___y_6034_ = v___x_6087_;
goto v___jp_6033_;
}
}
}
v___jp_6033_:
{
size_t v_sz_6035_; size_t v___x_6036_; uint8_t v___x_6037_; lean_object* v___x_6038_; 
v_sz_6035_ = lean_array_size(v___y_6034_);
v___x_6036_ = ((size_t)0ULL);
v___x_6037_ = lean_unbox(v_a_6029_);
v___x_6038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___x_6037_, v_sz_6035_, v___x_6036_, v___y_6034_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_toSignature_6039_; lean_object* v_a_6040_; lean_object* v_name_6041_; lean_object* v___x_6042_; uint8_t v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6054_; 
v_toSignature_6039_ = lean_ctor_get(v_decl_5987_, 0);
v_a_6040_ = lean_ctor_get(v___x_6038_, 0);
lean_inc(v_a_6040_);
lean_dec_ref(v___x_6038_);
v_name_6041_ = lean_ctor_get(v_toSignature_6039_, 0);
v___x_6042_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
v___x_6043_ = lean_unbox(v_a_6029_);
lean_dec(v_a_6029_);
lean_inc(v_name_6041_);
v___x_6044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6041_, v___x_6043_);
v___x_6045_ = lean_string_append(v___x_6042_, v___x_6044_);
lean_dec_ref(v___x_6044_);
v___x_6046_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6047_ = lean_string_append(v___x_6045_, v___x_6046_);
v___x_6048_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6040_);
v___x_6049_ = l_Std_Format_defWidth;
v___x_6050_ = lean_unsigned_to_nat(0u);
v___x_6051_ = l_Std_Format_pretty(v___x_6048_, v___x_6049_, v___x_6050_, v___x_6050_);
v___x_6052_ = lean_string_append(v___x_6047_, v___x_6051_);
lean_dec_ref(v___x_6051_);
if (v_isShared_6032_ == 0)
{
lean_ctor_set_tag(v___x_6031_, 3);
lean_ctor_set(v___x_6031_, 0, v___x_6052_);
v___x_6054_ = v___x_6031_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v___x_6052_);
v___x_6054_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
lean_object* v___x_6055_; lean_object* v___x_6056_; 
v___x_6055_ = l_Lean_MessageData_ofFormat(v___x_6054_);
v___x_6056_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_cls_6027_, v___x_6055_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_);
if (lean_obj_tag(v___x_6056_) == 0)
{
lean_dec_ref(v___x_6056_);
v___y_5994_ = v_a_5988_;
v___y_5995_ = v_a_5989_;
v___y_5996_ = v_a_5990_;
v___y_5997_ = v_a_5991_;
goto v___jp_5993_;
}
else
{
lean_object* v_a_6057_; lean_object* v___x_6059_; uint8_t v_isShared_6060_; uint8_t v_isSharedCheck_6064_; 
lean_dec(v_a_5991_);
lean_dec_ref(v_a_5990_);
lean_dec(v_a_5989_);
lean_dec_ref(v_a_5988_);
lean_dec_ref(v_decl_5987_);
lean_dec_ref(v_assignment_5986_);
v_a_6057_ = lean_ctor_get(v___x_6056_, 0);
v_isSharedCheck_6064_ = !lean_is_exclusive(v___x_6056_);
if (v_isSharedCheck_6064_ == 0)
{
v___x_6059_ = v___x_6056_;
v_isShared_6060_ = v_isSharedCheck_6064_;
goto v_resetjp_6058_;
}
else
{
lean_inc(v_a_6057_);
lean_dec(v___x_6056_);
v___x_6059_ = lean_box(0);
v_isShared_6060_ = v_isSharedCheck_6064_;
goto v_resetjp_6058_;
}
v_resetjp_6058_:
{
lean_object* v___x_6062_; 
if (v_isShared_6060_ == 0)
{
v___x_6062_ = v___x_6059_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_a_6057_);
v___x_6062_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
return v___x_6062_;
}
}
}
}
}
else
{
lean_object* v_a_6066_; lean_object* v___x_6068_; uint8_t v_isShared_6069_; uint8_t v_isSharedCheck_6073_; 
lean_del_object(v___x_6031_);
lean_dec(v_a_6029_);
lean_dec(v_a_5991_);
lean_dec_ref(v_a_5990_);
lean_dec(v_a_5989_);
lean_dec_ref(v_a_5988_);
lean_dec_ref(v_decl_5987_);
lean_dec_ref(v_assignment_5986_);
v_a_6066_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6073_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6073_ == 0)
{
v___x_6068_ = v___x_6038_;
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
else
{
lean_inc(v_a_6066_);
lean_dec(v___x_6038_);
v___x_6068_ = lean_box(0);
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
v_resetjp_6067_:
{
lean_object* v___x_6071_; 
if (v_isShared_6069_ == 0)
{
v___x_6071_ = v___x_6068_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
v___x_6071_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
return v___x_6071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6089_, lean_object* v_decl_6090_, lean_object* v_a_6091_, lean_object* v_a_6092_, lean_object* v_a_6093_, lean_object* v_a_6094_, lean_object* v_a_6095_){
_start:
{
lean_object* v_res_6096_; 
v_res_6096_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6089_, v_decl_6090_, v_a_6091_, v_a_6092_, v_a_6093_, v_a_6094_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6097_, lean_object* v_x_6098_){
_start:
{
lean_object* v___x_6099_; 
v___x_6099_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6097_);
return v___x_6099_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6100_, lean_object* v_x_6101_){
_start:
{
lean_object* v_res_6102_; 
v_res_6102_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6100_, v_x_6101_);
lean_dec(v_x_6101_);
return v_res_6102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6103_, size_t v_i_6104_, lean_object* v_bs_6105_){
_start:
{
uint8_t v___x_6106_; 
v___x_6106_ = lean_usize_dec_lt(v_i_6104_, v_sz_6103_);
if (v___x_6106_ == 0)
{
return v_bs_6105_;
}
else
{
lean_object* v_v_6107_; lean_object* v_toSignature_6108_; lean_object* v_name_6109_; lean_object* v___x_6110_; lean_object* v_bs_x27_6111_; size_t v___x_6112_; size_t v___x_6113_; lean_object* v___x_6114_; 
v_v_6107_ = lean_array_uget_borrowed(v_bs_6105_, v_i_6104_);
v_toSignature_6108_ = lean_ctor_get(v_v_6107_, 0);
v_name_6109_ = lean_ctor_get(v_toSignature_6108_, 0);
lean_inc(v_name_6109_);
v___x_6110_ = lean_unsigned_to_nat(0u);
v_bs_x27_6111_ = lean_array_uset(v_bs_6105_, v_i_6104_, v___x_6110_);
v___x_6112_ = ((size_t)1ULL);
v___x_6113_ = lean_usize_add(v_i_6104_, v___x_6112_);
v___x_6114_ = lean_array_uset(v_bs_x27_6111_, v_i_6104_, v_name_6109_);
v_i_6104_ = v___x_6113_;
v_bs_6105_ = v___x_6114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6116_, lean_object* v_i_6117_, lean_object* v_bs_6118_){
_start:
{
size_t v_sz_boxed_6119_; size_t v_i_boxed_6120_; lean_object* v_res_6121_; 
v_sz_boxed_6119_ = lean_unbox_usize(v_sz_6116_);
lean_dec(v_sz_6116_);
v_i_boxed_6120_ = lean_unbox_usize(v_i_6117_);
lean_dec(v_i_6117_);
v_res_6121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6119_, v_i_boxed_6120_, v_bs_6118_);
return v_res_6121_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6122_, lean_object* v_a_6123_){
_start:
{
if (lean_obj_tag(v_a_6122_) == 0)
{
lean_object* v___x_6124_; 
v___x_6124_ = l_List_reverse___redArg(v_a_6123_);
return v___x_6124_;
}
else
{
lean_object* v_head_6125_; lean_object* v_tail_6126_; lean_object* v___x_6128_; uint8_t v_isShared_6129_; uint8_t v_isSharedCheck_6135_; 
v_head_6125_ = lean_ctor_get(v_a_6122_, 0);
v_tail_6126_ = lean_ctor_get(v_a_6122_, 1);
v_isSharedCheck_6135_ = !lean_is_exclusive(v_a_6122_);
if (v_isSharedCheck_6135_ == 0)
{
v___x_6128_ = v_a_6122_;
v_isShared_6129_ = v_isSharedCheck_6135_;
goto v_resetjp_6127_;
}
else
{
lean_inc(v_tail_6126_);
lean_inc(v_head_6125_);
lean_dec(v_a_6122_);
v___x_6128_ = lean_box(0);
v_isShared_6129_ = v_isSharedCheck_6135_;
goto v_resetjp_6127_;
}
v_resetjp_6127_:
{
lean_object* v___x_6130_; lean_object* v___x_6132_; 
v___x_6130_ = l_Lean_MessageData_ofName(v_head_6125_);
if (v_isShared_6129_ == 0)
{
lean_ctor_set(v___x_6128_, 1, v_a_6123_);
lean_ctor_set(v___x_6128_, 0, v___x_6130_);
v___x_6132_ = v___x_6128_;
goto v_reusejp_6131_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v___x_6130_);
lean_ctor_set(v_reuseFailAlloc_6134_, 1, v_a_6123_);
v___x_6132_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6131_;
}
v_reusejp_6131_:
{
v_a_6122_ = v_tail_6126_;
v_a_6123_ = v___x_6132_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6137_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6138_ = l_Lean_stringToMessageData(v___x_6137_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6139_, lean_object* v_x_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_){
_start:
{
lean_object* v___x_6148_; size_t v_sz_6149_; size_t v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; 
v___x_6148_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6149_ = lean_array_size(v___y_6139_);
v___x_6150_ = ((size_t)0ULL);
v___x_6151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6149_, v___x_6150_, v___y_6139_);
v___x_6152_ = lean_array_to_list(v___x_6151_);
v___x_6153_ = lean_box(0);
v___x_6154_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6152_, v___x_6153_);
v___x_6155_ = l_Lean_MessageData_ofList(v___x_6154_);
v___x_6156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6148_);
lean_ctor_set(v___x_6156_, 1, v___x_6155_);
v___x_6157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6156_);
return v___x_6157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6158_, lean_object* v_x_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_){
_start:
{
lean_object* v_res_6167_; 
v_res_6167_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6158_, v_x_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
lean_dec(v___y_6165_);
lean_dec_ref(v___y_6164_);
lean_dec(v___y_6163_);
lean_dec_ref(v___y_6162_);
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
lean_dec_ref(v_x_6159_);
return v_res_6167_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6168_; lean_object* v___x_6169_; 
v___x_6168_ = 0;
v___x_6169_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6168_);
return v___x_6169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6170_, lean_object* v_n_6171_, lean_object* v_j_6172_, lean_object* v_a_6173_){
_start:
{
lean_object* v_zero_6174_; uint8_t v_isZero_6175_; 
v_zero_6174_ = lean_unsigned_to_nat(0u);
v_isZero_6175_ = lean_nat_dec_eq(v_j_6172_, v_zero_6174_);
if (v_isZero_6175_ == 1)
{
lean_dec(v_j_6172_);
return v_a_6173_;
}
else
{
lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v_toSignature_6179_; uint8_t v_safe_6180_; lean_object* v_one_6181_; lean_object* v_n_6182_; 
v___x_6176_ = lean_nat_sub(v_n_6171_, v_j_6172_);
v___x_6177_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6178_ = lean_array_get_borrowed(v___x_6177_, v___y_6170_, v___x_6176_);
lean_dec(v___x_6176_);
v_toSignature_6179_ = lean_ctor_get(v___x_6178_, 0);
v_safe_6180_ = lean_ctor_get_uint8(v_toSignature_6179_, sizeof(void*)*4);
v_one_6181_ = lean_unsigned_to_nat(1u);
v_n_6182_ = lean_nat_sub(v_j_6172_, v_one_6181_);
lean_dec(v_j_6172_);
if (v_safe_6180_ == 0)
{
lean_object* v___x_6183_; lean_object* v___x_6184_; 
v___x_6183_ = lean_box(1);
v___x_6184_ = lean_array_push(v_a_6173_, v___x_6183_);
v_j_6172_ = v_n_6182_;
v_a_6173_ = v___x_6184_;
goto _start;
}
else
{
lean_object* v___x_6186_; lean_object* v___x_6187_; 
v___x_6186_ = lean_box(0);
v___x_6187_ = lean_array_push(v_a_6173_, v___x_6186_);
v_j_6172_ = v_n_6182_;
v_a_6173_ = v___x_6187_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6189_, lean_object* v_n_6190_, lean_object* v_j_6191_, lean_object* v_a_6192_){
_start:
{
lean_object* v_res_6193_; 
v_res_6193_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6189_, v_n_6190_, v_j_6191_, v_a_6192_);
lean_dec(v_n_6190_);
lean_dec_ref(v___y_6189_);
return v_res_6193_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6194_, lean_object* v_as_6195_, lean_object* v_i_6196_, lean_object* v_j_6197_, lean_object* v_bs_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_){
_start:
{
lean_object* v_zero_6204_; uint8_t v_isZero_6205_; 
v_zero_6204_ = lean_unsigned_to_nat(0u);
v_isZero_6205_ = lean_nat_dec_eq(v_i_6196_, v_zero_6204_);
if (v_isZero_6205_ == 1)
{
lean_object* v___x_6206_; 
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6199_);
lean_dec(v_j_6197_);
lean_dec(v_i_6196_);
v___x_6206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6206_, 0, v_bs_6198_);
return v___x_6206_;
}
else
{
lean_object* v___x_6207_; lean_object* v_toSignature_6208_; uint8_t v_safe_6209_; lean_object* v_one_6210_; lean_object* v_n_6211_; lean_object* v_a_6213_; 
v___x_6207_ = lean_array_fget_borrowed(v_as_6195_, v_j_6197_);
v_toSignature_6208_ = lean_ctor_get(v___x_6207_, 0);
v_safe_6209_ = lean_ctor_get_uint8(v_toSignature_6208_, sizeof(void*)*4);
v_one_6210_ = lean_unsigned_to_nat(1u);
v_n_6211_ = lean_nat_sub(v_i_6196_, v_one_6210_);
lean_dec(v_i_6196_);
if (v_safe_6209_ == 0)
{
lean_inc(v___x_6207_);
v_a_6213_ = v___x_6207_;
goto v___jp_6212_;
}
else
{
lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; 
v___x_6217_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6218_ = lean_array_get_borrowed(v___x_6217_, v___x_6194_, v_j_6197_);
lean_inc(v___y_6202_);
lean_inc_ref(v___y_6201_);
lean_inc(v___y_6200_);
lean_inc_ref(v___y_6199_);
lean_inc(v___x_6207_);
lean_inc(v___x_6218_);
v___x_6219_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6218_, v___x_6207_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_);
if (lean_obj_tag(v___x_6219_) == 0)
{
lean_object* v_a_6220_; 
v_a_6220_ = lean_ctor_get(v___x_6219_, 0);
lean_inc(v_a_6220_);
lean_dec_ref(v___x_6219_);
v_a_6213_ = v_a_6220_;
goto v___jp_6212_;
}
else
{
lean_object* v_a_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6228_; 
lean_dec(v_n_6211_);
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6199_);
lean_dec_ref(v_bs_6198_);
lean_dec(v_j_6197_);
v_a_6221_ = lean_ctor_get(v___x_6219_, 0);
v_isSharedCheck_6228_ = !lean_is_exclusive(v___x_6219_);
if (v_isSharedCheck_6228_ == 0)
{
v___x_6223_ = v___x_6219_;
v_isShared_6224_ = v_isSharedCheck_6228_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_a_6221_);
lean_dec(v___x_6219_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6228_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
lean_object* v___x_6226_; 
if (v_isShared_6224_ == 0)
{
v___x_6226_ = v___x_6223_;
goto v_reusejp_6225_;
}
else
{
lean_object* v_reuseFailAlloc_6227_; 
v_reuseFailAlloc_6227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_a_6221_);
v___x_6226_ = v_reuseFailAlloc_6227_;
goto v_reusejp_6225_;
}
v_reusejp_6225_:
{
return v___x_6226_;
}
}
}
}
v___jp_6212_:
{
lean_object* v___x_6214_; lean_object* v___x_6215_; 
v___x_6214_ = lean_nat_add(v_j_6197_, v_one_6210_);
lean_dec(v_j_6197_);
v___x_6215_ = lean_array_push(v_bs_6198_, v_a_6213_);
v_i_6196_ = v_n_6211_;
v_j_6197_ = v___x_6214_;
v_bs_6198_ = v___x_6215_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6229_, lean_object* v_as_6230_, lean_object* v_i_6231_, lean_object* v_j_6232_, lean_object* v_bs_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_){
_start:
{
lean_object* v_res_6239_; 
v_res_6239_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6229_, v_as_6230_, v_i_6231_, v_j_6232_, v_bs_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
lean_dec_ref(v_as_6230_);
lean_dec_ref(v___x_6229_);
return v_res_6239_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6242_, lean_object* v_l_6243_, lean_object* v_r_6244_){
_start:
{
lean_object* v_toSignature_6245_; lean_object* v_toSignature_6246_; lean_object* v_name_6247_; lean_object* v_name_6248_; uint8_t v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; uint8_t v___x_6259_; 
v_toSignature_6245_ = lean_ctor_get(v_l_6243_, 0);
v_toSignature_6246_ = lean_ctor_get(v_r_6244_, 0);
v_name_6247_ = lean_ctor_get(v_toSignature_6245_, 0);
lean_inc(v_name_6247_);
v_name_6248_ = lean_ctor_get(v_toSignature_6246_, 0);
lean_inc(v_name_6248_);
v___x_6249_ = 0;
v___x_6250_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6249_, v_l_6243_);
lean_dec_ref(v_l_6243_);
v___x_6251_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6252_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__0));
v___x_6253_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__1));
v___x_6254_ = l_Lean_Name_toString(v_name_6247_, v___x_6242_);
v___x_6255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6255_, 0, v___x_6250_);
lean_ctor_set(v___x_6255_, 1, v___x_6254_);
v___x_6256_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6249_, v_r_6244_);
lean_dec_ref(v_r_6244_);
v___x_6257_ = l_Lean_Name_toString(v_name_6248_, v___x_6242_);
v___x_6258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6258_, 0, v___x_6256_);
lean_ctor_set(v___x_6258_, 1, v___x_6257_);
v___x_6259_ = l_Prod_lexLtDec___redArg(v___x_6251_, v___x_6252_, v___x_6253_, v___x_6255_, v___x_6258_);
return v___x_6259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6260_, lean_object* v_l_6261_, lean_object* v_r_6262_){
_start:
{
uint8_t v___x_11121__boxed_6263_; uint8_t v_res_6264_; lean_object* v_r_6265_; 
v___x_11121__boxed_6263_ = lean_unbox(v___x_6260_);
v_res_6264_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_11121__boxed_6263_, v_l_6261_, v_r_6262_);
v_r_6265_ = lean_box(v_res_6264_);
return v_r_6265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_as_6266_, lean_object* v_lo_6267_, lean_object* v_hi_6268_){
_start:
{
uint8_t v___x_6269_; 
v___x_6269_ = lean_nat_dec_lt(v_lo_6267_, v_hi_6268_);
if (v___x_6269_ == 0)
{
lean_dec(v_lo_6267_);
return v_as_6266_;
}
else
{
lean_object* v___x_6270_; lean_object* v___f_6271_; lean_object* v___x_6272_; lean_object* v_fst_6273_; lean_object* v_snd_6274_; uint8_t v___x_6275_; 
v___x_6270_ = lean_box(v___x_6269_);
v___f_6271_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_6271_, 0, v___x_6270_);
lean_inc(v_lo_6267_);
v___x_6272_ = l_Array_qpartition___redArg(v_as_6266_, v___f_6271_, v_lo_6267_, v_hi_6268_);
v_fst_6273_ = lean_ctor_get(v___x_6272_, 0);
lean_inc(v_fst_6273_);
v_snd_6274_ = lean_ctor_get(v___x_6272_, 1);
lean_inc(v_snd_6274_);
lean_dec_ref(v___x_6272_);
v___x_6275_ = lean_nat_dec_le(v_hi_6268_, v_fst_6273_);
if (v___x_6275_ == 0)
{
lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6276_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_snd_6274_, v_lo_6267_, v_fst_6273_);
v___x_6277_ = lean_unsigned_to_nat(1u);
v___x_6278_ = lean_nat_add(v_fst_6273_, v___x_6277_);
lean_dec(v_fst_6273_);
v_as_6266_ = v___x_6276_;
v_lo_6267_ = v___x_6278_;
goto _start;
}
else
{
lean_dec(v_fst_6273_);
lean_dec(v_lo_6267_);
return v_snd_6274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_as_6280_, lean_object* v_lo_6281_, lean_object* v_hi_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_as_6280_, v_lo_6281_, v_hi_6282_);
lean_dec(v_hi_6282_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6284_, lean_object* v___x_6285_, lean_object* v_n_6286_, lean_object* v_j_6287_, lean_object* v_a_6288_){
_start:
{
lean_object* v_zero_6289_; uint8_t v_isZero_6290_; 
v_zero_6289_ = lean_unsigned_to_nat(0u);
v_isZero_6290_ = lean_nat_dec_eq(v_j_6287_, v_zero_6289_);
if (v_isZero_6290_ == 1)
{
lean_dec(v_j_6287_);
return v_a_6288_;
}
else
{
lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v_toSignature_6293_; lean_object* v_name_6294_; lean_object* v___x_6295_; lean_object* v_one_6296_; lean_object* v_n_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v___x_6291_ = lean_nat_sub(v_n_6286_, v_j_6287_);
v___x_6292_ = lean_array_fget_borrowed(v___y_6284_, v___x_6291_);
v_toSignature_6293_ = lean_ctor_get(v___x_6292_, 0);
v_name_6294_ = lean_ctor_get(v_toSignature_6293_, 0);
v___x_6295_ = lean_box(0);
v_one_6296_ = lean_unsigned_to_nat(1u);
v_n_6297_ = lean_nat_sub(v_j_6287_, v_one_6296_);
lean_dec(v_j_6287_);
v___x_6298_ = lean_array_get_borrowed(v___x_6295_, v___x_6285_, v___x_6291_);
lean_dec(v___x_6291_);
lean_inc(v___x_6298_);
lean_inc(v_name_6294_);
v___x_6299_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6288_, v_name_6294_, v___x_6298_);
v_j_6287_ = v_n_6297_;
v_a_6288_ = v___x_6299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6301_, lean_object* v___x_6302_, lean_object* v_n_6303_, lean_object* v_j_6304_, lean_object* v_a_6305_){
_start:
{
lean_object* v_res_6306_; 
v_res_6306_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6301_, v___x_6302_, v_n_6303_, v_j_6304_, v_a_6305_);
lean_dec(v_n_6303_);
lean_dec_ref(v___x_6302_);
lean_dec_ref(v___y_6301_);
return v_res_6306_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6307_; 
v___x_6307_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6307_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; 
v___x_6308_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6309_, 0, v___x_6308_);
return v___x_6309_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6310_; lean_object* v___x_6311_; 
v___x_6310_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6311_, 0, v___x_6310_);
lean_ctor_set(v___x_6311_, 1, v___x_6310_);
return v___x_6311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_){
_start:
{
lean_object* v___x_6320_; lean_object* v___y_6322_; lean_object* v___y_6323_; lean_object* v___y_6324_; lean_object* v___y_6325_; lean_object* v___y_6360_; lean_object* v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; lean_object* v___y_6368_; uint8_t v___y_6369_; uint8_t v___y_6370_; lean_object* v___y_6371_; lean_object* v_a_6372_; lean_object* v___y_6382_; lean_object* v___y_6383_; lean_object* v___y_6384_; lean_object* v___y_6385_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v___y_6388_; lean_object* v___y_6389_; lean_object* v___y_6390_; lean_object* v___y_6391_; uint8_t v___y_6392_; uint8_t v___y_6393_; lean_object* v_a_6394_; lean_object* v___y_6407_; lean_object* v___y_6408_; lean_object* v___y_6409_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v___y_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; uint8_t v___y_6415_; uint8_t v___y_6416_; lean_object* v___y_6458_; lean_object* v___y_6483_; lean_object* v___y_6484_; lean_object* v___x_6486_; uint8_t v___x_6487_; 
v___x_6320_ = lean_unsigned_to_nat(0u);
v___x_6486_ = lean_array_get_size(v_decls_6314_);
v___x_6487_ = lean_nat_dec_eq(v___x_6486_, v___x_6320_);
if (v___x_6487_ == 0)
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___y_6491_; uint8_t v___x_6493_; 
v___x_6488_ = lean_unsigned_to_nat(1u);
v___x_6489_ = lean_nat_sub(v___x_6486_, v___x_6488_);
v___x_6493_ = lean_nat_dec_le(v___x_6320_, v___x_6489_);
if (v___x_6493_ == 0)
{
lean_inc(v___x_6489_);
v___y_6491_ = v___x_6489_;
goto v___jp_6490_;
}
else
{
v___y_6491_ = v___x_6320_;
goto v___jp_6490_;
}
v___jp_6490_:
{
uint8_t v___x_6492_; 
v___x_6492_ = lean_nat_dec_le(v___y_6491_, v___x_6489_);
if (v___x_6492_ == 0)
{
lean_dec(v___x_6489_);
lean_inc(v___y_6491_);
v___y_6483_ = v___y_6491_;
v___y_6484_ = v___y_6491_;
goto v___jp_6482_;
}
else
{
v___y_6483_ = v___y_6491_;
v___y_6484_ = v___x_6489_;
goto v___jp_6482_;
}
}
}
else
{
v___y_6458_ = v_decls_6314_;
goto v___jp_6457_;
}
v___jp_6321_:
{
if (lean_obj_tag(v___y_6325_) == 0)
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v_assignments_6328_; lean_object* v_funVals_6329_; lean_object* v_env_6330_; lean_object* v_nextMacroScope_6331_; lean_object* v_ngen_6332_; lean_object* v_auxDeclNGen_6333_; lean_object* v_traceState_6334_; lean_object* v_messages_6335_; lean_object* v_infoState_6336_; lean_object* v_snapshotTasks_6337_; lean_object* v___x_6339_; uint8_t v_isShared_6340_; uint8_t v_isSharedCheck_6349_; 
lean_dec_ref(v___y_6325_);
v___x_6326_ = lean_st_ref_get(v___y_6324_);
lean_dec(v___y_6324_);
v___x_6327_ = lean_st_ref_take(v_a_6318_);
v_assignments_6328_ = lean_ctor_get(v___x_6326_, 0);
lean_inc_ref(v_assignments_6328_);
v_funVals_6329_ = lean_ctor_get(v___x_6326_, 1);
lean_inc_ref(v_funVals_6329_);
lean_dec(v___x_6326_);
v_env_6330_ = lean_ctor_get(v___x_6327_, 0);
v_nextMacroScope_6331_ = lean_ctor_get(v___x_6327_, 1);
v_ngen_6332_ = lean_ctor_get(v___x_6327_, 2);
v_auxDeclNGen_6333_ = lean_ctor_get(v___x_6327_, 3);
v_traceState_6334_ = lean_ctor_get(v___x_6327_, 4);
v_messages_6335_ = lean_ctor_get(v___x_6327_, 6);
v_infoState_6336_ = lean_ctor_get(v___x_6327_, 7);
v_snapshotTasks_6337_ = lean_ctor_get(v___x_6327_, 8);
v_isSharedCheck_6349_ = !lean_is_exclusive(v___x_6327_);
if (v_isSharedCheck_6349_ == 0)
{
lean_object* v_unused_6350_; 
v_unused_6350_ = lean_ctor_get(v___x_6327_, 5);
lean_dec(v_unused_6350_);
v___x_6339_ = v___x_6327_;
v_isShared_6340_ = v_isSharedCheck_6349_;
goto v_resetjp_6338_;
}
else
{
lean_inc(v_snapshotTasks_6337_);
lean_inc(v_infoState_6336_);
lean_inc(v_messages_6335_);
lean_inc(v_traceState_6334_);
lean_inc(v_auxDeclNGen_6333_);
lean_inc(v_ngen_6332_);
lean_inc(v_nextMacroScope_6331_);
lean_inc(v_env_6330_);
lean_dec(v___x_6327_);
v___x_6339_ = lean_box(0);
v_isShared_6340_ = v_isSharedCheck_6349_;
goto v_resetjp_6338_;
}
v_resetjp_6338_:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6344_; 
lean_inc(v___y_6322_);
v___x_6341_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6323_, v_funVals_6329_, v___y_6322_, v___y_6322_, v_env_6330_);
lean_dec_ref(v_funVals_6329_);
v___x_6342_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6340_ == 0)
{
lean_ctor_set(v___x_6339_, 5, v___x_6342_);
lean_ctor_set(v___x_6339_, 0, v___x_6341_);
v___x_6344_ = v___x_6339_;
goto v_reusejp_6343_;
}
else
{
lean_object* v_reuseFailAlloc_6348_; 
v_reuseFailAlloc_6348_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6348_, 0, v___x_6341_);
lean_ctor_set(v_reuseFailAlloc_6348_, 1, v_nextMacroScope_6331_);
lean_ctor_set(v_reuseFailAlloc_6348_, 2, v_ngen_6332_);
lean_ctor_set(v_reuseFailAlloc_6348_, 3, v_auxDeclNGen_6333_);
lean_ctor_set(v_reuseFailAlloc_6348_, 4, v_traceState_6334_);
lean_ctor_set(v_reuseFailAlloc_6348_, 5, v___x_6342_);
lean_ctor_set(v_reuseFailAlloc_6348_, 6, v_messages_6335_);
lean_ctor_set(v_reuseFailAlloc_6348_, 7, v_infoState_6336_);
lean_ctor_set(v_reuseFailAlloc_6348_, 8, v_snapshotTasks_6337_);
v___x_6344_ = v_reuseFailAlloc_6348_;
goto v_reusejp_6343_;
}
v_reusejp_6343_:
{
lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; 
v___x_6345_ = lean_st_ref_set(v_a_6318_, v___x_6344_);
v___x_6346_ = lean_mk_empty_array_with_capacity(v___y_6322_);
v___x_6347_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6328_, v___y_6323_, v___y_6322_, v___x_6320_, v___x_6346_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
lean_dec_ref(v___y_6323_);
lean_dec_ref(v_assignments_6328_);
return v___x_6347_;
}
}
}
else
{
lean_object* v_a_6351_; lean_object* v___x_6353_; uint8_t v_isShared_6354_; uint8_t v_isSharedCheck_6358_; 
lean_dec(v___y_6324_);
lean_dec_ref(v___y_6323_);
lean_dec(v___y_6322_);
lean_dec(v_a_6318_);
lean_dec_ref(v_a_6317_);
lean_dec(v_a_6316_);
lean_dec_ref(v_a_6315_);
v_a_6351_ = lean_ctor_get(v___y_6325_, 0);
v_isSharedCheck_6358_ = !lean_is_exclusive(v___y_6325_);
if (v_isSharedCheck_6358_ == 0)
{
v___x_6353_ = v___y_6325_;
v_isShared_6354_ = v_isSharedCheck_6358_;
goto v_resetjp_6352_;
}
else
{
lean_inc(v_a_6351_);
lean_dec(v___y_6325_);
v___x_6353_ = lean_box(0);
v_isShared_6354_ = v_isSharedCheck_6358_;
goto v_resetjp_6352_;
}
v_resetjp_6352_:
{
lean_object* v___x_6356_; 
if (v_isShared_6354_ == 0)
{
v___x_6356_ = v___x_6353_;
goto v_reusejp_6355_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
v___x_6356_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6355_;
}
v_reusejp_6355_:
{
return v___x_6356_;
}
}
}
}
v___jp_6359_:
{
lean_object* v___x_6373_; double v___x_6374_; double v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6373_ = lean_io_get_num_heartbeats();
v___x_6374_ = lean_float_of_nat(v___y_6371_);
v___x_6375_ = lean_float_of_nat(v___x_6373_);
v___x_6376_ = lean_box_float(v___x_6374_);
v___x_6377_ = lean_box_float(v___x_6375_);
v___x_6378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6378_, 0, v___x_6376_);
lean_ctor_set(v___x_6378_, 1, v___x_6377_);
v___x_6379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6379_, 0, v_a_6372_);
lean_ctor_set(v___x_6379_, 1, v___x_6378_);
lean_inc(v_a_6318_);
lean_inc_ref(v_a_6317_);
lean_inc(v_a_6316_);
lean_inc_ref(v_a_6315_);
lean_inc(v___y_6368_);
v___x_6380_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_6366_, v___y_6369_, v___y_6365_, v___y_6364_, v___y_6370_, v___y_6360_, v___y_6362_, v___x_6379_, v___y_6367_, v___y_6368_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
lean_dec_ref(v___y_6364_);
v___y_6322_ = v___y_6361_;
v___y_6323_ = v___y_6363_;
v___y_6324_ = v___y_6368_;
v___y_6325_ = v___x_6380_;
goto v___jp_6321_;
}
v___jp_6381_:
{
lean_object* v___x_6395_; double v___x_6396_; double v___x_6397_; double v___x_6398_; double v___x_6399_; double v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6395_ = lean_io_mono_nanos_now();
v___x_6396_ = lean_float_of_nat(v___y_6387_);
v___x_6397_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1);
v___x_6398_ = lean_float_div(v___x_6396_, v___x_6397_);
v___x_6399_ = lean_float_of_nat(v___x_6395_);
v___x_6400_ = lean_float_div(v___x_6399_, v___x_6397_);
v___x_6401_ = lean_box_float(v___x_6398_);
v___x_6402_ = lean_box_float(v___x_6400_);
v___x_6403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6403_, 0, v___x_6401_);
lean_ctor_set(v___x_6403_, 1, v___x_6402_);
v___x_6404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6404_, 0, v_a_6394_);
lean_ctor_set(v___x_6404_, 1, v___x_6403_);
lean_inc(v_a_6318_);
lean_inc_ref(v_a_6317_);
lean_inc(v_a_6316_);
lean_inc_ref(v_a_6315_);
lean_inc(v___y_6391_);
v___x_6405_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_6389_, v___y_6392_, v___y_6388_, v___y_6386_, v___y_6393_, v___y_6382_, v___y_6384_, v___x_6404_, v___y_6390_, v___y_6391_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
lean_dec_ref(v___y_6386_);
v___y_6322_ = v___y_6383_;
v___y_6323_ = v___y_6385_;
v___y_6324_ = v___y_6391_;
v___y_6325_ = v___x_6405_;
goto v___jp_6321_;
}
v___jp_6406_:
{
lean_object* v___x_6417_; lean_object* v_a_6418_; lean_object* v___x_6419_; uint8_t v___x_6420_; 
v___x_6417_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v_a_6318_);
v_a_6418_ = lean_ctor_get(v___x_6417_, 0);
lean_inc(v_a_6418_);
lean_dec_ref(v___x_6417_);
v___x_6419_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6420_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6410_, v___x_6419_);
if (v___x_6420_ == 0)
{
lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6421_ = lean_io_mono_nanos_now();
lean_inc(v_a_6318_);
lean_inc_ref(v_a_6317_);
lean_inc(v_a_6316_);
lean_inc_ref(v_a_6315_);
lean_inc(v___y_6414_);
lean_inc_ref(v___y_6413_);
v___x_6422_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6320_, v___y_6413_, v___y_6414_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
if (lean_obj_tag(v___x_6422_) == 0)
{
lean_object* v_a_6423_; lean_object* v___x_6425_; uint8_t v_isShared_6426_; uint8_t v_isSharedCheck_6430_; 
v_a_6423_ = lean_ctor_get(v___x_6422_, 0);
v_isSharedCheck_6430_ = !lean_is_exclusive(v___x_6422_);
if (v_isSharedCheck_6430_ == 0)
{
v___x_6425_ = v___x_6422_;
v_isShared_6426_ = v_isSharedCheck_6430_;
goto v_resetjp_6424_;
}
else
{
lean_inc(v_a_6423_);
lean_dec(v___x_6422_);
v___x_6425_ = lean_box(0);
v_isShared_6426_ = v_isSharedCheck_6430_;
goto v_resetjp_6424_;
}
v_resetjp_6424_:
{
lean_object* v___x_6428_; 
if (v_isShared_6426_ == 0)
{
lean_ctor_set_tag(v___x_6425_, 1);
v___x_6428_ = v___x_6425_;
goto v_reusejp_6427_;
}
else
{
lean_object* v_reuseFailAlloc_6429_; 
v_reuseFailAlloc_6429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6429_, 0, v_a_6423_);
v___x_6428_ = v_reuseFailAlloc_6429_;
goto v_reusejp_6427_;
}
v_reusejp_6427_:
{
v___y_6382_ = v_a_6418_;
v___y_6383_ = v___y_6407_;
v___y_6384_ = v___y_6408_;
v___y_6385_ = v___y_6409_;
v___y_6386_ = v___y_6410_;
v___y_6387_ = v___x_6421_;
v___y_6388_ = v___y_6412_;
v___y_6389_ = v___y_6411_;
v___y_6390_ = v___y_6413_;
v___y_6391_ = v___y_6414_;
v___y_6392_ = v___y_6415_;
v___y_6393_ = v___y_6416_;
v_a_6394_ = v___x_6428_;
goto v___jp_6381_;
}
}
}
else
{
lean_object* v_a_6431_; lean_object* v___x_6433_; uint8_t v_isShared_6434_; uint8_t v_isSharedCheck_6438_; 
v_a_6431_ = lean_ctor_get(v___x_6422_, 0);
v_isSharedCheck_6438_ = !lean_is_exclusive(v___x_6422_);
if (v_isSharedCheck_6438_ == 0)
{
v___x_6433_ = v___x_6422_;
v_isShared_6434_ = v_isSharedCheck_6438_;
goto v_resetjp_6432_;
}
else
{
lean_inc(v_a_6431_);
lean_dec(v___x_6422_);
v___x_6433_ = lean_box(0);
v_isShared_6434_ = v_isSharedCheck_6438_;
goto v_resetjp_6432_;
}
v_resetjp_6432_:
{
lean_object* v___x_6436_; 
if (v_isShared_6434_ == 0)
{
lean_ctor_set_tag(v___x_6433_, 0);
v___x_6436_ = v___x_6433_;
goto v_reusejp_6435_;
}
else
{
lean_object* v_reuseFailAlloc_6437_; 
v_reuseFailAlloc_6437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6437_, 0, v_a_6431_);
v___x_6436_ = v_reuseFailAlloc_6437_;
goto v_reusejp_6435_;
}
v_reusejp_6435_:
{
v___y_6382_ = v_a_6418_;
v___y_6383_ = v___y_6407_;
v___y_6384_ = v___y_6408_;
v___y_6385_ = v___y_6409_;
v___y_6386_ = v___y_6410_;
v___y_6387_ = v___x_6421_;
v___y_6388_ = v___y_6412_;
v___y_6389_ = v___y_6411_;
v___y_6390_ = v___y_6413_;
v___y_6391_ = v___y_6414_;
v___y_6392_ = v___y_6415_;
v___y_6393_ = v___y_6416_;
v_a_6394_ = v___x_6436_;
goto v___jp_6381_;
}
}
}
}
else
{
lean_object* v___x_6439_; lean_object* v___x_6440_; 
v___x_6439_ = lean_io_get_num_heartbeats();
lean_inc(v_a_6318_);
lean_inc_ref(v_a_6317_);
lean_inc(v_a_6316_);
lean_inc_ref(v_a_6315_);
lean_inc(v___y_6414_);
lean_inc_ref(v___y_6413_);
v___x_6440_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6320_, v___y_6413_, v___y_6414_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
if (lean_obj_tag(v___x_6440_) == 0)
{
lean_object* v_a_6441_; lean_object* v___x_6443_; uint8_t v_isShared_6444_; uint8_t v_isSharedCheck_6448_; 
v_a_6441_ = lean_ctor_get(v___x_6440_, 0);
v_isSharedCheck_6448_ = !lean_is_exclusive(v___x_6440_);
if (v_isSharedCheck_6448_ == 0)
{
v___x_6443_ = v___x_6440_;
v_isShared_6444_ = v_isSharedCheck_6448_;
goto v_resetjp_6442_;
}
else
{
lean_inc(v_a_6441_);
lean_dec(v___x_6440_);
v___x_6443_ = lean_box(0);
v_isShared_6444_ = v_isSharedCheck_6448_;
goto v_resetjp_6442_;
}
v_resetjp_6442_:
{
lean_object* v___x_6446_; 
if (v_isShared_6444_ == 0)
{
lean_ctor_set_tag(v___x_6443_, 1);
v___x_6446_ = v___x_6443_;
goto v_reusejp_6445_;
}
else
{
lean_object* v_reuseFailAlloc_6447_; 
v_reuseFailAlloc_6447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_a_6441_);
v___x_6446_ = v_reuseFailAlloc_6447_;
goto v_reusejp_6445_;
}
v_reusejp_6445_:
{
v___y_6360_ = v_a_6418_;
v___y_6361_ = v___y_6407_;
v___y_6362_ = v___y_6408_;
v___y_6363_ = v___y_6409_;
v___y_6364_ = v___y_6410_;
v___y_6365_ = v___y_6412_;
v___y_6366_ = v___y_6411_;
v___y_6367_ = v___y_6413_;
v___y_6368_ = v___y_6414_;
v___y_6369_ = v___y_6415_;
v___y_6370_ = v___y_6416_;
v___y_6371_ = v___x_6439_;
v_a_6372_ = v___x_6446_;
goto v___jp_6359_;
}
}
}
else
{
lean_object* v_a_6449_; lean_object* v___x_6451_; uint8_t v_isShared_6452_; uint8_t v_isSharedCheck_6456_; 
v_a_6449_ = lean_ctor_get(v___x_6440_, 0);
v_isSharedCheck_6456_ = !lean_is_exclusive(v___x_6440_);
if (v_isSharedCheck_6456_ == 0)
{
v___x_6451_ = v___x_6440_;
v_isShared_6452_ = v_isSharedCheck_6456_;
goto v_resetjp_6450_;
}
else
{
lean_inc(v_a_6449_);
lean_dec(v___x_6440_);
v___x_6451_ = lean_box(0);
v_isShared_6452_ = v_isSharedCheck_6456_;
goto v_resetjp_6450_;
}
v_resetjp_6450_:
{
lean_object* v___x_6454_; 
if (v_isShared_6452_ == 0)
{
lean_ctor_set_tag(v___x_6451_, 0);
v___x_6454_ = v___x_6451_;
goto v_reusejp_6453_;
}
else
{
lean_object* v_reuseFailAlloc_6455_; 
v_reuseFailAlloc_6455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6455_, 0, v_a_6449_);
v___x_6454_ = v_reuseFailAlloc_6455_;
goto v_reusejp_6453_;
}
v_reusejp_6453_:
{
v___y_6360_ = v_a_6418_;
v___y_6361_ = v___y_6407_;
v___y_6362_ = v___y_6408_;
v___y_6363_ = v___y_6409_;
v___y_6364_ = v___y_6410_;
v___y_6365_ = v___y_6412_;
v___y_6366_ = v___y_6411_;
v___y_6367_ = v___y_6413_;
v___y_6368_ = v___y_6414_;
v___y_6369_ = v___y_6415_;
v___y_6370_ = v___y_6416_;
v___y_6371_ = v___x_6439_;
v_a_6372_ = v___x_6454_;
goto v___jp_6359_;
}
}
}
}
}
v___jp_6457_:
{
size_t v_sz_6459_; size_t v___x_6460_; lean_object* v_assignments_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v_funVals_6464_; lean_object* v_state_6465_; lean_object* v___x_6466_; lean_object* v_options_6467_; uint8_t v_hasTrace_6468_; lean_object* v_ctx_6469_; 
v_sz_6459_ = lean_array_size(v___y_6458_);
v___x_6460_ = ((size_t)0ULL);
lean_inc_ref(v___y_6458_);
v_assignments_6461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6459_, v___x_6460_, v___y_6458_);
v___x_6462_ = lean_array_get_size(v___y_6458_);
v___x_6463_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6464_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6458_, v___x_6462_, v___x_6462_, v___x_6463_);
v_state_6465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6465_, 0, v_assignments_6461_);
lean_ctor_set(v_state_6465_, 1, v_funVals_6464_);
v___x_6466_ = lean_st_mk_ref(v_state_6465_);
v_options_6467_ = lean_ctor_get(v_a_6317_, 2);
v_hasTrace_6468_ = lean_ctor_get_uint8(v_options_6467_, sizeof(void*)*1);
lean_inc_ref(v___y_6458_);
v_ctx_6469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6469_, 0, v___y_6458_);
lean_ctor_set(v_ctx_6469_, 1, v___x_6320_);
if (v_hasTrace_6468_ == 0)
{
lean_object* v___x_6470_; 
lean_inc(v_a_6318_);
lean_inc_ref(v_a_6317_);
lean_inc(v_a_6316_);
lean_inc_ref(v_a_6315_);
lean_inc(v___x_6466_);
v___x_6470_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6320_, v_ctx_6469_, v___x_6466_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
v___y_6322_ = v___x_6462_;
v___y_6323_ = v___y_6458_;
v___y_6324_ = v___x_6466_;
v___y_6325_ = v___x_6470_;
goto v___jp_6321_;
}
else
{
lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v_a_6473_; lean_object* v___f_6474_; lean_object* v___x_6475_; uint8_t v___x_6476_; 
v___x_6471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_6472_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___x_6471_, v_a_6317_);
v_a_6473_ = lean_ctor_get(v___x_6472_, 0);
lean_inc(v_a_6473_);
lean_dec_ref(v___x_6472_);
lean_inc_ref(v___y_6458_);
v___f_6474_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6474_, 0, v___y_6458_);
v___x_6475_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
v___x_6476_ = lean_unbox(v_a_6473_);
if (v___x_6476_ == 0)
{
lean_object* v___x_6477_; uint8_t v___x_6478_; 
v___x_6477_ = l_Lean_trace_profiler;
v___x_6478_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_options_6467_, v___x_6477_);
if (v___x_6478_ == 0)
{
lean_object* v___x_6479_; 
lean_dec_ref(v___f_6474_);
lean_dec(v_a_6473_);
lean_inc(v_a_6318_);
lean_inc_ref(v_a_6317_);
lean_inc(v_a_6316_);
lean_inc_ref(v_a_6315_);
lean_inc(v___x_6466_);
v___x_6479_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6320_, v_ctx_6469_, v___x_6466_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
v___y_6322_ = v___x_6462_;
v___y_6323_ = v___y_6458_;
v___y_6324_ = v___x_6466_;
v___y_6325_ = v___x_6479_;
goto v___jp_6321_;
}
else
{
uint8_t v___x_6480_; 
v___x_6480_ = lean_unbox(v_a_6473_);
lean_dec(v_a_6473_);
lean_inc_ref(v_options_6467_);
v___y_6407_ = v___x_6462_;
v___y_6408_ = v___f_6474_;
v___y_6409_ = v___y_6458_;
v___y_6410_ = v_options_6467_;
v___y_6411_ = v___x_6471_;
v___y_6412_ = v___x_6475_;
v___y_6413_ = v_ctx_6469_;
v___y_6414_ = v___x_6466_;
v___y_6415_ = v_hasTrace_6468_;
v___y_6416_ = v___x_6480_;
goto v___jp_6406_;
}
}
else
{
uint8_t v___x_6481_; 
v___x_6481_ = lean_unbox(v_a_6473_);
lean_dec(v_a_6473_);
lean_inc_ref(v_options_6467_);
v___y_6407_ = v___x_6462_;
v___y_6408_ = v___f_6474_;
v___y_6409_ = v___y_6458_;
v___y_6410_ = v_options_6467_;
v___y_6411_ = v___x_6471_;
v___y_6412_ = v___x_6475_;
v___y_6413_ = v_ctx_6469_;
v___y_6414_ = v___x_6466_;
v___y_6415_ = v_hasTrace_6468_;
v___y_6416_ = v___x_6481_;
goto v___jp_6406_;
}
}
}
v___jp_6482_:
{
lean_object* v___x_6485_; 
v___x_6485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_decls_6314_, v___y_6483_, v___y_6484_);
lean_dec(v___y_6484_);
v___y_6458_ = v___x_6485_;
goto v___jp_6457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6494_, lean_object* v_a_6495_, lean_object* v_a_6496_, lean_object* v_a_6497_, lean_object* v_a_6498_, lean_object* v_a_6499_){
_start:
{
lean_object* v_res_6500_; 
v_res_6500_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6494_, v_a_6495_, v_a_6496_, v_a_6497_, v_a_6498_);
return v_res_6500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6501_, lean_object* v_n_6502_, lean_object* v_j_6503_, lean_object* v_a_6504_, lean_object* v_a_6505_){
_start:
{
lean_object* v___x_6506_; 
v___x_6506_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6501_, v_n_6502_, v_j_6503_, v_a_6505_);
return v___x_6506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6507_, lean_object* v_n_6508_, lean_object* v_j_6509_, lean_object* v_a_6510_, lean_object* v_a_6511_){
_start:
{
lean_object* v_res_6512_; 
v_res_6512_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6507_, v_n_6508_, v_j_6509_, v_a_6510_, v_a_6511_);
lean_dec(v_n_6508_);
lean_dec_ref(v___y_6507_);
return v_res_6512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6513_, lean_object* v___x_6514_, lean_object* v_n_6515_, lean_object* v_j_6516_, lean_object* v_a_6517_, lean_object* v_a_6518_){
_start:
{
lean_object* v___x_6519_; 
v___x_6519_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6513_, v___x_6514_, v_n_6515_, v_j_6516_, v_a_6518_);
return v___x_6519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6520_, lean_object* v___x_6521_, lean_object* v_n_6522_, lean_object* v_j_6523_, lean_object* v_a_6524_, lean_object* v_a_6525_){
_start:
{
lean_object* v_res_6526_; 
v_res_6526_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6520_, v___x_6521_, v_n_6522_, v_j_6523_, v_a_6524_, v_a_6525_);
lean_dec(v_n_6522_);
lean_dec_ref(v___x_6521_);
lean_dec_ref(v___y_6520_);
return v_res_6526_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6527_, lean_object* v_as_6528_, lean_object* v_i_6529_, lean_object* v_j_6530_, lean_object* v_inv_6531_, lean_object* v_bs_6532_, lean_object* v___y_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_){
_start:
{
lean_object* v___x_6538_; 
v___x_6538_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6527_, v_as_6528_, v_i_6529_, v_j_6530_, v_bs_6532_, v___y_6533_, v___y_6534_, v___y_6535_, v___y_6536_);
return v___x_6538_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6539_, lean_object* v_as_6540_, lean_object* v_i_6541_, lean_object* v_j_6542_, lean_object* v_inv_6543_, lean_object* v_bs_6544_, lean_object* v___y_6545_, lean_object* v___y_6546_, lean_object* v___y_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_){
_start:
{
lean_object* v_res_6550_; 
v_res_6550_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6539_, v_as_6540_, v_i_6541_, v_j_6542_, v_inv_6543_, v_bs_6544_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_);
lean_dec_ref(v_as_6540_);
lean_dec_ref(v___x_6539_);
return v_res_6550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6551_, lean_object* v_as_6552_, lean_object* v_lo_6553_, lean_object* v_hi_6554_, lean_object* v_w_6555_, lean_object* v_hlo_6556_, lean_object* v_hhi_6557_){
_start:
{
lean_object* v___x_6558_; 
v___x_6558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_as_6552_, v_lo_6553_, v_hi_6554_);
return v___x_6558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6559_, lean_object* v_as_6560_, lean_object* v_lo_6561_, lean_object* v_hi_6562_, lean_object* v_w_6563_, lean_object* v_hlo_6564_, lean_object* v_hhi_6565_){
_start:
{
lean_object* v_res_6566_; 
v_res_6566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6559_, v_as_6560_, v_lo_6561_, v_hi_6562_, v_w_6563_, v_hlo_6564_, v_hhi_6565_);
lean_dec(v_hi_6562_);
lean_dec(v_n_6559_);
return v_res_6566_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; 
v___x_6626_ = lean_unsigned_to_nat(3955956072u);
v___x_6627_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6628_ = l_Lean_Name_num___override(v___x_6627_, v___x_6626_);
return v___x_6628_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; 
v___x_6630_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6631_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6632_ = l_Lean_Name_str___override(v___x_6631_, v___x_6630_);
return v___x_6632_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; 
v___x_6634_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6635_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6636_ = l_Lean_Name_str___override(v___x_6635_, v___x_6634_);
return v___x_6636_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; 
v___x_6637_ = lean_unsigned_to_nat(2u);
v___x_6638_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6639_ = l_Lean_Name_num___override(v___x_6638_, v___x_6637_);
return v___x_6639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6641_; uint8_t v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; 
v___x_6641_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_6642_ = 1;
v___x_6643_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6644_ = l_Lean_registerTraceClass(v___x_6641_, v___x_6642_, v___x_6643_);
return v___x_6644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6645_){
_start:
{
lean_object* v_res_6646_; 
v_res_6646_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6646_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue_default = _init_l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue_default);
l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue = _init_l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue();
lean_mark_persistent(l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue);
l_Lean_Compiler_LCNF_UnreachableBranches_Value_maxValueDepth = _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_maxValueDepth();
lean_mark_persistent(l_Lean_Compiler_LCNF_UnreachableBranches_Value_maxValueDepth);
res = l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin);
}
#ifdef __cplusplus
}
#endif
