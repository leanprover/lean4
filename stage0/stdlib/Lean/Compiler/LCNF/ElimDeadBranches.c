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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Format_join(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(uint8_t, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
uint8_t l_Prod_lexLtDec___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default(uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "UnreachableBranches"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "functionSummariesExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 130, 135, 69, 155, 14, 96, 131)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 217, 249, 17, 195, 152, 212, 89)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Analyzing "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elimDeadBranches"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 80, 110, 205, 32, 43, 118, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Threw away cases "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " branch "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Compiler_LCNF_elimDeadBranches___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 204, 232, 255, 130, 130, 66, 205)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ElimDeadBranches"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 48, 204, 64, 9, 167, 133, 249)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(200, 150, 161, 93, 149, 239, 245, 119)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 115, 55, 70, 37, 185, 29, 189)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 112, 73, 71, 157, 233, 191, 127)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 232, 253, 11, 187, 111, 207, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 23, 231, 170, 231, 155, 87, 99)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 213, 22, 254, 230, 125, 90, 112)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 11, 80, 195, 104, 227, 74, 88)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 249, 148, 177, 5, 97, 125, 57)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 90, 29, 229, 248, 57, 61, 64)}};
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
lean_inc_n(v_vs_105_, 2);
lean_dec_ref(v_x_89_);
v_vs_106_ = lean_ctor_get(v_x_90_, 0);
lean_inc_n(v_vs_106_, 2);
lean_dec_ref(v_x_90_);
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
v___x_289_ = lean_panic_fn_borrowed(v___x_288_, v_msg_276_);
lean_dec(v___x_288_);
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
v___x_389_ = lean_panic_fn_borrowed(v___x_388_, v_msg_376_);
lean_dec(v___x_388_);
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
v___x_447_ = lean_panic_fn_borrowed(v___x_446_, v_msg_445_);
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
lean_inc_ref_n(v_env_895_, 2);
v___x_901_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_895_, v_head_899_, v_x_896_);
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
v___x_947_ = lean_panic_fn_borrowed(v___x_946_, v_msg_945_);
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
v___x_984_ = l_instMonadEIO(lean_box(0));
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
v___x_995_ = l_StateRefT_x27_instMonad___redArg(v___x_994_);
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
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___x_1978__overap_1025_; lean_object* v___x_1026_; 
v___x_1019_ = l_StateRefT_x27_instMonad___redArg(v___x_1018_);
v___x_1020_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_instInhabitedOfMonad___redArg(v___x_1019_, v___x_1022_);
v___f_1024_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1024_, 0, v___x_1023_);
v___x_1978__overap_1025_ = lean_panic_fn_borrowed(v___f_1024_, v_msg_988_);
lean_dec_ref(v___f_1024_);
lean_inc(v___y_992_);
lean_inc_ref(v___y_991_);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
v___x_1026_ = lean_apply_5(v___x_1978__overap_1025_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, lean_box(0));
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
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
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
lean_inc_ref(v_str_1193_);
lean_inc(v_pre_1192_);
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
v___y_1099_ = v___y_1155_;
v___y_1100_ = v___y_1154_;
v___y_1101_ = v___y_1156_;
v___y_1102_ = v___y_1157_;
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
v___y_1099_ = v___y_1155_;
v___y_1100_ = v___y_1154_;
v___y_1101_ = v___y_1156_;
v___y_1102_ = v___y_1157_;
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
v___y_1132_ = v___y_1155_;
v___y_1133_ = v___y_1154_;
v___y_1134_ = v___y_1156_;
v___y_1135_ = v_ctorName_1153_;
v___y_1136_ = v___y_1157_;
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
v___y_1132_ = v___y_1155_;
v___y_1133_ = v___y_1154_;
v___y_1134_ = v___y_1156_;
v___y_1135_ = v_ctorName_1153_;
v___y_1136_ = v___y_1157_;
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
v___x_1110_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1106_, v___x_1108_, v___x_1109_, v___y_1100_, v___y_1099_, v___y_1101_, v___y_1102_);
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
v___y_1101_ = v___y_1134_;
v___y_1102_ = v___y_1136_;
v___y_1103_ = v___y_1135_;
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
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_bs_1274_);
return v___x_1281_;
}
else
{
lean_object* v_v_1282_; lean_object* v___x_1283_; 
v_v_1282_ = lean_array_uget_borrowed(v_bs_1274_, v_i_1273_);
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
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
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
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_es_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_array_mk(v_es_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1392_, lean_object* v_i_1393_, lean_object* v_k_1394_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1402_, lean_object* v_i_1403_, lean_object* v_k_1404_){
_start:
{
uint8_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1402_, v_i_1403_, v_k_1404_);
lean_dec(v_k_1404_);
lean_dec_ref(v_keys_1402_);
v_r_1406_ = lean_box(v_res_1405_);
return v_r_1406_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; 
v___x_1407_ = ((size_t)5ULL);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_shift_left(v___x_1408_, v___x_1407_);
return v___x_1409_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; 
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_1412_ = lean_usize_sub(v___x_1411_, v___x_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1413_, size_t v_x_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v_es_1416_; lean_object* v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; size_t v___x_1420_; lean_object* v_j_1421_; lean_object* v___x_1422_; 
v_es_1416_ = lean_ctor_get(v_x_1413_, 0);
v___x_1417_ = lean_box(2);
v___x_1418_ = ((size_t)5ULL);
v___x_1419_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1420_ = lean_usize_land(v_x_1414_, v___x_1419_);
v_j_1421_ = lean_usize_to_nat(v___x_1420_);
v___x_1422_ = lean_array_get_borrowed(v___x_1417_, v_es_1416_, v_j_1421_);
lean_dec(v_j_1421_);
switch(lean_obj_tag(v___x_1422_))
{
case 0:
{
lean_object* v_key_1423_; uint8_t v___x_1424_; 
v_key_1423_ = lean_ctor_get(v___x_1422_, 0);
v___x_1424_ = lean_name_eq(v_x_1415_, v_key_1423_);
return v___x_1424_;
}
case 1:
{
lean_object* v_node_1425_; size_t v___x_1426_; 
v_node_1425_ = lean_ctor_get(v___x_1422_, 0);
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
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1429_, v___x_1430_, v_x_1415_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
size_t v_x_1078__boxed_1435_; uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_x_1078__boxed_1435_ = lean_unbox_usize(v_x_1433_);
lean_dec(v_x_1433_);
v_res_1436_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1432_, v_x_1078__boxed_1435_, v_x_1434_);
lean_dec(v_x_1434_);
lean_dec_ref(v_x_1432_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1438_; uint64_t v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1723u);
v___x_1439_ = lean_uint64_of_nat(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
uint64_t v___y_1443_; 
if (lean_obj_tag(v_x_1441_) == 0)
{
uint64_t v___x_1446_; 
v___x_1446_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
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
v___x_1445_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1440_, v___x_1444_, v_x_1441_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1448_, v_x_1449_);
lean_dec(v_x_1449_);
lean_dec_ref(v_x_1448_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x1_1452_, lean_object* v_x2_1453_){
_start:
{
lean_object* v_fst_1454_; uint8_t v___x_1455_; 
v_fst_1454_ = lean_ctor_get(v_x2_1453_, 0);
v___x_1455_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x1_1452_, v_fst_1454_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x1_1458_, lean_object* v_x2_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x1_1458_, v_x2_1459_);
lean_dec_ref(v_x2_1459_);
lean_dec_ref(v_x1_1458_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1462_, lean_object* v_keys_1463_, lean_object* v_vals_1464_, lean_object* v_i_1465_, lean_object* v_acc_1466_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_array_get_size(v_keys_1463_);
v___x_1468_ = lean_nat_dec_lt(v_i_1465_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_dec(v_i_1465_);
lean_dec(v_f_1462_);
return v_acc_1466_;
}
else
{
lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_k_1469_ = lean_array_fget_borrowed(v_keys_1463_, v_i_1465_);
v_v_1470_ = lean_array_fget_borrowed(v_vals_1464_, v_i_1465_);
lean_inc(v_f_1462_);
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
v___x_1471_ = lean_apply_3(v_f_1462_, v_acc_1466_, v_k_1469_, v_v_1470_);
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_add(v_i_1465_, v___x_1472_);
lean_dec(v_i_1465_);
v_i_1465_ = v___x_1473_;
v_acc_1466_ = v___x_1471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_i_1478_, lean_object* v_acc_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1475_, v_keys_1476_, v_vals_1477_, v_i_1478_, v_acc_1479_);
lean_dec_ref(v_vals_1477_);
lean_dec_ref(v_keys_1476_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 0)
{
lean_object* v_es_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_es_1484_ = lean_ctor_get(v_x_1482_, 0);
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = lean_array_get_size(v_es_1484_);
v___x_1487_ = lean_nat_dec_lt(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_dec(v_f_1481_);
return v_x_1483_;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_le(v___x_1486_, v___x_1486_);
if (v___x_1488_ == 0)
{
if (v___x_1487_ == 0)
{
lean_dec(v_f_1481_);
return v_x_1483_;
}
else
{
size_t v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = ((size_t)0ULL);
v___x_1490_ = lean_usize_of_nat(v___x_1486_);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1481_, v_es_1484_, v___x_1489_, v___x_1490_, v_x_1483_);
return v___x_1491_;
}
}
else
{
size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = lean_usize_of_nat(v___x_1486_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1481_, v_es_1484_, v___x_1492_, v___x_1493_, v_x_1483_);
return v___x_1494_;
}
}
}
else
{
lean_object* v_ks_1495_; lean_object* v_vs_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_ks_1495_ = lean_ctor_get(v_x_1482_, 0);
v_vs_1496_ = lean_ctor_get(v_x_1482_, 1);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1481_, v_ks_1495_, v_vs_1496_, v___x_1497_, v_x_1483_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(lean_object* v_f_1499_, lean_object* v_as_1500_, size_t v_i_1501_, size_t v_stop_1502_, lean_object* v_b_1503_){
_start:
{
lean_object* v___y_1505_; uint8_t v___x_1509_; 
v___x_1509_ = lean_usize_dec_eq(v_i_1501_, v_stop_1502_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_array_uget_borrowed(v_as_1500_, v_i_1501_);
switch(lean_obj_tag(v___x_1510_))
{
case 0:
{
lean_object* v_key_1511_; lean_object* v_val_1512_; lean_object* v___x_1513_; 
v_key_1511_ = lean_ctor_get(v___x_1510_, 0);
v_val_1512_ = lean_ctor_get(v___x_1510_, 1);
lean_inc(v_f_1499_);
lean_inc(v_val_1512_);
lean_inc(v_key_1511_);
v___x_1513_ = lean_apply_3(v_f_1499_, v_b_1503_, v_key_1511_, v_val_1512_);
v___y_1505_ = v___x_1513_;
goto v___jp_1504_;
}
case 1:
{
lean_object* v_node_1514_; lean_object* v___x_1515_; 
v_node_1514_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_f_1499_);
v___x_1515_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1499_, v_node_1514_, v_b_1503_);
v___y_1505_ = v___x_1515_;
goto v___jp_1504_;
}
default: 
{
v___y_1505_ = v_b_1503_;
goto v___jp_1504_;
}
}
}
else
{
lean_dec(v_f_1499_);
return v_b_1503_;
}
v___jp_1504_:
{
size_t v___x_1506_; size_t v___x_1507_; 
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1501_, v___x_1506_);
v_i_1501_ = v___x_1507_;
v_b_1503_ = v___y_1505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_f_1516_, lean_object* v_as_1517_, lean_object* v_i_1518_, lean_object* v_stop_1519_, lean_object* v_b_1520_){
_start:
{
size_t v_i_boxed_1521_; size_t v_stop_boxed_1522_; lean_object* v_res_1523_; 
v_i_boxed_1521_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_stop_boxed_1522_ = lean_unbox_usize(v_stop_1519_);
lean_dec(v_stop_1519_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1516_, v_as_1517_, v_i_boxed_1521_, v_stop_boxed_1522_, v_b_1520_);
lean_dec_ref(v_as_1517_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1524_, v_x_1525_, v_x_1526_);
lean_dec_ref(v_x_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1528_, lean_object* v_x1_1529_, lean_object* v_x2_1530_, lean_object* v_x3_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_apply_3(v_f_1528_, v_x1_1529_, v_x2_1530_, v_x3_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1533_, lean_object* v_f_1534_, lean_object* v_init_1535_){
_start:
{
lean_object* v___f_1536_; lean_object* v___x_1537_; 
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1536_, 0, v_f_1534_);
v___x_1537_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1536_, v_map_1533_, v_init_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1538_, lean_object* v_f_1539_, lean_object* v_init_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1538_, v_f_1539_, v_init_1540_);
lean_dec_ref(v_map_1538_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1542_, lean_object* v_k_1543_, lean_object* v_v_1544_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_k_1543_);
lean_ctor_set(v___x_1545_, 1, v_v_1544_);
v___x_1546_ = lean_array_push(v_ps_1542_, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1550_){
_start:
{
lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___f_1551_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1552_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1553_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1550_, v___f_1551_, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1554_);
lean_dec_ref(v_m_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_fst_1558_; lean_object* v_fst_1559_; uint8_t v___x_1560_; 
v_fst_1558_ = lean_ctor_get(v___y_1556_, 0);
v_fst_1559_ = lean_ctor_get(v___y_1557_, 0);
v___x_1560_ = l_Lean_Name_quickLt(v_fst_1558_, v_fst_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_res_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1561_, v___y_1562_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_1566_, lean_object* v_lo_1567_, lean_object* v_hi_1568_){
_start:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_lt(v_lo_1567_, v_hi_1568_);
if (v___x_1569_ == 0)
{
lean_dec(v_lo_1567_);
return v_as_1566_;
}
else
{
lean_object* v___f_1570_; lean_object* v___x_1571_; lean_object* v_fst_1572_; lean_object* v_snd_1573_; uint8_t v___x_1574_; 
v___f_1570_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_1567_);
v___x_1571_ = l_Array_qpartition___redArg(v_as_1566_, v___f_1570_, v_lo_1567_, v_hi_1568_);
v_fst_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_fst_1572_);
v_snd_1573_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_snd_1573_);
lean_dec_ref(v___x_1571_);
v___x_1574_ = lean_nat_dec_le(v_hi_1568_, v_fst_1572_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_snd_1573_, v_lo_1567_, v_fst_1572_);
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_add(v_fst_1572_, v___x_1576_);
lean_dec(v_fst_1572_);
v_as_1566_ = v___x_1575_;
v_lo_1567_ = v___x_1577_;
goto _start;
}
else
{
lean_dec(v_fst_1572_);
lean_dec(v_lo_1567_);
return v_snd_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_1579_, lean_object* v_lo_1580_, lean_object* v_hi_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_as_1579_, v_lo_1580_, v_hi_1581_);
lean_dec(v_hi_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1585_, lean_object* v_s_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1588_ = lean_unsigned_to_nat(0u);
v___x_1589_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1590_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1586_);
v___x_1596_ = lean_array_get_size(v___x_1590_);
v___x_1597_ = lean_nat_dec_eq(v___x_1596_, v___x_1588_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___y_1601_; uint8_t v___x_1603_; 
v___x_1598_ = lean_unsigned_to_nat(1u);
v___x_1599_ = lean_nat_sub(v___x_1596_, v___x_1598_);
v___x_1603_ = lean_nat_dec_le(v___x_1588_, v___x_1599_);
if (v___x_1603_ == 0)
{
lean_inc(v___x_1599_);
v___y_1601_ = v___x_1599_;
goto v___jp_1600_;
}
else
{
v___y_1601_ = v___x_1588_;
goto v___jp_1600_;
}
v___jp_1600_:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_le(v___y_1601_, v___x_1599_);
if (v___x_1602_ == 0)
{
lean_dec(v___x_1599_);
lean_inc(v___y_1601_);
v___y_1592_ = v___y_1601_;
v___y_1593_ = v___y_1601_;
goto v___jp_1591_;
}
else
{
v___y_1592_ = v___y_1601_;
v___y_1593_ = v___x_1599_;
goto v___jp_1591_;
}
}
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1589_);
lean_ctor_set(v___x_1604_, 1, v___x_1589_);
lean_ctor_set(v___x_1604_, 2, v___x_1590_);
return v___x_1604_;
}
v___jp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1590_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
v___x_1595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1589_);
lean_ctor_set(v___x_1595_, 1, v___x_1589_);
lean_ctor_set(v___x_1595_, 2, v___x_1594_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1605_, lean_object* v_s_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1605_, v_s_1606_, v_x_1607_);
lean_dec(v_x_1607_);
lean_dec_ref(v_s_1606_);
lean_dec_ref(v_x_1605_);
return v_res_1608_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1609_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1614_);
lean_dec_ref(v_x_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v_ks_1620_; lean_object* v_vs_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1645_; 
v_ks_1620_ = lean_ctor_get(v_x_1616_, 0);
v_vs_1621_ = lean_ctor_get(v_x_1616_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1616_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1623_ = v_x_1616_;
v_isShared_1624_ = v_isSharedCheck_1645_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_vs_1621_);
lean_inc(v_ks_1620_);
lean_dec(v_x_1616_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1645_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_array_get_size(v_ks_1620_);
v___x_1626_ = lean_nat_dec_lt(v_x_1617_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_dec(v_x_1617_);
v___x_1627_ = lean_array_push(v_ks_1620_, v_x_1618_);
v___x_1628_ = lean_array_push(v_vs_1621_, v_x_1619_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 1, v___x_1628_);
lean_ctor_set(v___x_1623_, 0, v___x_1627_);
v___x_1630_ = v___x_1623_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
else
{
lean_object* v_k_x27_1632_; uint8_t v___x_1633_; 
v_k_x27_1632_ = lean_array_fget_borrowed(v_ks_1620_, v_x_1617_);
v___x_1633_ = lean_name_eq(v_x_1618_, v_k_x27_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1635_; 
if (v_isShared_1624_ == 0)
{
v___x_1635_ = v___x_1623_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_ks_1620_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_vs_1621_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_add(v_x_1617_, v___x_1636_);
lean_dec(v_x_1617_);
v_x_1616_ = v___x_1635_;
v_x_1617_ = v___x_1637_;
goto _start;
}
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1640_ = lean_array_fset(v_ks_1620_, v_x_1617_, v_x_1618_);
v___x_1641_ = lean_array_fset(v_vs_1621_, v_x_1617_, v_x_1619_);
lean_dec(v_x_1617_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 1, v___x_1641_);
lean_ctor_set(v___x_1623_, 0, v___x_1640_);
v___x_1643_ = v___x_1623_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object* v_n_1646_, lean_object* v_k_1647_, lean_object* v_v_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(v_n_1646_, v___x_1649_, v_k_1647_, v_v_1648_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_1652_, size_t v_x_1653_, size_t v_x_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1652_) == 0)
{
lean_object* v_es_1657_; size_t v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v_j_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_es_1657_ = lean_ctor_get(v_x_1652_, 0);
v___x_1658_ = ((size_t)5ULL);
v___x_1659_ = ((size_t)1ULL);
v___x_1660_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1661_ = lean_usize_land(v_x_1653_, v___x_1660_);
v_j_1662_ = lean_usize_to_nat(v___x_1661_);
v___x_1663_ = lean_array_get_size(v_es_1657_);
v___x_1664_ = lean_nat_dec_lt(v_j_1662_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_dec(v_j_1662_);
lean_dec(v_x_1656_);
lean_dec(v_x_1655_);
return v_x_1652_;
}
else
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1701_; 
lean_inc_ref(v_es_1657_);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1652_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v_x_1652_, 0);
lean_dec(v_unused_1702_);
v___x_1666_ = v_x_1652_;
v_isShared_1667_ = v_isSharedCheck_1701_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v_x_1652_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1701_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_v_1668_; lean_object* v___x_1669_; lean_object* v_xs_x27_1670_; lean_object* v___y_1672_; 
v_v_1668_ = lean_array_fget(v_es_1657_, v_j_1662_);
v___x_1669_ = lean_box(0);
v_xs_x27_1670_ = lean_array_fset(v_es_1657_, v_j_1662_, v___x_1669_);
switch(lean_obj_tag(v_v_1668_))
{
case 0:
{
lean_object* v_key_1677_; lean_object* v_val_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1688_; 
v_key_1677_ = lean_ctor_get(v_v_1668_, 0);
v_val_1678_ = lean_ctor_get(v_v_1668_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_v_1668_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1680_ = v_v_1668_;
v_isShared_1681_ = v_isSharedCheck_1688_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_val_1678_);
lean_inc(v_key_1677_);
lean_dec(v_v_1668_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1688_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_name_eq(v_x_1655_, v_key_1677_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_del_object(v___x_1680_);
v___x_1683_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1677_, v_val_1678_, v_x_1655_, v_x_1656_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___y_1672_ = v___x_1684_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1686_; 
lean_dec(v_val_1678_);
lean_dec(v_key_1677_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_x_1656_);
lean_ctor_set(v___x_1680_, 0, v_x_1655_);
v___x_1686_ = v___x_1680_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_x_1655_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_x_1656_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v___y_1672_ = v___x_1686_;
goto v___jp_1671_;
}
}
}
}
case 1:
{
lean_object* v_node_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1699_; 
v_node_1689_ = lean_ctor_get(v_v_1668_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_v_1668_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1691_ = v_v_1668_;
v_isShared_1692_ = v_isSharedCheck_1699_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_node_1689_);
lean_dec(v_v_1668_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1699_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
size_t v___x_1693_; size_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1693_ = lean_usize_shift_right(v_x_1653_, v___x_1658_);
v___x_1694_ = lean_usize_add(v_x_1654_, v___x_1659_);
v___x_1695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_1689_, v___x_1693_, v___x_1694_, v_x_1655_, v_x_1656_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1695_);
v___x_1697_ = v___x_1691_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
v___y_1672_ = v___x_1697_;
goto v___jp_1671_;
}
}
}
default: 
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_x_1655_);
lean_ctor_set(v___x_1700_, 1, v_x_1656_);
v___y_1672_ = v___x_1700_;
goto v___jp_1671_;
}
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_array_fset(v_xs_x27_1670_, v_j_1662_, v___y_1672_);
lean_dec(v_j_1662_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1673_);
v___x_1675_ = v___x_1666_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
else
{
lean_object* v_ks_1703_; lean_object* v_vs_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1724_; 
v_ks_1703_ = lean_ctor_get(v_x_1652_, 0);
v_vs_1704_ = lean_ctor_get(v_x_1652_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_x_1652_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1706_ = v_x_1652_;
v_isShared_1707_ = v_isSharedCheck_1724_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_vs_1704_);
lean_inc(v_ks_1703_);
lean_dec(v_x_1652_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1724_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_ks_1703_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_vs_1704_);
v___x_1709_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v_newNode_1710_; uint8_t v___y_1712_; size_t v___x_1718_; uint8_t v___x_1719_; 
v_newNode_1710_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v___x_1709_, v_x_1655_, v_x_1656_);
v___x_1718_ = ((size_t)7ULL);
v___x_1719_ = lean_usize_dec_le(v___x_1718_, v_x_1654_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1720_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1710_);
v___x_1721_ = lean_unsigned_to_nat(4u);
v___x_1722_ = lean_nat_dec_lt(v___x_1720_, v___x_1721_);
lean_dec(v___x_1720_);
v___y_1712_ = v___x_1722_;
goto v___jp_1711_;
}
else
{
v___y_1712_ = v___x_1719_;
goto v___jp_1711_;
}
v___jp_1711_:
{
if (v___y_1712_ == 0)
{
lean_object* v_ks_1713_; lean_object* v_vs_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_ks_1713_ = lean_ctor_get(v_newNode_1710_, 0);
lean_inc_ref(v_ks_1713_);
v_vs_1714_ = lean_ctor_get(v_newNode_1710_, 1);
lean_inc_ref(v_vs_1714_);
lean_dec_ref(v_newNode_1710_);
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_1717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_x_1654_, v_ks_1713_, v_vs_1714_, v___x_1715_, v___x_1716_);
lean_dec_ref(v_vs_1714_);
lean_dec_ref(v_ks_1713_);
return v___x_1717_;
}
else
{
return v_newNode_1710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(size_t v_depth_1725_, lean_object* v_keys_1726_, lean_object* v_vals_1727_, lean_object* v_i_1728_, lean_object* v_entries_1729_){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = lean_array_get_size(v_keys_1726_);
v___x_1731_ = lean_nat_dec_lt(v_i_1728_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_dec(v_i_1728_);
return v_entries_1729_;
}
else
{
lean_object* v_k_1732_; lean_object* v_v_1733_; uint64_t v___y_1735_; 
v_k_1732_ = lean_array_fget_borrowed(v_keys_1726_, v_i_1728_);
v_v_1733_ = lean_array_fget_borrowed(v_vals_1727_, v_i_1728_);
if (lean_obj_tag(v_k_1732_) == 0)
{
uint64_t v___x_1746_; 
v___x_1746_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1735_ = v___x_1746_;
goto v___jp_1734_;
}
else
{
uint64_t v_hash_1747_; 
v_hash_1747_ = lean_ctor_get_uint64(v_k_1732_, sizeof(void*)*2);
v___y_1735_ = v_hash_1747_;
goto v___jp_1734_;
}
v___jp_1734_:
{
size_t v_h_1736_; size_t v___x_1737_; lean_object* v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; size_t v_h_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_h_1736_ = lean_uint64_to_usize(v___y_1735_);
v___x_1737_ = ((size_t)5ULL);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_sub(v_depth_1725_, v___x_1739_);
v___x_1741_ = lean_usize_mul(v___x_1737_, v___x_1740_);
v_h_1742_ = lean_usize_shift_right(v_h_1736_, v___x_1741_);
v___x_1743_ = lean_nat_add(v_i_1728_, v___x_1738_);
lean_dec(v_i_1728_);
lean_inc(v_v_1733_);
lean_inc(v_k_1732_);
v___x_1744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_1729_, v_h_1742_, v_depth_1725_, v_k_1732_, v_v_1733_);
v_i_1728_ = v___x_1743_;
v_entries_1729_ = v___x_1744_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_1748_, lean_object* v_keys_1749_, lean_object* v_vals_1750_, lean_object* v_i_1751_, lean_object* v_entries_1752_){
_start:
{
size_t v_depth_boxed_1753_; lean_object* v_res_1754_; 
v_depth_boxed_1753_ = lean_unbox_usize(v_depth_1748_);
lean_dec(v_depth_1748_);
v_res_1754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_depth_boxed_1753_, v_keys_1749_, v_vals_1750_, v_i_1751_, v_entries_1752_);
lean_dec_ref(v_vals_1750_);
lean_dec_ref(v_keys_1749_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
size_t v_x_1440__boxed_1760_; size_t v_x_1441__boxed_1761_; lean_object* v_res_1762_; 
v_x_1440__boxed_1760_ = lean_unbox_usize(v_x_1756_);
lean_dec(v_x_1756_);
v_x_1441__boxed_1761_ = lean_unbox_usize(v_x_1757_);
lean_dec(v_x_1757_);
v_res_1762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1755_, v_x_1440__boxed_1760_, v_x_1441__boxed_1761_, v_x_1758_, v_x_1759_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
uint64_t v___y_1767_; 
if (lean_obj_tag(v_x_1764_) == 0)
{
uint64_t v___x_1771_; 
v___x_1771_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1767_ = v___x_1771_;
goto v___jp_1766_;
}
else
{
uint64_t v_hash_1772_; 
v_hash_1772_ = lean_ctor_get_uint64(v_x_1764_, sizeof(void*)*2);
v___y_1767_ = v_hash_1772_;
goto v___jp_1766_;
}
v___jp_1766_:
{
size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = lean_uint64_to_usize(v___y_1767_);
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1763_, v___x_1768_, v___x_1769_, v_x_1764_, v_x_1765_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1773_, lean_object* v_x_1774_){
_start:
{
lean_object* v_fst_1775_; lean_object* v_snd_1776_; lean_object* v___x_1777_; 
v_fst_1775_ = lean_ctor_get(v_x_1774_, 0);
lean_inc(v_fst_1775_);
v_snd_1776_ = lean_ctor_get(v_x_1774_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v_x_1774_);
v___x_1777_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1773_, v_fst_1775_, v_snd_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1811_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1813_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
uint8_t v_res_1821_; lean_object* v_r_1822_; 
v_res_1821_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1818_, v_x_1819_, v_x_1820_);
lean_dec(v_x_1820_);
lean_dec_ref(v_x_1819_);
v_r_1822_ = lean_box(v_res_1821_);
return v_r_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1823_, lean_object* v_m_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1826_, lean_object* v_m_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1826_, v_m_1827_);
lean_dec_ref(v_m_1827_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1829_, lean_object* v_as_1830_, lean_object* v_lo_1831_, lean_object* v_hi_1832_, lean_object* v_w_1833_, lean_object* v_hlo_1834_, lean_object* v_hhi_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_as_1830_, v_lo_1831_, v_hi_1832_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1837_, lean_object* v_as_1838_, lean_object* v_lo_1839_, lean_object* v_hi_1840_, lean_object* v_w_1841_, lean_object* v_hlo_1842_, lean_object* v_hhi_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1837_, v_as_1838_, v_lo_1839_, v_hi_1840_, v_w_1841_, v_hlo_1842_, v_hhi_1843_);
lean_dec(v_hi_1840_);
lean_dec(v_n_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1846_, v_x_1847_, v_x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1850_, lean_object* v_x_1851_, size_t v_x_1852_, lean_object* v_x_1853_){
_start:
{
uint8_t v___x_1854_; 
v___x_1854_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1851_, v_x_1852_, v_x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_, lean_object* v_x_1858_){
_start:
{
size_t v_x_1747__boxed_1859_; uint8_t v_res_1860_; lean_object* v_r_1861_; 
v_x_1747__boxed_1859_ = lean_unbox_usize(v_x_1857_);
lean_dec(v_x_1857_);
v_res_1860_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1855_, v_x_1856_, v_x_1747__boxed_1859_, v_x_1858_);
lean_dec(v_x_1858_);
lean_dec_ref(v_x_1856_);
v_r_1861_ = lean_box(v_res_1860_);
return v_r_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1862_, lean_object* v_00_u03b2_1863_, lean_object* v_map_1864_, lean_object* v_f_1865_, lean_object* v_init_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1864_, v_f_1865_, v_init_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1868_, lean_object* v_00_u03b2_1869_, lean_object* v_map_1870_, lean_object* v_f_1871_, lean_object* v_init_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1868_, v_00_u03b2_1869_, v_map_1870_, v_f_1871_, v_init_1872_);
lean_dec_ref(v_map_1870_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_1874_, lean_object* v_x_1875_, size_t v_x_1876_, size_t v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1875_, v_x_1876_, v_x_1877_, v_x_1878_, v_x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
size_t v_x_1760__boxed_1887_; size_t v_x_1761__boxed_1888_; lean_object* v_res_1889_; 
v_x_1760__boxed_1887_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_x_1761__boxed_1888_ = lean_unbox_usize(v_x_1884_);
lean_dec(v_x_1884_);
v_res_1889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_1881_, v_x_1882_, v_x_1760__boxed_1887_, v_x_1761__boxed_1888_, v_x_1885_, v_x_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1890_, lean_object* v_keys_1891_, lean_object* v_vals_1892_, lean_object* v_heq_1893_, lean_object* v_i_1894_, lean_object* v_k_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1891_, v_i_1894_, v_k_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1897_, lean_object* v_keys_1898_, lean_object* v_vals_1899_, lean_object* v_heq_1900_, lean_object* v_i_1901_, lean_object* v_k_1902_){
_start:
{
uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_res_1903_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1897_, v_keys_1898_, v_vals_1899_, v_heq_1900_, v_i_1901_, v_k_1902_);
lean_dec(v_k_1902_);
lean_dec_ref(v_vals_1899_);
lean_dec_ref(v_keys_1898_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1905_, lean_object* v_f_1906_, lean_object* v_init_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1906_, v_map_1905_, v_init_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1909_, lean_object* v_f_1910_, lean_object* v_init_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1909_, v_f_1910_, v_init_1911_);
lean_dec_ref(v_map_1909_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_map_1915_, lean_object* v_f_1916_, lean_object* v_init_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1916_, v_map_1915_, v_init_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_map_1921_, lean_object* v_f_1922_, lean_object* v_init_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1919_, v_00_u03b2_1920_, v_map_1921_, v_f_1922_, v_init_1923_);
lean_dec_ref(v_map_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1925_, lean_object* v_n_1926_, lean_object* v_k_1927_, lean_object* v_v_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_n_1926_, v_k_1927_, v_v_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1930_, size_t v_depth_1931_, lean_object* v_keys_1932_, lean_object* v_vals_1933_, lean_object* v_heq_1934_, lean_object* v_i_1935_, lean_object* v_entries_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_depth_1931_, v_keys_1932_, v_vals_1933_, v_i_1935_, v_entries_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1938_, lean_object* v_depth_1939_, lean_object* v_keys_1940_, lean_object* v_vals_1941_, lean_object* v_heq_1942_, lean_object* v_i_1943_, lean_object* v_entries_1944_){
_start:
{
size_t v_depth_boxed_1945_; lean_object* v_res_1946_; 
v_depth_boxed_1945_ = lean_unbox_usize(v_depth_1939_);
lean_dec(v_depth_1939_);
v_res_1946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__9(v_00_u03b2_1938_, v_depth_boxed_1945_, v_keys_1940_, v_vals_1941_, v_heq_1942_, v_i_1943_, v_entries_1944_);
lean_dec_ref(v_vals_1941_);
lean_dec_ref(v_keys_1940_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_1947_, lean_object* v_00_u03b1_1948_, lean_object* v_00_u03b2_1949_, lean_object* v_f_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1950_, v_x_1951_, v_x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_1954_, lean_object* v_00_u03b1_1955_, lean_object* v_00_u03b2_1956_, lean_object* v_f_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_1954_, v_00_u03b1_1955_, v_00_u03b2_1956_, v_f_1957_, v_x_1958_, v_x_1959_);
lean_dec_ref(v_x_1958_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(v_x_1962_, v_x_1963_, v_x_1964_, v_x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1967_, lean_object* v_00_u03b2_1968_, lean_object* v_00_u03c3_1969_, lean_object* v_f_1970_, lean_object* v_as_1971_, size_t v_i_1972_, size_t v_stop_1973_, lean_object* v_b_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1970_, v_as_1971_, v_i_1972_, v_stop_1973_, v_b_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1976_, lean_object* v_00_u03b2_1977_, lean_object* v_00_u03c3_1978_, lean_object* v_f_1979_, lean_object* v_as_1980_, lean_object* v_i_1981_, lean_object* v_stop_1982_, lean_object* v_b_1983_){
_start:
{
size_t v_i_boxed_1984_; size_t v_stop_boxed_1985_; lean_object* v_res_1986_; 
v_i_boxed_1984_ = lean_unbox_usize(v_i_1981_);
lean_dec(v_i_1981_);
v_stop_boxed_1985_ = lean_unbox_usize(v_stop_1982_);
lean_dec(v_stop_1982_);
v_res_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(v_00_u03b1_1976_, v_00_u03b2_1977_, v_00_u03c3_1978_, v_f_1979_, v_as_1980_, v_i_boxed_1984_, v_stop_boxed_1985_, v_b_1983_);
lean_dec_ref(v_as_1980_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03c3_1987_, lean_object* v_00_u03b1_1988_, lean_object* v_00_u03b2_1989_, lean_object* v_f_1990_, lean_object* v_keys_1991_, lean_object* v_vals_1992_, lean_object* v_heq_1993_, lean_object* v_i_1994_, lean_object* v_acc_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1990_, v_keys_1991_, v_vals_1992_, v_i_1994_, v_acc_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03c3_1997_, lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_f_2000_, lean_object* v_keys_2001_, lean_object* v_vals_2002_, lean_object* v_heq_2003_, lean_object* v_i_2004_, lean_object* v_acc_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03c3_1997_, v_00_u03b1_1998_, v_00_u03b2_1999_, v_f_2000_, v_keys_2001_, v_vals_2002_, v_heq_2003_, v_i_2004_, v_acc_2005_);
lean_dec_ref(v_vals_2002_);
lean_dec_ref(v_keys_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2007_, lean_object* v_fid_2008_, lean_object* v_v_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v_toEnvExtension_2011_; lean_object* v_asyncMode_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2010_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2011_ = lean_ctor_get(v___x_2010_, 0);
v_asyncMode_2012_ = lean_ctor_get(v_toEnvExtension_2011_, 2);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_fid_2008_);
lean_ctor_set(v___x_2013_, 1, v_v_2009_);
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2010_, v_env_2007_, v___x_2013_, v_asyncMode_2012_, v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2016_, lean_object* v_vals_2017_, lean_object* v_i_2018_, lean_object* v_k_2019_){
_start:
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = lean_array_get_size(v_keys_2016_);
v___x_2021_ = lean_nat_dec_lt(v_i_2018_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec(v_i_2018_);
v___x_2022_ = lean_box(0);
return v___x_2022_;
}
else
{
lean_object* v_k_x27_2023_; uint8_t v___x_2024_; 
v_k_x27_2023_ = lean_array_fget_borrowed(v_keys_2016_, v_i_2018_);
v___x_2024_ = lean_name_eq(v_k_2019_, v_k_x27_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_unsigned_to_nat(1u);
v___x_2026_ = lean_nat_add(v_i_2018_, v___x_2025_);
lean_dec(v_i_2018_);
v_i_2018_ = v___x_2026_;
goto _start;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_array_fget_borrowed(v_vals_2017_, v_i_2018_);
lean_dec(v_i_2018_);
lean_inc(v___x_2028_);
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2030_, lean_object* v_vals_2031_, lean_object* v_i_2032_, lean_object* v_k_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2030_, v_vals_2031_, v_i_2032_, v_k_2033_);
lean_dec(v_k_2033_);
lean_dec_ref(v_vals_2031_);
lean_dec_ref(v_keys_2030_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2035_, size_t v_x_2036_, lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2035_) == 0)
{
lean_object* v_es_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2059_; 
v_es_2038_ = lean_ctor_get(v_x_2035_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_x_2035_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2040_ = v_x_2035_;
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_es_2038_);
lean_dec(v_x_2035_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; lean_object* v_j_2046_; lean_object* v___x_2047_; 
v___x_2042_ = lean_box(2);
v___x_2043_ = ((size_t)5ULL);
v___x_2044_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_2045_ = lean_usize_land(v_x_2036_, v___x_2044_);
v_j_2046_ = lean_usize_to_nat(v___x_2045_);
v___x_2047_ = lean_array_get(v___x_2042_, v_es_2038_, v_j_2046_);
lean_dec(v_j_2046_);
lean_dec_ref(v_es_2038_);
switch(lean_obj_tag(v___x_2047_))
{
case 0:
{
lean_object* v_key_2048_; lean_object* v_val_2049_; uint8_t v___x_2050_; 
v_key_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_key_2048_);
v_val_2049_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_val_2049_);
lean_dec_ref(v___x_2047_);
v___x_2050_ = lean_name_eq(v_x_2037_, v_key_2048_);
lean_dec(v_key_2048_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_dec(v_val_2049_);
lean_del_object(v___x_2040_);
v___x_2051_ = lean_box(0);
return v___x_2051_;
}
else
{
lean_object* v___x_2053_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 1);
lean_ctor_set(v___x_2040_, 0, v_val_2049_);
v___x_2053_ = v___x_2040_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_val_2049_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
case 1:
{
lean_object* v_node_2055_; size_t v___x_2056_; 
lean_del_object(v___x_2040_);
v_node_2055_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_node_2055_);
lean_dec_ref(v___x_2047_);
v___x_2056_ = lean_usize_shift_right(v_x_2036_, v___x_2043_);
v_x_2035_ = v_node_2055_;
v_x_2036_ = v___x_2056_;
goto _start;
}
default: 
{
lean_object* v___x_2058_; 
lean_del_object(v___x_2040_);
v___x_2058_ = lean_box(0);
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_ks_2060_; lean_object* v_vs_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_ks_2060_ = lean_ctor_get(v_x_2035_, 0);
lean_inc_ref(v_ks_2060_);
v_vs_2061_ = lean_ctor_get(v_x_2035_, 1);
lean_inc_ref(v_vs_2061_);
lean_dec_ref(v_x_2035_);
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2060_, v_vs_2061_, v___x_2062_, v_x_2037_);
lean_dec_ref(v_vs_2061_);
lean_dec_ref(v_ks_2060_);
return v___x_2063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
size_t v_x_396__boxed_2067_; lean_object* v_res_2068_; 
v_x_396__boxed_2067_ = lean_unbox_usize(v_x_2065_);
lean_dec(v_x_2065_);
v_res_2068_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2064_, v_x_396__boxed_2067_, v_x_2066_);
lean_dec(v_x_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
uint64_t v___y_2072_; 
if (lean_obj_tag(v_x_2070_) == 0)
{
uint64_t v___x_2075_; 
v___x_2075_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_2072_ = v___x_2075_;
goto v___jp_2071_;
}
else
{
uint64_t v_hash_2076_; 
v_hash_2076_ = lean_ctor_get_uint64(v_x_2070_, sizeof(void*)*2);
v___y_2072_ = v_hash_2076_;
goto v___jp_2071_;
}
v___jp_2071_:
{
size_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_uint64_to_usize(v___y_2072_);
v___x_2074_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2069_, v___x_2073_, v_x_2070_);
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2077_, v_x_2078_);
lean_dec(v_x_2078_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2080_, lean_object* v_k_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_m_2086_; lean_object* v_a_2087_; uint8_t v___x_2088_; 
v___x_2084_ = lean_nat_add(v_x_2082_, v_x_2083_);
v___x_2085_ = lean_unsigned_to_nat(1u);
v_m_2086_ = lean_nat_shiftr(v___x_2084_, v___x_2085_);
lean_dec(v___x_2084_);
v_a_2087_ = lean_array_fget_borrowed(v_as_2080_, v_m_2086_);
v___x_2088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2087_, v_k_2081_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; 
lean_dec(v_x_2083_);
v___x_2089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2081_, v_a_2087_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v_m_2086_);
lean_dec(v_x_2082_);
lean_inc(v_a_2087_);
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_a_2087_);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_nat_dec_eq(v_m_2086_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_nat_sub(v_m_2086_, v___x_2085_);
lean_dec(v_m_2086_);
v___x_2094_ = lean_nat_dec_lt(v___x_2093_, v_x_2082_);
if (v___x_2094_ == 0)
{
v_x_2083_ = v___x_2093_;
goto _start;
}
else
{
lean_object* v___x_2096_; 
lean_dec(v___x_2093_);
lean_dec(v_x_2082_);
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
}
else
{
lean_object* v___x_2097_; 
lean_dec(v_m_2086_);
lean_dec(v_x_2082_);
v___x_2097_ = lean_box(0);
return v___x_2097_;
}
}
}
else
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
lean_dec(v_x_2082_);
v___x_2098_ = lean_nat_add(v_m_2086_, v___x_2085_);
lean_dec(v_m_2086_);
v___x_2099_ = lean_nat_dec_le(v___x_2098_, v_x_2083_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_dec(v___x_2098_);
lean_dec(v_x_2083_);
v___x_2100_ = lean_box(0);
return v___x_2100_;
}
else
{
v_x_2082_ = v___x_2098_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2102_, lean_object* v_k_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2102_, v_k_2103_, v_x_2104_, v_x_2105_);
lean_dec_ref(v_k_2103_);
lean_dec_ref(v_as_2102_);
return v_res_2106_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2110_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2111_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2110_, v___x_2109_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2115_, lean_object* v_fid_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2126_; 
v___x_2117_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2118_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2126_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2115_, v_fid_2116_);
if (lean_obj_tag(v___x_2126_) == 0)
{
goto v___jp_2119_;
}
else
{
lean_object* v_val_2127_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_val_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_val_2127_);
lean_dec_ref(v___x_2126_);
v___x_2149_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_2117_, v___x_2118_, v_env_2115_, v_val_2127_);
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = lean_array_get_size(v___x_2149_);
v___x_2152_ = lean_nat_dec_lt(v___x_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec_ref(v___x_2149_);
goto v___jp_2128_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_sub(v___x_2151_, v___x_2153_);
v___x_2155_ = lean_nat_dec_le(v___x_2150_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_dec(v___x_2154_);
lean_dec_ref(v___x_2149_);
goto v___jp_2128_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_box(0);
lean_inc(v_fid_2116_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v_fid_2116_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2149_, v___x_2157_, v___x_2150_, v___x_2154_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2149_);
if (lean_obj_tag(v___x_2158_) == 0)
{
goto v___jp_2128_;
}
else
{
lean_object* v_val_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_val_2127_);
lean_dec(v_fid_2116_);
lean_dec_ref(v_env_2115_);
v_val_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_val_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2167_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_snd_2163_; lean_object* v___x_2165_; 
v_snd_2163_ = lean_ctor_get(v_val_2159_, 1);
lean_inc(v_snd_2163_);
lean_dec(v_val_2159_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v_snd_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_snd_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
v___jp_2128_:
{
uint8_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2129_ = 0;
v___x_2130_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2117_, v___x_2118_, v_env_2115_, v_val_2127_, v___x_2129_);
lean_dec(v_val_2127_);
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = lean_array_get_size(v___x_2130_);
v___x_2133_ = lean_nat_dec_lt(v___x_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_dec_ref(v___x_2130_);
goto v___jp_2119_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2134_ = lean_unsigned_to_nat(1u);
v___x_2135_ = lean_nat_sub(v___x_2132_, v___x_2134_);
v___x_2136_ = lean_nat_dec_le(v___x_2131_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_dec(v___x_2135_);
lean_dec_ref(v___x_2130_);
goto v___jp_2119_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_box(0);
lean_inc(v_fid_2116_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_fid_2116_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2130_, v___x_2138_, v___x_2131_, v___x_2135_);
lean_dec_ref(v___x_2138_);
lean_dec_ref(v___x_2130_);
if (lean_obj_tag(v___x_2139_) == 0)
{
goto v___jp_2119_;
}
else
{
lean_object* v_val_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_fid_2116_);
lean_dec_ref(v_env_2115_);
v_val_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_val_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_snd_2144_; lean_object* v___x_2146_; 
v_snd_2144_ = lean_ctor_get(v_val_2140_, 1);
lean_inc(v_snd_2144_);
lean_dec(v_val_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v_snd_2144_);
v___x_2146_ = v___x_2142_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_snd_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
}
v___jp_2119_:
{
lean_object* v_toEnvExtension_2120_; lean_object* v_asyncMode_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_snd_2124_; lean_object* v___x_2125_; 
v_toEnvExtension_2120_ = lean_ctor_get(v___x_2118_, 0);
v_asyncMode_2121_ = lean_ctor_get(v_toEnvExtension_2120_, 2);
v___x_2122_ = lean_box(0);
v___x_2123_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2117_, v___x_2118_, v_env_2115_, v_asyncMode_2121_, v___x_2122_);
v_snd_2124_ = lean_ctor_get(v___x_2123_, 1);
lean_inc(v_snd_2124_);
lean_dec(v___x_2123_);
v___x_2125_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2124_, v_fid_2116_);
lean_dec(v_fid_2116_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2169_, v_x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2172_, v_x_2173_, v_x_2174_);
lean_dec(v_x_2174_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2176_, lean_object* v_k_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2176_, v_k_2177_, v_x_2178_, v_x_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2182_, lean_object* v_k_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_, lean_object* v_x_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2182_, v_k_2183_, v_x_2184_, v_x_2185_, v_x_2186_);
lean_dec_ref(v_k_2183_);
lean_dec_ref(v_as_2182_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2188_, lean_object* v_x_2189_, size_t v_x_2190_, lean_object* v_x_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2189_, v_x_2190_, v_x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
size_t v_x_649__boxed_2197_; lean_object* v_res_2198_; 
v_x_649__boxed_2197_ = lean_unbox_usize(v_x_2195_);
lean_dec(v_x_2195_);
v_res_2198_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2193_, v_x_2194_, v_x_649__boxed_2197_, v_x_2196_);
lean_dec(v_x_2196_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2199_, lean_object* v_keys_2200_, lean_object* v_vals_2201_, lean_object* v_heq_2202_, lean_object* v_i_2203_, lean_object* v_k_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2200_, v_vals_2201_, v_i_2203_, v_k_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2206_, lean_object* v_keys_2207_, lean_object* v_vals_2208_, lean_object* v_heq_2209_, lean_object* v_i_2210_, lean_object* v_k_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2206_, v_keys_2207_, v_vals_2208_, v_heq_2209_, v_i_2210_, v_k_2211_);
lean_dec(v_k_2211_);
lean_dec_ref(v_vals_2208_);
lean_dec_ref(v_keys_2207_);
return v_res_2212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2216_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2217_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2216_, v___x_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___x_2221_; lean_object* v_assignments_2222_; lean_object* v_currFnIdx_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2221_ = lean_st_ref_get(v_a_2219_);
v_assignments_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc_ref(v_assignments_2222_);
lean_dec(v___x_2221_);
v_currFnIdx_2223_ = lean_ctor_get(v_a_2218_, 1);
v___x_2224_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2225_ = lean_array_get(v___x_2224_, v_assignments_2222_, v_currFnIdx_2223_);
lean_dec_ref(v_assignments_2222_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2231_, v_a_2232_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v_funVals_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2250_ = lean_st_ref_get(v_a_2248_);
v_funVals_2251_ = lean_ctor_get(v___x_2250_, 1);
lean_inc_ref(v_funVals_2251_);
lean_dec(v___x_2250_);
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_array_get(v___x_2252_, v_funVals_2251_, v_funIdx_2247_);
lean_dec_ref(v_funVals_2251_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec(v_funIdx_2255_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2259_, v_a_2261_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_funIdx_2268_);
return v_res_2276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0(lean_object* v_declName_2277_, lean_object* v_x_2278_){
_start:
{
lean_object* v_toSignature_2279_; lean_object* v_name_2280_; uint8_t v___x_2281_; 
v_toSignature_2279_ = lean_ctor_get(v_x_2278_, 0);
v_name_2280_ = lean_ctor_get(v_toSignature_2279_, 0);
v___x_2281_ = lean_name_eq(v_name_2280_, v_declName_2277_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0___boxed(lean_object* v_declName_2282_, lean_object* v_x_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0(v_declName_2282_, v_x_2283_);
lean_dec_ref(v_x_2283_);
lean_dec(v_declName_2282_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_decls_2290_; lean_object* v___f_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_decls_2290_ = lean_ctor_get(v_a_2287_, 0);
v___f_2291_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2291_, 0, v_declName_2286_);
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = l_Array_findIdx_x3f_loop___redArg(v___f_2291_, v_decls_2290_, v___x_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
else
{
lean_object* v_val_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2312_; 
v_val_2296_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2298_ = v___x_2293_;
v_isShared_2299_ = v_isSharedCheck_2312_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_val_2296_);
lean_dec(v___x_2293_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2312_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2311_; 
v___x_2300_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2296_, v_a_2288_);
lean_dec(v_val_2296_);
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2311_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2311_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v_a_2301_);
v___x_2306_ = v___x_2298_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2306_);
v___x_2308_ = v___x_2303_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2313_, v_a_2314_, v_a_2315_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2318_, v_a_2319_, v_a_2320_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v_currFnIdx_2341_; lean_object* v_assignments_2342_; lean_object* v_funVals_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2361_; 
v___x_2340_ = lean_st_ref_take(v_a_2338_);
v_currFnIdx_2341_ = lean_ctor_get(v_a_2337_, 1);
v_assignments_2342_ = lean_ctor_get(v___x_2340_, 0);
v_funVals_2343_ = lean_ctor_get(v___x_2340_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2345_ = v___x_2340_;
v_isShared_2346_ = v_isSharedCheck_2361_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_funVals_2343_);
lean_inc(v_assignments_2342_);
lean_dec(v___x_2340_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2361_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___y_2349_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2347_ = lean_box(0);
v___x_2355_ = lean_array_get_size(v_assignments_2342_);
v___x_2356_ = lean_nat_dec_lt(v_currFnIdx_2341_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_dec_ref(v_f_2336_);
v___y_2349_ = v_assignments_2342_;
goto v___jp_2348_;
}
else
{
lean_object* v_v_2357_; lean_object* v_xs_x27_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_v_2357_ = lean_array_fget(v_assignments_2342_, v_currFnIdx_2341_);
v_xs_x27_2358_ = lean_array_fset(v_assignments_2342_, v_currFnIdx_2341_, v___x_2347_);
v___x_2359_ = lean_apply_1(v_f_2336_, v_v_2357_);
v___x_2360_ = lean_array_fset(v_xs_x27_2358_, v_currFnIdx_2341_, v___x_2359_);
v___y_2349_ = v___x_2360_;
goto v___jp_2348_;
}
v___jp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___y_2349_);
v___x_2351_ = v___x_2345_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___y_2349_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_funVals_2343_);
v___x_2351_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_st_ref_set(v_a_2338_, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2347_);
return v___x_2353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2367_, v_a_2368_, v_a_2369_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2385_, lean_object* v_fallback_2386_, lean_object* v_x_2387_){
_start:
{
if (lean_obj_tag(v_x_2387_) == 0)
{
lean_inc(v_fallback_2386_);
return v_fallback_2386_;
}
else
{
lean_object* v_key_2388_; lean_object* v_value_2389_; lean_object* v_tail_2390_; uint8_t v___x_2391_; 
v_key_2388_ = lean_ctor_get(v_x_2387_, 0);
v_value_2389_ = lean_ctor_get(v_x_2387_, 1);
v_tail_2390_ = lean_ctor_get(v_x_2387_, 2);
v___x_2391_ = l_Lean_instBEqFVarId_beq(v_key_2388_, v_a_2385_);
if (v___x_2391_ == 0)
{
v_x_2387_ = v_tail_2390_;
goto _start;
}
else
{
lean_inc(v_value_2389_);
return v_value_2389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2393_, lean_object* v_fallback_2394_, lean_object* v_x_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2393_, v_fallback_2394_, v_x_2395_);
lean_dec(v_x_2395_);
lean_dec(v_fallback_2394_);
lean_dec(v_a_2393_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2397_, lean_object* v_a_2398_, lean_object* v_fallback_2399_){
_start:
{
lean_object* v_buckets_2400_; lean_object* v___x_2401_; uint64_t v___x_2402_; uint64_t v___x_2403_; uint64_t v___x_2404_; uint64_t v_fold_2405_; uint64_t v___x_2406_; uint64_t v___x_2407_; uint64_t v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_buckets_2400_ = lean_ctor_get(v_m_2397_, 1);
v___x_2401_ = lean_array_get_size(v_buckets_2400_);
v___x_2402_ = l_Lean_instHashableFVarId_hash(v_a_2398_);
v___x_2403_ = 32ULL;
v___x_2404_ = lean_uint64_shift_right(v___x_2402_, v___x_2403_);
v_fold_2405_ = lean_uint64_xor(v___x_2402_, v___x_2404_);
v___x_2406_ = 16ULL;
v___x_2407_ = lean_uint64_shift_right(v_fold_2405_, v___x_2406_);
v___x_2408_ = lean_uint64_xor(v_fold_2405_, v___x_2407_);
v___x_2409_ = lean_uint64_to_usize(v___x_2408_);
v___x_2410_ = lean_usize_of_nat(v___x_2401_);
v___x_2411_ = ((size_t)1ULL);
v___x_2412_ = lean_usize_sub(v___x_2410_, v___x_2411_);
v___x_2413_ = lean_usize_land(v___x_2409_, v___x_2412_);
v___x_2414_ = lean_array_uget_borrowed(v_buckets_2400_, v___x_2413_);
v___x_2415_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2398_, v_fallback_2399_, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2416_, lean_object* v_a_2417_, lean_object* v_fallback_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2416_, v_a_2417_, v_fallback_2418_);
lean_dec(v_fallback_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_m_2416_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2434_; 
v___x_2424_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2421_, v_a_2422_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2434_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2434_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2429_ = lean_box(0);
v___x_2430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2425_, v_var_2420_, v___x_2429_);
lean_dec(v_a_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2430_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_var_2435_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2440_, v_a_2441_, v_a_2442_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_var_2449_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2458_, lean_object* v_m_2459_, lean_object* v_a_2460_, lean_object* v_fallback_2461_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2459_, v_a_2460_, v_fallback_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2463_, lean_object* v_m_2464_, lean_object* v_a_2465_, lean_object* v_fallback_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2463_, v_m_2464_, v_a_2465_, v_fallback_2466_);
lean_dec(v_fallback_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_m_2464_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2468_, lean_object* v_a_2469_, lean_object* v_fallback_2470_, lean_object* v_x_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2469_, v_fallback_2470_, v_x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2473_, lean_object* v_a_2474_, lean_object* v_fallback_2475_, lean_object* v_x_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2473_, v_a_2474_, v_fallback_2475_, v_x_2476_);
lean_dec(v_x_2476_);
lean_dec(v_fallback_2475_);
lean_dec(v_a_2474_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
if (lean_obj_tag(v_arg_2478_) == 1)
{
lean_object* v_fvarId_2482_; lean_object* v___x_2483_; 
v_fvarId_2482_ = lean_ctor_get(v_arg_2478_, 0);
v___x_2483_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2482_, v_a_2479_, v_a_2480_);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_box(1);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_arg_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2491_, v_a_2492_, v_a_2493_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_arg_2500_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2509_, lean_object* v_b_2510_, lean_object* v_x_2511_){
_start:
{
if (lean_obj_tag(v_x_2511_) == 0)
{
lean_dec(v_b_2510_);
lean_dec(v_a_2509_);
return v_x_2511_;
}
else
{
lean_object* v_key_2512_; lean_object* v_value_2513_; lean_object* v_tail_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2526_; 
v_key_2512_ = lean_ctor_get(v_x_2511_, 0);
v_value_2513_ = lean_ctor_get(v_x_2511_, 1);
v_tail_2514_ = lean_ctor_get(v_x_2511_, 2);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_x_2511_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2516_ = v_x_2511_;
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_tail_2514_);
lean_inc(v_value_2513_);
lean_inc(v_key_2512_);
lean_dec(v_x_2511_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
uint8_t v___x_2518_; 
v___x_2518_ = l_Lean_instBEqFVarId_beq(v_key_2512_, v_a_2509_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2519_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2509_, v_b_2510_, v_tail_2514_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 2, v___x_2519_);
v___x_2521_ = v___x_2516_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_key_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_value_2513_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
else
{
lean_object* v___x_2524_; 
lean_dec(v_value_2513_);
lean_dec(v_key_2512_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 1, v_b_2510_);
lean_ctor_set(v___x_2516_, 0, v_a_2509_);
v___x_2524_ = v___x_2516_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2509_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_b_2510_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_tail_2514_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2527_, lean_object* v_x_2528_){
_start:
{
if (lean_obj_tag(v_x_2528_) == 0)
{
return v_x_2527_;
}
else
{
lean_object* v_key_2529_; lean_object* v_value_2530_; lean_object* v_tail_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2554_; 
v_key_2529_ = lean_ctor_get(v_x_2528_, 0);
v_value_2530_ = lean_ctor_get(v_x_2528_, 1);
v_tail_2531_ = lean_ctor_get(v_x_2528_, 2);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_x_2528_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2533_ = v_x_2528_;
v_isShared_2534_ = v_isSharedCheck_2554_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_tail_2531_);
lean_inc(v_value_2530_);
lean_inc(v_key_2529_);
lean_dec(v_x_2528_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2554_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; uint64_t v___x_2536_; uint64_t v___x_2537_; uint64_t v___x_2538_; uint64_t v_fold_2539_; uint64_t v___x_2540_; uint64_t v___x_2541_; uint64_t v___x_2542_; size_t v___x_2543_; size_t v___x_2544_; size_t v___x_2545_; size_t v___x_2546_; size_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2535_ = lean_array_get_size(v_x_2527_);
v___x_2536_ = l_Lean_instHashableFVarId_hash(v_key_2529_);
v___x_2537_ = 32ULL;
v___x_2538_ = lean_uint64_shift_right(v___x_2536_, v___x_2537_);
v_fold_2539_ = lean_uint64_xor(v___x_2536_, v___x_2538_);
v___x_2540_ = 16ULL;
v___x_2541_ = lean_uint64_shift_right(v_fold_2539_, v___x_2540_);
v___x_2542_ = lean_uint64_xor(v_fold_2539_, v___x_2541_);
v___x_2543_ = lean_uint64_to_usize(v___x_2542_);
v___x_2544_ = lean_usize_of_nat(v___x_2535_);
v___x_2545_ = ((size_t)1ULL);
v___x_2546_ = lean_usize_sub(v___x_2544_, v___x_2545_);
v___x_2547_ = lean_usize_land(v___x_2543_, v___x_2546_);
v___x_2548_ = lean_array_uget_borrowed(v_x_2527_, v___x_2547_);
lean_inc(v___x_2548_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 2, v___x_2548_);
v___x_2550_ = v___x_2533_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_key_2529_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_value_2530_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_array_uset(v_x_2527_, v___x_2547_, v___x_2550_);
v_x_2527_ = v___x_2551_;
v_x_2528_ = v_tail_2531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2555_, lean_object* v_source_2556_, lean_object* v_target_2557_){
_start:
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = lean_array_get_size(v_source_2556_);
v___x_2559_ = lean_nat_dec_lt(v_i_2555_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_dec_ref(v_source_2556_);
lean_dec(v_i_2555_);
return v_target_2557_;
}
else
{
lean_object* v_es_2560_; lean_object* v___x_2561_; lean_object* v_source_2562_; lean_object* v_target_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_es_2560_ = lean_array_fget(v_source_2556_, v_i_2555_);
v___x_2561_ = lean_box(0);
v_source_2562_ = lean_array_fset(v_source_2556_, v_i_2555_, v___x_2561_);
v_target_2563_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2557_, v_es_2560_);
v___x_2564_ = lean_unsigned_to_nat(1u);
v___x_2565_ = lean_nat_add(v_i_2555_, v___x_2564_);
lean_dec(v_i_2555_);
v_i_2555_ = v___x_2565_;
v_source_2556_ = v_source_2562_;
v_target_2557_ = v_target_2563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2567_){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_nbuckets_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2568_ = lean_array_get_size(v_data_2567_);
v___x_2569_ = lean_unsigned_to_nat(2u);
v_nbuckets_2570_ = lean_nat_mul(v___x_2568_, v___x_2569_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_mk_array(v_nbuckets_2570_, v___x_2572_);
v___x_2574_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2571_, v_data_2567_, v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2575_, lean_object* v_x_2576_){
_start:
{
if (lean_obj_tag(v_x_2576_) == 0)
{
uint8_t v___x_2577_; 
v___x_2577_ = 0;
return v___x_2577_;
}
else
{
lean_object* v_key_2578_; lean_object* v_tail_2579_; uint8_t v___x_2580_; 
v_key_2578_ = lean_ctor_get(v_x_2576_, 0);
v_tail_2579_ = lean_ctor_get(v_x_2576_, 2);
v___x_2580_ = l_Lean_instBEqFVarId_beq(v_key_2578_, v_a_2575_);
if (v___x_2580_ == 0)
{
v_x_2576_ = v_tail_2579_;
goto _start;
}
else
{
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2582_, lean_object* v_x_2583_){
_start:
{
uint8_t v_res_2584_; lean_object* v_r_2585_; 
v_res_2584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2582_, v_x_2583_);
lean_dec(v_x_2583_);
lean_dec(v_a_2582_);
v_r_2585_ = lean_box(v_res_2584_);
return v_r_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2586_, lean_object* v_a_2587_, lean_object* v_b_2588_){
_start:
{
lean_object* v_size_2589_; lean_object* v_buckets_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2633_; 
v_size_2589_ = lean_ctor_get(v_m_2586_, 0);
v_buckets_2590_ = lean_ctor_get(v_m_2586_, 1);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_m_2586_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2592_ = v_m_2586_;
v_isShared_2593_ = v_isSharedCheck_2633_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_buckets_2590_);
lean_inc(v_size_2589_);
lean_dec(v_m_2586_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2633_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; uint64_t v___x_2595_; uint64_t v___x_2596_; uint64_t v___x_2597_; uint64_t v_fold_2598_; uint64_t v___x_2599_; uint64_t v___x_2600_; uint64_t v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; lean_object* v_bkt_2607_; uint8_t v___x_2608_; 
v___x_2594_ = lean_array_get_size(v_buckets_2590_);
v___x_2595_ = l_Lean_instHashableFVarId_hash(v_a_2587_);
v___x_2596_ = 32ULL;
v___x_2597_ = lean_uint64_shift_right(v___x_2595_, v___x_2596_);
v_fold_2598_ = lean_uint64_xor(v___x_2595_, v___x_2597_);
v___x_2599_ = 16ULL;
v___x_2600_ = lean_uint64_shift_right(v_fold_2598_, v___x_2599_);
v___x_2601_ = lean_uint64_xor(v_fold_2598_, v___x_2600_);
v___x_2602_ = lean_uint64_to_usize(v___x_2601_);
v___x_2603_ = lean_usize_of_nat(v___x_2594_);
v___x_2604_ = ((size_t)1ULL);
v___x_2605_ = lean_usize_sub(v___x_2603_, v___x_2604_);
v___x_2606_ = lean_usize_land(v___x_2602_, v___x_2605_);
v_bkt_2607_ = lean_array_uget_borrowed(v_buckets_2590_, v___x_2606_);
v___x_2608_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2587_, v_bkt_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v_size_x27_2610_; lean_object* v___x_2611_; lean_object* v_buckets_x27_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2609_ = lean_unsigned_to_nat(1u);
v_size_x27_2610_ = lean_nat_add(v_size_2589_, v___x_2609_);
lean_dec(v_size_2589_);
lean_inc(v_bkt_2607_);
v___x_2611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2611_, 0, v_a_2587_);
lean_ctor_set(v___x_2611_, 1, v_b_2588_);
lean_ctor_set(v___x_2611_, 2, v_bkt_2607_);
v_buckets_x27_2612_ = lean_array_uset(v_buckets_2590_, v___x_2606_, v___x_2611_);
v___x_2613_ = lean_unsigned_to_nat(4u);
v___x_2614_ = lean_nat_mul(v_size_x27_2610_, v___x_2613_);
v___x_2615_ = lean_unsigned_to_nat(3u);
v___x_2616_ = lean_nat_div(v___x_2614_, v___x_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_array_get_size(v_buckets_x27_2612_);
v___x_2618_ = lean_nat_dec_le(v___x_2616_, v___x_2617_);
lean_dec(v___x_2616_);
if (v___x_2618_ == 0)
{
lean_object* v_val_2619_; lean_object* v___x_2621_; 
v_val_2619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2612_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v_val_2619_);
lean_ctor_set(v___x_2592_, 0, v_size_x27_2610_);
v___x_2621_ = v___x_2592_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_size_x27_2610_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_val_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2624_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v_buckets_x27_2612_);
lean_ctor_set(v___x_2592_, 0, v_size_x27_2610_);
v___x_2624_ = v___x_2592_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_size_x27_2610_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_buckets_x27_2612_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v___x_2626_; lean_object* v_buckets_x27_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
lean_inc(v_bkt_2607_);
v___x_2626_ = lean_box(0);
v_buckets_x27_2627_ = lean_array_uset(v_buckets_2590_, v___x_2606_, v___x_2626_);
v___x_2628_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2587_, v_b_2588_, v_bkt_2607_);
v___x_2629_ = lean_array_uset(v_buckets_x27_2627_, v___x_2606_, v___x_2628_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v___x_2629_);
v___x_2631_ = v___x_2592_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_size_2589_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2634_, lean_object* v___x_2635_, lean_object* v_x_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2636_, v_var_2634_, v___x_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2638_, lean_object* v_newVal_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = lean_st_ref_get(v_a_2642_);
v___x_2645_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2638_, v_a_2640_, v_a_2641_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v_env_2647_; lean_object* v___x_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v_env_2647_ = lean_ctor_get(v___x_2644_, 0);
lean_inc_ref(v_env_2647_);
lean_dec(v___x_2644_);
v___x_2648_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2647_, v_a_2646_, v_newVal_2639_);
v___f_2649_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2649_, 0, v_var_2638_);
lean_closure_set(v___f_2649_, 1, v___x_2648_);
v___x_2650_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2649_, v_a_2640_, v_a_2641_);
return v___x_2650_;
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v___x_2644_);
lean_dec(v_newVal_2639_);
lean_dec(v_var_2638_);
v_a_2651_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2645_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2645_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2659_, lean_object* v_newVal_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2659_, v_newVal_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2666_, lean_object* v_newVal_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2666_, v_newVal_2667_, v_a_2668_, v_a_2669_, v_a_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2676_, lean_object* v_newVal_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2676_, v_newVal_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2686_, lean_object* v_m_2687_, lean_object* v_a_2688_, lean_object* v_b_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2687_, v_a_2688_, v_b_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2691_, lean_object* v_a_2692_, lean_object* v_x_2693_){
_start:
{
uint8_t v___x_2694_; 
v___x_2694_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2692_, v_x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2695_, lean_object* v_a_2696_, lean_object* v_x_2697_){
_start:
{
uint8_t v_res_2698_; lean_object* v_r_2699_; 
v_res_2698_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2695_, v_a_2696_, v_x_2697_);
lean_dec(v_x_2697_);
lean_dec(v_a_2696_);
v_r_2699_ = lean_box(v_res_2698_);
return v_r_2699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2700_, lean_object* v_data_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2703_, lean_object* v_a_2704_, lean_object* v_b_2705_, lean_object* v_x_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2704_, v_b_2705_, v_x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2708_, lean_object* v_i_2709_, lean_object* v_source_2710_, lean_object* v_target_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2709_, v_source_2710_, v_target_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2714_, v_x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2717_, lean_object* v_x_2718_){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = lean_box(0);
v___x_2720_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2718_, v_var_2717_, v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v___f_2725_; lean_object* v___x_2726_; 
v___f_2725_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2725_, 0, v_var_2721_);
v___x_2726_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2725_, v_a_2722_, v_a_2723_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2732_, v_a_2733_, v_a_2734_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v_fst_2758_; lean_object* v_snd_2759_; lean_object* v_currFnIdx_2762_; lean_object* v_assignments_2763_; lean_object* v_funVals_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2755_ = lean_st_ref_get(v_a_2753_);
v___x_2756_ = lean_st_ref_take(v_a_2752_);
v_currFnIdx_2762_ = lean_ctor_get(v_a_2751_, 1);
v_assignments_2763_ = lean_ctor_get(v___x_2756_, 0);
lean_inc_ref(v_assignments_2763_);
v_funVals_2764_ = lean_ctor_get(v___x_2756_, 1);
lean_inc_ref(v_funVals_2764_);
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_array_get_size(v_funVals_2764_);
v___x_2767_ = lean_nat_dec_lt(v_currFnIdx_2762_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_dec_ref(v_funVals_2764_);
lean_dec_ref(v_assignments_2763_);
lean_dec(v___x_2755_);
lean_dec(v_v_2750_);
v_fst_2758_ = v___x_2765_;
v_snd_2759_ = v___x_2756_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2779_; 
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; lean_object* v_unused_2781_; 
v_unused_2780_ = lean_ctor_get(v___x_2756_, 1);
lean_dec(v_unused_2780_);
v_unused_2781_ = lean_ctor_get(v___x_2756_, 0);
lean_dec(v_unused_2781_);
v___x_2769_ = v___x_2756_;
v_isShared_2770_ = v_isSharedCheck_2779_;
goto v_resetjp_2768_;
}
else
{
lean_dec(v___x_2756_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2779_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_env_2771_; lean_object* v_v_2772_; lean_object* v_xs_x27_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v_env_2771_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_ref(v_env_2771_);
lean_dec(v___x_2755_);
v_v_2772_ = lean_array_fget(v_funVals_2764_, v_currFnIdx_2762_);
v_xs_x27_2773_ = lean_array_fset(v_funVals_2764_, v_currFnIdx_2762_, v___x_2765_);
v___x_2774_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2771_, v_v_2750_, v_v_2772_);
v___x_2775_ = lean_array_fset(v_xs_x27_2773_, v_currFnIdx_2762_, v___x_2774_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2775_);
v___x_2777_ = v___x_2769_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_assignments_2763_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
v_fst_2758_ = v___x_2765_;
v_snd_2759_ = v___x_2777_;
goto v___jp_2757_;
}
}
}
v___jp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_st_ref_set(v_a_2752_, v_snd_2759_);
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_fst_2758_);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2788_, v_a_2789_, v_a_2790_, v_a_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2806_, uint8_t v_b_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_array_2812_; lean_object* v_start_2813_; lean_object* v_stop_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2851_; 
v_array_2812_ = lean_ctor_get(v_a_2806_, 0);
v_start_2813_ = lean_ctor_get(v_a_2806_, 1);
v_stop_2814_ = lean_ctor_get(v_a_2806_, 2);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_a_2806_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2816_ = v_a_2806_;
v_isShared_2817_ = v_isSharedCheck_2851_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_stop_2814_);
lean_inc(v_start_2813_);
lean_inc(v_array_2812_);
lean_dec(v_a_2806_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2851_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_nat_dec_lt(v_start_2813_, v_stop_2814_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_del_object(v___x_2816_);
lean_dec(v_stop_2814_);
lean_dec(v_start_2813_);
lean_dec_ref(v_array_2812_);
v___x_2819_ = lean_box(v_b_2807_);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v_fvarId_2822_; lean_object* v___x_2823_; 
v___x_2821_ = lean_array_fget_borrowed(v_array_2812_, v_start_2813_);
v_fvarId_2822_ = lean_ctor_get(v___x_2821_, 0);
v___x_2823_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2822_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = lean_box(1);
lean_inc(v_fvarId_2822_);
v___x_2826_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2822_, v___x_2825_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
lean_dec_ref(v___x_2826_);
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_start_2813_, v___x_2827_);
lean_dec(v_start_2813_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 1, v___x_2828_);
v___x_2830_ = v___x_2816_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_array_2812_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2834_, 2, v_stop_2814_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = lean_box(0);
v___x_2832_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2824_, v___x_2831_);
v_a_2806_ = v___x_2830_;
v_b_2807_ = v___x_2832_;
goto _start;
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2824_);
lean_del_object(v___x_2816_);
lean_dec(v_stop_2814_);
lean_dec(v_start_2813_);
lean_dec_ref(v_array_2812_);
v_a_2835_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2826_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2826_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_del_object(v___x_2816_);
lean_dec(v_stop_2814_);
lean_dec(v_start_2813_);
lean_dec_ref(v_array_2812_);
v_a_2843_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2823_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2823_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2852_, lean_object* v_b_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
uint8_t v_b_boxed_2858_; lean_object* v_res_2859_; 
v_b_boxed_2858_ = lean_unbox(v_b_2853_);
v_res_2859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2852_, v_b_boxed_2858_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2860_, lean_object* v___x_2861_, lean_object* v_x_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2862_, v_fvarId_2860_, v___x_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2864_, lean_object* v_as_2865_, size_t v_sz_2866_, size_t v_i_2867_, lean_object* v_b_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_a_2873_; uint8_t v___x_2877_; 
v___x_2877_ = lean_usize_dec_lt(v_i_2867_, v_sz_2866_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec_ref(v___x_2864_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_b_2868_);
return v___x_2878_;
}
else
{
lean_object* v_snd_2879_; lean_object* v_fst_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2946_; 
v_snd_2879_ = lean_ctor_get(v_b_2868_, 1);
v_fst_2880_ = lean_ctor_get(v_b_2868_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_b_2868_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2882_ = v_b_2868_;
v_isShared_2883_ = v_isSharedCheck_2946_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_snd_2879_);
lean_inc(v_fst_2880_);
lean_dec(v_b_2868_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2946_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_array_2884_; lean_object* v_start_2885_; lean_object* v_stop_2886_; uint8_t v___x_2887_; 
v_array_2884_ = lean_ctor_get(v_snd_2879_, 0);
v_start_2885_ = lean_ctor_get(v_snd_2879_, 1);
v_stop_2886_ = lean_ctor_get(v_snd_2879_, 2);
v___x_2887_ = lean_nat_dec_lt(v_start_2885_, v_stop_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2889_; 
lean_dec_ref(v___x_2864_);
if (v_isShared_2883_ == 0)
{
v___x_2889_ = v___x_2882_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_fst_2880_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_snd_2879_);
v___x_2889_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
}
else
{
lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2942_; 
lean_inc(v_stop_2886_);
lean_inc(v_start_2885_);
lean_inc_ref(v_array_2884_);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_snd_2879_);
if (v_isSharedCheck_2942_ == 0)
{
lean_object* v_unused_2943_; lean_object* v_unused_2944_; lean_object* v_unused_2945_; 
v_unused_2943_ = lean_ctor_get(v_snd_2879_, 2);
lean_dec(v_unused_2943_);
v_unused_2944_ = lean_ctor_get(v_snd_2879_, 1);
lean_dec(v_unused_2944_);
v_unused_2945_ = lean_ctor_get(v_snd_2879_, 0);
lean_dec(v_unused_2945_);
v___x_2893_ = v_snd_2879_;
v_isShared_2894_ = v_isSharedCheck_2942_;
goto v_resetjp_2892_;
}
else
{
lean_dec(v_snd_2879_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2942_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_a_2895_; lean_object* v_fvarId_2896_; lean_object* v___x_2897_; 
v_a_2895_ = lean_array_uget_borrowed(v_as_2865_, v_i_2867_);
v_fvarId_2896_ = lean_ctor_get(v_a_2895_, 0);
v___x_2897_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2896_, v___y_2869_, v___y_2870_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = lean_array_fget_borrowed(v_array_2884_, v_start_2885_);
v___x_2900_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2899_, v___y_2869_, v___y_2870_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref(v___x_2900_);
v___x_2902_ = lean_unsigned_to_nat(1u);
v___x_2903_ = lean_nat_add(v_start_2885_, v___x_2902_);
lean_dec(v_start_2885_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v___x_2903_);
v___x_2905_ = v___x_2893_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_array_2884_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_stop_2886_);
v___x_2905_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
lean_inc(v_a_2898_);
lean_inc_ref(v___x_2864_);
v___x_2906_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2864_, v_a_2898_, v_a_2901_);
lean_inc(v___x_2906_);
v___x_2907_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2906_, v_a_2898_);
if (v___x_2907_ == 0)
{
lean_object* v___f_2908_; lean_object* v___x_2909_; 
lean_dec(v_fst_2880_);
lean_inc(v_fvarId_2896_);
v___f_2908_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2908_, 0, v_fvarId_2896_);
lean_closure_set(v___f_2908_, 1, v___x_2906_);
v___x_2909_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2908_, v___y_2869_, v___y_2870_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
lean_dec_ref(v___x_2909_);
v___x_2910_ = lean_box(v___x_2887_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v___x_2905_);
lean_ctor_set(v___x_2882_, 0, v___x_2910_);
v___x_2912_ = v___x_2882_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___x_2905_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
v_a_2873_ = v___x_2912_;
goto v___jp_2872_;
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___x_2905_);
lean_del_object(v___x_2882_);
lean_dec_ref(v___x_2864_);
v_a_2914_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2909_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2909_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v___x_2923_; 
lean_dec(v___x_2906_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v___x_2905_);
v___x_2923_ = v___x_2882_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_fst_2880_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v___x_2905_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
v_a_2873_ = v___x_2923_;
goto v___jp_2872_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_a_2898_);
lean_del_object(v___x_2893_);
lean_dec(v_stop_2886_);
lean_dec(v_start_2885_);
lean_dec_ref(v_array_2884_);
lean_del_object(v___x_2882_);
lean_dec(v_fst_2880_);
lean_dec_ref(v___x_2864_);
v_a_2926_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2900_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2900_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_del_object(v___x_2893_);
lean_dec(v_stop_2886_);
lean_dec(v_start_2885_);
lean_dec_ref(v_array_2884_);
lean_del_object(v___x_2882_);
lean_dec(v_fst_2880_);
lean_dec_ref(v___x_2864_);
v_a_2934_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2897_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2897_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
}
v___jp_2872_:
{
size_t v___x_2874_; size_t v___x_2875_; 
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_add(v_i_2867_, v___x_2874_);
v_i_2867_ = v___x_2875_;
v_b_2868_ = v_a_2873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_2947_, lean_object* v_as_2948_, lean_object* v_sz_2949_, lean_object* v_i_2950_, lean_object* v_b_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
size_t v_sz_boxed_2955_; size_t v_i_boxed_2956_; lean_object* v_res_2957_; 
v_sz_boxed_2955_ = lean_unbox_usize(v_sz_2949_);
lean_dec(v_sz_2949_);
v_i_boxed_2956_ = lean_unbox_usize(v_i_2950_);
lean_dec(v_i_2950_);
v_res_2957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_2947_, v_as_2948_, v_sz_boxed_2955_, v_i_boxed_2956_, v_b_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v_as_2948_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_2958_, lean_object* v_args_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___x_2967_; lean_object* v_env_2968_; uint8_t v_ret_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; size_t v_sz_2975_; size_t v___x_2976_; lean_object* v___x_2977_; 
v___x_2967_ = lean_st_ref_get(v_a_2965_);
v_env_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc_ref(v_env_2968_);
lean_dec(v___x_2967_);
v_ret_2969_ = 0;
v___x_2970_ = lean_unsigned_to_nat(0u);
v___x_2971_ = lean_array_get_size(v_args_2959_);
v___x_2972_ = l_Array_toSubarray___redArg(v_args_2959_, v___x_2970_, v___x_2971_);
v___x_2973_ = lean_box(v_ret_2969_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___x_2972_);
v_sz_2975_ = lean_array_size(v_params_2958_);
v___x_2976_ = ((size_t)0ULL);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_2968_, v_params_2958_, v_sz_2975_, v___x_2976_, v___x_2974_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2995_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_2995_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2995_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v_fst_2982_; lean_object* v_lower_2984_; lean_object* v_upper_2985_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v_fst_2982_ = lean_ctor_get(v_a_2978_, 0);
lean_inc(v_fst_2982_);
lean_dec(v_a_2978_);
v___x_2989_ = lean_array_get_size(v_params_2958_);
v___x_2990_ = lean_nat_dec_eq(v___x_2989_, v___x_2971_);
if (v___x_2990_ == 0)
{
uint8_t v___x_2991_; 
lean_del_object(v___x_2980_);
v___x_2991_ = lean_nat_dec_le(v___x_2971_, v___x_2970_);
if (v___x_2991_ == 0)
{
v_lower_2984_ = v___x_2971_;
v_upper_2985_ = v___x_2989_;
goto v___jp_2983_;
}
else
{
v_lower_2984_ = v___x_2970_;
v_upper_2985_ = v___x_2989_;
goto v___jp_2983_;
}
}
else
{
lean_object* v___x_2993_; 
lean_dec_ref(v_params_2958_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v_fst_2982_);
v___x_2993_ = v___x_2980_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_fst_2982_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
v___jp_2983_:
{
lean_object* v___x_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = l_Array_toSubarray___redArg(v_params_2958_, v_lower_2984_, v_upper_2985_);
v___x_2987_ = lean_unbox(v_fst_2982_);
lean_dec(v_fst_2982_);
v___x_2988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_2986_, v___x_2987_, v_a_2960_, v_a_2961_, v_a_2965_);
return v___x_2988_;
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v_params_2958_);
v_a_2996_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2977_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2977_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3004_, lean_object* v_args_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3004_, v_args_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3014_, lean_object* v_as_3015_, size_t v_sz_3016_, size_t v_i_3017_, lean_object* v_b_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3014_, v_as_3015_, v_sz_3016_, v_i_3017_, v_b_3018_, v___y_3019_, v___y_3020_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3027_, lean_object* v_as_3028_, lean_object* v_sz_3029_, lean_object* v_i_3030_, lean_object* v_b_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
size_t v_sz_boxed_3039_; size_t v_i_boxed_3040_; lean_object* v_res_3041_; 
v_sz_boxed_3039_ = lean_unbox_usize(v_sz_3029_);
lean_dec(v_sz_3029_);
v_i_boxed_3040_ = lean_unbox_usize(v_i_3030_);
lean_dec(v_i_3030_);
v_res_3041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3027_, v_as_3028_, v_sz_boxed_3039_, v_i_boxed_3040_, v_b_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v_as_3028_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3042_, lean_object* v_R_3043_, lean_object* v_a_3044_, uint8_t v_b_3045_, lean_object* v_c_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3044_, v_b_3045_, v___y_3047_, v___y_3048_, v___y_3052_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3055_, lean_object* v_R_3056_, lean_object* v_a_3057_, lean_object* v_b_3058_, lean_object* v_c_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
uint8_t v_b_boxed_3067_; lean_object* v_res_3068_; 
v_b_boxed_3067_ = lean_unbox(v_b_3058_);
v_res_3068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3055_, v_R_3056_, v_a_3057_, v_b_boxed_3067_, v_c_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3069_, size_t v_sz_3070_, size_t v_i_3071_, uint8_t v_b_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
uint8_t v_a_3077_; uint8_t v___x_3081_; 
v___x_3081_ = lean_usize_dec_lt(v_i_3071_, v_sz_3070_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_box(v_b_3072_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
return v___x_3083_;
}
else
{
lean_object* v_a_3084_; lean_object* v_fvarId_3085_; lean_object* v___x_3086_; 
v_a_3084_ = lean_array_uget_borrowed(v_as_3069_, v_i_3071_);
v_fvarId_3085_ = lean_ctor_get(v_a_3084_, 0);
v___x_3086_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3085_, v___y_3073_, v___y_3074_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3086_);
v___x_3088_ = lean_box(1);
v___x_3089_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3088_, v_a_3087_);
if (v___x_3089_ == 0)
{
lean_object* v___f_3090_; lean_object* v___x_3091_; 
lean_inc(v_fvarId_3085_);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3090_, 0, v_fvarId_3085_);
lean_closure_set(v___f_3090_, 1, v___x_3088_);
v___x_3091_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3090_, v___y_3073_, v___y_3074_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_dec_ref(v___x_3091_);
v_a_3077_ = v___x_3081_;
goto v___jp_3076_;
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
v_a_3077_ = v_b_3072_;
goto v___jp_3076_;
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
v_a_3100_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3086_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3086_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
v___jp_3076_:
{
size_t v___x_3078_; size_t v___x_3079_; 
v___x_3078_ = ((size_t)1ULL);
v___x_3079_ = lean_usize_add(v_i_3071_, v___x_3078_);
v_i_3071_ = v___x_3079_;
v_b_3072_ = v_a_3077_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3108_, lean_object* v_sz_3109_, lean_object* v_i_3110_, lean_object* v_b_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
size_t v_sz_boxed_3115_; size_t v_i_boxed_3116_; uint8_t v_b_boxed_3117_; lean_object* v_res_3118_; 
v_sz_boxed_3115_ = lean_unbox_usize(v_sz_3109_);
lean_dec(v_sz_3109_);
v_i_boxed_3116_ = lean_unbox_usize(v_i_3110_);
lean_dec(v_i_3110_);
v_b_boxed_3117_ = lean_unbox(v_b_3111_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3108_, v_sz_boxed_3115_, v_i_boxed_3116_, v_b_boxed_3117_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v_as_3108_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
uint8_t v_ret_3127_; size_t v_sz_3128_; size_t v___x_3129_; lean_object* v___x_3130_; 
v_ret_3127_ = 0;
v_sz_3128_ = lean_array_size(v_params_3119_);
v___x_3129_ = ((size_t)0ULL);
v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3119_, v_sz_3128_, v___x_3129_, v_ret_3127_, v_a_3120_, v_a_3121_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec_ref(v_params_3131_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3140_, size_t v_sz_3141_, size_t v_i_3142_, uint8_t v_b_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3140_, v_sz_3141_, v_i_3142_, v_b_3143_, v___y_3144_, v___y_3145_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3152_, lean_object* v_sz_3153_, lean_object* v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
size_t v_sz_boxed_3163_; size_t v_i_boxed_3164_; uint8_t v_b_boxed_3165_; lean_object* v_res_3166_; 
v_sz_boxed_3163_ = lean_unbox_usize(v_sz_3153_);
lean_dec(v_sz_3153_);
v_i_boxed_3164_ = lean_unbox_usize(v_i_3154_);
lean_dec(v_i_3154_);
v_b_boxed_3165_ = lean_unbox(v_b_3155_);
v_res_3166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3152_, v_sz_boxed_3163_, v_i_boxed_3164_, v_b_boxed_3165_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v_as_3152_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3167_, size_t v_i_3168_, size_t v_stop_3169_, lean_object* v_b_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_usize_dec_eq(v_i_3168_, v_stop_3169_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v_fvarId_3176_; lean_object* v___x_3177_; 
v___x_3175_ = lean_array_uget_borrowed(v_as_3167_, v_i_3168_);
v_fvarId_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_fvarId_3176_);
v___x_3177_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3176_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; size_t v___x_3179_; size_t v___x_3180_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3177_);
v___x_3179_ = ((size_t)1ULL);
v___x_3180_ = lean_usize_add(v_i_3168_, v___x_3179_);
v_i_3168_ = v___x_3180_;
v_b_3170_ = v_a_3178_;
goto _start;
}
else
{
return v___x_3177_;
}
}
else
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_b_3170_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3183_, lean_object* v_i_3184_, lean_object* v_stop_3185_, lean_object* v_b_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
size_t v_i_boxed_3190_; size_t v_stop_boxed_3191_; lean_object* v_res_3192_; 
v_i_boxed_3190_ = lean_unbox_usize(v_i_3184_);
lean_dec(v_i_3184_);
v_stop_boxed_3191_ = lean_unbox_usize(v_stop_3185_);
lean_dec(v_stop_3185_);
v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3183_, v_i_boxed_3190_, v_stop_boxed_3191_, v_b_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec_ref(v_as_3183_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v_decl_3212_; lean_object* v_k_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; 
switch(lean_obj_tag(v_x_3193_))
{
case 0:
{
lean_object* v_k_3234_; 
v_k_3234_ = lean_ctor_get(v_x_3193_, 1);
lean_inc_ref(v_k_3234_);
lean_dec_ref(v_x_3193_);
v_x_3193_ = v_k_3234_;
goto _start;
}
case 3:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_dec_ref(v_x_3193_);
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
return v___x_3237_;
}
case 4:
{
lean_object* v_cases_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3260_; 
v_cases_3238_ = lean_ctor_get(v_x_3193_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_x_3193_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3240_ = v_x_3193_;
v_isShared_3241_ = v_isSharedCheck_3260_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_cases_3238_);
lean_dec(v_x_3193_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3260_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_alts_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; uint8_t v___x_3246_; 
v_alts_3242_ = lean_ctor_get(v_cases_3238_, 3);
lean_inc_ref(v_alts_3242_);
lean_dec_ref(v_cases_3238_);
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = lean_array_get_size(v_alts_3242_);
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_nat_dec_lt(v___x_3243_, v___x_3244_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3248_; 
lean_dec_ref(v_alts_3242_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set_tag(v___x_3240_, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3245_);
v___x_3248_ = v___x_3240_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3245_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
else
{
uint8_t v___x_3250_; 
v___x_3250_ = lean_nat_dec_le(v___x_3244_, v___x_3244_);
if (v___x_3250_ == 0)
{
if (v___x_3246_ == 0)
{
lean_object* v___x_3252_; 
lean_dec_ref(v_alts_3242_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set_tag(v___x_3240_, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3245_);
v___x_3252_ = v___x_3240_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3245_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
else
{
size_t v___x_3254_; size_t v___x_3255_; lean_object* v___x_3256_; 
lean_del_object(v___x_3240_);
v___x_3254_ = ((size_t)0ULL);
v___x_3255_ = lean_usize_of_nat(v___x_3244_);
v___x_3256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3242_, v___x_3254_, v___x_3255_, v___x_3245_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
lean_dec_ref(v_alts_3242_);
return v___x_3256_;
}
}
else
{
size_t v___x_3257_; size_t v___x_3258_; lean_object* v___x_3259_; 
lean_del_object(v___x_3240_);
v___x_3257_ = ((size_t)0ULL);
v___x_3258_ = lean_usize_of_nat(v___x_3244_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3242_, v___x_3257_, v___x_3258_, v___x_3245_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
lean_dec_ref(v_alts_3242_);
return v___x_3259_;
}
}
}
}
case 5:
{
lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3268_; 
v_isSharedCheck_3268_ = !lean_is_exclusive(v_x_3193_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v_x_3193_, 0);
lean_dec(v_unused_3269_);
v___x_3262_ = v_x_3193_;
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
else
{
lean_dec(v_x_3193_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3264_ = lean_box(0);
if (v_isShared_3263_ == 0)
{
lean_ctor_set_tag(v___x_3262_, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3264_);
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
case 6:
{
lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3277_; 
v_isSharedCheck_3277_ = !lean_is_exclusive(v_x_3193_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v_x_3193_, 0);
lean_dec(v_unused_3278_);
v___x_3271_ = v_x_3193_;
v_isShared_3272_ = v_isSharedCheck_3277_;
goto v_resetjp_3270_;
}
else
{
lean_dec(v_x_3193_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3277_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3273_ = lean_box(0);
if (v_isShared_3272_ == 0)
{
lean_ctor_set_tag(v___x_3271_, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3273_);
v___x_3275_ = v___x_3271_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
default: 
{
lean_object* v_decl_3279_; lean_object* v_k_3280_; 
v_decl_3279_ = lean_ctor_get(v_x_3193_, 0);
lean_inc_ref(v_decl_3279_);
v_k_3280_ = lean_ctor_get(v_x_3193_, 1);
lean_inc_ref(v_k_3280_);
lean_dec_ref(v_x_3193_);
v_decl_3212_ = v_decl_3279_;
v_k_3213_ = v_k_3280_;
v___y_3214_ = v_a_3194_;
v___y_3215_ = v_a_3195_;
v___y_3216_ = v_a_3196_;
v___y_3217_ = v_a_3197_;
v___y_3218_ = v_a_3198_;
v___y_3219_ = v_a_3199_;
goto v___jp_3211_;
}
}
v___jp_3201_:
{
if (lean_obj_tag(v___y_3209_) == 0)
{
lean_dec_ref(v___y_3209_);
v_x_3193_ = v___y_3205_;
v_a_3194_ = v___y_3204_;
v_a_3195_ = v___y_3202_;
v_a_3196_ = v___y_3207_;
v_a_3197_ = v___y_3203_;
v_a_3198_ = v___y_3208_;
v_a_3199_ = v___y_3206_;
goto _start;
}
else
{
lean_dec_ref(v___y_3205_);
return v___y_3209_;
}
}
v___jp_3211_:
{
lean_object* v_params_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v_params_3220_ = lean_ctor_get(v_decl_3212_, 2);
lean_inc_ref(v_params_3220_);
lean_dec_ref(v_decl_3212_);
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = lean_array_get_size(v_params_3220_);
v___x_3223_ = lean_nat_dec_lt(v___x_3221_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_dec_ref(v_params_3220_);
v_x_3193_ = v_k_3213_;
v_a_3194_ = v___y_3214_;
v_a_3195_ = v___y_3215_;
v_a_3196_ = v___y_3216_;
v_a_3197_ = v___y_3217_;
v_a_3198_ = v___y_3218_;
v_a_3199_ = v___y_3219_;
goto _start;
}
else
{
lean_object* v___x_3225_; uint8_t v___x_3226_; 
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_nat_dec_le(v___x_3222_, v___x_3222_);
if (v___x_3226_ == 0)
{
if (v___x_3223_ == 0)
{
lean_dec_ref(v_params_3220_);
v_x_3193_ = v_k_3213_;
v_a_3194_ = v___y_3214_;
v_a_3195_ = v___y_3215_;
v_a_3196_ = v___y_3216_;
v_a_3197_ = v___y_3217_;
v_a_3198_ = v___y_3218_;
v_a_3199_ = v___y_3219_;
goto _start;
}
else
{
size_t v___x_3228_; size_t v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = ((size_t)0ULL);
v___x_3229_ = lean_usize_of_nat(v___x_3222_);
v___x_3230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3220_, v___x_3228_, v___x_3229_, v___x_3225_, v___y_3214_, v___y_3215_);
lean_dec_ref(v_params_3220_);
v___y_3202_ = v___y_3215_;
v___y_3203_ = v___y_3217_;
v___y_3204_ = v___y_3214_;
v___y_3205_ = v_k_3213_;
v___y_3206_ = v___y_3219_;
v___y_3207_ = v___y_3216_;
v___y_3208_ = v___y_3218_;
v___y_3209_ = v___x_3230_;
goto v___jp_3201_;
}
}
else
{
size_t v___x_3231_; size_t v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = ((size_t)0ULL);
v___x_3232_ = lean_usize_of_nat(v___x_3222_);
v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3220_, v___x_3231_, v___x_3232_, v___x_3225_, v___y_3214_, v___y_3215_);
lean_dec_ref(v_params_3220_);
v___y_3202_ = v___y_3215_;
v___y_3203_ = v___y_3217_;
v___y_3204_ = v___y_3214_;
v___y_3205_ = v_k_3213_;
v___y_3206_ = v___y_3219_;
v___y_3207_ = v___y_3216_;
v___y_3208_ = v___y_3218_;
v___y_3209_ = v___x_3233_;
goto v___jp_3201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3281_, size_t v_i_3282_, size_t v_stop_3283_, lean_object* v_b_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___y_3293_; uint8_t v___x_3299_; 
v___x_3299_ = lean_usize_dec_eq(v_i_3282_, v_stop_3283_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_array_uget_borrowed(v_as_3281_, v_i_3282_);
switch(lean_obj_tag(v___x_3300_))
{
case 0:
{
lean_object* v_code_3301_; 
v_code_3301_ = lean_ctor_get(v___x_3300_, 2);
lean_inc_ref(v_code_3301_);
v___y_3293_ = v_code_3301_;
goto v___jp_3292_;
}
case 1:
{
lean_object* v_code_3302_; 
v_code_3302_ = lean_ctor_get(v___x_3300_, 1);
lean_inc_ref(v_code_3302_);
v___y_3293_ = v_code_3302_;
goto v___jp_3292_;
}
default: 
{
lean_object* v_code_3303_; 
v_code_3303_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_code_3303_);
v___y_3293_ = v_code_3303_;
goto v___jp_3292_;
}
}
}
else
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v_b_3284_);
return v___x_3304_;
}
v___jp_3292_:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3293_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; size_t v___x_3296_; size_t v___x_3297_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref(v___x_3294_);
v___x_3296_ = ((size_t)1ULL);
v___x_3297_ = lean_usize_add(v_i_3282_, v___x_3296_);
v_i_3282_ = v___x_3297_;
v_b_3284_ = v_a_3295_;
goto _start;
}
else
{
return v___x_3294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3305_, lean_object* v_i_3306_, lean_object* v_stop_3307_, lean_object* v_b_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
size_t v_i_boxed_3316_; size_t v_stop_boxed_3317_; lean_object* v_res_3318_; 
v_i_boxed_3316_ = lean_unbox_usize(v_i_3306_);
lean_dec(v_i_3306_);
v_stop_boxed_3317_ = lean_unbox_usize(v_stop_3307_);
lean_dec(v_stop_3307_);
v_res_3318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3305_, v_i_boxed_3316_, v_stop_boxed_3317_, v_b_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec_ref(v_as_3305_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3328_, size_t v_i_3329_, size_t v_stop_3330_, lean_object* v_b_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3328_, v_i_3329_, v_stop_3330_, v_b_3331_, v___y_3332_, v___y_3333_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3340_, lean_object* v_i_3341_, lean_object* v_stop_3342_, lean_object* v_b_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
size_t v_i_boxed_3351_; size_t v_stop_boxed_3352_; lean_object* v_res_3353_; 
v_i_boxed_3351_ = lean_unbox_usize(v_i_3341_);
lean_dec(v_i_3341_);
v_stop_boxed_3352_ = lean_unbox_usize(v_stop_3342_);
lean_dec(v_stop_3342_);
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3340_, v_i_boxed_3351_, v_stop_boxed_3352_, v_b_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec_ref(v_as_3340_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3354_, lean_object* v_b_3355_){
_start:
{
lean_object* v_array_3356_; lean_object* v_start_3357_; lean_object* v_stop_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3371_; 
v_array_3356_ = lean_ctor_get(v_a_3354_, 0);
v_start_3357_ = lean_ctor_get(v_a_3354_, 1);
v_stop_3358_ = lean_ctor_get(v_a_3354_, 2);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_a_3354_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3360_ = v_a_3354_;
v_isShared_3361_ = v_isSharedCheck_3371_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_stop_3358_);
lean_inc(v_start_3357_);
lean_inc(v_array_3356_);
lean_dec(v_a_3354_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3371_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_nat_dec_lt(v_start_3357_, v_stop_3358_);
if (v___x_3362_ == 0)
{
lean_del_object(v___x_3360_);
lean_dec(v_stop_3358_);
lean_dec(v_start_3357_);
lean_dec_ref(v_array_3356_);
return v_b_3355_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3363_ = lean_unsigned_to_nat(1u);
v___x_3364_ = lean_nat_add(v_start_3357_, v___x_3363_);
lean_inc_ref(v_array_3356_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v___x_3364_);
v___x_3366_ = v___x_3360_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_array_3356_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_stop_3358_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_array_fget(v_array_3356_, v_start_3357_);
lean_dec(v_start_3357_);
lean_dec_ref(v_array_3356_);
v___x_3368_ = lean_array_push(v_b_3355_, v___x_3367_);
v_a_3354_ = v___x_3366_;
v_b_3355_ = v___x_3368_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3372_, size_t v_i_3373_, lean_object* v_bs_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_usize_dec_lt(v_i_3373_, v_sz_3372_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_bs_3374_);
return v___x_3379_;
}
else
{
lean_object* v_v_3380_; lean_object* v___x_3381_; 
v_v_3380_ = lean_array_uget_borrowed(v_bs_3374_, v_i_3373_);
v___x_3381_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3380_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; lean_object* v_bs_x27_3384_; size_t v___x_3385_; size_t v___x_3386_; lean_object* v___x_3387_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3381_);
v___x_3383_ = lean_unsigned_to_nat(0u);
v_bs_x27_3384_ = lean_array_uset(v_bs_3374_, v_i_3373_, v___x_3383_);
v___x_3385_ = ((size_t)1ULL);
v___x_3386_ = lean_usize_add(v_i_3373_, v___x_3385_);
v___x_3387_ = lean_array_uset(v_bs_x27_3384_, v_i_3373_, v_a_3382_);
v_i_3373_ = v___x_3386_;
v_bs_3374_ = v___x_3387_;
goto _start;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v_bs_3374_);
v_a_3389_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3381_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3381_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3397_, lean_object* v_i_3398_, lean_object* v_bs_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
size_t v_sz_boxed_3403_; size_t v_i_boxed_3404_; lean_object* v_res_3405_; 
v_sz_boxed_3403_ = lean_unbox_usize(v_sz_3397_);
lean_dec(v_sz_3397_);
v_i_boxed_3404_ = lean_unbox_usize(v_i_3398_);
lean_dec(v_i_3398_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3403_, v_i_boxed_3404_, v_bs_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3406_, size_t v_i_3407_, size_t v_stop_3408_, lean_object* v_b_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
uint8_t v___x_3414_; 
v___x_3414_ = lean_usize_dec_eq(v_i_3407_, v_stop_3408_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v_fvarId_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3415_ = lean_array_uget_borrowed(v_as_3406_, v_i_3407_);
v_fvarId_3416_ = lean_ctor_get(v___x_3415_, 0);
v___x_3417_ = lean_box(1);
lean_inc(v_fvarId_3416_);
v___x_3418_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3416_, v___x_3417_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; size_t v___x_3420_; size_t v___x_3421_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref(v___x_3418_);
v___x_3420_ = ((size_t)1ULL);
v___x_3421_ = lean_usize_add(v_i_3407_, v___x_3420_);
v_i_3407_ = v___x_3421_;
v_b_3409_ = v_a_3419_;
goto _start;
}
else
{
return v___x_3418_;
}
}
else
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v_b_3409_);
return v___x_3423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3424_, lean_object* v_i_3425_, lean_object* v_stop_3426_, lean_object* v_b_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
size_t v_i_boxed_3432_; size_t v_stop_boxed_3433_; lean_object* v_res_3434_; 
v_i_boxed_3432_ = lean_unbox_usize(v_i_3425_);
lean_dec(v_i_3425_);
v_stop_boxed_3433_ = lean_unbox_usize(v_stop_3426_);
lean_dec(v_stop_3426_);
v_res_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3424_, v_i_boxed_3432_, v_stop_boxed_3433_, v_b_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v_as_3424_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3435_, size_t v_i_3436_, size_t v_stop_3437_, lean_object* v_b_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_usize_dec_eq(v_i_3436_, v_stop_3437_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v_fst_3445_; lean_object* v_snd_3446_; lean_object* v_fvarId_3447_; lean_object* v___x_3448_; 
v___x_3444_ = lean_array_uget_borrowed(v_as_3435_, v_i_3436_);
v_fst_3445_ = lean_ctor_get(v___x_3444_, 0);
v_snd_3446_ = lean_ctor_get(v___x_3444_, 1);
v_fvarId_3447_ = lean_ctor_get(v_fst_3445_, 0);
lean_inc(v_snd_3446_);
lean_inc(v_fvarId_3447_);
v___x_3448_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3447_, v_snd_3446_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; size_t v___x_3450_; size_t v___x_3451_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref(v___x_3448_);
v___x_3450_ = ((size_t)1ULL);
v___x_3451_ = lean_usize_add(v_i_3436_, v___x_3450_);
v_i_3436_ = v___x_3451_;
v_b_3438_ = v_a_3449_;
goto _start;
}
else
{
return v___x_3448_;
}
}
else
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v_b_3438_);
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3454_, lean_object* v_i_3455_, lean_object* v_stop_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
size_t v_i_boxed_3462_; size_t v_stop_boxed_3463_; lean_object* v_res_3464_; 
v_i_boxed_3462_ = lean_unbox_usize(v_i_3455_);
lean_dec(v_i_3455_);
v_stop_boxed_3463_ = lean_unbox_usize(v_stop_3456_);
lean_dec(v_stop_3456_);
v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3454_, v_i_boxed_3462_, v_stop_boxed_3463_, v_b_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v_as_3454_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3467_, size_t v_i_3468_, size_t v_stop_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_usize_dec_eq(v_i_3468_, v_stop_3469_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = lean_array_uget_borrowed(v_as_3467_, v_i_3468_);
v___x_3480_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3479_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; size_t v___x_3482_; size_t v___x_3483_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3480_);
v___x_3482_ = ((size_t)1ULL);
v___x_3483_ = lean_usize_add(v_i_3468_, v___x_3482_);
v_i_3468_ = v___x_3483_;
v_b_3470_ = v_a_3481_;
goto _start;
}
else
{
return v___x_3480_;
}
}
else
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_b_3470_);
return v___x_3485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___y_3501_; 
switch(lean_obj_tag(v_letVal_3486_))
{
case 0:
{
lean_object* v_value_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3518_; 
v_value_3510_ = lean_ctor_get(v_letVal_3486_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_letVal_3486_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3512_ = v_letVal_3486_;
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_value_3510_);
lean_dec(v_letVal_3486_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3514_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3510_);
lean_dec_ref(v_value_3510_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3514_);
v___x_3516_ = v___x_3512_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
case 1:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_box(1);
v___x_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
return v___x_3520_;
}
case 2:
{
lean_object* v_idx_3521_; lean_object* v_struct_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_idx_3521_ = lean_ctor_get(v_letVal_3486_, 1);
lean_inc(v_idx_3521_);
v_struct_3522_ = lean_ctor_get(v_letVal_3486_, 2);
lean_inc(v_struct_3522_);
lean_dec_ref(v_letVal_3486_);
v___x_3523_ = lean_st_ref_get(v_a_3492_);
v___x_3524_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3522_, v_a_3487_, v_a_3488_);
lean_dec(v_struct_3522_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3534_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3534_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3534_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v_env_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
v_env_3529_ = lean_ctor_get(v___x_3523_, 0);
lean_inc_ref(v_env_3529_);
lean_dec(v___x_3523_);
v___x_3530_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3529_, v_a_3525_, v_idx_3521_);
lean_dec(v_idx_3521_);
lean_dec(v_a_3525_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3530_);
v___x_3532_ = v___x_3527_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
else
{
lean_dec(v___x_3523_);
lean_dec(v_idx_3521_);
return v___x_3524_;
}
}
case 3:
{
lean_object* v_declName_3535_; lean_object* v_args_3536_; lean_object* v___x_3537_; lean_object* v_env_3538_; lean_object* v___x_3539_; lean_object* v_numFields_3541_; lean_object* v_lower_3542_; lean_object* v_upper_3543_; lean_object* v___x_3571_; lean_object* v___y_3640_; uint8_t v___x_3649_; 
v_declName_3535_ = lean_ctor_get(v_letVal_3486_, 0);
lean_inc(v_declName_3535_);
v_args_3536_ = lean_ctor_get(v_letVal_3486_, 2);
lean_inc_ref(v_args_3536_);
lean_dec_ref(v_letVal_3486_);
v___x_3537_ = lean_st_ref_get(v_a_3492_);
v_env_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc_ref(v_env_3538_);
lean_dec(v___x_3537_);
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3571_ = lean_array_get_size(v_args_3536_);
v___x_3649_ = lean_nat_dec_lt(v___x_3539_, v___x_3571_);
if (v___x_3649_ == 0)
{
goto v___jp_3572_;
}
else
{
lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3650_ = lean_box(0);
v___x_3651_ = lean_nat_dec_le(v___x_3571_, v___x_3571_);
if (v___x_3651_ == 0)
{
if (v___x_3649_ == 0)
{
goto v___jp_3572_;
}
else
{
size_t v___x_3652_; size_t v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = ((size_t)0ULL);
v___x_3653_ = lean_usize_of_nat(v___x_3571_);
v___x_3654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3536_, v___x_3652_, v___x_3653_, v___x_3650_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
v___y_3640_ = v___x_3654_;
goto v___jp_3639_;
}
}
else
{
size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = ((size_t)0ULL);
v___x_3656_ = lean_usize_of_nat(v___x_3571_);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3536_, v___x_3655_, v___x_3656_, v___x_3650_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
v___y_3640_ = v___x_3657_;
goto v___jp_3639_;
}
}
v___jp_3540_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3544_ = l_Array_toSubarray___redArg(v_args_3536_, v_lower_3542_, v_upper_3543_);
v___x_3545_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3546_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3544_, v___x_3545_);
v___x_3547_ = lean_array_get_size(v___x_3546_);
v___x_3548_ = lean_nat_dec_eq(v_numFields_3541_, v___x_3547_);
lean_dec(v_numFields_3541_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref(v___x_3546_);
lean_dec(v_declName_3535_);
v___x_3549_ = lean_box(1);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
else
{
size_t v_sz_3551_; size_t v___x_3552_; lean_object* v___x_3553_; 
v_sz_3551_ = lean_array_size(v___x_3546_);
v___x_3552_ = ((size_t)0ULL);
v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3551_, v___x_3552_, v___x_3546_, v_a_3487_, v_a_3488_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3562_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3562_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3562_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3558_, 0, v_declName_3535_);
lean_ctor_set(v___x_3558_, 1, v_a_3554_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3558_);
v___x_3560_ = v___x_3556_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec(v_declName_3535_);
v_a_3563_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3553_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3553_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
v___jp_3572_:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3489_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref(v___x_3573_);
v___x_3575_ = lean_unbox(v_a_3574_);
lean_dec(v_a_3574_);
lean_inc(v_declName_3535_);
v___x_3576_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3535_, v___x_3575_, v_a_3491_, v_a_3492_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3622_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3622_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3622_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
if (lean_obj_tag(v_a_3577_) == 1)
{
lean_object* v_val_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; 
lean_dec_ref(v_args_3536_);
v_val_3581_ = lean_ctor_get(v_a_3577_, 0);
lean_inc(v_val_3581_);
lean_dec_ref(v_a_3577_);
v___x_3582_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3581_);
lean_dec(v_val_3581_);
v___x_3583_ = lean_nat_dec_eq(v___x_3582_, v___x_3571_);
lean_dec(v___x_3582_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; lean_object* v___x_3586_; 
lean_dec_ref(v_env_3538_);
lean_dec(v_declName_3535_);
v___x_3584_ = lean_box(1);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3584_);
v___x_3586_ = v___x_3579_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
else
{
lean_object* v___x_3588_; 
lean_inc(v_declName_3535_);
v___x_3588_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3538_, v_declName_3535_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3589_; 
lean_del_object(v___x_3579_);
v___x_3589_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3535_, v_a_3487_, v_a_3488_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3602_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3602_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3602_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
if (lean_obj_tag(v_a_3590_) == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = lean_box(1);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3594_);
v___x_3596_ = v___x_3592_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
else
{
lean_object* v_val_3598_; lean_object* v___x_3600_; 
v_val_3598_ = lean_ctor_get(v_a_3590_, 0);
lean_inc(v_val_3598_);
lean_dec_ref(v_a_3590_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v_val_3598_);
v___x_3600_ = v___x_3592_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_val_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
v_a_3603_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3589_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3589_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_val_3611_; lean_object* v___x_3613_; 
lean_dec(v_declName_3535_);
v_val_3611_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_val_3611_);
lean_dec_ref(v___x_3588_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v_val_3611_);
v___x_3613_ = v___x_3579_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_val_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
else
{
uint8_t v___x_3615_; lean_object* v___x_3616_; 
lean_del_object(v___x_3579_);
lean_dec(v_a_3577_);
v___x_3615_ = 0;
lean_inc(v_declName_3535_);
v___x_3616_ = l_Lean_Environment_find_x3f(v_env_3538_, v_declName_3535_, v___x_3615_);
if (lean_obj_tag(v___x_3616_) == 1)
{
lean_object* v_val_3617_; 
v_val_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_val_3617_);
lean_dec_ref(v___x_3616_);
if (lean_obj_tag(v_val_3617_) == 6)
{
lean_object* v_val_3618_; lean_object* v_numParams_3619_; lean_object* v_numFields_3620_; uint8_t v___x_3621_; 
v_val_3618_ = lean_ctor_get(v_val_3617_, 0);
lean_inc_ref(v_val_3618_);
lean_dec_ref(v_val_3617_);
v_numParams_3619_ = lean_ctor_get(v_val_3618_, 3);
lean_inc(v_numParams_3619_);
v_numFields_3620_ = lean_ctor_get(v_val_3618_, 4);
lean_inc(v_numFields_3620_);
lean_dec_ref(v_val_3618_);
v___x_3621_ = lean_nat_dec_le(v_numParams_3619_, v___x_3539_);
if (v___x_3621_ == 0)
{
v_numFields_3541_ = v_numFields_3620_;
v_lower_3542_ = v_numParams_3619_;
v_upper_3543_ = v___x_3571_;
goto v___jp_3540_;
}
else
{
lean_dec(v_numParams_3619_);
v_numFields_3541_ = v_numFields_3620_;
v_lower_3542_ = v___x_3539_;
v_upper_3543_ = v___x_3571_;
goto v___jp_3540_;
}
}
else
{
lean_dec(v_val_3617_);
lean_dec_ref(v_args_3536_);
lean_dec(v_declName_3535_);
goto v___jp_3494_;
}
}
else
{
lean_dec(v___x_3616_);
lean_dec_ref(v_args_3536_);
lean_dec(v_declName_3535_);
goto v___jp_3494_;
}
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref(v_env_3538_);
lean_dec_ref(v_args_3536_);
lean_dec(v_declName_3535_);
v_a_3623_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3576_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3576_);
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
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref(v_env_3538_);
lean_dec_ref(v_args_3536_);
lean_dec(v_declName_3535_);
v_a_3631_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3573_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3573_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
v___jp_3639_:
{
if (lean_obj_tag(v___y_3640_) == 0)
{
lean_dec_ref(v___y_3640_);
goto v___jp_3572_;
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec_ref(v_env_3538_);
lean_dec_ref(v_args_3536_);
lean_dec(v_declName_3535_);
v_a_3641_ = lean_ctor_get(v___y_3640_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___y_3640_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___y_3640_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___y_3640_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
default: 
{
lean_object* v_args_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v_args_3658_ = lean_ctor_get(v_letVal_3486_, 1);
lean_inc_ref(v_args_3658_);
lean_dec_ref(v_letVal_3486_);
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = lean_array_get_size(v_args_3658_);
v___x_3661_ = lean_nat_dec_lt(v___x_3659_, v___x_3660_);
if (v___x_3661_ == 0)
{
lean_dec_ref(v_args_3658_);
goto v___jp_3497_;
}
else
{
lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3662_ = lean_box(0);
v___x_3663_ = lean_nat_dec_le(v___x_3660_, v___x_3660_);
if (v___x_3663_ == 0)
{
if (v___x_3661_ == 0)
{
lean_dec_ref(v_args_3658_);
goto v___jp_3497_;
}
else
{
size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = ((size_t)0ULL);
v___x_3665_ = lean_usize_of_nat(v___x_3660_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3658_, v___x_3664_, v___x_3665_, v___x_3662_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
lean_dec_ref(v_args_3658_);
v___y_3501_ = v___x_3666_;
goto v___jp_3500_;
}
}
else
{
size_t v___x_3667_; size_t v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = ((size_t)0ULL);
v___x_3668_ = lean_usize_of_nat(v___x_3660_);
v___x_3669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3658_, v___x_3667_, v___x_3668_, v___x_3662_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
lean_dec_ref(v_args_3658_);
v___y_3501_ = v___x_3669_;
goto v___jp_3500_;
}
}
}
}
v___jp_3494_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = lean_box(1);
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
return v___x_3496_;
}
v___jp_3497_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_box(1);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
v___jp_3500_:
{
if (lean_obj_tag(v___y_3501_) == 0)
{
lean_dec_ref(v___y_3501_);
goto v___jp_3497_;
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
v_a_3502_ = lean_ctor_get(v___y_3501_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___y_3501_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___y_3501_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___y_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3670_, lean_object* v_args_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_params_3679_; lean_object* v_value_3680_; lean_object* v___x_3681_; 
v_params_3679_ = lean_ctor_get(v_funDecl_3670_, 2);
lean_inc_ref(v_params_3679_);
v_value_3680_ = lean_ctor_get(v_funDecl_3670_, 4);
lean_inc_ref(v_value_3680_);
lean_dec_ref(v_funDecl_3670_);
v___x_3681_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3679_, v_args_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3693_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3684_ = v___x_3681_;
v_isShared_3685_ = v_isSharedCheck_3693_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3681_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3693_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_unbox(v_a_3682_);
lean_dec(v_a_3682_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
lean_dec_ref(v_value_3680_);
v___x_3687_ = lean_box(0);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3687_);
v___x_3689_ = v___x_3684_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
else
{
lean_object* v___x_3691_; 
lean_del_object(v___x_3684_);
lean_inc_ref(v_value_3680_);
v___x_3691_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3680_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v___x_3692_; 
lean_dec_ref(v___x_3691_);
v___x_3692_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3680_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3692_;
}
else
{
lean_dec_ref(v_value_3680_);
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v_value_3680_);
v_a_3694_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3681_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3681_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3702_, lean_object* v_as_3703_, size_t v_sz_3704_, size_t v_i_3705_, lean_object* v_b_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_a_3715_; uint8_t v___x_3719_; 
v___x_3719_ = lean_usize_dec_lt(v_i_3705_, v_sz_3704_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_dec(v_a_3702_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_b_3706_);
return v___x_3720_;
}
else
{
lean_object* v___x_3721_; lean_object* v_a_3722_; 
v___x_3721_ = lean_box(0);
v_a_3722_ = lean_array_uget_borrowed(v_as_3703_, v_i_3705_);
if (lean_obj_tag(v_a_3722_) == 0)
{
lean_object* v_ctorName_3723_; lean_object* v_params_3724_; lean_object* v_code_3725_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3735_; lean_object* v___y_3737_; lean_object* v___x_3738_; 
v_ctorName_3723_ = lean_ctor_get(v_a_3722_, 0);
v_params_3724_ = lean_ctor_get(v_a_3722_, 1);
v_code_3725_ = lean_ctor_get(v_a_3722_, 2);
lean_inc(v_a_3702_);
v___x_3738_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3702_, v_ctorName_3723_);
if (lean_obj_tag(v___x_3738_) == 1)
{
lean_object* v_val_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v_val_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_val_3739_);
lean_dec_ref(v___x_3738_);
v___x_3740_ = l_Array_zip___redArg(v_params_3724_, v_val_3739_);
lean_dec(v_val_3739_);
v___x_3741_ = lean_unsigned_to_nat(0u);
v___x_3742_ = lean_array_get_size(v___x_3740_);
v___x_3743_ = lean_nat_dec_lt(v___x_3741_, v___x_3742_);
if (v___x_3743_ == 0)
{
lean_dec_ref(v___x_3740_);
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
v___y_3732_ = v___y_3712_;
goto v___jp_3726_;
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = lean_nat_dec_le(v___x_3742_, v___x_3742_);
if (v___x_3744_ == 0)
{
if (v___x_3743_ == 0)
{
lean_dec_ref(v___x_3740_);
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
v___y_3732_ = v___y_3712_;
goto v___jp_3726_;
}
else
{
size_t v___x_3745_; size_t v___x_3746_; lean_object* v___x_3747_; 
v___x_3745_ = ((size_t)0ULL);
v___x_3746_ = lean_usize_of_nat(v___x_3742_);
v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3740_, v___x_3745_, v___x_3746_, v___x_3721_, v___y_3707_, v___y_3708_, v___y_3712_);
lean_dec_ref(v___x_3740_);
v___y_3735_ = v___x_3747_;
goto v___jp_3734_;
}
}
else
{
size_t v___x_3748_; size_t v___x_3749_; lean_object* v___x_3750_; 
v___x_3748_ = ((size_t)0ULL);
v___x_3749_ = lean_usize_of_nat(v___x_3742_);
v___x_3750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3740_, v___x_3748_, v___x_3749_, v___x_3721_, v___y_3707_, v___y_3708_, v___y_3712_);
lean_dec_ref(v___x_3740_);
v___y_3735_ = v___x_3750_;
goto v___jp_3734_;
}
}
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
lean_dec(v___x_3738_);
v___x_3751_ = lean_unsigned_to_nat(0u);
v___x_3752_ = lean_array_get_size(v_params_3724_);
v___x_3753_ = lean_nat_dec_lt(v___x_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
v___y_3732_ = v___y_3712_;
goto v___jp_3726_;
}
else
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_nat_dec_le(v___x_3752_, v___x_3752_);
if (v___x_3754_ == 0)
{
if (v___x_3753_ == 0)
{
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
v___y_3732_ = v___y_3712_;
goto v___jp_3726_;
}
else
{
size_t v___x_3755_; size_t v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = ((size_t)0ULL);
v___x_3756_ = lean_usize_of_nat(v___x_3752_);
v___x_3757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3724_, v___x_3755_, v___x_3756_, v___x_3721_, v___y_3707_, v___y_3708_, v___y_3712_);
v___y_3737_ = v___x_3757_;
goto v___jp_3736_;
}
}
else
{
size_t v___x_3758_; size_t v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = ((size_t)0ULL);
v___x_3759_ = lean_usize_of_nat(v___x_3752_);
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3724_, v___x_3758_, v___x_3759_, v___x_3721_, v___y_3707_, v___y_3708_, v___y_3712_);
v___y_3737_ = v___x_3760_;
goto v___jp_3736_;
}
}
}
v___jp_3726_:
{
lean_object* v___x_3733_; 
lean_inc_ref(v_code_3725_);
v___x_3733_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3725_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_dec_ref(v___x_3733_);
v_a_3715_ = v___x_3721_;
goto v___jp_3714_;
}
else
{
lean_dec(v_a_3702_);
return v___x_3733_;
}
}
v___jp_3734_:
{
if (lean_obj_tag(v___y_3735_) == 0)
{
lean_dec_ref(v___y_3735_);
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
v___y_3732_ = v___y_3712_;
goto v___jp_3726_;
}
else
{
lean_dec(v_a_3702_);
return v___y_3735_;
}
}
v___jp_3736_:
{
if (lean_obj_tag(v___y_3737_) == 0)
{
lean_dec_ref(v___y_3737_);
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
v___y_3732_ = v___y_3712_;
goto v___jp_3726_;
}
else
{
lean_dec(v_a_3702_);
return v___y_3737_;
}
}
}
else
{
lean_object* v_code_3761_; lean_object* v___x_3762_; 
v_code_3761_ = lean_ctor_get(v_a_3722_, 0);
lean_inc_ref(v_code_3761_);
v___x_3762_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3761_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec_ref(v___x_3762_);
v_a_3715_ = v___x_3721_;
goto v___jp_3714_;
}
else
{
lean_dec(v_a_3702_);
return v___x_3762_;
}
}
}
v___jp_3714_:
{
size_t v___x_3716_; size_t v___x_3717_; 
v___x_3716_ = ((size_t)1ULL);
v___x_3717_ = lean_usize_add(v_i_3705_, v___x_3716_);
v_i_3705_ = v___x_3717_;
v_b_3706_ = v_a_3715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
lean_object* v_decl_3772_; lean_object* v_k_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; 
switch(lean_obj_tag(v_x_3763_))
{
case 0:
{
lean_object* v_decl_3783_; lean_object* v_k_3784_; lean_object* v_fvarId_3785_; lean_object* v_value_3786_; lean_object* v___x_3787_; 
v_decl_3783_ = lean_ctor_get(v_x_3763_, 0);
lean_inc_ref(v_decl_3783_);
v_k_3784_ = lean_ctor_get(v_x_3763_, 1);
lean_inc_ref(v_k_3784_);
lean_dec_ref(v_x_3763_);
v_fvarId_3785_ = lean_ctor_get(v_decl_3783_, 0);
lean_inc(v_fvarId_3785_);
v_value_3786_ = lean_ctor_get(v_decl_3783_, 3);
lean_inc_n(v_value_3786_, 2);
lean_dec_ref(v_decl_3783_);
v___x_3787_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3786_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
v___x_3789_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3785_, v_a_3788_, v_a_3764_, v_a_3765_, v_a_3769_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_dec_ref(v___x_3789_);
if (lean_obj_tag(v_value_3786_) == 4)
{
lean_object* v_fvarId_3790_; lean_object* v_args_3791_; uint8_t v___x_3792_; lean_object* v___x_3793_; 
v_fvarId_3790_ = lean_ctor_get(v_value_3786_, 0);
lean_inc(v_fvarId_3790_);
v_args_3791_ = lean_ctor_get(v_value_3786_, 1);
lean_inc_ref(v_args_3791_);
lean_dec_ref(v_value_3786_);
v___x_3792_ = 0;
v___x_3793_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3792_, v_fvarId_3790_, v_a_3767_);
lean_dec(v_fvarId_3790_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3793_);
if (lean_obj_tag(v_a_3794_) == 1)
{
lean_object* v_val_3795_; lean_object* v___x_3796_; 
v_val_3795_ = lean_ctor_get(v_a_3794_, 0);
lean_inc(v_val_3795_);
lean_dec_ref(v_a_3794_);
v___x_3796_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3795_, v_args_3791_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_dec_ref(v___x_3796_);
v_x_3763_ = v_k_3784_;
goto _start;
}
else
{
lean_dec_ref(v_k_3784_);
return v___x_3796_;
}
}
else
{
lean_dec(v_a_3794_);
lean_dec_ref(v_args_3791_);
v_x_3763_ = v_k_3784_;
goto _start;
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_args_3791_);
lean_dec_ref(v_k_3784_);
v_a_3799_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3793_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3793_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_dec(v_value_3786_);
v_x_3763_ = v_k_3784_;
goto _start;
}
}
else
{
lean_dec(v_value_3786_);
lean_dec_ref(v_k_3784_);
return v___x_3789_;
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_value_3786_);
lean_dec(v_fvarId_3785_);
lean_dec_ref(v_k_3784_);
v_a_3808_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3787_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3787_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3816_; lean_object* v_args_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; 
v_fvarId_3816_ = lean_ctor_get(v_x_3763_, 0);
lean_inc(v_fvarId_3816_);
v_args_3817_ = lean_ctor_get(v_x_3763_, 1);
lean_inc_ref(v_args_3817_);
lean_dec_ref(v_x_3763_);
v___x_3818_ = 0;
v___x_3819_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3818_, v_fvarId_3816_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___y_3822_; lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3819_);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = lean_array_get_size(v_args_3817_);
v___x_3826_ = lean_nat_dec_lt(v___x_3824_, v___x_3825_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; 
v___x_3827_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3820_, v_args_3817_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
return v___x_3827_;
}
else
{
lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3828_ = lean_box(0);
v___x_3829_ = lean_nat_dec_le(v___x_3825_, v___x_3825_);
if (v___x_3829_ == 0)
{
if (v___x_3826_ == 0)
{
lean_object* v___x_3830_; 
v___x_3830_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3820_, v_args_3817_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
return v___x_3830_;
}
else
{
size_t v___x_3831_; size_t v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = ((size_t)0ULL);
v___x_3832_ = lean_usize_of_nat(v___x_3825_);
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3817_, v___x_3831_, v___x_3832_, v___x_3828_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
v___y_3822_ = v___x_3833_;
goto v___jp_3821_;
}
}
else
{
size_t v___x_3834_; size_t v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = ((size_t)0ULL);
v___x_3835_ = lean_usize_of_nat(v___x_3825_);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3817_, v___x_3834_, v___x_3835_, v___x_3828_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
v___y_3822_ = v___x_3836_;
goto v___jp_3821_;
}
}
v___jp_3821_:
{
if (lean_obj_tag(v___y_3822_) == 0)
{
lean_object* v___x_3823_; 
lean_dec_ref(v___y_3822_);
v___x_3823_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3820_, v_args_3817_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
return v___x_3823_;
}
else
{
lean_dec(v_a_3820_);
lean_dec_ref(v_args_3817_);
return v___y_3822_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_args_3817_);
v_a_3837_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3819_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3819_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
case 4:
{
lean_object* v_cases_3845_; lean_object* v_discr_3846_; lean_object* v_alts_3847_; lean_object* v___x_3848_; 
v_cases_3845_ = lean_ctor_get(v_x_3763_, 0);
lean_inc_ref(v_cases_3845_);
lean_dec_ref(v_x_3763_);
v_discr_3846_ = lean_ctor_get(v_cases_3845_, 2);
lean_inc(v_discr_3846_);
v_alts_3847_ = lean_ctor_get(v_cases_3845_, 3);
lean_inc_ref(v_alts_3847_);
lean_dec_ref(v_cases_3845_);
v___x_3848_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3846_, v_a_3764_, v_a_3765_);
lean_dec(v_discr_3846_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3850_; size_t v_sz_3851_; size_t v___x_3852_; lean_object* v___x_3853_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref(v___x_3848_);
v___x_3850_ = lean_box(0);
v_sz_3851_ = lean_array_size(v_alts_3847_);
v___x_3852_ = ((size_t)0ULL);
v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3849_, v_alts_3847_, v_sz_3851_, v___x_3852_, v___x_3850_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec_ref(v_alts_3847_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3860_ == 0)
{
lean_object* v_unused_3861_; 
v_unused_3861_ = lean_ctor_get(v___x_3853_, 0);
lean_dec(v_unused_3861_);
v___x_3855_ = v___x_3853_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_dec(v___x_3853_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3850_);
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3850_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
else
{
return v___x_3853_;
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v_alts_3847_);
v_a_3862_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3848_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3848_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3870_; lean_object* v___x_3871_; 
v_fvarId_3870_ = lean_ctor_get(v_x_3763_, 0);
lean_inc(v_fvarId_3870_);
lean_dec_ref(v_x_3763_);
v___x_3871_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3870_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v___x_3872_; 
lean_dec_ref(v___x_3871_);
v___x_3872_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3870_, v_a_3764_, v_a_3765_);
lean_dec(v_fvarId_3870_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3874_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref(v___x_3872_);
v___x_3874_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3873_, v_a_3764_, v_a_3765_, v_a_3769_);
return v___x_3874_;
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3872_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3872_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_dec(v_fvarId_3870_);
return v___x_3871_;
}
}
case 6:
{
lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
v_isSharedCheck_3890_ = !lean_is_exclusive(v_x_3763_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v_x_3763_, 0);
lean_dec(v_unused_3891_);
v___x_3884_ = v_x_3763_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_dec(v_x_3763_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = lean_box(0);
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
default: 
{
lean_object* v_decl_3892_; lean_object* v_k_3893_; 
v_decl_3892_ = lean_ctor_get(v_x_3763_, 0);
lean_inc_ref(v_decl_3892_);
v_k_3893_ = lean_ctor_get(v_x_3763_, 1);
lean_inc_ref(v_k_3893_);
lean_dec_ref(v_x_3763_);
v_decl_3772_ = v_decl_3892_;
v_k_3773_ = v_k_3893_;
v___y_3774_ = v_a_3764_;
v___y_3775_ = v_a_3765_;
v___y_3776_ = v_a_3766_;
v___y_3777_ = v_a_3767_;
v___y_3778_ = v_a_3768_;
v___y_3779_ = v_a_3769_;
goto v___jp_3771_;
}
}
v___jp_3771_:
{
lean_object* v_value_3780_; lean_object* v___x_3781_; 
v_value_3780_ = lean_ctor_get(v_decl_3772_, 4);
lean_inc_ref(v_value_3780_);
lean_dec_ref(v_decl_3772_);
v___x_3781_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3780_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_dec_ref(v___x_3781_);
v_x_3763_ = v_k_3773_;
v_a_3764_ = v___y_3774_;
v_a_3765_ = v___y_3775_;
v_a_3766_ = v___y_3776_;
v_a_3767_ = v___y_3777_;
v_a_3768_ = v___y_3778_;
v_a_3769_ = v___y_3779_;
goto _start;
}
else
{
lean_dec_ref(v_k_3773_);
return v___x_3781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
uint8_t v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = 0;
v___x_3903_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3902_, v_var_3894_, v_a_3898_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3936_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3936_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3936_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
if (lean_obj_tag(v_a_3904_) == 1)
{
lean_object* v_val_3908_; lean_object* v_params_3909_; lean_object* v_value_3910_; lean_object* v___x_3911_; 
lean_del_object(v___x_3906_);
v_val_3908_ = lean_ctor_get(v_a_3904_, 0);
lean_inc(v_val_3908_);
lean_dec_ref(v_a_3904_);
v_params_3909_ = lean_ctor_get(v_val_3908_, 2);
lean_inc_ref(v_params_3909_);
v_value_3910_ = lean_ctor_get(v_val_3908_, 4);
lean_inc_ref(v_value_3910_);
lean_dec(v_val_3908_);
v___x_3911_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3909_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
lean_dec_ref(v_params_3909_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3923_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3914_ = v___x_3911_;
v_isShared_3915_ = v_isSharedCheck_3923_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3923_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_unbox(v_a_3912_);
lean_dec(v_a_3912_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
lean_dec_ref(v_value_3910_);
v___x_3917_ = lean_box(0);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3917_);
v___x_3919_ = v___x_3914_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
else
{
lean_object* v___x_3921_; 
lean_del_object(v___x_3914_);
lean_inc_ref(v_value_3910_);
v___x_3921_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3910_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v___x_3922_; 
lean_dec_ref(v___x_3921_);
v___x_3922_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3910_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
return v___x_3922_;
}
else
{
lean_dec_ref(v_value_3910_);
return v___x_3921_;
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v_value_3910_);
v_a_3924_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3911_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3911_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_a_3904_);
v___x_3932_ = lean_box(0);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3932_);
v___x_3934_ = v___x_3906_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
v_a_3937_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3903_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3903_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
if (lean_obj_tag(v_arg_3945_) == 1)
{
lean_object* v_fvarId_3953_; lean_object* v___x_3954_; 
v_fvarId_3953_ = lean_ctor_get(v_arg_3945_, 0);
v___x_3954_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3953_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3954_;
}
else
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = lean_box(0);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_arg_3957_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_3966_, lean_object* v_i_3967_, lean_object* v_stop_3968_, lean_object* v_b_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
size_t v_i_boxed_3977_; size_t v_stop_boxed_3978_; lean_object* v_res_3979_; 
v_i_boxed_3977_ = lean_unbox_usize(v_i_3967_);
lean_dec(v_i_3967_);
v_stop_boxed_3978_ = lean_unbox_usize(v_stop_3968_);
lean_dec(v_stop_3968_);
v_res_3979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_3966_, v_i_boxed_3977_, v_stop_boxed_3978_, v_b_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec_ref(v_as_3966_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_3980_, lean_object* v_args_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_3980_, v_args_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_var_3990_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_3999_, lean_object* v_as_4000_, lean_object* v_sz_4001_, lean_object* v_i_4002_, lean_object* v_b_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
size_t v_sz_boxed_4011_; size_t v_i_boxed_4012_; lean_object* v_res_4013_; 
v_sz_boxed_4011_ = lean_unbox_usize(v_sz_4001_);
lean_dec(v_sz_4001_);
v_i_boxed_4012_ = lean_unbox_usize(v_i_4002_);
lean_dec(v_i_4002_);
v_res_4013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3999_, v_as_4000_, v_sz_boxed_4011_, v_i_boxed_4012_, v_b_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec_ref(v_as_4000_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4032_, lean_object* v_R_4033_, lean_object* v_a_4034_, lean_object* v_b_4035_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4034_, v_b_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4037_, size_t v_i_4038_, lean_object* v_bs_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4037_, v_i_4038_, v_bs_4039_, v___y_4040_, v___y_4041_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4048_, lean_object* v_i_4049_, lean_object* v_bs_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
size_t v_sz_boxed_4058_; size_t v_i_boxed_4059_; lean_object* v_res_4060_; 
v_sz_boxed_4058_ = lean_unbox_usize(v_sz_4048_);
lean_dec(v_sz_4048_);
v_i_boxed_4059_ = lean_unbox_usize(v_i_4049_);
lean_dec(v_i_4049_);
v_res_4060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4058_, v_i_boxed_4059_, v_bs_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4061_, size_t v_i_4062_, size_t v_stop_4063_, lean_object* v_b_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4061_, v_i_4062_, v_stop_4063_, v_b_4064_, v___y_4065_, v___y_4066_, v___y_4070_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4073_, lean_object* v_i_4074_, lean_object* v_stop_4075_, lean_object* v_b_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
size_t v_i_boxed_4084_; size_t v_stop_boxed_4085_; lean_object* v_res_4086_; 
v_i_boxed_4084_ = lean_unbox_usize(v_i_4074_);
lean_dec(v_i_4074_);
v_stop_boxed_4085_ = lean_unbox_usize(v_stop_4075_);
lean_dec(v_stop_4075_);
v_res_4086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4073_, v_i_boxed_4084_, v_stop_boxed_4085_, v_b_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec_ref(v_as_4073_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4087_, size_t v_i_4088_, size_t v_stop_4089_, lean_object* v_b_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4087_, v_i_4088_, v_stop_4089_, v_b_4090_, v___y_4091_, v___y_4092_, v___y_4096_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4099_, lean_object* v_i_4100_, lean_object* v_stop_4101_, lean_object* v_b_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
size_t v_i_boxed_4110_; size_t v_stop_boxed_4111_; lean_object* v_res_4112_; 
v_i_boxed_4110_ = lean_unbox_usize(v_i_4100_);
lean_dec(v_i_4100_);
v_stop_boxed_4111_ = lean_unbox_usize(v_stop_4101_);
lean_dec(v_stop_4101_);
v_res_4112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4099_, v_i_boxed_4110_, v_stop_boxed_4111_, v_b_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec_ref(v_as_4099_);
return v_res_4112_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = lean_unsigned_to_nat(32u);
v___x_4114_ = lean_mk_empty_array_with_capacity(v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4116_ = ((size_t)5ULL);
v___x_4117_ = lean_unsigned_to_nat(0u);
v___x_4118_ = lean_unsigned_to_nat(32u);
v___x_4119_ = lean_mk_empty_array_with_capacity(v___x_4118_);
v___x_4120_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4121_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v___x_4119_);
lean_ctor_set(v___x_4121_, 2, v___x_4117_);
lean_ctor_set(v___x_4121_, 3, v___x_4117_);
lean_ctor_set_usize(v___x_4121_, 4, v___x_4116_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4122_){
_start:
{
lean_object* v___x_4124_; lean_object* v_traceState_4125_; lean_object* v_traces_4126_; lean_object* v___x_4127_; lean_object* v_traceState_4128_; lean_object* v_env_4129_; lean_object* v_nextMacroScope_4130_; lean_object* v_ngen_4131_; lean_object* v_auxDeclNGen_4132_; lean_object* v_cache_4133_; lean_object* v_messages_4134_; lean_object* v_infoState_4135_; lean_object* v_snapshotTasks_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4155_; 
v___x_4124_ = lean_st_ref_get(v___y_4122_);
v_traceState_4125_ = lean_ctor_get(v___x_4124_, 4);
lean_inc_ref(v_traceState_4125_);
lean_dec(v___x_4124_);
v_traces_4126_ = lean_ctor_get(v_traceState_4125_, 0);
lean_inc_ref(v_traces_4126_);
lean_dec_ref(v_traceState_4125_);
v___x_4127_ = lean_st_ref_take(v___y_4122_);
v_traceState_4128_ = lean_ctor_get(v___x_4127_, 4);
v_env_4129_ = lean_ctor_get(v___x_4127_, 0);
v_nextMacroScope_4130_ = lean_ctor_get(v___x_4127_, 1);
v_ngen_4131_ = lean_ctor_get(v___x_4127_, 2);
v_auxDeclNGen_4132_ = lean_ctor_get(v___x_4127_, 3);
v_cache_4133_ = lean_ctor_get(v___x_4127_, 5);
v_messages_4134_ = lean_ctor_get(v___x_4127_, 6);
v_infoState_4135_ = lean_ctor_get(v___x_4127_, 7);
v_snapshotTasks_4136_ = lean_ctor_get(v___x_4127_, 8);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4138_ = v___x_4127_;
v_isShared_4139_ = v_isSharedCheck_4155_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_snapshotTasks_4136_);
lean_inc(v_infoState_4135_);
lean_inc(v_messages_4134_);
lean_inc(v_cache_4133_);
lean_inc(v_traceState_4128_);
lean_inc(v_auxDeclNGen_4132_);
lean_inc(v_ngen_4131_);
lean_inc(v_nextMacroScope_4130_);
lean_inc(v_env_4129_);
lean_dec(v___x_4127_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4155_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
uint64_t v_tid_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4153_; 
v_tid_4140_ = lean_ctor_get_uint64(v_traceState_4128_, sizeof(void*)*1);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_traceState_4128_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v_traceState_4128_, 0);
lean_dec(v_unused_4154_);
v___x_4142_ = v_traceState_4128_;
v_isShared_4143_ = v_isSharedCheck_4153_;
goto v_resetjp_4141_;
}
else
{
lean_dec(v_traceState_4128_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4153_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4144_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 0, v___x_4144_);
v___x_4146_ = v___x_4142_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4144_);
lean_ctor_set_uint64(v_reuseFailAlloc_4152_, sizeof(void*)*1, v_tid_4140_);
v___x_4146_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4148_; 
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 4, v___x_4146_);
v___x_4148_ = v___x_4138_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_env_4129_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v_nextMacroScope_4130_);
lean_ctor_set(v_reuseFailAlloc_4151_, 2, v_ngen_4131_);
lean_ctor_set(v_reuseFailAlloc_4151_, 3, v_auxDeclNGen_4132_);
lean_ctor_set(v_reuseFailAlloc_4151_, 4, v___x_4146_);
lean_ctor_set(v_reuseFailAlloc_4151_, 5, v_cache_4133_);
lean_ctor_set(v_reuseFailAlloc_4151_, 6, v_messages_4134_);
lean_ctor_set(v_reuseFailAlloc_4151_, 7, v_infoState_4135_);
lean_ctor_set(v_reuseFailAlloc_4151_, 8, v_snapshotTasks_4136_);
v___x_4148_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_st_ref_set(v___y_4122_, v___x_4148_);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_traces_4126_);
return v___x_4150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4156_);
lean_dec(v___y_4156_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4164_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4175_, lean_object* v_opt_4176_){
_start:
{
lean_object* v_name_4177_; lean_object* v_defValue_4178_; lean_object* v_map_4179_; lean_object* v___x_4180_; 
v_name_4177_ = lean_ctor_get(v_opt_4176_, 0);
v_defValue_4178_ = lean_ctor_get(v_opt_4176_, 1);
v_map_4179_ = lean_ctor_get(v_opts_4175_, 0);
v___x_4180_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4179_, v_name_4177_);
if (lean_obj_tag(v___x_4180_) == 0)
{
uint8_t v___x_4181_; 
v___x_4181_ = lean_unbox(v_defValue_4178_);
return v___x_4181_;
}
else
{
lean_object* v_val_4182_; 
v_val_4182_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_val_4182_);
lean_dec_ref(v___x_4180_);
if (lean_obj_tag(v_val_4182_) == 1)
{
uint8_t v_v_4183_; 
v_v_4183_ = lean_ctor_get_uint8(v_val_4182_, 0);
lean_dec_ref(v_val_4182_);
return v_v_4183_;
}
else
{
uint8_t v___x_4184_; 
lean_dec(v_val_4182_);
v___x_4184_ = lean_unbox(v_defValue_4178_);
return v___x_4184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4185_, lean_object* v_opt_4186_){
_start:
{
uint8_t v_res_4187_; lean_object* v_r_4188_; 
v_res_4187_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4185_, v_opt_4186_);
lean_dec_ref(v_opt_4186_);
lean_dec_ref(v_opts_4185_);
v_r_4188_ = lean_box(v_res_4187_);
return v_r_4188_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4191_ = l_Lean_stringToMessageData(v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4192_, lean_object* v_x_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4201_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4202_ = l_Lean_MessageData_ofName(v_name_4192_);
v___x_4203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4205_, lean_object* v_x_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4205_, v_x_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v_x_4206_);
return v_res_4214_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_e_4215_){
_start:
{
if (lean_obj_tag(v_e_4215_) == 0)
{
uint8_t v___x_4216_; 
v___x_4216_ = 2;
return v___x_4216_;
}
else
{
uint8_t v___x_4217_; 
v___x_4217_ = 0;
return v___x_4217_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_e_4218_){
_start:
{
uint8_t v_res_4219_; lean_object* v_r_4220_; 
v_res_4219_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_e_4218_);
lean_dec_ref(v_e_4218_);
v_r_4220_ = lean_box(v_res_4219_);
return v_r_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4221_, lean_object* v_opt_4222_){
_start:
{
lean_object* v_name_4223_; lean_object* v_defValue_4224_; lean_object* v_map_4225_; lean_object* v___x_4226_; 
v_name_4223_ = lean_ctor_get(v_opt_4222_, 0);
v_defValue_4224_ = lean_ctor_get(v_opt_4222_, 1);
v_map_4225_ = lean_ctor_get(v_opts_4221_, 0);
v___x_4226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4225_, v_name_4223_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_inc(v_defValue_4224_);
return v_defValue_4224_;
}
else
{
lean_object* v_val_4227_; 
v_val_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_val_4227_);
lean_dec_ref(v___x_4226_);
if (lean_obj_tag(v_val_4227_) == 3)
{
lean_object* v_v_4228_; 
v_v_4228_ = lean_ctor_get(v_val_4227_, 0);
lean_inc(v_v_4228_);
lean_dec_ref(v_val_4227_);
return v_v_4228_;
}
else
{
lean_dec(v_val_4227_);
lean_inc(v_defValue_4224_);
return v_defValue_4224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4229_, lean_object* v_opt_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4229_, v_opt_4230_);
lean_dec_ref(v_opt_4230_);
lean_dec_ref(v_opts_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg(lean_object* v_x_4232_){
_start:
{
if (lean_obj_tag(v_x_4232_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
v_a_4234_ = lean_ctor_get(v_x_4232_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_x_4232_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v_x_4232_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v_x_4232_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
lean_ctor_set_tag(v___x_4236_, 1);
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_a_4242_ = lean_ctor_get(v_x_4232_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_x_4232_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v_x_4232_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v_x_4232_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 0);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg___boxed(lean_object* v_x_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg(v_x_4250_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3_spec__4(size_t v_sz_4253_, size_t v_i_4254_, lean_object* v_bs_4255_){
_start:
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_usize_dec_lt(v_i_4254_, v_sz_4253_);
if (v___x_4256_ == 0)
{
return v_bs_4255_;
}
else
{
lean_object* v_v_4257_; lean_object* v_msg_4258_; lean_object* v___x_4259_; lean_object* v_bs_x27_4260_; size_t v___x_4261_; size_t v___x_4262_; lean_object* v___x_4263_; 
v_v_4257_ = lean_array_uget_borrowed(v_bs_4255_, v_i_4254_);
v_msg_4258_ = lean_ctor_get(v_v_4257_, 1);
lean_inc_ref(v_msg_4258_);
v___x_4259_ = lean_unsigned_to_nat(0u);
v_bs_x27_4260_ = lean_array_uset(v_bs_4255_, v_i_4254_, v___x_4259_);
v___x_4261_ = ((size_t)1ULL);
v___x_4262_ = lean_usize_add(v_i_4254_, v___x_4261_);
v___x_4263_ = lean_array_uset(v_bs_x27_4260_, v_i_4254_, v_msg_4258_);
v_i_4254_ = v___x_4262_;
v_bs_4255_ = v___x_4263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_4265_, lean_object* v_i_4266_, lean_object* v_bs_4267_){
_start:
{
size_t v_sz_boxed_4268_; size_t v_i_boxed_4269_; lean_object* v_res_4270_; 
v_sz_boxed_4268_ = lean_unbox_usize(v_sz_4265_);
lean_dec(v_sz_4265_);
v_i_boxed_4269_ = lean_unbox_usize(v_i_4266_);
lean_dec(v_i_4266_);
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3_spec__4(v_sz_boxed_4268_, v_i_boxed_4269_, v_bs_4267_);
return v_res_4270_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4271_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__0);
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
return v___x_4273_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4274_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__1);
v___x_4275_ = lean_unsigned_to_nat(0u);
v___x_4276_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
lean_ctor_set(v___x_4276_, 2, v___x_4275_);
lean_ctor_set(v___x_4276_, 3, v___x_4275_);
lean_ctor_set(v___x_4276_, 4, v___x_4274_);
lean_ctor_set(v___x_4276_, 5, v___x_4274_);
lean_ctor_set(v___x_4276_, 6, v___x_4274_);
lean_ctor_set(v___x_4276_, 7, v___x_4274_);
lean_ctor_set(v___x_4276_, 8, v___x_4274_);
lean_ctor_set(v___x_4276_, 9, v___x_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_oldTraces_4277_, lean_object* v_data_4278_, lean_object* v_ref_4279_, lean_object* v_msg_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_options_4286_; lean_object* v___x_4287_; lean_object* v_traceState_4288_; lean_object* v_traces_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_options_4286_ = lean_ctor_get(v___y_4283_, 2);
v___x_4287_ = lean_st_ref_get(v___y_4284_);
v_traceState_4288_ = lean_ctor_get(v___x_4287_, 4);
lean_inc_ref(v_traceState_4288_);
lean_dec(v___x_4287_);
v_traces_4289_ = lean_ctor_get(v_traceState_4288_, 0);
lean_inc_ref(v_traces_4289_);
lean_dec_ref(v_traceState_4288_);
v___x_4290_ = lean_st_ref_get(v___y_4284_);
v___x_4291_ = lean_st_ref_get(v___y_4282_);
v___x_4292_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4281_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4349_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4349_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4349_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_env_4297_; lean_object* v_lctx_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4347_; 
v_env_4297_ = lean_ctor_get(v___x_4290_, 0);
lean_inc_ref(v_env_4297_);
lean_dec(v___x_4290_);
v_lctx_4298_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4347_ == 0)
{
lean_object* v_unused_4348_; 
v_unused_4348_ = lean_ctor_get(v___x_4291_, 1);
lean_dec(v_unused_4348_);
v___x_4300_ = v___x_4291_;
v_isShared_4301_ = v_isSharedCheck_4347_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_lctx_4298_);
lean_dec(v___x_4291_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4347_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v_traceState_4304_; lean_object* v_env_4305_; lean_object* v_nextMacroScope_4306_; lean_object* v_ngen_4307_; lean_object* v_auxDeclNGen_4308_; lean_object* v_cache_4309_; lean_object* v_messages_4310_; lean_object* v_infoState_4311_; lean_object* v_snapshotTasks_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4346_; 
v___x_4302_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2);
v___x_4303_ = lean_st_ref_take(v___y_4284_);
v_traceState_4304_ = lean_ctor_get(v___x_4303_, 4);
v_env_4305_ = lean_ctor_get(v___x_4303_, 0);
v_nextMacroScope_4306_ = lean_ctor_get(v___x_4303_, 1);
v_ngen_4307_ = lean_ctor_get(v___x_4303_, 2);
v_auxDeclNGen_4308_ = lean_ctor_get(v___x_4303_, 3);
v_cache_4309_ = lean_ctor_get(v___x_4303_, 5);
v_messages_4310_ = lean_ctor_get(v___x_4303_, 6);
v_infoState_4311_ = lean_ctor_get(v___x_4303_, 7);
v_snapshotTasks_4312_ = lean_ctor_get(v___x_4303_, 8);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4314_ = v___x_4303_;
v_isShared_4315_ = v_isSharedCheck_4346_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_snapshotTasks_4312_);
lean_inc(v_infoState_4311_);
lean_inc(v_messages_4310_);
lean_inc(v_cache_4309_);
lean_inc(v_traceState_4304_);
lean_inc(v_auxDeclNGen_4308_);
lean_inc(v_ngen_4307_);
lean_inc(v_nextMacroScope_4306_);
lean_inc(v_env_4305_);
lean_dec(v___x_4303_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4346_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
uint64_t v_tid_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4344_; 
v_tid_4316_ = lean_ctor_get_uint64(v_traceState_4304_, sizeof(void*)*1);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_traceState_4304_);
if (v_isSharedCheck_4344_ == 0)
{
lean_object* v_unused_4345_; 
v_unused_4345_ = lean_ctor_get(v_traceState_4304_, 0);
lean_dec(v_unused_4345_);
v___x_4318_ = v_traceState_4304_;
v_isShared_4319_ = v_isSharedCheck_4344_;
goto v_resetjp_4317_;
}
else
{
lean_dec(v_traceState_4304_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4344_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; size_t v_sz_4321_; size_t v___x_4322_; lean_object* v___x_4323_; lean_object* v_msg_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4329_; 
v___x_4320_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4289_);
lean_dec_ref(v_traces_4289_);
v_sz_4321_ = lean_array_size(v___x_4320_);
v___x_4322_ = ((size_t)0ULL);
v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3_spec__4(v_sz_4321_, v___x_4322_, v___x_4320_);
v_msg_4324_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4324_, 0, v_data_4278_);
lean_ctor_set(v_msg_4324_, 1, v_msg_4280_);
lean_ctor_set(v_msg_4324_, 2, v___x_4323_);
v___x_4325_ = lean_unbox(v_a_4293_);
lean_dec(v_a_4293_);
v___x_4326_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4298_, v___x_4325_);
lean_dec_ref(v_lctx_4298_);
lean_inc_ref(v_options_4286_);
v___x_4327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4327_, 0, v_env_4297_);
lean_ctor_set(v___x_4327_, 1, v___x_4302_);
lean_ctor_set(v___x_4327_, 2, v___x_4326_);
lean_ctor_set(v___x_4327_, 3, v_options_4286_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set_tag(v___x_4300_, 3);
lean_ctor_set(v___x_4300_, 1, v_msg_4324_);
lean_ctor_set(v___x_4300_, 0, v___x_4327_);
v___x_4329_ = v___x_4300_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_msg_4324_);
v___x_4329_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v_ref_4279_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4277_, v___x_4330_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v___x_4331_);
v___x_4333_ = v___x_4318_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4331_);
lean_ctor_set_uint64(v_reuseFailAlloc_4342_, sizeof(void*)*1, v_tid_4316_);
v___x_4333_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4335_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 4, v___x_4333_);
v___x_4335_ = v___x_4314_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_env_4305_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_nextMacroScope_4306_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_ngen_4307_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_auxDeclNGen_4308_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v___x_4333_);
lean_ctor_set(v_reuseFailAlloc_4341_, 5, v_cache_4309_);
lean_ctor_set(v_reuseFailAlloc_4341_, 6, v_messages_4310_);
lean_ctor_set(v_reuseFailAlloc_4341_, 7, v_infoState_4311_);
lean_ctor_set(v_reuseFailAlloc_4341_, 8, v_snapshotTasks_4312_);
v___x_4335_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4336_ = lean_st_ref_set(v___y_4284_, v___x_4335_);
v___x_4337_ = lean_box(0);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4337_);
v___x_4339_ = v___x_4295_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
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
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec(v___x_4291_);
lean_dec(v___x_4290_);
lean_dec_ref(v_traces_4289_);
lean_dec_ref(v_msg_4280_);
lean_dec(v_ref_4279_);
lean_dec_ref(v_data_4278_);
lean_dec_ref(v_oldTraces_4277_);
v_a_4350_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4292_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4292_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4358_, lean_object* v_data_4359_, lean_object* v_ref_4360_, lean_object* v_msg_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_oldTraces_4358_, v_data_4359_, v_ref_4360_, v_msg_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
return v_res_4367_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__0));
v___x_4369_ = l_Lean_stringToMessageData(v___x_4368_);
return v___x_4369_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1(void){
_start:
{
lean_object* v___x_4370_; double v___x_4371_; 
v___x_4370_ = lean_unsigned_to_nat(0u);
v___x_4371_ = lean_float_of_nat(v___x_4370_);
return v___x_4371_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2));
v___x_4374_ = l_Lean_stringToMessageData(v___x_4373_);
return v___x_4374_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__4(void){
_start:
{
lean_object* v___x_4375_; double v___x_4376_; 
v___x_4375_ = lean_unsigned_to_nat(1000u);
v___x_4376_ = lean_float_of_nat(v___x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4377_, uint8_t v_collapsed_4378_, lean_object* v_tag_4379_, lean_object* v_opts_4380_, uint8_t v_clsEnabled_4381_, lean_object* v_oldTraces_4382_, lean_object* v_msg_4383_, lean_object* v_resStartStop_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_fst_4392_; lean_object* v_snd_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4483_; 
v_fst_4392_ = lean_ctor_get(v_resStartStop_4384_, 0);
v_snd_4393_ = lean_ctor_get(v_resStartStop_4384_, 1);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_resStartStop_4384_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4395_ = v_resStartStop_4384_;
v_isShared_4396_ = v_isSharedCheck_4483_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_snd_4393_);
lean_inc(v_fst_4392_);
lean_dec(v_resStartStop_4384_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4483_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v_data_4400_; lean_object* v_fst_4403_; lean_object* v_snd_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4482_; 
v_fst_4403_ = lean_ctor_get(v_snd_4393_, 0);
v_snd_4404_ = lean_ctor_get(v_snd_4393_, 1);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_snd_4393_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4406_ = v_snd_4393_;
v_isShared_4407_ = v_isSharedCheck_4482_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_snd_4404_);
lean_inc(v_fst_4403_);
lean_dec(v_snd_4393_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4482_;
goto v_resetjp_4405_;
}
v___jp_4397_:
{
lean_object* v___x_4401_; 
lean_inc(v___y_4398_);
v___x_4401_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_oldTraces_4382_, v_data_4400_, v___y_4398_, v___y_4399_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v___x_4402_; 
lean_dec_ref(v___x_4401_);
v___x_4402_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg(v_fst_4392_);
return v___x_4402_;
}
else
{
lean_dec(v_fst_4392_);
return v___x_4401_;
}
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; uint8_t v___x_4409_; lean_object* v___y_4411_; lean_object* v_a_4412_; uint8_t v___y_4436_; double v___y_4467_; 
v___x_4408_ = l_Lean_trace_profiler;
v___x_4409_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4380_, v___x_4408_);
if (v___x_4409_ == 0)
{
v___y_4436_ = v___x_4409_;
goto v___jp_4435_;
}
else
{
lean_object* v___x_4472_; uint8_t v___x_4473_; 
v___x_4472_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4473_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4380_, v___x_4472_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4475_; double v___x_4476_; double v___x_4477_; double v___x_4478_; 
v___x_4474_ = l_Lean_trace_profiler_threshold;
v___x_4475_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4380_, v___x_4474_);
v___x_4476_ = lean_float_of_nat(v___x_4475_);
v___x_4477_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__4);
v___x_4478_ = lean_float_div(v___x_4476_, v___x_4477_);
v___y_4467_ = v___x_4478_;
goto v___jp_4466_;
}
else
{
lean_object* v___x_4479_; lean_object* v___x_4480_; double v___x_4481_; 
v___x_4479_ = l_Lean_trace_profiler_threshold;
v___x_4480_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4380_, v___x_4479_);
v___x_4481_ = lean_float_of_nat(v___x_4480_);
v___y_4467_ = v___x_4481_;
goto v___jp_4466_;
}
}
v___jp_4410_:
{
uint8_t v_result_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4418_; 
v_result_4413_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_fst_4392_);
v___x_4414_ = l_Lean_TraceResult_toEmoji(v_result_4413_);
v___x_4415_ = l_Lean_stringToMessageData(v___x_4414_);
v___x_4416_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
if (v_isShared_4407_ == 0)
{
lean_ctor_set_tag(v___x_4406_, 7);
lean_ctor_set(v___x_4406_, 1, v___x_4416_);
lean_ctor_set(v___x_4406_, 0, v___x_4415_);
v___x_4418_ = v___x_4406_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4415_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v_m_4420_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set_tag(v___x_4395_, 7);
lean_ctor_set(v___x_4395_, 1, v_a_4412_);
lean_ctor_set(v___x_4395_, 0, v___x_4418_);
v_m_4420_ = v___x_4395_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4418_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_a_4412_);
v_m_4420_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; double v___x_4423_; lean_object* v_data_4424_; 
v___x_4421_ = lean_box(v_result_4413_);
v___x_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
v___x_4423_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1);
lean_inc_ref(v_tag_4379_);
lean_inc_ref(v___x_4422_);
lean_inc(v_cls_4377_);
v_data_4424_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4424_, 0, v_cls_4377_);
lean_ctor_set(v_data_4424_, 1, v___x_4422_);
lean_ctor_set(v_data_4424_, 2, v_tag_4379_);
lean_ctor_set_float(v_data_4424_, sizeof(void*)*3, v___x_4423_);
lean_ctor_set_float(v_data_4424_, sizeof(void*)*3 + 8, v___x_4423_);
lean_ctor_set_uint8(v_data_4424_, sizeof(void*)*3 + 16, v_collapsed_4378_);
if (v___x_4409_ == 0)
{
lean_dec_ref(v___x_4422_);
lean_dec(v_snd_4404_);
lean_dec(v_fst_4403_);
lean_dec_ref(v_tag_4379_);
lean_dec(v_cls_4377_);
v___y_4398_ = v___y_4411_;
v___y_4399_ = v_m_4420_;
v_data_4400_ = v_data_4424_;
goto v___jp_4397_;
}
else
{
lean_object* v_data_4425_; double v___x_4426_; double v___x_4427_; 
lean_dec_ref(v_data_4424_);
v_data_4425_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4425_, 0, v_cls_4377_);
lean_ctor_set(v_data_4425_, 1, v___x_4422_);
lean_ctor_set(v_data_4425_, 2, v_tag_4379_);
v___x_4426_ = lean_unbox_float(v_fst_4403_);
lean_dec(v_fst_4403_);
lean_ctor_set_float(v_data_4425_, sizeof(void*)*3, v___x_4426_);
v___x_4427_ = lean_unbox_float(v_snd_4404_);
lean_dec(v_snd_4404_);
lean_ctor_set_float(v_data_4425_, sizeof(void*)*3 + 8, v___x_4427_);
lean_ctor_set_uint8(v_data_4425_, sizeof(void*)*3 + 16, v_collapsed_4378_);
v___y_4398_ = v___y_4411_;
v___y_4399_ = v_m_4420_;
v_data_4400_ = v_data_4425_;
goto v___jp_4397_;
}
}
}
}
v___jp_4430_:
{
lean_object* v_ref_4431_; lean_object* v___x_4432_; 
v_ref_4431_ = lean_ctor_get(v___y_4389_, 5);
lean_inc(v___y_4390_);
lean_inc_ref(v___y_4389_);
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc(v___y_4386_);
lean_inc_ref(v___y_4385_);
lean_inc(v_fst_4392_);
v___x_4432_ = lean_apply_8(v_msg_4383_, v_fst_4392_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, lean_box(0));
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref(v___x_4432_);
v___y_4411_ = v_ref_4431_;
v_a_4412_ = v_a_4433_;
goto v___jp_4410_;
}
else
{
lean_object* v___x_4434_; 
lean_dec_ref(v___x_4432_);
v___x_4434_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___y_4411_ = v_ref_4431_;
v_a_4412_ = v___x_4434_;
goto v___jp_4410_;
}
}
v___jp_4435_:
{
if (v_clsEnabled_4381_ == 0)
{
if (v___y_4436_ == 0)
{
lean_object* v___x_4437_; lean_object* v_traceState_4438_; lean_object* v_env_4439_; lean_object* v_nextMacroScope_4440_; lean_object* v_ngen_4441_; lean_object* v_auxDeclNGen_4442_; lean_object* v_cache_4443_; lean_object* v_messages_4444_; lean_object* v_infoState_4445_; lean_object* v_snapshotTasks_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4465_; 
lean_del_object(v___x_4406_);
lean_dec(v_snd_4404_);
lean_dec(v_fst_4403_);
lean_del_object(v___x_4395_);
lean_dec_ref(v_msg_4383_);
lean_dec_ref(v_tag_4379_);
lean_dec(v_cls_4377_);
v___x_4437_ = lean_st_ref_take(v___y_4390_);
v_traceState_4438_ = lean_ctor_get(v___x_4437_, 4);
v_env_4439_ = lean_ctor_get(v___x_4437_, 0);
v_nextMacroScope_4440_ = lean_ctor_get(v___x_4437_, 1);
v_ngen_4441_ = lean_ctor_get(v___x_4437_, 2);
v_auxDeclNGen_4442_ = lean_ctor_get(v___x_4437_, 3);
v_cache_4443_ = lean_ctor_get(v___x_4437_, 5);
v_messages_4444_ = lean_ctor_get(v___x_4437_, 6);
v_infoState_4445_ = lean_ctor_get(v___x_4437_, 7);
v_snapshotTasks_4446_ = lean_ctor_get(v___x_4437_, 8);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4448_ = v___x_4437_;
v_isShared_4449_ = v_isSharedCheck_4465_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_snapshotTasks_4446_);
lean_inc(v_infoState_4445_);
lean_inc(v_messages_4444_);
lean_inc(v_cache_4443_);
lean_inc(v_traceState_4438_);
lean_inc(v_auxDeclNGen_4442_);
lean_inc(v_ngen_4441_);
lean_inc(v_nextMacroScope_4440_);
lean_inc(v_env_4439_);
lean_dec(v___x_4437_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4465_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
uint64_t v_tid_4450_; lean_object* v_traces_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4464_; 
v_tid_4450_ = lean_ctor_get_uint64(v_traceState_4438_, sizeof(void*)*1);
v_traces_4451_ = lean_ctor_get(v_traceState_4438_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_traceState_4438_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4453_ = v_traceState_4438_;
v_isShared_4454_ = v_isSharedCheck_4464_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_traces_4451_);
lean_dec(v_traceState_4438_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4464_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4455_; lean_object* v___x_4457_; 
v___x_4455_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4382_, v_traces_4451_);
lean_dec_ref(v_traces_4451_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4455_);
v___x_4457_ = v___x_4453_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4455_);
lean_ctor_set_uint64(v_reuseFailAlloc_4463_, sizeof(void*)*1, v_tid_4450_);
v___x_4457_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 4, v___x_4457_);
v___x_4459_ = v___x_4448_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_env_4439_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_nextMacroScope_4440_);
lean_ctor_set(v_reuseFailAlloc_4462_, 2, v_ngen_4441_);
lean_ctor_set(v_reuseFailAlloc_4462_, 3, v_auxDeclNGen_4442_);
lean_ctor_set(v_reuseFailAlloc_4462_, 4, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4462_, 5, v_cache_4443_);
lean_ctor_set(v_reuseFailAlloc_4462_, 6, v_messages_4444_);
lean_ctor_set(v_reuseFailAlloc_4462_, 7, v_infoState_4445_);
lean_ctor_set(v_reuseFailAlloc_4462_, 8, v_snapshotTasks_4446_);
v___x_4459_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4460_ = lean_st_ref_set(v___y_4390_, v___x_4459_);
v___x_4461_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg(v_fst_4392_);
return v___x_4461_;
}
}
}
}
}
else
{
goto v___jp_4430_;
}
}
else
{
goto v___jp_4430_;
}
}
v___jp_4466_:
{
double v___x_4468_; double v___x_4469_; double v___x_4470_; uint8_t v___x_4471_; 
v___x_4468_ = lean_unbox_float(v_snd_4404_);
v___x_4469_ = lean_unbox_float(v_fst_4403_);
v___x_4470_ = lean_float_sub(v___x_4468_, v___x_4469_);
v___x_4471_ = lean_float_decLt(v___y_4467_, v___x_4470_);
v___y_4436_ = v___x_4471_;
goto v___jp_4435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4484_, lean_object* v_collapsed_4485_, lean_object* v_tag_4486_, lean_object* v_opts_4487_, lean_object* v_clsEnabled_4488_, lean_object* v_oldTraces_4489_, lean_object* v_msg_4490_, lean_object* v_resStartStop_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
uint8_t v_collapsed_boxed_4499_; uint8_t v_clsEnabled_boxed_4500_; lean_object* v_res_4501_; 
v_collapsed_boxed_4499_ = lean_unbox(v_collapsed_4485_);
v_clsEnabled_boxed_4500_ = lean_unbox(v_clsEnabled_4488_);
v_res_4501_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4484_, v_collapsed_boxed_4499_, v_tag_4486_, v_opts_4487_, v_clsEnabled_boxed_4500_, v_oldTraces_4489_, v_msg_4490_, v_resStartStop_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec_ref(v_opts_4487_);
return v_res_4501_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4505_; double v___x_4506_; 
v___x_4505_ = lean_unsigned_to_nat(1000000000u);
v___x_4506_ = lean_float_of_nat(v___x_4505_);
return v___x_4506_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4516_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4517_ = l_Lean_Name_append(v___x_4516_, v___x_4515_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4518_, lean_object* v___x_4519_, lean_object* v_a_4520_, lean_object* v_b_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_a_4530_; uint8_t v___x_4534_; 
v___x_4534_ = lean_nat_dec_lt(v_a_4520_, v_upperBound_4518_);
if (v___x_4534_ == 0)
{
lean_object* v___x_4535_; 
lean_dec(v_a_4520_);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v_b_4521_);
return v___x_4535_;
}
else
{
lean_object* v___x_4536_; lean_object* v_toSignature_4537_; lean_object* v_value_4538_; lean_object* v_name_4539_; lean_object* v_params_4540_; uint8_t v_safe_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec_ref(v_b_4521_);
v___x_4536_ = lean_array_fget_borrowed(v___x_4519_, v_a_4520_);
v_toSignature_4537_ = lean_ctor_get(v___x_4536_, 0);
v_value_4538_ = lean_ctor_get(v___x_4536_, 1);
v_name_4539_ = lean_ctor_get(v_toSignature_4537_, 0);
v_params_4540_ = lean_ctor_get(v_toSignature_4537_, 3);
v_safe_4541_ = lean_ctor_get_uint8(v_toSignature_4537_, sizeof(void*)*4);
v___x_4542_ = lean_box(0);
v___x_4543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4541_ == 0)
{
v_a_4530_ = v___x_4543_;
goto v___jp_4529_;
}
else
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4520_, v___y_4523_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___y_4547_; lean_object* v_decls_4577_; lean_object* v___f_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; uint8_t v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v_a_4589_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; uint8_t v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v_a_4608_; lean_object* v___y_4618_; lean_object* v___y_4619_; uint8_t v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4688_; uint8_t v___x_4697_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_a_4545_);
lean_dec_ref(v___x_4544_);
v_decls_4577_ = lean_ctor_get(v___y_4522_, 0);
lean_inc(v_name_4539_);
v___f_4578_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4578_, 0, v_name_4539_);
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = lean_array_get_size(v_params_4540_);
lean_inc(v_a_4520_);
lean_inc_ref(v_decls_4577_);
v___x_4581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4581_, 0, v_decls_4577_);
lean_ctor_set(v___x_4581_, 1, v_a_4520_);
v___x_4697_ = lean_nat_dec_lt(v___x_4579_, v___x_4580_);
if (v___x_4697_ == 0)
{
goto v___jp_4671_;
}
else
{
uint8_t v___x_4698_; 
v___x_4698_ = lean_nat_dec_le(v___x_4580_, v___x_4580_);
if (v___x_4698_ == 0)
{
if (v___x_4697_ == 0)
{
goto v___jp_4671_;
}
else
{
size_t v___x_4699_; size_t v___x_4700_; lean_object* v___x_4701_; 
v___x_4699_ = ((size_t)0ULL);
v___x_4700_ = lean_usize_of_nat(v___x_4580_);
v___x_4701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4540_, v___x_4699_, v___x_4700_, v___x_4542_, v___x_4581_, v___y_4523_, v___y_4527_);
v___y_4688_ = v___x_4701_;
goto v___jp_4687_;
}
}
else
{
size_t v___x_4702_; size_t v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = ((size_t)0ULL);
v___x_4703_ = lean_usize_of_nat(v___x_4580_);
v___x_4704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4540_, v___x_4702_, v___x_4703_, v___x_4542_, v___x_4581_, v___y_4523_, v___y_4527_);
v___y_4688_ = v___x_4704_;
goto v___jp_4687_;
}
}
v___jp_4546_:
{
if (lean_obj_tag(v___y_4547_) == 0)
{
lean_object* v___x_4548_; 
lean_dec_ref(v___y_4547_);
v___x_4548_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4520_, v___y_4523_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4560_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4560_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4560_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
uint8_t v___x_4553_; 
v___x_4553_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4545_, v_a_4549_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
lean_dec(v_a_4520_);
v___x_4554_ = lean_box(v_safe_4541_);
v___x_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
v___x_4556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
lean_ctor_set(v___x_4556_, 1, v___x_4542_);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4556_);
v___x_4558_ = v___x_4551_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
else
{
lean_del_object(v___x_4551_);
v_a_4530_ = v___x_4543_;
goto v___jp_4529_;
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec(v_a_4545_);
lean_dec(v_a_4520_);
v_a_4561_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4548_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4548_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec(v_a_4545_);
lean_dec(v_a_4520_);
v_a_4569_ = lean_ctor_get(v___y_4547_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___y_4547_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___y_4547_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___y_4547_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
v___jp_4582_:
{
lean_object* v___x_4590_; double v___x_4591_; double v___x_4592_; double v___x_4593_; double v___x_4594_; double v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4590_ = lean_io_mono_nanos_now();
v___x_4591_ = lean_float_of_nat(v___y_4583_);
v___x_4592_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4593_ = lean_float_div(v___x_4591_, v___x_4592_);
v___x_4594_ = lean_float_of_nat(v___x_4590_);
v___x_4595_ = lean_float_div(v___x_4594_, v___x_4592_);
v___x_4596_ = lean_box_float(v___x_4593_);
v___x_4597_ = lean_box_float(v___x_4595_);
v___x_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4596_);
lean_ctor_set(v___x_4598_, 1, v___x_4597_);
v___x_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4599_, 0, v_a_4589_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
lean_inc_ref(v___y_4584_);
lean_inc(v___y_4588_);
v___x_4600_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4588_, v_safe_4541_, v___y_4584_, v___y_4587_, v___y_4586_, v___y_4585_, v___f_4578_, v___x_4599_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref(v___x_4581_);
v___y_4547_ = v___x_4600_;
goto v___jp_4546_;
}
v___jp_4601_:
{
lean_object* v___x_4609_; double v___x_4610_; double v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4609_ = lean_io_get_num_heartbeats();
v___x_4610_ = lean_float_of_nat(v___y_4602_);
v___x_4611_ = lean_float_of_nat(v___x_4609_);
v___x_4612_ = lean_box_float(v___x_4610_);
v___x_4613_ = lean_box_float(v___x_4611_);
v___x_4614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4612_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4615_, 0, v_a_4608_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
lean_inc_ref(v___y_4603_);
lean_inc(v___y_4607_);
v___x_4616_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4607_, v_safe_4541_, v___y_4603_, v___y_4606_, v___y_4605_, v___y_4604_, v___f_4578_, v___x_4615_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref(v___x_4581_);
v___y_4547_ = v___x_4616_;
goto v___jp_4546_;
}
v___jp_4617_:
{
lean_object* v___x_4623_; 
v___x_4623_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4527_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4625_; uint8_t v___x_4626_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_a_4624_);
lean_dec_ref(v___x_4623_);
v___x_4625_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4626_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4621_, v___x_4625_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = lean_io_mono_nanos_now();
v___x_4628_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4619_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4628_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4628_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
lean_ctor_set_tag(v___x_4631_, 1);
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
v___y_4583_ = v___x_4627_;
v___y_4584_ = v___y_4618_;
v___y_4585_ = v_a_4624_;
v___y_4586_ = v___y_4620_;
v___y_4587_ = v___y_4621_;
v___y_4588_ = v___y_4622_;
v_a_4589_ = v___x_4634_;
goto v___jp_4582_;
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
v_a_4637_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4628_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4628_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
lean_ctor_set_tag(v___x_4639_, 0);
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
v___y_4583_ = v___x_4627_;
v___y_4584_ = v___y_4618_;
v___y_4585_ = v_a_4624_;
v___y_4586_ = v___y_4620_;
v___y_4587_ = v___y_4621_;
v___y_4588_ = v___y_4622_;
v_a_4589_ = v___x_4642_;
goto v___jp_4582_;
}
}
}
}
else
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = lean_io_get_num_heartbeats();
v___x_4646_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4619_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4646_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4646_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
lean_ctor_set_tag(v___x_4649_, 1);
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
v___y_4602_ = v___x_4645_;
v___y_4603_ = v___y_4618_;
v___y_4604_ = v_a_4624_;
v___y_4605_ = v___y_4620_;
v___y_4606_ = v___y_4621_;
v___y_4607_ = v___y_4622_;
v_a_4608_ = v___x_4652_;
goto v___jp_4601_;
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
v_a_4655_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4646_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4646_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
lean_ctor_set_tag(v___x_4657_, 0);
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
v___y_4602_ = v___x_4645_;
v___y_4603_ = v___y_4618_;
v___y_4604_ = v_a_4624_;
v___y_4605_ = v___y_4620_;
v___y_4606_ = v___y_4621_;
v___y_4607_ = v___y_4622_;
v_a_4608_ = v___x_4660_;
goto v___jp_4601_;
}
}
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec_ref(v___y_4619_);
lean_dec_ref(v___x_4581_);
lean_dec_ref(v___f_4578_);
lean_dec(v_a_4545_);
lean_dec(v_a_4520_);
v_a_4663_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4623_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4623_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
v___jp_4671_:
{
if (lean_obj_tag(v_value_4538_) == 0)
{
lean_object* v_options_4672_; uint8_t v_hasTrace_4673_; 
v_options_4672_ = lean_ctor_get(v___y_4526_, 2);
v_hasTrace_4673_ = lean_ctor_get_uint8(v_options_4672_, sizeof(void*)*1);
if (v_hasTrace_4673_ == 0)
{
lean_object* v_code_4674_; lean_object* v___x_4675_; 
lean_dec_ref(v___f_4578_);
v_code_4674_ = lean_ctor_get(v_value_4538_, 0);
lean_inc_ref(v_code_4674_);
v___x_4675_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4674_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref(v___x_4581_);
v___y_4547_ = v___x_4675_;
goto v___jp_4546_;
}
else
{
lean_object* v_code_4676_; lean_object* v_inheritedTraceOptions_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; 
v_code_4676_ = lean_ctor_get(v_value_4538_, 0);
v_inheritedTraceOptions_4677_ = lean_ctor_get(v___y_4526_, 13);
v___x_4678_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4677_, v_options_4672_, v___x_4680_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4682_ = l_Lean_trace_profiler;
v___x_4683_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4672_, v___x_4682_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4684_; 
lean_dec_ref(v___f_4578_);
lean_inc_ref(v_code_4676_);
v___x_4684_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4676_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref(v___x_4581_);
v___y_4547_ = v___x_4684_;
goto v___jp_4546_;
}
else
{
lean_inc_ref(v_code_4676_);
v___y_4618_ = v___x_4679_;
v___y_4619_ = v_code_4676_;
v___y_4620_ = v___x_4681_;
v___y_4621_ = v_options_4672_;
v___y_4622_ = v___x_4678_;
goto v___jp_4617_;
}
}
else
{
lean_inc_ref(v_code_4676_);
v___y_4618_ = v___x_4679_;
v___y_4619_ = v_code_4676_;
v___y_4620_ = v___x_4681_;
v___y_4621_ = v_options_4672_;
v___y_4622_ = v___x_4678_;
goto v___jp_4617_;
}
}
}
else
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
lean_dec_ref(v___f_4578_);
v___x_4685_ = lean_box(1);
v___x_4686_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4685_, v___x_4581_, v___y_4523_, v___y_4527_);
lean_dec_ref(v___x_4581_);
v___y_4547_ = v___x_4686_;
goto v___jp_4546_;
}
}
v___jp_4687_:
{
if (lean_obj_tag(v___y_4688_) == 0)
{
lean_dec_ref(v___y_4688_);
goto v___jp_4671_;
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec_ref(v___x_4581_);
lean_dec_ref(v___f_4578_);
lean_dec(v_a_4545_);
lean_dec(v_a_4520_);
v_a_4689_ = lean_ctor_get(v___y_4688_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___y_4688_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___y_4688_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___y_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec(v_a_4520_);
v_a_4705_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4544_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4544_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
}
v___jp_4529_:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = lean_nat_add(v_a_4520_, v___x_4531_);
lean_dec(v_a_4520_);
lean_inc_ref(v_a_4530_);
v_a_4520_ = v___x_4532_;
v_b_4521_ = v_a_4530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4713_, lean_object* v___x_4714_, lean_object* v_a_4715_, lean_object* v_b_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4713_, v___x_4714_, v_a_4715_, v_b_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec_ref(v___x_4714_);
lean_dec(v_upperBound_4713_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_decls_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v_decls_4732_ = lean_ctor_get(v_a_4725_, 0);
v___x_4733_ = lean_array_get_size(v_decls_4732_);
v___x_4734_ = lean_unsigned_to_nat(0u);
v___x_4735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4736_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4733_, v_decls_4732_, v___x_4734_, v___x_4735_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4751_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4751_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4751_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v_fst_4741_; 
v_fst_4741_ = lean_ctor_get(v_a_4737_, 0);
lean_inc(v_fst_4741_);
lean_dec(v_a_4737_);
if (lean_obj_tag(v_fst_4741_) == 0)
{
uint8_t v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4745_; 
v___x_4742_ = 0;
v___x_4743_ = lean_box(v___x_4742_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4743_);
v___x_4745_ = v___x_4739_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4743_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
else
{
lean_object* v_val_4747_; lean_object* v___x_4749_; 
v_val_4747_ = lean_ctor_get(v_fst_4741_, 0);
lean_inc(v_val_4747_);
lean_dec_ref(v_fst_4741_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v_val_4747_);
v___x_4749_ = v___x_4739_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_val_4747_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
v_a_4752_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4736_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4736_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_00_u03b1_4768_, lean_object* v_x_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v___x_4777_; 
v___x_4777_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___redArg(v_x_4769_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4778_, lean_object* v_x_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_00_u03b1_4778_, v_x_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4788_, lean_object* v___x_4789_, lean_object* v_inst_4790_, lean_object* v_R_4791_, lean_object* v_a_4792_, lean_object* v_b_4793_, lean_object* v_c_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v___x_4802_; 
v___x_4802_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4788_, v___x_4789_, v_a_4792_, v_b_4793_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4803_, lean_object* v___x_4804_, lean_object* v_inst_4805_, lean_object* v_R_4806_, lean_object* v_a_4807_, lean_object* v_b_4808_, lean_object* v_c_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4803_, v___x_4804_, v_inst_4805_, v_R_4806_, v_a_4807_, v_b_4808_, v_c_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec_ref(v___x_4804_);
lean_dec(v_upperBound_4803_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_oldTraces_4818_, lean_object* v_data_4819_, lean_object* v_ref_4820_, lean_object* v_msg_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_oldTraces_4818_, v_data_4819_, v_ref_4820_, v_msg_4821_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_oldTraces_4830_, lean_object* v_data_4831_, lean_object* v_ref_4832_, lean_object* v_msg_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_oldTraces_4830_, v_data_4831_, v_ref_4832_, v_msg_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4844_, lean_object* v_msg_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v_options_4851_; lean_object* v_ref_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v_options_4851_ = lean_ctor_get(v___y_4848_, 2);
v_ref_4852_ = lean_ctor_get(v___y_4848_, 5);
v___x_4853_ = lean_st_ref_get(v___y_4849_);
v___x_4854_ = lean_st_ref_get(v___y_4847_);
v___x_4855_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4846_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4914_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4858_ = v___x_4855_;
v_isShared_4859_ = v_isSharedCheck_4914_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4855_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4914_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v_env_4860_; lean_object* v_lctx_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4912_; 
v_env_4860_ = lean_ctor_get(v___x_4853_, 0);
lean_inc_ref(v_env_4860_);
lean_dec(v___x_4853_);
v_lctx_4861_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4912_ == 0)
{
lean_object* v_unused_4913_; 
v_unused_4913_ = lean_ctor_get(v___x_4854_, 1);
lean_dec(v_unused_4913_);
v___x_4863_ = v___x_4854_;
v_isShared_4864_ = v_isSharedCheck_4912_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_lctx_4861_);
lean_dec(v___x_4854_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4912_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v_traceState_4867_; lean_object* v_env_4868_; lean_object* v_nextMacroScope_4869_; lean_object* v_ngen_4870_; lean_object* v_auxDeclNGen_4871_; lean_object* v_cache_4872_; lean_object* v_messages_4873_; lean_object* v_infoState_4874_; lean_object* v_snapshotTasks_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4911_; 
v___x_4865_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2);
v___x_4866_ = lean_st_ref_take(v___y_4849_);
v_traceState_4867_ = lean_ctor_get(v___x_4866_, 4);
v_env_4868_ = lean_ctor_get(v___x_4866_, 0);
v_nextMacroScope_4869_ = lean_ctor_get(v___x_4866_, 1);
v_ngen_4870_ = lean_ctor_get(v___x_4866_, 2);
v_auxDeclNGen_4871_ = lean_ctor_get(v___x_4866_, 3);
v_cache_4872_ = lean_ctor_get(v___x_4866_, 5);
v_messages_4873_ = lean_ctor_get(v___x_4866_, 6);
v_infoState_4874_ = lean_ctor_get(v___x_4866_, 7);
v_snapshotTasks_4875_ = lean_ctor_get(v___x_4866_, 8);
v_isSharedCheck_4911_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4877_ = v___x_4866_;
v_isShared_4878_ = v_isSharedCheck_4911_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_snapshotTasks_4875_);
lean_inc(v_infoState_4874_);
lean_inc(v_messages_4873_);
lean_inc(v_cache_4872_);
lean_inc(v_traceState_4867_);
lean_inc(v_auxDeclNGen_4871_);
lean_inc(v_ngen_4870_);
lean_inc(v_nextMacroScope_4869_);
lean_inc(v_env_4868_);
lean_dec(v___x_4866_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4911_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
uint64_t v_tid_4879_; lean_object* v_traces_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4910_; 
v_tid_4879_ = lean_ctor_get_uint64(v_traceState_4867_, sizeof(void*)*1);
v_traces_4880_ = lean_ctor_get(v_traceState_4867_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v_traceState_4867_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4882_ = v_traceState_4867_;
v_isShared_4883_ = v_isSharedCheck_4910_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_traces_4880_);
lean_dec(v_traceState_4867_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4910_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
uint8_t v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4884_ = lean_unbox(v_a_4856_);
lean_dec(v_a_4856_);
v___x_4885_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4861_, v___x_4884_);
lean_dec_ref(v_lctx_4861_);
lean_inc_ref(v_options_4851_);
v___x_4886_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4886_, 0, v_env_4860_);
lean_ctor_set(v___x_4886_, 1, v___x_4865_);
lean_ctor_set(v___x_4886_, 2, v___x_4885_);
lean_ctor_set(v___x_4886_, 3, v_options_4851_);
if (v_isShared_4864_ == 0)
{
lean_ctor_set_tag(v___x_4863_, 3);
lean_ctor_set(v___x_4863_, 1, v_msg_4845_);
lean_ctor_set(v___x_4863_, 0, v___x_4886_);
v___x_4888_ = v___x_4863_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4886_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_msg_4845_);
v___x_4888_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
lean_object* v___x_4889_; double v___x_4890_; uint8_t v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4899_; 
v___x_4889_ = lean_box(0);
v___x_4890_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1);
v___x_4891_ = 0;
v___x_4892_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4893_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4893_, 0, v_cls_4844_);
lean_ctor_set(v___x_4893_, 1, v___x_4889_);
lean_ctor_set(v___x_4893_, 2, v___x_4892_);
lean_ctor_set_float(v___x_4893_, sizeof(void*)*3, v___x_4890_);
lean_ctor_set_float(v___x_4893_, sizeof(void*)*3 + 8, v___x_4890_);
lean_ctor_set_uint8(v___x_4893_, sizeof(void*)*3 + 16, v___x_4891_);
v___x_4894_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4895_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4893_);
lean_ctor_set(v___x_4895_, 1, v___x_4888_);
lean_ctor_set(v___x_4895_, 2, v___x_4894_);
lean_inc(v_ref_4852_);
v___x_4896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4896_, 0, v_ref_4852_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
v___x_4897_ = l_Lean_PersistentArray_push___redArg(v_traces_4880_, v___x_4896_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4897_);
v___x_4899_ = v___x_4882_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4897_);
lean_ctor_set_uint64(v_reuseFailAlloc_4908_, sizeof(void*)*1, v_tid_4879_);
v___x_4899_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
lean_object* v___x_4901_; 
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 4, v___x_4899_);
v___x_4901_ = v___x_4877_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_env_4868_);
lean_ctor_set(v_reuseFailAlloc_4907_, 1, v_nextMacroScope_4869_);
lean_ctor_set(v_reuseFailAlloc_4907_, 2, v_ngen_4870_);
lean_ctor_set(v_reuseFailAlloc_4907_, 3, v_auxDeclNGen_4871_);
lean_ctor_set(v_reuseFailAlloc_4907_, 4, v___x_4899_);
lean_ctor_set(v_reuseFailAlloc_4907_, 5, v_cache_4872_);
lean_ctor_set(v_reuseFailAlloc_4907_, 6, v_messages_4873_);
lean_ctor_set(v_reuseFailAlloc_4907_, 7, v_infoState_4874_);
lean_ctor_set(v_reuseFailAlloc_4907_, 8, v_snapshotTasks_4875_);
v___x_4901_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4905_; 
v___x_4902_ = lean_st_ref_set(v___y_4849_, v___x_4901_);
v___x_4903_ = lean_box(0);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 0, v___x_4903_);
v___x_4905_ = v___x_4858_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
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
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_dec(v___x_4854_);
lean_dec(v___x_4853_);
lean_dec_ref(v_msg_4845_);
lean_dec(v_cls_4844_);
v_a_4915_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4855_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4855_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4923_, lean_object* v_msg_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4923_, v_msg_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4931_, lean_object* v_msg_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v___x_4940_; 
v___x_4940_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4931_, v_msg_4932_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4941_, lean_object* v_msg_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4941_, v_msg_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
return v_res_4950_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = lean_box(0);
v___x_4952_ = lean_unsigned_to_nat(16u);
v___x_4953_ = lean_mk_array(v___x_4952_, v___x_4951_);
return v___x_4953_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4954_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_4955_ = lean_unsigned_to_nat(0u);
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
lean_ctor_set(v___x_4956_, 1, v___x_4954_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_4957_, size_t v_i_4958_, lean_object* v_bs_4959_){
_start:
{
uint8_t v___x_4960_; 
v___x_4960_ = lean_usize_dec_lt(v_i_4958_, v_sz_4957_);
if (v___x_4960_ == 0)
{
return v_bs_4959_;
}
else
{
lean_object* v___x_4961_; lean_object* v_bs_x27_4962_; lean_object* v___x_4963_; size_t v___x_4964_; size_t v___x_4965_; lean_object* v___x_4966_; 
v___x_4961_ = lean_unsigned_to_nat(0u);
v_bs_x27_4962_ = lean_array_uset(v_bs_4959_, v_i_4958_, v___x_4961_);
v___x_4963_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_4964_ = ((size_t)1ULL);
v___x_4965_ = lean_usize_add(v_i_4958_, v___x_4964_);
v___x_4966_ = lean_array_uset(v_bs_x27_4962_, v_i_4958_, v___x_4963_);
v_i_4958_ = v___x_4965_;
v_bs_4959_ = v___x_4966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_4968_, lean_object* v_i_4969_, lean_object* v_bs_4970_){
_start:
{
size_t v_sz_boxed_4971_; size_t v_i_boxed_4972_; lean_object* v_res_4973_; 
v_sz_boxed_4971_ = lean_unbox_usize(v_sz_4968_);
lean_dec(v_sz_4968_);
v_i_boxed_4972_ = lean_unbox_usize(v_i_4969_);
lean_dec(v_i_4969_);
v_res_4973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_4971_, v_i_boxed_4972_, v_bs_4970_);
return v_res_4973_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_4976_ = l_Lean_stringToMessageData(v___x_4975_);
return v___x_4976_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_4979_ = l_Lean_stringToMessageData(v___x_4978_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v___x_4991_; lean_object* v_decls_4992_; lean_object* v_funVals_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5032_; 
v___x_4991_ = lean_st_ref_take(v_a_4982_);
v_decls_4992_ = lean_ctor_get(v_a_4981_, 0);
v_funVals_4993_ = lean_ctor_get(v___x_4991_, 1);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_5032_ == 0)
{
lean_object* v_unused_5033_; 
v_unused_5033_ = lean_ctor_get(v___x_4991_, 0);
lean_dec(v_unused_5033_);
v___x_4995_ = v___x_4991_;
v_isShared_4996_ = v_isSharedCheck_5032_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_funVals_4993_);
lean_dec(v___x_4991_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5032_;
goto v_resetjp_4994_;
}
v___jp_4988_:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = lean_box(0);
v___x_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
return v___x_4990_;
}
v_resetjp_4994_:
{
size_t v_sz_4997_; size_t v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5001_; 
v_sz_4997_ = lean_array_size(v_decls_4992_);
v___x_4998_ = ((size_t)0ULL);
lean_inc_ref(v_decls_4992_);
v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_4997_, v___x_4998_, v_decls_4992_);
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 0, v___x_4999_);
v___x_5001_ = v___x_4995_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_4999_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_funVals_4993_);
v___x_5001_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5002_ = lean_st_ref_set(v_a_4982_, v___x_5001_);
v___x_5003_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; uint8_t v___x_5005_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref(v___x_5003_);
v___x_5005_ = lean_unbox(v_a_5004_);
lean_dec(v_a_5004_);
if (v___x_5005_ == 0)
{
lean_object* v_options_5006_; uint8_t v_hasTrace_5007_; 
v_options_5006_ = lean_ctor_get(v_a_4985_, 2);
v_hasTrace_5007_ = lean_ctor_get_uint8(v_options_5006_, sizeof(void*)*1);
if (v_hasTrace_5007_ == 0)
{
lean_dec(v_n_4980_);
goto v___jp_4988_;
}
else
{
lean_object* v_inheritedTraceOptions_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; uint8_t v___x_5011_; 
v_inheritedTraceOptions_5008_ = lean_ctor_get(v_a_4985_, 13);
v___x_5009_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5010_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5011_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5008_, v_options_5006_, v___x_5010_);
if (v___x_5011_ == 0)
{
lean_dec(v_n_4980_);
goto v___jp_4988_;
}
else
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5012_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5013_ = l_Nat_reprFast(v_n_4980_);
v___x_5014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5013_);
v___x_5015_ = l_Lean_MessageData_ofFormat(v___x_5014_);
v___x_5016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5012_);
lean_ctor_set(v___x_5016_, 1, v___x_5015_);
v___x_5017_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5016_);
lean_ctor_set(v___x_5018_, 1, v___x_5017_);
v___x_5019_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5009_, v___x_5018_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_dec_ref(v___x_5019_);
goto v___jp_4988_;
}
else
{
return v___x_5019_;
}
}
}
}
else
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_unsigned_to_nat(1u);
v___x_5021_ = lean_nat_add(v_n_4980_, v___x_5020_);
lean_dec(v_n_4980_);
v_n_4980_ = v___x_5021_;
goto _start;
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5030_; 
lean_dec(v_n_4980_);
v_a_5023_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5025_ = v___x_5003_;
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5003_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5028_; 
if (v_isShared_5026_ == 0)
{
v___x_5028_ = v___x_5025_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
return v_res_5042_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = 0;
v___x_5044_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5043_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5045_){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5046_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5047_ = lean_panic_fn_borrowed(v___x_5046_, v_msg_5045_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5048_, lean_object* v_msg_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_options_5055_; lean_object* v_ref_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v_options_5055_ = lean_ctor_get(v___y_5052_, 2);
v_ref_5056_ = lean_ctor_get(v___y_5052_, 5);
v___x_5057_ = lean_st_ref_get(v___y_5053_);
v___x_5058_ = lean_st_ref_get(v___y_5051_);
v___x_5059_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5050_);
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5118_; 
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5062_ = v___x_5059_;
v_isShared_5063_ = v_isSharedCheck_5118_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5059_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5118_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v_env_5064_; lean_object* v_lctx_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5116_; 
v_env_5064_ = lean_ctor_get(v___x_5057_, 0);
lean_inc_ref(v_env_5064_);
lean_dec(v___x_5057_);
v_lctx_5065_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5116_ == 0)
{
lean_object* v_unused_5117_; 
v_unused_5117_ = lean_ctor_get(v___x_5058_, 1);
lean_dec(v_unused_5117_);
v___x_5067_ = v___x_5058_;
v_isShared_5068_ = v_isSharedCheck_5116_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_lctx_5065_);
lean_dec(v___x_5058_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5116_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v_traceState_5071_; lean_object* v_env_5072_; lean_object* v_nextMacroScope_5073_; lean_object* v_ngen_5074_; lean_object* v_auxDeclNGen_5075_; lean_object* v_cache_5076_; lean_object* v_messages_5077_; lean_object* v_infoState_5078_; lean_object* v_snapshotTasks_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5115_; 
v___x_5069_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___closed__2);
v___x_5070_ = lean_st_ref_take(v___y_5053_);
v_traceState_5071_ = lean_ctor_get(v___x_5070_, 4);
v_env_5072_ = lean_ctor_get(v___x_5070_, 0);
v_nextMacroScope_5073_ = lean_ctor_get(v___x_5070_, 1);
v_ngen_5074_ = lean_ctor_get(v___x_5070_, 2);
v_auxDeclNGen_5075_ = lean_ctor_get(v___x_5070_, 3);
v_cache_5076_ = lean_ctor_get(v___x_5070_, 5);
v_messages_5077_ = lean_ctor_get(v___x_5070_, 6);
v_infoState_5078_ = lean_ctor_get(v___x_5070_, 7);
v_snapshotTasks_5079_ = lean_ctor_get(v___x_5070_, 8);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5081_ = v___x_5070_;
v_isShared_5082_ = v_isSharedCheck_5115_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_snapshotTasks_5079_);
lean_inc(v_infoState_5078_);
lean_inc(v_messages_5077_);
lean_inc(v_cache_5076_);
lean_inc(v_traceState_5071_);
lean_inc(v_auxDeclNGen_5075_);
lean_inc(v_ngen_5074_);
lean_inc(v_nextMacroScope_5073_);
lean_inc(v_env_5072_);
lean_dec(v___x_5070_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5115_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
uint64_t v_tid_5083_; lean_object* v_traces_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5114_; 
v_tid_5083_ = lean_ctor_get_uint64(v_traceState_5071_, sizeof(void*)*1);
v_traces_5084_ = lean_ctor_get(v_traceState_5071_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v_traceState_5071_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5086_ = v_traceState_5071_;
v_isShared_5087_ = v_isSharedCheck_5114_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_traces_5084_);
lean_dec(v_traceState_5071_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5114_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
uint8_t v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5092_; 
v___x_5088_ = lean_unbox(v_a_5060_);
lean_dec(v_a_5060_);
v___x_5089_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5065_, v___x_5088_);
lean_dec_ref(v_lctx_5065_);
lean_inc_ref(v_options_5055_);
v___x_5090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5090_, 0, v_env_5064_);
lean_ctor_set(v___x_5090_, 1, v___x_5069_);
lean_ctor_set(v___x_5090_, 2, v___x_5089_);
lean_ctor_set(v___x_5090_, 3, v_options_5055_);
if (v_isShared_5068_ == 0)
{
lean_ctor_set_tag(v___x_5067_, 3);
lean_ctor_set(v___x_5067_, 1, v_msg_5049_);
lean_ctor_set(v___x_5067_, 0, v___x_5090_);
v___x_5092_ = v___x_5067_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5090_);
lean_ctor_set(v_reuseFailAlloc_5113_, 1, v_msg_5049_);
v___x_5092_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
lean_object* v___x_5093_; double v___x_5094_; uint8_t v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5103_; 
v___x_5093_ = lean_box(0);
v___x_5094_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1);
v___x_5095_ = 0;
v___x_5096_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5097_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5097_, 0, v_cls_5048_);
lean_ctor_set(v___x_5097_, 1, v___x_5093_);
lean_ctor_set(v___x_5097_, 2, v___x_5096_);
lean_ctor_set_float(v___x_5097_, sizeof(void*)*3, v___x_5094_);
lean_ctor_set_float(v___x_5097_, sizeof(void*)*3 + 8, v___x_5094_);
lean_ctor_set_uint8(v___x_5097_, sizeof(void*)*3 + 16, v___x_5095_);
v___x_5098_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5099_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5092_);
lean_ctor_set(v___x_5099_, 2, v___x_5098_);
lean_inc(v_ref_5056_);
v___x_5100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5100_, 0, v_ref_5056_);
lean_ctor_set(v___x_5100_, 1, v___x_5099_);
v___x_5101_ = l_Lean_PersistentArray_push___redArg(v_traces_5084_, v___x_5100_);
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 0, v___x_5101_);
v___x_5103_ = v___x_5086_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5101_);
lean_ctor_set_uint64(v_reuseFailAlloc_5112_, sizeof(void*)*1, v_tid_5083_);
v___x_5103_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___x_5105_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 4, v___x_5103_);
v___x_5105_ = v___x_5081_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v_env_5072_);
lean_ctor_set(v_reuseFailAlloc_5111_, 1, v_nextMacroScope_5073_);
lean_ctor_set(v_reuseFailAlloc_5111_, 2, v_ngen_5074_);
lean_ctor_set(v_reuseFailAlloc_5111_, 3, v_auxDeclNGen_5075_);
lean_ctor_set(v_reuseFailAlloc_5111_, 4, v___x_5103_);
lean_ctor_set(v_reuseFailAlloc_5111_, 5, v_cache_5076_);
lean_ctor_set(v_reuseFailAlloc_5111_, 6, v_messages_5077_);
lean_ctor_set(v_reuseFailAlloc_5111_, 7, v_infoState_5078_);
lean_ctor_set(v_reuseFailAlloc_5111_, 8, v_snapshotTasks_5079_);
v___x_5105_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5109_; 
v___x_5106_ = lean_st_ref_set(v___y_5053_, v___x_5105_);
v___x_5107_ = lean_box(0);
if (v_isShared_5063_ == 0)
{
lean_ctor_set(v___x_5062_, 0, v___x_5107_);
v___x_5109_ = v___x_5062_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
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
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec(v___x_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v_msg_5049_);
lean_dec(v_cls_5048_);
v_a_5119_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5059_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5059_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5127_, lean_object* v_msg_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5127_, v_msg_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5135_, size_t v_i_5136_, size_t v_stop_5137_, lean_object* v_b_5138_){
_start:
{
uint8_t v___x_5140_; 
v___x_5140_ = lean_usize_dec_eq(v_i_5136_, v_stop_5137_);
if (v___x_5140_ == 0)
{
lean_object* v_fst_5141_; lean_object* v_snd_5142_; lean_object* v___x_5143_; lean_object* v_snd_5144_; lean_object* v_fst_5145_; lean_object* v_fst_5146_; lean_object* v_snd_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5162_; 
v_fst_5141_ = lean_ctor_get(v_b_5138_, 0);
lean_inc(v_fst_5141_);
v_snd_5142_ = lean_ctor_get(v_b_5138_, 1);
lean_inc(v_snd_5142_);
lean_dec_ref(v_b_5138_);
v___x_5143_ = lean_array_uget_borrowed(v_as_5135_, v_i_5136_);
v_snd_5144_ = lean_ctor_get(v___x_5143_, 1);
lean_inc(v_snd_5144_);
v_fst_5145_ = lean_ctor_get(v___x_5143_, 0);
v_fst_5146_ = lean_ctor_get(v_snd_5144_, 0);
v_snd_5147_ = lean_ctor_get(v_snd_5144_, 1);
v_isSharedCheck_5162_ = !lean_is_exclusive(v_snd_5144_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5149_ = v_snd_5144_;
v_isShared_5150_ = v_isSharedCheck_5162_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_snd_5147_);
lean_inc(v_fst_5146_);
lean_dec(v_snd_5144_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5162_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v_fvarId_5151_; uint8_t v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5157_; 
v_fvarId_5151_ = lean_ctor_get(v_fst_5145_, 0);
v___x_5152_ = 0;
v___x_5153_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5152_, v_fst_5146_, v_fst_5141_);
lean_dec(v_fst_5146_);
v___x_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5154_, 0, v_snd_5147_);
lean_inc(v_fvarId_5151_);
v___x_5155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5142_, v_fvarId_5151_, v___x_5154_);
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 1, v___x_5155_);
lean_ctor_set(v___x_5149_, 0, v___x_5153_);
v___x_5157_ = v___x_5149_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v___x_5153_);
lean_ctor_set(v_reuseFailAlloc_5161_, 1, v___x_5155_);
v___x_5157_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
size_t v___x_5158_; size_t v___x_5159_; 
v___x_5158_ = ((size_t)1ULL);
v___x_5159_ = lean_usize_add(v_i_5136_, v___x_5158_);
v_i_5136_ = v___x_5159_;
v_b_5138_ = v___x_5157_;
goto _start;
}
}
}
else
{
lean_object* v___x_5163_; 
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v_b_5138_);
return v___x_5163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5164_, lean_object* v_i_5165_, lean_object* v_stop_5166_, lean_object* v_b_5167_, lean_object* v___y_5168_){
_start:
{
size_t v_i_boxed_5169_; size_t v_stop_boxed_5170_; lean_object* v_res_5171_; 
v_i_boxed_5169_ = lean_unbox_usize(v_i_5165_);
lean_dec(v_i_5165_);
v_stop_boxed_5170_ = lean_unbox_usize(v_stop_5166_);
lean_dec(v_stop_5166_);
v_res_5171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5164_, v_i_boxed_5169_, v_stop_boxed_5170_, v_b_5167_);
lean_dec_ref(v_as_5164_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5172_, lean_object* v_x_5173_){
_start:
{
if (lean_obj_tag(v_x_5173_) == 0)
{
lean_object* v___x_5174_; 
v___x_5174_ = lean_box(0);
return v___x_5174_;
}
else
{
lean_object* v_key_5175_; lean_object* v_value_5176_; lean_object* v_tail_5177_; uint8_t v___x_5178_; 
v_key_5175_ = lean_ctor_get(v_x_5173_, 0);
v_value_5176_ = lean_ctor_get(v_x_5173_, 1);
v_tail_5177_ = lean_ctor_get(v_x_5173_, 2);
v___x_5178_ = l_Lean_instBEqFVarId_beq(v_key_5175_, v_a_5172_);
if (v___x_5178_ == 0)
{
v_x_5173_ = v_tail_5177_;
goto _start;
}
else
{
lean_object* v___x_5180_; 
lean_inc(v_value_5176_);
v___x_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5180_, 0, v_value_5176_);
return v___x_5180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5181_, lean_object* v_x_5182_){
_start:
{
lean_object* v_res_5183_; 
v_res_5183_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5181_, v_x_5182_);
lean_dec(v_x_5182_);
lean_dec(v_a_5181_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v_buckets_5186_; lean_object* v___x_5187_; uint64_t v___x_5188_; uint64_t v___x_5189_; uint64_t v___x_5190_; uint64_t v_fold_5191_; uint64_t v___x_5192_; uint64_t v___x_5193_; uint64_t v___x_5194_; size_t v___x_5195_; size_t v___x_5196_; size_t v___x_5197_; size_t v___x_5198_; size_t v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v_buckets_5186_ = lean_ctor_get(v_m_5184_, 1);
v___x_5187_ = lean_array_get_size(v_buckets_5186_);
v___x_5188_ = l_Lean_instHashableFVarId_hash(v_a_5185_);
v___x_5189_ = 32ULL;
v___x_5190_ = lean_uint64_shift_right(v___x_5188_, v___x_5189_);
v_fold_5191_ = lean_uint64_xor(v___x_5188_, v___x_5190_);
v___x_5192_ = 16ULL;
v___x_5193_ = lean_uint64_shift_right(v_fold_5191_, v___x_5192_);
v___x_5194_ = lean_uint64_xor(v_fold_5191_, v___x_5193_);
v___x_5195_ = lean_uint64_to_usize(v___x_5194_);
v___x_5196_ = lean_usize_of_nat(v___x_5187_);
v___x_5197_ = ((size_t)1ULL);
v___x_5198_ = lean_usize_sub(v___x_5196_, v___x_5197_);
v___x_5199_ = lean_usize_land(v___x_5195_, v___x_5198_);
v___x_5200_ = lean_array_uget_borrowed(v_buckets_5186_, v___x_5199_);
v___x_5201_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5185_, v___x_5200_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5202_, lean_object* v_a_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5202_, v_a_5203_);
lean_dec(v_a_5203_);
lean_dec_ref(v_m_5202_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5205_, lean_object* v_as_5206_, size_t v_i_5207_, size_t v_stop_5208_, lean_object* v_b_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v_a_5216_; uint8_t v___x_5220_; 
v___x_5220_ = lean_usize_dec_eq(v_i_5207_, v_stop_5208_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; lean_object* v_fvarId_5222_; lean_object* v___x_5223_; 
v___x_5221_ = lean_array_uget_borrowed(v_as_5206_, v_i_5207_);
v_fvarId_5222_ = lean_ctor_get(v___x_5221_, 0);
v___x_5223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5205_, v_fvarId_5222_);
if (lean_obj_tag(v___x_5223_) == 1)
{
lean_object* v_val_5224_; lean_object* v___x_5225_; 
v_val_5224_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_val_5224_);
lean_dec_ref(v___x_5223_);
v___x_5225_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5224_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5226_);
lean_dec_ref(v___x_5225_);
if (lean_obj_tag(v_a_5226_) == 1)
{
lean_object* v_val_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v_val_5227_ = lean_ctor_get(v_a_5226_, 0);
lean_inc(v_val_5227_);
lean_dec_ref(v_a_5226_);
lean_inc(v___x_5221_);
v___x_5228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5221_);
lean_ctor_set(v___x_5228_, 1, v_val_5227_);
v___x_5229_ = lean_array_push(v_b_5209_, v___x_5228_);
v_a_5216_ = v___x_5229_;
goto v___jp_5215_;
}
else
{
lean_dec(v_a_5226_);
v_a_5216_ = v_b_5209_;
goto v___jp_5215_;
}
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
lean_dec_ref(v_b_5209_);
v_a_5230_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5225_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5225_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5235_; 
if (v_isShared_5233_ == 0)
{
v___x_5235_ = v___x_5232_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5230_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
else
{
lean_dec(v___x_5223_);
v_a_5216_ = v_b_5209_;
goto v___jp_5215_;
}
}
else
{
lean_object* v___x_5238_; 
v___x_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5238_, 0, v_b_5209_);
return v___x_5238_;
}
v___jp_5215_:
{
size_t v___x_5217_; size_t v___x_5218_; 
v___x_5217_ = ((size_t)1ULL);
v___x_5218_ = lean_usize_add(v_i_5207_, v___x_5217_);
v_i_5207_ = v___x_5218_;
v_b_5209_ = v_a_5216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5239_, lean_object* v_as_5240_, lean_object* v_i_5241_, lean_object* v_stop_5242_, lean_object* v_b_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
size_t v_i_boxed_5249_; size_t v_stop_boxed_5250_; lean_object* v_res_5251_; 
v_i_boxed_5249_ = lean_unbox_usize(v_i_5241_);
lean_dec(v_i_5241_);
v_stop_boxed_5250_ = lean_unbox_usize(v_stop_5242_);
lean_dec(v_stop_5242_);
v_res_5251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5239_, v_as_5240_, v_i_boxed_5249_, v_stop_boxed_5250_, v_b_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec_ref(v_as_5240_);
lean_dec_ref(v_assignment_5239_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5254_, lean_object* v_as_5255_, lean_object* v_start_5256_, lean_object* v_stop_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v___x_5263_; uint8_t v___x_5264_; 
v___x_5263_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5264_ = lean_nat_dec_lt(v_start_5256_, v_stop_5257_);
if (v___x_5264_ == 0)
{
lean_object* v___x_5265_; 
v___x_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5263_);
return v___x_5265_;
}
else
{
lean_object* v___x_5266_; uint8_t v___x_5267_; 
v___x_5266_ = lean_array_get_size(v_as_5255_);
v___x_5267_ = lean_nat_dec_le(v_stop_5257_, v___x_5266_);
if (v___x_5267_ == 0)
{
uint8_t v___x_5268_; 
v___x_5268_ = lean_nat_dec_lt(v_start_5256_, v___x_5266_);
if (v___x_5268_ == 0)
{
lean_object* v___x_5269_; 
v___x_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5263_);
return v___x_5269_;
}
else
{
size_t v___x_5270_; size_t v___x_5271_; lean_object* v___x_5272_; 
v___x_5270_ = lean_usize_of_nat(v_start_5256_);
v___x_5271_ = lean_usize_of_nat(v___x_5266_);
v___x_5272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5254_, v_as_5255_, v___x_5270_, v___x_5271_, v___x_5263_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
return v___x_5272_;
}
}
else
{
size_t v___x_5273_; size_t v___x_5274_; lean_object* v___x_5275_; 
v___x_5273_ = lean_usize_of_nat(v_start_5256_);
v___x_5274_ = lean_usize_of_nat(v_stop_5257_);
v___x_5275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5254_, v_as_5255_, v___x_5273_, v___x_5274_, v___x_5263_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
return v___x_5275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5276_, lean_object* v_as_5277_, lean_object* v_start_5278_, lean_object* v_stop_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5276_, v_as_5277_, v_start_5278_, v_stop_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v_stop_5279_);
lean_dec(v_start_5278_);
lean_dec_ref(v_as_5277_);
lean_dec_ref(v_assignment_5276_);
return v_res_5285_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5288_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5289_ = lean_unsigned_to_nat(9u);
v___x_5290_ = lean_unsigned_to_nat(640u);
v___x_5291_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5292_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5293_ = l_mkPanicMessageWithDecl(v___x_5292_, v___x_5291_, v___x_5290_, v___x_5289_, v___x_5288_);
return v___x_5293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5296_, lean_object* v_discrVal_5297_, lean_object* v_discr_5298_, lean_object* v_assignment_5299_, lean_object* v_i_5300_, lean_object* v_as_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v___x_5307_; uint8_t v___x_5308_; 
v___x_5307_ = lean_array_get_size(v_as_5301_);
v___x_5308_ = lean_nat_dec_lt(v_i_5300_, v___x_5307_);
if (v___x_5308_ == 0)
{
lean_object* v___x_5309_; 
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v___x_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5309_, 0, v_as_5301_);
return v___x_5309_;
}
else
{
lean_object* v_a_5310_; lean_object* v_a_5312_; 
v_a_5310_ = lean_array_fget_borrowed(v_as_5301_, v_i_5300_);
if (lean_obj_tag(v_a_5310_) == 0)
{
lean_object* v_ctorName_5323_; lean_object* v_params_5324_; lean_object* v_code_5325_; uint8_t v___x_5326_; lean_object* v___y_5328_; lean_object* v___y_5329_; lean_object* v___y_5342_; uint8_t v___x_5346_; 
v_ctorName_5323_ = lean_ctor_get(v_a_5310_, 0);
v_params_5324_ = lean_ctor_get(v_a_5310_, 1);
v_code_5325_ = lean_ctor_get(v_a_5310_, 2);
v___x_5326_ = 0;
lean_inc(v_ctorName_5323_);
lean_inc(v_discrVal_5297_);
v___x_5346_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5297_, v_ctorName_5323_);
if (v___x_5346_ == 0)
{
lean_object* v_options_5347_; uint8_t v_hasTrace_5348_; 
v_options_5347_ = lean_ctor_get(v___y_5304_, 2);
v_hasTrace_5348_ = lean_ctor_get_uint8(v_options_5347_, sizeof(void*)*1);
if (v_hasTrace_5348_ == 0)
{
v___y_5342_ = v___y_5303_;
goto v___jp_5341_;
}
else
{
lean_object* v_inheritedTraceOptions_5349_; lean_object* v_cls_5350_; lean_object* v___x_5351_; uint8_t v___x_5352_; 
v_inheritedTraceOptions_5349_ = lean_ctor_get(v___y_5304_, 13);
v_cls_5350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5351_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5349_, v_options_5347_, v___x_5351_);
if (v___x_5352_ == 0)
{
v___y_5342_ = v___y_5303_;
goto v___jp_5341_;
}
else
{
lean_object* v___x_5353_; 
lean_inc(v_discr_5298_);
v___x_5353_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5298_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
if (lean_obj_tag(v___x_5353_) == 0)
{
lean_object* v_a_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc(v_a_5354_);
lean_dec_ref(v___x_5353_);
v___x_5355_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5356_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5354_, v___x_5352_);
v___x_5357_ = lean_string_append(v___x_5355_, v___x_5356_);
lean_dec_ref(v___x_5356_);
v___x_5358_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5359_ = lean_string_append(v___x_5357_, v___x_5358_);
lean_inc(v_ctorName_5323_);
v___x_5360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5323_, v___x_5352_);
v___x_5361_ = lean_string_append(v___x_5359_, v___x_5360_);
lean_dec_ref(v___x_5360_);
v___x_5362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5362_, 0, v___x_5361_);
v___x_5363_ = l_Lean_MessageData_ofFormat(v___x_5362_);
v___x_5364_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5350_, v___x_5363_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
if (lean_obj_tag(v___x_5364_) == 0)
{
lean_dec_ref(v___x_5364_);
v___y_5342_ = v___y_5303_;
goto v___jp_5341_;
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5365_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5364_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5364_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5373_ = lean_ctor_get(v___x_5353_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5353_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5353_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5353_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
}
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5381_ = lean_unsigned_to_nat(0u);
v___x_5382_ = lean_array_get_size(v_params_5324_);
v___x_5383_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5299_, v_params_5324_, v___x_5381_, v___x_5382_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
if (lean_obj_tag(v___x_5383_) == 0)
{
lean_object* v_a_5384_; lean_object* v___x_5397_; uint8_t v___x_5398_; lean_object* v_fst_5400_; lean_object* v_snd_5401_; lean_object* v___y_5414_; 
v_a_5384_ = lean_ctor_get(v___x_5383_, 0);
lean_inc(v_a_5384_);
lean_dec_ref(v___x_5383_);
v___x_5397_ = lean_array_get_size(v_a_5384_);
v___x_5398_ = lean_nat_dec_eq(v___x_5397_, v___x_5381_);
if (v___x_5398_ == 0)
{
if (v___x_5346_ == 0)
{
lean_dec(v_a_5384_);
goto v___jp_5385_;
}
else
{
lean_object* v___x_5426_; 
lean_inc_ref(v_code_5325_);
v___x_5426_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5299_, v_code_5325_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_a_5427_);
lean_dec_ref(v___x_5426_);
v___x_5428_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5429_ = lean_nat_dec_lt(v___x_5381_, v___x_5397_);
if (v___x_5429_ == 0)
{
lean_dec(v_a_5384_);
v_fst_5400_ = v_a_5427_;
v_snd_5401_ = v___x_5428_;
goto v___jp_5399_;
}
else
{
lean_object* v___x_5430_; uint8_t v___x_5431_; 
lean_inc(v_a_5427_);
v___x_5430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5430_, 0, v_a_5427_);
lean_ctor_set(v___x_5430_, 1, v___x_5428_);
v___x_5431_ = lean_nat_dec_le(v___x_5397_, v___x_5397_);
if (v___x_5431_ == 0)
{
if (v___x_5429_ == 0)
{
lean_dec_ref(v___x_5430_);
lean_dec(v_a_5384_);
v_fst_5400_ = v_a_5427_;
v_snd_5401_ = v___x_5428_;
goto v___jp_5399_;
}
else
{
size_t v___x_5432_; size_t v___x_5433_; lean_object* v___x_5434_; 
lean_dec(v_a_5427_);
v___x_5432_ = ((size_t)0ULL);
v___x_5433_ = lean_usize_of_nat(v___x_5397_);
v___x_5434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5384_, v___x_5432_, v___x_5433_, v___x_5430_);
lean_dec(v_a_5384_);
v___y_5414_ = v___x_5434_;
goto v___jp_5413_;
}
}
else
{
size_t v___x_5435_; size_t v___x_5436_; lean_object* v___x_5437_; 
lean_dec(v_a_5427_);
v___x_5435_ = ((size_t)0ULL);
v___x_5436_ = lean_usize_of_nat(v___x_5397_);
v___x_5437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5384_, v___x_5435_, v___x_5436_, v___x_5430_);
lean_dec(v_a_5384_);
v___y_5414_ = v___x_5437_;
goto v___jp_5413_;
}
}
}
else
{
lean_object* v_a_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5445_; 
lean_dec(v_a_5384_);
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5438_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5440_ = v___x_5426_;
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_a_5438_);
lean_dec(v___x_5426_);
v___x_5440_ = lean_box(0);
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
v_resetjp_5439_:
{
lean_object* v___x_5443_; 
if (v_isShared_5441_ == 0)
{
v___x_5443_ = v___x_5440_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5438_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
}
else
{
lean_dec(v_a_5384_);
goto v___jp_5385_;
}
v___jp_5385_:
{
lean_object* v___x_5386_; 
lean_inc_ref(v_code_5325_);
v___x_5386_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5299_, v_code_5325_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v_a_5387_; lean_object* v___x_5388_; 
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref(v___x_5386_);
lean_inc_ref(v_a_5310_);
v___x_5388_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5310_, v_a_5387_);
v_a_5312_ = v___x_5388_;
goto v___jp_5311_;
}
else
{
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5389_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5386_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5386_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
}
v___jp_5399_:
{
lean_object* v___x_5402_; 
v___x_5402_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5326_, v_fst_5400_, v_snd_5401_, v___x_5398_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
lean_dec_ref(v_snd_5401_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v_a_5403_; lean_object* v___x_5404_; 
v_a_5403_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v_a_5403_);
lean_dec_ref(v___x_5402_);
lean_inc_ref(v_a_5310_);
v___x_5404_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5310_, v_a_5403_);
v_a_5312_ = v___x_5404_;
goto v___jp_5311_;
}
else
{
lean_object* v_a_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5412_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5405_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5412_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5412_ == 0)
{
v___x_5407_ = v___x_5402_;
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_a_5405_);
lean_dec(v___x_5402_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v___x_5410_; 
if (v_isShared_5408_ == 0)
{
v___x_5410_ = v___x_5407_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5405_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
return v___x_5410_;
}
}
}
}
v___jp_5413_:
{
if (lean_obj_tag(v___y_5414_) == 0)
{
lean_object* v_a_5415_; lean_object* v_fst_5416_; lean_object* v_snd_5417_; 
v_a_5415_ = lean_ctor_get(v___y_5414_, 0);
lean_inc(v_a_5415_);
lean_dec_ref(v___y_5414_);
v_fst_5416_ = lean_ctor_get(v_a_5415_, 0);
lean_inc(v_fst_5416_);
v_snd_5417_ = lean_ctor_get(v_a_5415_, 1);
lean_inc(v_snd_5417_);
lean_dec(v_a_5415_);
v_fst_5400_ = v_fst_5416_;
v_snd_5401_ = v_snd_5417_;
goto v___jp_5399_;
}
else
{
lean_object* v_a_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5425_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5418_ = lean_ctor_get(v___y_5414_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___y_5414_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5420_ = v___y_5414_;
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_a_5418_);
lean_dec(v___y_5414_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5423_; 
if (v_isShared_5421_ == 0)
{
v___x_5423_ = v___x_5420_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5418_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
}
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5453_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5446_ = lean_ctor_get(v___x_5383_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5448_ = v___x_5383_;
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___x_5383_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v___x_5451_; 
if (v_isShared_5449_ == 0)
{
v___x_5451_ = v___x_5448_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
v___jp_5327_:
{
lean_object* v___x_5330_; 
v___x_5330_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5326_, v___y_5329_, v___y_5328_);
lean_dec_ref(v___y_5329_);
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_object* v___x_5331_; lean_object* v___x_5332_; 
lean_dec_ref(v___x_5330_);
lean_inc_ref(v_resultType_5296_);
v___x_5331_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5331_, 0, v_resultType_5296_);
lean_inc_ref(v_a_5310_);
v___x_5332_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5310_, v___x_5331_);
v_a_5312_ = v___x_5332_;
goto v___jp_5311_;
}
else
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5333_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5335_ = v___x_5330_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5330_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5333_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
v___jp_5341_:
{
switch(lean_obj_tag(v_a_5310_))
{
case 0:
{
lean_object* v_code_5343_; 
v_code_5343_ = lean_ctor_get(v_a_5310_, 2);
lean_inc_ref(v_code_5343_);
v___y_5328_ = v___y_5342_;
v___y_5329_ = v_code_5343_;
goto v___jp_5327_;
}
case 1:
{
lean_object* v_code_5344_; 
v_code_5344_ = lean_ctor_get(v_a_5310_, 1);
lean_inc_ref(v_code_5344_);
v___y_5328_ = v___y_5342_;
v___y_5329_ = v_code_5344_;
goto v___jp_5327_;
}
default: 
{
lean_object* v_code_5345_; 
v_code_5345_ = lean_ctor_get(v_a_5310_, 0);
lean_inc_ref(v_code_5345_);
v___y_5328_ = v___y_5342_;
v___y_5329_ = v_code_5345_;
goto v___jp_5327_;
}
}
}
}
else
{
lean_object* v_code_5454_; lean_object* v___x_5455_; 
v_code_5454_ = lean_ctor_get(v_a_5310_, 0);
lean_inc_ref(v_code_5454_);
v___x_5455_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5299_, v_code_5454_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_a_5456_; lean_object* v___x_5457_; 
v_a_5456_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_a_5456_);
lean_dec_ref(v___x_5455_);
lean_inc_ref(v_a_5310_);
v___x_5457_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5310_, v_a_5456_);
v_a_5312_ = v___x_5457_;
goto v___jp_5311_;
}
else
{
lean_object* v_a_5458_; lean_object* v___x_5460_; uint8_t v_isShared_5461_; uint8_t v_isSharedCheck_5465_; 
lean_dec_ref(v_as_5301_);
lean_dec(v_i_5300_);
lean_dec(v_discr_5298_);
lean_dec(v_discrVal_5297_);
lean_dec_ref(v_resultType_5296_);
v_a_5458_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5460_ = v___x_5455_;
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
else
{
lean_inc(v_a_5458_);
lean_dec(v___x_5455_);
v___x_5460_ = lean_box(0);
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
v_resetjp_5459_:
{
lean_object* v___x_5463_; 
if (v_isShared_5461_ == 0)
{
v___x_5463_ = v___x_5460_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_a_5458_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
}
v___jp_5311_:
{
size_t v___x_5313_; size_t v___x_5314_; uint8_t v___x_5315_; 
v___x_5313_ = lean_ptr_addr(v_a_5310_);
v___x_5314_ = lean_ptr_addr(v_a_5312_);
v___x_5315_ = lean_usize_dec_eq(v___x_5313_, v___x_5314_);
if (v___x_5315_ == 0)
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5316_ = lean_unsigned_to_nat(1u);
v___x_5317_ = lean_nat_add(v_i_5300_, v___x_5316_);
v___x_5318_ = lean_array_fset(v_as_5301_, v_i_5300_, v_a_5312_);
lean_dec(v_i_5300_);
v_i_5300_ = v___x_5317_;
v_as_5301_ = v___x_5318_;
goto _start;
}
else
{
lean_object* v___x_5320_; lean_object* v___x_5321_; 
lean_dec_ref(v_a_5312_);
v___x_5320_ = lean_unsigned_to_nat(1u);
v___x_5321_ = lean_nat_add(v_i_5300_, v___x_5320_);
lean_dec(v_i_5300_);
v_i_5300_ = v___x_5321_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5466_, lean_object* v_code_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_){
_start:
{
lean_object* v___y_5474_; lean_object* v___y_5475_; uint8_t v___y_5476_; lean_object* v___y_5481_; lean_object* v___y_5482_; uint8_t v___y_5483_; lean_object* v_decl_5488_; lean_object* v_k_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v___y_5493_; 
switch(lean_obj_tag(v_code_5467_))
{
case 0:
{
lean_object* v_decl_5539_; lean_object* v_k_5540_; lean_object* v___x_5541_; 
v_decl_5539_ = lean_ctor_get(v_code_5467_, 0);
v_k_5540_ = lean_ctor_get(v_code_5467_, 1);
lean_inc_ref(v_k_5540_);
v___x_5541_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5466_, v_k_5540_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5568_; 
v_a_5542_ = lean_ctor_get(v___x_5541_, 0);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5544_ = v___x_5541_;
v_isShared_5545_ = v_isSharedCheck_5568_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5541_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5568_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
uint8_t v___y_5547_; size_t v___x_5563_; size_t v___x_5564_; uint8_t v___x_5565_; 
v___x_5563_ = lean_ptr_addr(v_k_5540_);
v___x_5564_ = lean_ptr_addr(v_a_5542_);
v___x_5565_ = lean_usize_dec_eq(v___x_5563_, v___x_5564_);
if (v___x_5565_ == 0)
{
v___y_5547_ = v___x_5565_;
goto v___jp_5546_;
}
else
{
size_t v___x_5566_; uint8_t v___x_5567_; 
v___x_5566_ = lean_ptr_addr(v_decl_5539_);
v___x_5567_ = lean_usize_dec_eq(v___x_5566_, v___x_5566_);
v___y_5547_ = v___x_5567_;
goto v___jp_5546_;
}
v___jp_5546_:
{
if (v___y_5547_ == 0)
{
lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5557_; 
lean_inc_ref(v_decl_5539_);
v_isSharedCheck_5557_ = !lean_is_exclusive(v_code_5467_);
if (v_isSharedCheck_5557_ == 0)
{
lean_object* v_unused_5558_; lean_object* v_unused_5559_; 
v_unused_5558_ = lean_ctor_get(v_code_5467_, 1);
lean_dec(v_unused_5558_);
v_unused_5559_ = lean_ctor_get(v_code_5467_, 0);
lean_dec(v_unused_5559_);
v___x_5549_ = v_code_5467_;
v_isShared_5550_ = v_isSharedCheck_5557_;
goto v_resetjp_5548_;
}
else
{
lean_dec(v_code_5467_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5557_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 1, v_a_5542_);
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_decl_5539_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v_a_5542_);
v___x_5552_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
lean_object* v___x_5554_; 
if (v_isShared_5545_ == 0)
{
lean_ctor_set(v___x_5544_, 0, v___x_5552_);
v___x_5554_ = v___x_5544_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5552_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
}
else
{
lean_object* v___x_5561_; 
lean_dec(v_a_5542_);
if (v_isShared_5545_ == 0)
{
lean_ctor_set(v___x_5544_, 0, v_code_5467_);
v___x_5561_ = v___x_5544_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_code_5467_);
v___x_5561_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
return v___x_5561_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_5467_);
return v___x_5541_;
}
}
case 1:
{
lean_object* v_decl_5569_; lean_object* v_k_5570_; 
v_decl_5569_ = lean_ctor_get(v_code_5467_, 0);
v_k_5570_ = lean_ctor_get(v_code_5467_, 1);
lean_inc_ref(v_k_5570_);
lean_inc_ref(v_decl_5569_);
v_decl_5488_ = v_decl_5569_;
v_k_5489_ = v_k_5570_;
v___y_5490_ = v_a_5468_;
v___y_5491_ = v_a_5469_;
v___y_5492_ = v_a_5470_;
v___y_5493_ = v_a_5471_;
goto v___jp_5487_;
}
case 2:
{
lean_object* v_decl_5571_; lean_object* v_k_5572_; 
v_decl_5571_ = lean_ctor_get(v_code_5467_, 0);
v_k_5572_ = lean_ctor_get(v_code_5467_, 1);
lean_inc_ref(v_k_5572_);
lean_inc_ref(v_decl_5571_);
v_decl_5488_ = v_decl_5571_;
v_k_5489_ = v_k_5572_;
v___y_5490_ = v_a_5468_;
v___y_5491_ = v_a_5469_;
v___y_5492_ = v_a_5470_;
v___y_5493_ = v_a_5471_;
goto v___jp_5487_;
}
case 4:
{
lean_object* v_cases_5573_; lean_object* v_typeName_5574_; lean_object* v_resultType_5575_; lean_object* v_discr_5576_; lean_object* v_alts_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5618_; 
v_cases_5573_ = lean_ctor_get(v_code_5467_, 0);
lean_inc_ref(v_cases_5573_);
v_typeName_5574_ = lean_ctor_get(v_cases_5573_, 0);
v_resultType_5575_ = lean_ctor_get(v_cases_5573_, 1);
v_discr_5576_ = lean_ctor_get(v_cases_5573_, 2);
v_alts_5577_ = lean_ctor_get(v_cases_5573_, 3);
v_isSharedCheck_5618_ = !lean_is_exclusive(v_cases_5573_);
if (v_isSharedCheck_5618_ == 0)
{
v___x_5579_ = v_cases_5573_;
v_isShared_5580_ = v_isSharedCheck_5618_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_alts_5577_);
lean_inc(v_discr_5576_);
lean_inc(v_resultType_5575_);
lean_inc(v_typeName_5574_);
lean_dec(v_cases_5573_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5618_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5581_; lean_object* v_discrVal_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; 
v___x_5581_ = lean_box(0);
v_discrVal_5582_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5466_, v_discr_5576_, v___x_5581_);
v___x_5583_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5577_);
lean_inc(v_discr_5576_);
lean_inc_ref(v_resultType_5575_);
v___x_5584_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5575_, v_discrVal_5582_, v_discr_5576_, v_assignment_5466_, v___x_5583_, v_alts_5577_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
if (lean_obj_tag(v___x_5584_) == 0)
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5609_; 
v_a_5585_ = lean_ctor_get(v___x_5584_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5587_ = v___x_5584_;
v_isShared_5588_ = v_isSharedCheck_5609_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___x_5584_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5609_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
size_t v___x_5589_; size_t v___x_5590_; uint8_t v___x_5591_; 
v___x_5589_ = lean_ptr_addr(v_alts_5577_);
lean_dec_ref(v_alts_5577_);
v___x_5590_ = lean_ptr_addr(v_a_5585_);
v___x_5591_ = lean_usize_dec_eq(v___x_5589_, v___x_5590_);
if (v___x_5591_ == 0)
{
lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5604_; 
v_isSharedCheck_5604_ = !lean_is_exclusive(v_code_5467_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; 
v_unused_5605_ = lean_ctor_get(v_code_5467_, 0);
lean_dec(v_unused_5605_);
v___x_5593_ = v_code_5467_;
v_isShared_5594_ = v_isSharedCheck_5604_;
goto v_resetjp_5592_;
}
else
{
lean_dec(v_code_5467_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5604_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5596_; 
if (v_isShared_5580_ == 0)
{
lean_ctor_set(v___x_5579_, 3, v_a_5585_);
v___x_5596_ = v___x_5579_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_typeName_5574_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_resultType_5575_);
lean_ctor_set(v_reuseFailAlloc_5603_, 2, v_discr_5576_);
lean_ctor_set(v_reuseFailAlloc_5603_, 3, v_a_5585_);
v___x_5596_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
lean_object* v___x_5598_; 
if (v_isShared_5594_ == 0)
{
lean_ctor_set(v___x_5593_, 0, v___x_5596_);
v___x_5598_ = v___x_5593_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5596_);
v___x_5598_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5600_; 
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 0, v___x_5598_);
v___x_5600_ = v___x_5587_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5598_);
v___x_5600_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
return v___x_5600_;
}
}
}
}
}
else
{
lean_object* v___x_5607_; 
lean_dec(v_a_5585_);
lean_del_object(v___x_5579_);
lean_dec(v_discr_5576_);
lean_dec_ref(v_resultType_5575_);
lean_dec(v_typeName_5574_);
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 0, v_code_5467_);
v___x_5607_ = v___x_5587_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_code_5467_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
return v___x_5607_;
}
}
}
}
else
{
lean_object* v_a_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5617_; 
lean_del_object(v___x_5579_);
lean_dec_ref(v_alts_5577_);
lean_dec(v_discr_5576_);
lean_dec_ref(v_resultType_5575_);
lean_dec(v_typeName_5574_);
lean_dec_ref(v_code_5467_);
v_a_5610_ = lean_ctor_get(v___x_5584_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5617_ == 0)
{
v___x_5612_ = v___x_5584_;
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_a_5610_);
lean_dec(v___x_5584_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5615_; 
if (v_isShared_5613_ == 0)
{
v___x_5615_ = v___x_5612_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_a_5610_);
v___x_5615_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
return v___x_5615_;
}
}
}
}
}
default: 
{
lean_object* v___x_5619_; 
v___x_5619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5619_, 0, v_code_5467_);
return v___x_5619_;
}
}
v___jp_5473_:
{
if (v___y_5476_ == 0)
{
lean_object* v___x_5477_; lean_object* v___x_5478_; 
lean_dec_ref(v_code_5467_);
v___x_5477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5477_, 0, v___y_5475_);
lean_ctor_set(v___x_5477_, 1, v___y_5474_);
v___x_5478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5478_, 0, v___x_5477_);
return v___x_5478_;
}
else
{
lean_object* v___x_5479_; 
lean_dec_ref(v___y_5475_);
lean_dec_ref(v___y_5474_);
v___x_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5479_, 0, v_code_5467_);
return v___x_5479_;
}
}
v___jp_5480_:
{
if (v___y_5483_ == 0)
{
lean_object* v___x_5484_; lean_object* v___x_5485_; 
lean_dec_ref(v_code_5467_);
v___x_5484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5484_, 0, v___y_5482_);
lean_ctor_set(v___x_5484_, 1, v___y_5481_);
v___x_5485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5484_);
return v___x_5485_;
}
else
{
lean_object* v___x_5486_; 
lean_dec_ref(v___y_5482_);
lean_dec_ref(v___y_5481_);
v___x_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5486_, 0, v_code_5467_);
return v___x_5486_;
}
}
v___jp_5487_:
{
lean_object* v_params_5494_; lean_object* v_type_5495_; lean_object* v_value_5496_; lean_object* v___x_5497_; 
v_params_5494_ = lean_ctor_get(v_decl_5488_, 2);
lean_inc_ref(v_params_5494_);
v_type_5495_ = lean_ctor_get(v_decl_5488_, 3);
lean_inc_ref(v_type_5495_);
v_value_5496_ = lean_ctor_get(v_decl_5488_, 4);
lean_inc_ref(v_value_5496_);
v___x_5497_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5466_, v_value_5496_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v_a_5498_; uint8_t v___x_5499_; lean_object* v___x_5500_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref(v___x_5497_);
v___x_5499_ = 0;
v___x_5500_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5499_, v_decl_5488_, v_type_5495_, v_params_5494_, v_a_5498_, v___y_5491_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v___x_5502_; 
v_a_5501_ = lean_ctor_get(v___x_5500_, 0);
lean_inc(v_a_5501_);
lean_dec_ref(v___x_5500_);
v___x_5502_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5466_, v_k_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5502_) == 0)
{
switch(lean_obj_tag(v_code_5467_))
{
case 1:
{
lean_object* v_a_5503_; lean_object* v_decl_5504_; lean_object* v_k_5505_; size_t v___x_5506_; size_t v___x_5507_; uint8_t v___x_5508_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
lean_dec_ref(v___x_5502_);
v_decl_5504_ = lean_ctor_get(v_code_5467_, 0);
v_k_5505_ = lean_ctor_get(v_code_5467_, 1);
v___x_5506_ = lean_ptr_addr(v_k_5505_);
v___x_5507_ = lean_ptr_addr(v_a_5503_);
v___x_5508_ = lean_usize_dec_eq(v___x_5506_, v___x_5507_);
if (v___x_5508_ == 0)
{
v___y_5474_ = v_a_5503_;
v___y_5475_ = v_a_5501_;
v___y_5476_ = v___x_5508_;
goto v___jp_5473_;
}
else
{
size_t v___x_5509_; size_t v___x_5510_; uint8_t v___x_5511_; 
v___x_5509_ = lean_ptr_addr(v_decl_5504_);
v___x_5510_ = lean_ptr_addr(v_a_5501_);
v___x_5511_ = lean_usize_dec_eq(v___x_5509_, v___x_5510_);
v___y_5474_ = v_a_5503_;
v___y_5475_ = v_a_5501_;
v___y_5476_ = v___x_5511_;
goto v___jp_5473_;
}
}
case 2:
{
lean_object* v_a_5512_; lean_object* v_decl_5513_; lean_object* v_k_5514_; size_t v___x_5515_; size_t v___x_5516_; uint8_t v___x_5517_; 
v_a_5512_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5512_);
lean_dec_ref(v___x_5502_);
v_decl_5513_ = lean_ctor_get(v_code_5467_, 0);
v_k_5514_ = lean_ctor_get(v_code_5467_, 1);
v___x_5515_ = lean_ptr_addr(v_k_5514_);
v___x_5516_ = lean_ptr_addr(v_a_5512_);
v___x_5517_ = lean_usize_dec_eq(v___x_5515_, v___x_5516_);
if (v___x_5517_ == 0)
{
v___y_5481_ = v_a_5512_;
v___y_5482_ = v_a_5501_;
v___y_5483_ = v___x_5517_;
goto v___jp_5480_;
}
else
{
size_t v___x_5518_; size_t v___x_5519_; uint8_t v___x_5520_; 
v___x_5518_ = lean_ptr_addr(v_decl_5513_);
v___x_5519_ = lean_ptr_addr(v_a_5501_);
v___x_5520_ = lean_usize_dec_eq(v___x_5518_, v___x_5519_);
v___y_5481_ = v_a_5512_;
v___y_5482_ = v_a_5501_;
v___y_5483_ = v___x_5520_;
goto v___jp_5480_;
}
}
default: 
{
lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5529_; 
lean_dec(v_a_5501_);
lean_dec_ref(v_code_5467_);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5529_ == 0)
{
lean_object* v_unused_5530_; 
v_unused_5530_ = lean_ctor_get(v___x_5502_, 0);
lean_dec(v_unused_5530_);
v___x_5522_ = v___x_5502_;
v_isShared_5523_ = v_isSharedCheck_5529_;
goto v_resetjp_5521_;
}
else
{
lean_dec(v___x_5502_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5529_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5527_; 
v___x_5524_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5525_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5524_);
if (v_isShared_5523_ == 0)
{
lean_ctor_set(v___x_5522_, 0, v___x_5525_);
v___x_5527_ = v___x_5522_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
}
else
{
lean_dec(v_a_5501_);
lean_dec_ref(v_code_5467_);
return v___x_5502_;
}
}
else
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5538_; 
lean_dec_ref(v_k_5489_);
lean_dec_ref(v_code_5467_);
v_a_5531_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5500_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5500_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5536_; 
if (v_isShared_5534_ == 0)
{
v___x_5536_ = v___x_5533_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
else
{
lean_dec_ref(v_type_5495_);
lean_dec_ref(v_params_5494_);
lean_dec_ref(v_k_5489_);
lean_dec_ref(v_decl_5488_);
lean_dec_ref(v_code_5467_);
return v___x_5497_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5620_, lean_object* v_code_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_){
_start:
{
lean_object* v_res_5627_; 
v_res_5627_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5620_, v_code_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
lean_dec(v_a_5625_);
lean_dec_ref(v_a_5624_);
lean_dec(v_a_5623_);
lean_dec_ref(v_a_5622_);
lean_dec_ref(v_assignment_5620_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5628_, lean_object* v_discrVal_5629_, lean_object* v_discr_5630_, lean_object* v_assignment_5631_, lean_object* v_i_5632_, lean_object* v_as_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5628_, v_discrVal_5629_, v_discr_5630_, v_assignment_5631_, v_i_5632_, v_as_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec_ref(v_assignment_5631_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5640_, lean_object* v_m_5641_, lean_object* v_a_5642_){
_start:
{
lean_object* v___x_5643_; 
v___x_5643_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5641_, v_a_5642_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5644_, lean_object* v_m_5645_, lean_object* v_a_5646_){
_start:
{
lean_object* v_res_5647_; 
v_res_5647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5644_, v_m_5645_, v_a_5646_);
lean_dec(v_a_5646_);
lean_dec_ref(v_m_5645_);
return v_res_5647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5648_, size_t v_i_5649_, size_t v_stop_5650_, lean_object* v_b_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_){
_start:
{
lean_object* v___x_5657_; 
v___x_5657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5648_, v_i_5649_, v_stop_5650_, v_b_5651_);
return v___x_5657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5658_, lean_object* v_i_5659_, lean_object* v_stop_5660_, lean_object* v_b_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_){
_start:
{
size_t v_i_boxed_5667_; size_t v_stop_boxed_5668_; lean_object* v_res_5669_; 
v_i_boxed_5667_ = lean_unbox_usize(v_i_5659_);
lean_dec(v_i_5659_);
v_stop_boxed_5668_ = lean_unbox_usize(v_stop_5660_);
lean_dec(v_stop_5660_);
v_res_5669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5658_, v_i_boxed_5667_, v_stop_boxed_5668_, v_b_5661_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_);
lean_dec(v___y_5665_);
lean_dec_ref(v___y_5664_);
lean_dec(v___y_5663_);
lean_dec_ref(v___y_5662_);
lean_dec_ref(v_as_5658_);
return v_res_5669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5670_, lean_object* v_a_5671_, lean_object* v_x_5672_){
_start:
{
lean_object* v___x_5673_; 
v___x_5673_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5671_, v_x_5672_);
return v___x_5673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5674_, lean_object* v_a_5675_, lean_object* v_x_5676_){
_start:
{
lean_object* v_res_5677_; 
v_res_5677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5674_, v_a_5675_, v_x_5676_);
lean_dec(v_x_5676_);
lean_dec(v_a_5675_);
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5678_, lean_object* v_v_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_){
_start:
{
if (lean_obj_tag(v_v_5679_) == 0)
{
lean_object* v_code_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5709_; 
v_code_5685_ = lean_ctor_get(v_v_5679_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v_v_5679_);
if (v_isSharedCheck_5709_ == 0)
{
v___x_5687_ = v_v_5679_;
v_isShared_5688_ = v_isSharedCheck_5709_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_code_5685_);
lean_dec(v_v_5679_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5709_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5689_; 
lean_inc(v___y_5683_);
lean_inc_ref(v___y_5682_);
lean_inc(v___y_5681_);
lean_inc_ref(v___y_5680_);
v___x_5689_ = lean_apply_6(v_f_5678_, v_code_5685_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, lean_box(0));
if (lean_obj_tag(v___x_5689_) == 0)
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5700_; 
v_a_5690_ = lean_ctor_get(v___x_5689_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5689_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5692_ = v___x_5689_;
v_isShared_5693_ = v_isSharedCheck_5700_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5689_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5700_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 0, v_a_5690_);
v___x_5695_ = v___x_5687_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_a_5690_);
v___x_5695_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 0, v___x_5695_);
v___x_5697_ = v___x_5692_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
else
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5708_; 
lean_del_object(v___x_5687_);
v_a_5701_ = lean_ctor_get(v___x_5689_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5689_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5703_ = v___x_5689_;
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v___x_5689_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5706_; 
if (v_isShared_5704_ == 0)
{
v___x_5706_ = v___x_5703_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v_a_5701_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
}
}
else
{
lean_object* v___x_5710_; 
lean_dec_ref(v_f_5678_);
v___x_5710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5710_, 0, v_v_5679_);
return v___x_5710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5711_, lean_object* v_v_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_){
_start:
{
lean_object* v_res_5718_; 
v_res_5718_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5711_, v_v_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5719_, lean_object* v_f_5720_, lean_object* v_v_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
lean_object* v___x_5727_; 
v___x_5727_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5720_, v_v_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
return v___x_5727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5728_, lean_object* v_f_5729_, lean_object* v_v_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_){
_start:
{
uint8_t v_pu_boxed_5736_; lean_object* v_res_5737_; 
v_pu_boxed_5736_ = lean_unbox(v_pu_5728_);
v_res_5737_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5736_, v_f_5729_, v_v_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
lean_dec(v___y_5734_);
lean_dec_ref(v___y_5733_);
lean_dec(v___y_5732_);
lean_dec_ref(v___y_5731_);
return v_res_5737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5738_, lean_object* v_x_5739_){
_start:
{
if (lean_obj_tag(v_x_5739_) == 0)
{
return v_x_5738_;
}
else
{
lean_object* v_key_5740_; lean_object* v_value_5741_; lean_object* v_tail_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; 
v_key_5740_ = lean_ctor_get(v_x_5739_, 0);
v_value_5741_ = lean_ctor_get(v_x_5739_, 1);
v_tail_5742_ = lean_ctor_get(v_x_5739_, 2);
lean_inc(v_value_5741_);
lean_inc(v_key_5740_);
v___x_5743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5743_, 0, v_key_5740_);
lean_ctor_set(v___x_5743_, 1, v_value_5741_);
v___x_5744_ = lean_array_push(v_x_5738_, v___x_5743_);
v_x_5738_ = v___x_5744_;
v_x_5739_ = v_tail_5742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5746_, lean_object* v_x_5747_){
_start:
{
lean_object* v_res_5748_; 
v_res_5748_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5746_, v_x_5747_);
lean_dec(v_x_5747_);
return v_res_5748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5749_, size_t v_i_5750_, size_t v_stop_5751_, lean_object* v_b_5752_){
_start:
{
uint8_t v___x_5753_; 
v___x_5753_ = lean_usize_dec_eq(v_i_5750_, v_stop_5751_);
if (v___x_5753_ == 0)
{
lean_object* v___x_5754_; lean_object* v___x_5755_; size_t v___x_5756_; size_t v___x_5757_; 
v___x_5754_ = lean_array_uget_borrowed(v_as_5749_, v_i_5750_);
v___x_5755_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5752_, v___x_5754_);
v___x_5756_ = ((size_t)1ULL);
v___x_5757_ = lean_usize_add(v_i_5750_, v___x_5756_);
v_i_5750_ = v___x_5757_;
v_b_5752_ = v___x_5755_;
goto _start;
}
else
{
return v_b_5752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5759_, lean_object* v_i_5760_, lean_object* v_stop_5761_, lean_object* v_b_5762_){
_start:
{
size_t v_i_boxed_5763_; size_t v_stop_boxed_5764_; lean_object* v_res_5765_; 
v_i_boxed_5763_ = lean_unbox_usize(v_i_5760_);
lean_dec(v_i_5760_);
v_stop_boxed_5764_ = lean_unbox_usize(v_stop_5761_);
lean_dec(v_stop_5761_);
v_res_5765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5759_, v_i_boxed_5763_, v_stop_boxed_5764_, v_b_5762_);
lean_dec_ref(v_as_5759_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5766_, size_t v_sz_5767_, size_t v_i_5768_, lean_object* v_bs_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_){
_start:
{
uint8_t v___x_5775_; 
v___x_5775_ = lean_usize_dec_lt(v_i_5768_, v_sz_5767_);
if (v___x_5775_ == 0)
{
lean_object* v___x_5776_; 
v___x_5776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5776_, 0, v_bs_5769_);
return v___x_5776_;
}
else
{
lean_object* v_v_5777_; lean_object* v_fst_5778_; lean_object* v_snd_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5803_; 
v_v_5777_ = lean_array_uget(v_bs_5769_, v_i_5768_);
v_fst_5778_ = lean_ctor_get(v_v_5777_, 0);
v_snd_5779_ = lean_ctor_get(v_v_5777_, 1);
v_isSharedCheck_5803_ = !lean_is_exclusive(v_v_5777_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5781_ = v_v_5777_;
v_isShared_5782_ = v_isSharedCheck_5803_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_snd_5779_);
lean_inc(v_fst_5778_);
lean_dec(v_v_5777_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5803_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v___x_5783_; 
v___x_5783_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5778_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
if (lean_obj_tag(v___x_5783_) == 0)
{
lean_object* v_a_5784_; lean_object* v___x_5785_; lean_object* v_bs_x27_5786_; lean_object* v___x_5787_; lean_object* v___x_5789_; 
v_a_5784_ = lean_ctor_get(v___x_5783_, 0);
lean_inc(v_a_5784_);
lean_dec_ref(v___x_5783_);
v___x_5785_ = lean_unsigned_to_nat(0u);
v_bs_x27_5786_ = lean_array_uset(v_bs_5769_, v_i_5768_, v___x_5785_);
v___x_5787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5784_, v_a_5766_);
if (v_isShared_5782_ == 0)
{
lean_ctor_set(v___x_5781_, 0, v___x_5787_);
v___x_5789_ = v___x_5781_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5787_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v_snd_5779_);
v___x_5789_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
size_t v___x_5790_; size_t v___x_5791_; lean_object* v___x_5792_; 
v___x_5790_ = ((size_t)1ULL);
v___x_5791_ = lean_usize_add(v_i_5768_, v___x_5790_);
v___x_5792_ = lean_array_uset(v_bs_x27_5786_, v_i_5768_, v___x_5789_);
v_i_5768_ = v___x_5791_;
v_bs_5769_ = v___x_5792_;
goto _start;
}
}
else
{
lean_object* v_a_5795_; lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5802_; 
lean_del_object(v___x_5781_);
lean_dec(v_snd_5779_);
lean_dec_ref(v_bs_5769_);
v_a_5795_ = lean_ctor_get(v___x_5783_, 0);
v_isSharedCheck_5802_ = !lean_is_exclusive(v___x_5783_);
if (v_isSharedCheck_5802_ == 0)
{
v___x_5797_ = v___x_5783_;
v_isShared_5798_ = v_isSharedCheck_5802_;
goto v_resetjp_5796_;
}
else
{
lean_inc(v_a_5795_);
lean_dec(v___x_5783_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5802_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
lean_object* v___x_5800_; 
if (v_isShared_5798_ == 0)
{
v___x_5800_ = v___x_5797_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v_a_5795_);
v___x_5800_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
return v___x_5800_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5804_, lean_object* v_sz_5805_, lean_object* v_i_5806_, lean_object* v_bs_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_){
_start:
{
uint8_t v_a_2700__boxed_5813_; size_t v_sz_boxed_5814_; size_t v_i_boxed_5815_; lean_object* v_res_5816_; 
v_a_2700__boxed_5813_ = lean_unbox(v_a_5804_);
v_sz_boxed_5814_ = lean_unbox_usize(v_sz_5805_);
lean_dec(v_sz_5805_);
v_i_boxed_5815_ = lean_unbox_usize(v_i_5806_);
lean_dec(v_i_5806_);
v_res_5816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2700__boxed_5813_, v_sz_boxed_5814_, v_i_boxed_5815_, v_bs_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5808_);
return v_res_5816_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5817_){
_start:
{
lean_object* v_fst_5818_; lean_object* v_snd_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5842_; 
v_fst_5818_ = lean_ctor_get(v_x_5817_, 0);
v_snd_5819_ = lean_ctor_get(v_x_5817_, 1);
v_isSharedCheck_5842_ = !lean_is_exclusive(v_x_5817_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5821_ = v_x_5817_;
v_isShared_5822_ = v_isSharedCheck_5842_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_snd_5819_);
lean_inc(v_fst_5818_);
lean_dec(v_x_5817_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5842_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5827_; 
v___x_5823_ = l_String_quote(v_fst_5818_);
v___x_5824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5823_);
v___x_5825_ = lean_box(0);
if (v_isShared_5822_ == 0)
{
lean_ctor_set_tag(v___x_5821_, 1);
lean_ctor_set(v___x_5821_, 1, v___x_5825_);
lean_ctor_set(v___x_5821_, 0, v___x_5824_);
v___x_5827_ = v___x_5821_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v___x_5824_);
lean_ctor_set(v_reuseFailAlloc_5841_, 1, v___x_5825_);
v___x_5827_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; uint8_t v___x_5839_; lean_object* v___x_5840_; 
v___x_5828_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5819_);
v___x_5829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5829_, 0, v___x_5828_);
lean_ctor_set(v___x_5829_, 1, v___x_5827_);
v___x_5830_ = l_List_reverse___redArg(v___x_5829_);
v___x_5831_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5832_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5830_, v___x_5831_);
v___x_5833_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5834_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5835_, 0, v___x_5834_);
lean_ctor_set(v___x_5835_, 1, v___x_5832_);
v___x_5836_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5837_, 0, v___x_5835_);
lean_ctor_set(v___x_5837_, 1, v___x_5836_);
v___x_5838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5838_, 0, v___x_5833_);
lean_ctor_set(v___x_5838_, 1, v___x_5837_);
v___x_5839_ = 0;
v___x_5840_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5840_, 0, v___x_5838_);
lean_ctor_set_uint8(v___x_5840_, sizeof(void*)*1, v___x_5839_);
return v___x_5840_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5843_, lean_object* v_x_5844_, lean_object* v_x_5845_){
_start:
{
if (lean_obj_tag(v_x_5845_) == 0)
{
lean_dec(v_x_5843_);
return v_x_5844_;
}
else
{
lean_object* v_head_5846_; lean_object* v_tail_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5857_; 
v_head_5846_ = lean_ctor_get(v_x_5845_, 0);
v_tail_5847_ = lean_ctor_get(v_x_5845_, 1);
v_isSharedCheck_5857_ = !lean_is_exclusive(v_x_5845_);
if (v_isSharedCheck_5857_ == 0)
{
v___x_5849_ = v_x_5845_;
v_isShared_5850_ = v_isSharedCheck_5857_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_tail_5847_);
lean_inc(v_head_5846_);
lean_dec(v_x_5845_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5857_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5852_; 
lean_inc(v_x_5843_);
if (v_isShared_5850_ == 0)
{
lean_ctor_set_tag(v___x_5849_, 5);
lean_ctor_set(v___x_5849_, 1, v_x_5843_);
lean_ctor_set(v___x_5849_, 0, v_x_5844_);
v___x_5852_ = v___x_5849_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_x_5844_);
lean_ctor_set(v_reuseFailAlloc_5856_, 1, v_x_5843_);
v___x_5852_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5846_);
v___x_5854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5852_);
lean_ctor_set(v___x_5854_, 1, v___x_5853_);
v_x_5844_ = v___x_5854_;
v_x_5845_ = v_tail_5847_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5858_, lean_object* v_x_5859_, lean_object* v_x_5860_){
_start:
{
if (lean_obj_tag(v_x_5860_) == 0)
{
lean_dec(v_x_5858_);
return v_x_5859_;
}
else
{
lean_object* v_head_5861_; lean_object* v_tail_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5872_; 
v_head_5861_ = lean_ctor_get(v_x_5860_, 0);
v_tail_5862_ = lean_ctor_get(v_x_5860_, 1);
v_isSharedCheck_5872_ = !lean_is_exclusive(v_x_5860_);
if (v_isSharedCheck_5872_ == 0)
{
v___x_5864_ = v_x_5860_;
v_isShared_5865_ = v_isSharedCheck_5872_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_tail_5862_);
lean_inc(v_head_5861_);
lean_dec(v_x_5860_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5872_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
lean_inc(v_x_5858_);
if (v_isShared_5865_ == 0)
{
lean_ctor_set_tag(v___x_5864_, 5);
lean_ctor_set(v___x_5864_, 1, v_x_5858_);
lean_ctor_set(v___x_5864_, 0, v_x_5859_);
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_x_5859_);
lean_ctor_set(v_reuseFailAlloc_5871_, 1, v_x_5858_);
v___x_5867_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5868_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5861_);
v___x_5869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5869_, 0, v___x_5867_);
lean_ctor_set(v___x_5869_, 1, v___x_5868_);
v___x_5870_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5858_, v___x_5869_, v_tail_5862_);
return v___x_5870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5873_, lean_object* v_x_5874_){
_start:
{
if (lean_obj_tag(v_x_5873_) == 0)
{
lean_object* v___x_5875_; 
lean_dec(v_x_5874_);
v___x_5875_ = lean_box(0);
return v___x_5875_;
}
else
{
lean_object* v_tail_5876_; 
v_tail_5876_ = lean_ctor_get(v_x_5873_, 1);
if (lean_obj_tag(v_tail_5876_) == 0)
{
lean_object* v_head_5877_; lean_object* v___x_5878_; 
lean_dec(v_x_5874_);
v_head_5877_ = lean_ctor_get(v_x_5873_, 0);
lean_inc(v_head_5877_);
lean_dec_ref(v_x_5873_);
v___x_5878_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5877_);
return v___x_5878_;
}
else
{
lean_object* v_head_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
lean_inc(v_tail_5876_);
v_head_5879_ = lean_ctor_get(v_x_5873_, 0);
lean_inc(v_head_5879_);
lean_dec_ref(v_x_5873_);
v___x_5880_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5879_);
v___x_5881_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5874_, v___x_5880_, v_tail_5876_);
return v___x_5881_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5883_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5884_ = lean_string_length(v___x_5883_);
return v___x_5884_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5885_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5886_ = lean_nat_to_int(v___x_5885_);
return v___x_5886_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5892_){
_start:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; uint8_t v___x_5895_; 
v___x_5893_ = lean_array_get_size(v_xs_5892_);
v___x_5894_ = lean_unsigned_to_nat(0u);
v___x_5895_ = lean_nat_dec_eq(v___x_5893_, v___x_5894_);
if (v___x_5895_ == 0)
{
lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
v___x_5896_ = lean_array_to_list(v_xs_5892_);
v___x_5897_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5898_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5896_, v___x_5897_);
v___x_5899_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5900_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5900_);
lean_ctor_set(v___x_5901_, 1, v___x_5898_);
v___x_5902_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5901_);
lean_ctor_set(v___x_5903_, 1, v___x_5902_);
v___x_5904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5899_);
lean_ctor_set(v___x_5904_, 1, v___x_5903_);
v___x_5905_ = l_Std_Format_fill(v___x_5904_);
return v___x_5905_;
}
else
{
lean_object* v___x_5906_; 
lean_dec_ref(v_xs_5892_);
v___x_5906_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_5906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_5909_, lean_object* v_decl_5910_, lean_object* v_a_5911_, lean_object* v_a_5912_, lean_object* v_a_5913_, lean_object* v_a_5914_){
_start:
{
lean_object* v___y_5917_; lean_object* v___y_5918_; lean_object* v___y_5919_; lean_object* v___y_5920_; lean_object* v_options_5950_; uint8_t v_hasTrace_5951_; 
v_options_5950_ = lean_ctor_get(v_a_5913_, 2);
v_hasTrace_5951_ = lean_ctor_get_uint8(v_options_5950_, sizeof(void*)*1);
if (v_hasTrace_5951_ == 0)
{
v___y_5917_ = v_a_5911_;
v___y_5918_ = v_a_5912_;
v___y_5919_ = v_a_5913_;
v___y_5920_ = v_a_5914_;
goto v___jp_5916_;
}
else
{
lean_object* v_inheritedTraceOptions_5952_; lean_object* v_cls_5953_; uint8_t v___y_5955_; lean_object* v___y_5956_; lean_object* v___x_5992_; uint8_t v___x_5993_; 
v_inheritedTraceOptions_5952_ = lean_ctor_get(v_a_5913_, 13);
v_cls_5953_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5992_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5993_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5952_, v_options_5950_, v___x_5992_);
if (v___x_5993_ == 0)
{
v___y_5917_ = v_a_5911_;
v___y_5918_ = v_a_5912_;
v___y_5919_ = v_a_5913_;
v___y_5920_ = v_a_5914_;
goto v___jp_5916_;
}
else
{
lean_object* v_size_5994_; lean_object* v_buckets_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; uint8_t v___x_5999_; 
v_size_5994_ = lean_ctor_get(v_assignment_5909_, 0);
v_buckets_5995_ = lean_ctor_get(v_assignment_5909_, 1);
v___x_5996_ = lean_mk_empty_array_with_capacity(v_size_5994_);
v___x_5997_ = lean_unsigned_to_nat(0u);
v___x_5998_ = lean_array_get_size(v_buckets_5995_);
v___x_5999_ = lean_nat_dec_lt(v___x_5997_, v___x_5998_);
if (v___x_5999_ == 0)
{
v___y_5955_ = v___x_5993_;
v___y_5956_ = v___x_5996_;
goto v___jp_5954_;
}
else
{
uint8_t v___x_6000_; 
v___x_6000_ = lean_nat_dec_le(v___x_5998_, v___x_5998_);
if (v___x_6000_ == 0)
{
if (v___x_5999_ == 0)
{
v___y_5955_ = v___x_5993_;
v___y_5956_ = v___x_5996_;
goto v___jp_5954_;
}
else
{
size_t v___x_6001_; size_t v___x_6002_; lean_object* v___x_6003_; 
v___x_6001_ = ((size_t)0ULL);
v___x_6002_ = lean_usize_of_nat(v___x_5998_);
v___x_6003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_5995_, v___x_6001_, v___x_6002_, v___x_5996_);
v___y_5955_ = v___x_5993_;
v___y_5956_ = v___x_6003_;
goto v___jp_5954_;
}
}
else
{
size_t v___x_6004_; size_t v___x_6005_; lean_object* v___x_6006_; 
v___x_6004_ = ((size_t)0ULL);
v___x_6005_ = lean_usize_of_nat(v___x_5998_);
v___x_6006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_5995_, v___x_6004_, v___x_6005_, v___x_5996_);
v___y_5955_ = v___x_5993_;
v___y_5956_ = v___x_6006_;
goto v___jp_5954_;
}
}
}
v___jp_5954_:
{
size_t v_sz_5957_; size_t v___x_5958_; lean_object* v___x_5959_; 
v_sz_5957_ = lean_array_size(v___y_5956_);
v___x_5958_ = ((size_t)0ULL);
v___x_5959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_5955_, v_sz_5957_, v___x_5958_, v___y_5956_, v_a_5911_, v_a_5912_, v_a_5913_, v_a_5914_);
if (lean_obj_tag(v___x_5959_) == 0)
{
lean_object* v_toSignature_5960_; lean_object* v_a_5961_; lean_object* v_name_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; 
v_toSignature_5960_ = lean_ctor_get(v_decl_5910_, 0);
v_a_5961_ = lean_ctor_get(v___x_5959_, 0);
lean_inc(v_a_5961_);
lean_dec_ref(v___x_5959_);
v_name_5962_ = lean_ctor_get(v_toSignature_5960_, 0);
v___x_5963_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_5962_);
v___x_5964_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5962_, v___y_5955_);
v___x_5965_ = lean_string_append(v___x_5963_, v___x_5964_);
lean_dec_ref(v___x_5964_);
v___x_5966_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_5967_ = lean_string_append(v___x_5965_, v___x_5966_);
v___x_5968_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_5961_);
v___x_5969_ = l_Std_Format_defWidth;
v___x_5970_ = lean_unsigned_to_nat(0u);
v___x_5971_ = l_Std_Format_pretty(v___x_5968_, v___x_5969_, v___x_5970_, v___x_5970_);
v___x_5972_ = lean_string_append(v___x_5967_, v___x_5971_);
lean_dec_ref(v___x_5971_);
v___x_5973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
v___x_5974_ = l_Lean_MessageData_ofFormat(v___x_5973_);
v___x_5975_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5953_, v___x_5974_, v_a_5911_, v_a_5912_, v_a_5913_, v_a_5914_);
if (lean_obj_tag(v___x_5975_) == 0)
{
lean_dec_ref(v___x_5975_);
v___y_5917_ = v_a_5911_;
v___y_5918_ = v_a_5912_;
v___y_5919_ = v_a_5913_;
v___y_5920_ = v_a_5914_;
goto v___jp_5916_;
}
else
{
lean_object* v_a_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_5983_; 
lean_dec_ref(v_decl_5910_);
lean_dec_ref(v_assignment_5909_);
v_a_5976_ = lean_ctor_get(v___x_5975_, 0);
v_isSharedCheck_5983_ = !lean_is_exclusive(v___x_5975_);
if (v_isSharedCheck_5983_ == 0)
{
v___x_5978_ = v___x_5975_;
v_isShared_5979_ = v_isSharedCheck_5983_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_a_5976_);
lean_dec(v___x_5975_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_5983_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5981_; 
if (v_isShared_5979_ == 0)
{
v___x_5981_ = v___x_5978_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5976_);
v___x_5981_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
return v___x_5981_;
}
}
}
}
else
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5991_; 
lean_dec_ref(v_decl_5910_);
lean_dec_ref(v_assignment_5909_);
v_a_5984_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_5991_ == 0)
{
v___x_5986_ = v___x_5959_;
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v___x_5959_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5989_; 
if (v_isShared_5987_ == 0)
{
v___x_5989_ = v___x_5986_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
v___x_5989_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
return v___x_5989_;
}
}
}
}
}
v___jp_5916_:
{
lean_object* v_toSignature_5921_; lean_object* v_value_5922_; uint8_t v_recursive_5923_; lean_object* v_inlineAttr_x3f_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5949_; 
v_toSignature_5921_ = lean_ctor_get(v_decl_5910_, 0);
v_value_5922_ = lean_ctor_get(v_decl_5910_, 1);
v_recursive_5923_ = lean_ctor_get_uint8(v_decl_5910_, sizeof(void*)*3);
v_inlineAttr_x3f_5924_ = lean_ctor_get(v_decl_5910_, 2);
v_isSharedCheck_5949_ = !lean_is_exclusive(v_decl_5910_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5926_ = v_decl_5910_;
v_isShared_5927_ = v_isSharedCheck_5949_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_inlineAttr_x3f_5924_);
lean_inc(v_value_5922_);
lean_inc(v_toSignature_5921_);
lean_dec(v_decl_5910_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5949_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5928_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_5928_, 0, v_assignment_5909_);
v___x_5929_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_5928_, v_value_5922_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_);
if (lean_obj_tag(v___x_5929_) == 0)
{
lean_object* v_a_5930_; lean_object* v___x_5932_; uint8_t v_isShared_5933_; uint8_t v_isSharedCheck_5940_; 
v_a_5930_ = lean_ctor_get(v___x_5929_, 0);
v_isSharedCheck_5940_ = !lean_is_exclusive(v___x_5929_);
if (v_isSharedCheck_5940_ == 0)
{
v___x_5932_ = v___x_5929_;
v_isShared_5933_ = v_isSharedCheck_5940_;
goto v_resetjp_5931_;
}
else
{
lean_inc(v_a_5930_);
lean_dec(v___x_5929_);
v___x_5932_ = lean_box(0);
v_isShared_5933_ = v_isSharedCheck_5940_;
goto v_resetjp_5931_;
}
v_resetjp_5931_:
{
lean_object* v___x_5935_; 
if (v_isShared_5927_ == 0)
{
lean_ctor_set(v___x_5926_, 1, v_a_5930_);
v___x_5935_ = v___x_5926_;
goto v_reusejp_5934_;
}
else
{
lean_object* v_reuseFailAlloc_5939_; 
v_reuseFailAlloc_5939_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5939_, 0, v_toSignature_5921_);
lean_ctor_set(v_reuseFailAlloc_5939_, 1, v_a_5930_);
lean_ctor_set(v_reuseFailAlloc_5939_, 2, v_inlineAttr_x3f_5924_);
lean_ctor_set_uint8(v_reuseFailAlloc_5939_, sizeof(void*)*3, v_recursive_5923_);
v___x_5935_ = v_reuseFailAlloc_5939_;
goto v_reusejp_5934_;
}
v_reusejp_5934_:
{
lean_object* v___x_5937_; 
if (v_isShared_5933_ == 0)
{
lean_ctor_set(v___x_5932_, 0, v___x_5935_);
v___x_5937_ = v___x_5932_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v___x_5935_);
v___x_5937_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
return v___x_5937_;
}
}
}
}
else
{
lean_object* v_a_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_5948_; 
lean_del_object(v___x_5926_);
lean_dec(v_inlineAttr_x3f_5924_);
lean_dec_ref(v_toSignature_5921_);
v_a_5941_ = lean_ctor_get(v___x_5929_, 0);
v_isSharedCheck_5948_ = !lean_is_exclusive(v___x_5929_);
if (v_isSharedCheck_5948_ == 0)
{
v___x_5943_ = v___x_5929_;
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_a_5941_);
lean_dec(v___x_5929_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v___x_5946_; 
if (v_isShared_5944_ == 0)
{
v___x_5946_ = v___x_5943_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_a_5941_);
v___x_5946_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
return v___x_5946_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6007_, lean_object* v_decl_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_){
_start:
{
lean_object* v_res_6014_; 
v_res_6014_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6007_, v_decl_6008_, v_a_6009_, v_a_6010_, v_a_6011_, v_a_6012_);
lean_dec(v_a_6012_);
lean_dec_ref(v_a_6011_);
lean_dec(v_a_6010_);
lean_dec_ref(v_a_6009_);
return v_res_6014_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6015_, lean_object* v_x_6016_){
_start:
{
lean_object* v___x_6017_; 
v___x_6017_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6015_);
return v___x_6017_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6018_, lean_object* v_x_6019_){
_start:
{
lean_object* v_res_6020_; 
v_res_6020_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6018_, v_x_6019_);
lean_dec(v_x_6019_);
return v_res_6020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6021_, size_t v_i_6022_, lean_object* v_bs_6023_){
_start:
{
uint8_t v___x_6024_; 
v___x_6024_ = lean_usize_dec_lt(v_i_6022_, v_sz_6021_);
if (v___x_6024_ == 0)
{
return v_bs_6023_;
}
else
{
lean_object* v_v_6025_; lean_object* v_toSignature_6026_; lean_object* v_name_6027_; lean_object* v___x_6028_; lean_object* v_bs_x27_6029_; size_t v___x_6030_; size_t v___x_6031_; lean_object* v___x_6032_; 
v_v_6025_ = lean_array_uget_borrowed(v_bs_6023_, v_i_6022_);
v_toSignature_6026_ = lean_ctor_get(v_v_6025_, 0);
v_name_6027_ = lean_ctor_get(v_toSignature_6026_, 0);
lean_inc(v_name_6027_);
v___x_6028_ = lean_unsigned_to_nat(0u);
v_bs_x27_6029_ = lean_array_uset(v_bs_6023_, v_i_6022_, v___x_6028_);
v___x_6030_ = ((size_t)1ULL);
v___x_6031_ = lean_usize_add(v_i_6022_, v___x_6030_);
v___x_6032_ = lean_array_uset(v_bs_x27_6029_, v_i_6022_, v_name_6027_);
v_i_6022_ = v___x_6031_;
v_bs_6023_ = v___x_6032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6034_, lean_object* v_i_6035_, lean_object* v_bs_6036_){
_start:
{
size_t v_sz_boxed_6037_; size_t v_i_boxed_6038_; lean_object* v_res_6039_; 
v_sz_boxed_6037_ = lean_unbox_usize(v_sz_6034_);
lean_dec(v_sz_6034_);
v_i_boxed_6038_ = lean_unbox_usize(v_i_6035_);
lean_dec(v_i_6035_);
v_res_6039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6037_, v_i_boxed_6038_, v_bs_6036_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6040_, lean_object* v_a_6041_){
_start:
{
if (lean_obj_tag(v_a_6040_) == 0)
{
lean_object* v___x_6042_; 
v___x_6042_ = l_List_reverse___redArg(v_a_6041_);
return v___x_6042_;
}
else
{
lean_object* v_head_6043_; lean_object* v_tail_6044_; lean_object* v___x_6046_; uint8_t v_isShared_6047_; uint8_t v_isSharedCheck_6053_; 
v_head_6043_ = lean_ctor_get(v_a_6040_, 0);
v_tail_6044_ = lean_ctor_get(v_a_6040_, 1);
v_isSharedCheck_6053_ = !lean_is_exclusive(v_a_6040_);
if (v_isSharedCheck_6053_ == 0)
{
v___x_6046_ = v_a_6040_;
v_isShared_6047_ = v_isSharedCheck_6053_;
goto v_resetjp_6045_;
}
else
{
lean_inc(v_tail_6044_);
lean_inc(v_head_6043_);
lean_dec(v_a_6040_);
v___x_6046_ = lean_box(0);
v_isShared_6047_ = v_isSharedCheck_6053_;
goto v_resetjp_6045_;
}
v_resetjp_6045_:
{
lean_object* v___x_6048_; lean_object* v___x_6050_; 
v___x_6048_ = l_Lean_MessageData_ofName(v_head_6043_);
if (v_isShared_6047_ == 0)
{
lean_ctor_set(v___x_6046_, 1, v_a_6041_);
lean_ctor_set(v___x_6046_, 0, v___x_6048_);
v___x_6050_ = v___x_6046_;
goto v_reusejp_6049_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v___x_6048_);
lean_ctor_set(v_reuseFailAlloc_6052_, 1, v_a_6041_);
v___x_6050_ = v_reuseFailAlloc_6052_;
goto v_reusejp_6049_;
}
v_reusejp_6049_:
{
v_a_6040_ = v_tail_6044_;
v_a_6041_ = v___x_6050_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6055_; lean_object* v___x_6056_; 
v___x_6055_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6056_ = l_Lean_stringToMessageData(v___x_6055_);
return v___x_6056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6057_, lean_object* v_x_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_, lean_object* v___y_6064_){
_start:
{
lean_object* v___x_6066_; size_t v_sz_6067_; size_t v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; 
v___x_6066_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6067_ = lean_array_size(v___y_6057_);
v___x_6068_ = ((size_t)0ULL);
v___x_6069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6067_, v___x_6068_, v___y_6057_);
v___x_6070_ = lean_array_to_list(v___x_6069_);
v___x_6071_ = lean_box(0);
v___x_6072_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6070_, v___x_6071_);
v___x_6073_ = l_Lean_MessageData_ofList(v___x_6072_);
v___x_6074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6066_);
lean_ctor_set(v___x_6074_, 1, v___x_6073_);
v___x_6075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
return v___x_6075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6076_, lean_object* v_x_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_){
_start:
{
lean_object* v_res_6085_; 
v_res_6085_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6076_, v_x_6077_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_);
lean_dec(v___y_6083_);
lean_dec_ref(v___y_6082_);
lean_dec(v___y_6081_);
lean_dec_ref(v___y_6080_);
lean_dec(v___y_6079_);
lean_dec_ref(v___y_6078_);
lean_dec_ref(v_x_6077_);
return v_res_6085_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6086_; lean_object* v___x_6087_; 
v___x_6086_ = 0;
v___x_6087_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6086_);
return v___x_6087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6088_, lean_object* v_n_6089_, lean_object* v_j_6090_, lean_object* v_a_6091_){
_start:
{
lean_object* v_zero_6092_; uint8_t v_isZero_6093_; 
v_zero_6092_ = lean_unsigned_to_nat(0u);
v_isZero_6093_ = lean_nat_dec_eq(v_j_6090_, v_zero_6092_);
if (v_isZero_6093_ == 1)
{
lean_dec(v_j_6090_);
return v_a_6091_;
}
else
{
lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v_toSignature_6097_; uint8_t v_safe_6098_; lean_object* v_one_6099_; lean_object* v_n_6100_; 
v___x_6094_ = lean_nat_sub(v_n_6089_, v_j_6090_);
v___x_6095_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6096_ = lean_array_get_borrowed(v___x_6095_, v___y_6088_, v___x_6094_);
lean_dec(v___x_6094_);
v_toSignature_6097_ = lean_ctor_get(v___x_6096_, 0);
v_safe_6098_ = lean_ctor_get_uint8(v_toSignature_6097_, sizeof(void*)*4);
v_one_6099_ = lean_unsigned_to_nat(1u);
v_n_6100_ = lean_nat_sub(v_j_6090_, v_one_6099_);
lean_dec(v_j_6090_);
if (v_safe_6098_ == 0)
{
lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6101_ = lean_box(1);
v___x_6102_ = lean_array_push(v_a_6091_, v___x_6101_);
v_j_6090_ = v_n_6100_;
v_a_6091_ = v___x_6102_;
goto _start;
}
else
{
lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6104_ = lean_box(0);
v___x_6105_ = lean_array_push(v_a_6091_, v___x_6104_);
v_j_6090_ = v_n_6100_;
v_a_6091_ = v___x_6105_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6107_, lean_object* v_n_6108_, lean_object* v_j_6109_, lean_object* v_a_6110_){
_start:
{
lean_object* v_res_6111_; 
v_res_6111_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6107_, v_n_6108_, v_j_6109_, v_a_6110_);
lean_dec(v_n_6108_);
lean_dec_ref(v___y_6107_);
return v_res_6111_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6112_, lean_object* v_as_6113_, lean_object* v_i_6114_, lean_object* v_j_6115_, lean_object* v_bs_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_){
_start:
{
lean_object* v_zero_6122_; uint8_t v_isZero_6123_; 
v_zero_6122_ = lean_unsigned_to_nat(0u);
v_isZero_6123_ = lean_nat_dec_eq(v_i_6114_, v_zero_6122_);
if (v_isZero_6123_ == 1)
{
lean_object* v___x_6124_; 
lean_dec(v_j_6115_);
lean_dec(v_i_6114_);
v___x_6124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6124_, 0, v_bs_6116_);
return v___x_6124_;
}
else
{
lean_object* v___x_6125_; lean_object* v_toSignature_6126_; uint8_t v_safe_6127_; lean_object* v_one_6128_; lean_object* v_n_6129_; lean_object* v_a_6131_; 
v___x_6125_ = lean_array_fget_borrowed(v_as_6113_, v_j_6115_);
v_toSignature_6126_ = lean_ctor_get(v___x_6125_, 0);
v_safe_6127_ = lean_ctor_get_uint8(v_toSignature_6126_, sizeof(void*)*4);
v_one_6128_ = lean_unsigned_to_nat(1u);
v_n_6129_ = lean_nat_sub(v_i_6114_, v_one_6128_);
lean_dec(v_i_6114_);
if (v_safe_6127_ == 0)
{
lean_inc(v___x_6125_);
v_a_6131_ = v___x_6125_;
goto v___jp_6130_;
}
else
{
lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; 
v___x_6135_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6136_ = lean_array_get_borrowed(v___x_6135_, v___x_6112_, v_j_6115_);
lean_inc(v___x_6125_);
lean_inc(v___x_6136_);
v___x_6137_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6136_, v___x_6125_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_);
if (lean_obj_tag(v___x_6137_) == 0)
{
lean_object* v_a_6138_; 
v_a_6138_ = lean_ctor_get(v___x_6137_, 0);
lean_inc(v_a_6138_);
lean_dec_ref(v___x_6137_);
v_a_6131_ = v_a_6138_;
goto v___jp_6130_;
}
else
{
lean_object* v_a_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6146_; 
lean_dec(v_n_6129_);
lean_dec_ref(v_bs_6116_);
lean_dec(v_j_6115_);
v_a_6139_ = lean_ctor_get(v___x_6137_, 0);
v_isSharedCheck_6146_ = !lean_is_exclusive(v___x_6137_);
if (v_isSharedCheck_6146_ == 0)
{
v___x_6141_ = v___x_6137_;
v_isShared_6142_ = v_isSharedCheck_6146_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_a_6139_);
lean_dec(v___x_6137_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6146_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6144_; 
if (v_isShared_6142_ == 0)
{
v___x_6144_ = v___x_6141_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_a_6139_);
v___x_6144_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
return v___x_6144_;
}
}
}
}
v___jp_6130_:
{
lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6132_ = lean_nat_add(v_j_6115_, v_one_6128_);
lean_dec(v_j_6115_);
v___x_6133_ = lean_array_push(v_bs_6116_, v_a_6131_);
v_i_6114_ = v_n_6129_;
v_j_6115_ = v___x_6132_;
v_bs_6116_ = v___x_6133_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6147_, lean_object* v_as_6148_, lean_object* v_i_6149_, lean_object* v_j_6150_, lean_object* v_bs_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_){
_start:
{
lean_object* v_res_6157_; 
v_res_6157_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6147_, v_as_6148_, v_i_6149_, v_j_6150_, v_bs_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
lean_dec(v___y_6155_);
lean_dec_ref(v___y_6154_);
lean_dec(v___y_6153_);
lean_dec_ref(v___y_6152_);
lean_dec_ref(v_as_6148_);
lean_dec_ref(v___x_6147_);
return v_res_6157_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6160_, lean_object* v_l_6161_, lean_object* v_r_6162_){
_start:
{
lean_object* v_toSignature_6163_; lean_object* v_toSignature_6164_; lean_object* v_name_6165_; lean_object* v_name_6166_; uint8_t v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; uint8_t v___x_6177_; 
v_toSignature_6163_ = lean_ctor_get(v_l_6161_, 0);
v_toSignature_6164_ = lean_ctor_get(v_r_6162_, 0);
v_name_6165_ = lean_ctor_get(v_toSignature_6163_, 0);
lean_inc(v_name_6165_);
v_name_6166_ = lean_ctor_get(v_toSignature_6164_, 0);
lean_inc(v_name_6166_);
v___x_6167_ = 0;
v___x_6168_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6167_, v_l_6161_);
lean_dec_ref(v_l_6161_);
v___x_6169_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6170_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__0));
v___x_6171_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__1));
v___x_6172_ = l_Lean_Name_toString(v_name_6165_, v___x_6160_);
v___x_6173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6168_);
lean_ctor_set(v___x_6173_, 1, v___x_6172_);
v___x_6174_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6167_, v_r_6162_);
lean_dec_ref(v_r_6162_);
v___x_6175_ = l_Lean_Name_toString(v_name_6166_, v___x_6160_);
v___x_6176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6174_);
lean_ctor_set(v___x_6176_, 1, v___x_6175_);
v___x_6177_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6169_, v___x_6170_, v___x_6171_, v___x_6173_, v___x_6176_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6178_, lean_object* v_l_6179_, lean_object* v_r_6180_){
_start:
{
uint8_t v___x_12948__boxed_6181_; uint8_t v_res_6182_; lean_object* v_r_6183_; 
v___x_12948__boxed_6181_ = lean_unbox(v___x_6178_);
v_res_6182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_12948__boxed_6181_, v_l_6179_, v_r_6180_);
v_r_6183_ = lean_box(v_res_6182_);
return v_r_6183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_as_6184_, lean_object* v_lo_6185_, lean_object* v_hi_6186_){
_start:
{
uint8_t v___x_6187_; 
v___x_6187_ = lean_nat_dec_lt(v_lo_6185_, v_hi_6186_);
if (v___x_6187_ == 0)
{
lean_dec(v_lo_6185_);
return v_as_6184_;
}
else
{
lean_object* v___x_6188_; lean_object* v___f_6189_; lean_object* v___x_6190_; lean_object* v_fst_6191_; lean_object* v_snd_6192_; uint8_t v___x_6193_; 
v___x_6188_ = lean_box(v___x_6187_);
v___f_6189_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_6189_, 0, v___x_6188_);
lean_inc(v_lo_6185_);
v___x_6190_ = l_Array_qpartition___redArg(v_as_6184_, v___f_6189_, v_lo_6185_, v_hi_6186_);
v_fst_6191_ = lean_ctor_get(v___x_6190_, 0);
lean_inc(v_fst_6191_);
v_snd_6192_ = lean_ctor_get(v___x_6190_, 1);
lean_inc(v_snd_6192_);
lean_dec_ref(v___x_6190_);
v___x_6193_ = lean_nat_dec_le(v_hi_6186_, v_fst_6191_);
if (v___x_6193_ == 0)
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_snd_6192_, v_lo_6185_, v_fst_6191_);
v___x_6195_ = lean_unsigned_to_nat(1u);
v___x_6196_ = lean_nat_add(v_fst_6191_, v___x_6195_);
lean_dec(v_fst_6191_);
v_as_6184_ = v___x_6194_;
v_lo_6185_ = v___x_6196_;
goto _start;
}
else
{
lean_dec(v_fst_6191_);
lean_dec(v_lo_6185_);
return v_snd_6192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_as_6198_, lean_object* v_lo_6199_, lean_object* v_hi_6200_){
_start:
{
lean_object* v_res_6201_; 
v_res_6201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_as_6198_, v_lo_6199_, v_hi_6200_);
lean_dec(v_hi_6200_);
return v_res_6201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6202_, lean_object* v___x_6203_, lean_object* v_n_6204_, lean_object* v_j_6205_, lean_object* v_a_6206_){
_start:
{
lean_object* v_zero_6207_; uint8_t v_isZero_6208_; 
v_zero_6207_ = lean_unsigned_to_nat(0u);
v_isZero_6208_ = lean_nat_dec_eq(v_j_6205_, v_zero_6207_);
if (v_isZero_6208_ == 1)
{
lean_dec(v_j_6205_);
return v_a_6206_;
}
else
{
lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v_toSignature_6211_; lean_object* v_name_6212_; lean_object* v___x_6213_; lean_object* v_one_6214_; lean_object* v_n_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; 
v___x_6209_ = lean_nat_sub(v_n_6204_, v_j_6205_);
v___x_6210_ = lean_array_fget_borrowed(v___y_6202_, v___x_6209_);
v_toSignature_6211_ = lean_ctor_get(v___x_6210_, 0);
v_name_6212_ = lean_ctor_get(v_toSignature_6211_, 0);
v___x_6213_ = lean_box(0);
v_one_6214_ = lean_unsigned_to_nat(1u);
v_n_6215_ = lean_nat_sub(v_j_6205_, v_one_6214_);
lean_dec(v_j_6205_);
v___x_6216_ = lean_array_get_borrowed(v___x_6213_, v___x_6203_, v___x_6209_);
lean_dec(v___x_6209_);
lean_inc(v___x_6216_);
lean_inc(v_name_6212_);
v___x_6217_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6206_, v_name_6212_, v___x_6216_);
v_j_6205_ = v_n_6215_;
v_a_6206_ = v___x_6217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6219_, lean_object* v___x_6220_, lean_object* v_n_6221_, lean_object* v_j_6222_, lean_object* v_a_6223_){
_start:
{
lean_object* v_res_6224_; 
v_res_6224_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6219_, v___x_6220_, v_n_6221_, v_j_6222_, v_a_6223_);
lean_dec(v_n_6221_);
lean_dec_ref(v___x_6220_);
lean_dec_ref(v___y_6219_);
return v_res_6224_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6225_; 
v___x_6225_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6225_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6226_; lean_object* v___x_6227_; 
v___x_6226_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6227_, 0, v___x_6226_);
return v___x_6227_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6228_; lean_object* v___x_6229_; 
v___x_6228_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6228_);
lean_ctor_set(v___x_6229_, 1, v___x_6228_);
return v___x_6229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6232_, lean_object* v_a_6233_, lean_object* v_a_6234_, lean_object* v_a_6235_, lean_object* v_a_6236_){
_start:
{
lean_object* v___x_6238_; lean_object* v___y_6240_; lean_object* v___y_6241_; lean_object* v___y_6242_; lean_object* v___y_6243_; lean_object* v___y_6278_; lean_object* v___y_6279_; uint8_t v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___y_6283_; lean_object* v___y_6284_; lean_object* v___y_6285_; lean_object* v___y_6286_; lean_object* v___y_6287_; lean_object* v___y_6288_; uint8_t v___y_6289_; lean_object* v_a_6290_; lean_object* v___y_6300_; uint8_t v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___y_6307_; lean_object* v___y_6308_; lean_object* v___y_6309_; lean_object* v___y_6310_; uint8_t v___y_6311_; lean_object* v_a_6312_; uint8_t v___y_6325_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; uint8_t v___y_6334_; lean_object* v___y_6376_; lean_object* v___y_6399_; lean_object* v___y_6400_; lean_object* v___x_6402_; uint8_t v___x_6403_; 
v___x_6238_ = lean_unsigned_to_nat(0u);
v___x_6402_ = lean_array_get_size(v_decls_6232_);
v___x_6403_ = lean_nat_dec_eq(v___x_6402_, v___x_6238_);
if (v___x_6403_ == 0)
{
lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___y_6407_; uint8_t v___x_6409_; 
v___x_6404_ = lean_unsigned_to_nat(1u);
v___x_6405_ = lean_nat_sub(v___x_6402_, v___x_6404_);
v___x_6409_ = lean_nat_dec_le(v___x_6238_, v___x_6405_);
if (v___x_6409_ == 0)
{
lean_inc(v___x_6405_);
v___y_6407_ = v___x_6405_;
goto v___jp_6406_;
}
else
{
v___y_6407_ = v___x_6238_;
goto v___jp_6406_;
}
v___jp_6406_:
{
uint8_t v___x_6408_; 
v___x_6408_ = lean_nat_dec_le(v___y_6407_, v___x_6405_);
if (v___x_6408_ == 0)
{
lean_dec(v___x_6405_);
lean_inc(v___y_6407_);
v___y_6399_ = v___y_6407_;
v___y_6400_ = v___y_6407_;
goto v___jp_6398_;
}
else
{
v___y_6399_ = v___y_6407_;
v___y_6400_ = v___x_6405_;
goto v___jp_6398_;
}
}
}
else
{
v___y_6376_ = v_decls_6232_;
goto v___jp_6375_;
}
v___jp_6239_:
{
if (lean_obj_tag(v___y_6243_) == 0)
{
lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v_assignments_6246_; lean_object* v_funVals_6247_; lean_object* v_env_6248_; lean_object* v_nextMacroScope_6249_; lean_object* v_ngen_6250_; lean_object* v_auxDeclNGen_6251_; lean_object* v_traceState_6252_; lean_object* v_messages_6253_; lean_object* v_infoState_6254_; lean_object* v_snapshotTasks_6255_; lean_object* v___x_6257_; uint8_t v_isShared_6258_; uint8_t v_isSharedCheck_6267_; 
lean_dec_ref(v___y_6243_);
v___x_6244_ = lean_st_ref_get(v___y_6242_);
lean_dec(v___y_6242_);
v___x_6245_ = lean_st_ref_take(v_a_6236_);
v_assignments_6246_ = lean_ctor_get(v___x_6244_, 0);
lean_inc_ref(v_assignments_6246_);
v_funVals_6247_ = lean_ctor_get(v___x_6244_, 1);
lean_inc_ref(v_funVals_6247_);
lean_dec(v___x_6244_);
v_env_6248_ = lean_ctor_get(v___x_6245_, 0);
v_nextMacroScope_6249_ = lean_ctor_get(v___x_6245_, 1);
v_ngen_6250_ = lean_ctor_get(v___x_6245_, 2);
v_auxDeclNGen_6251_ = lean_ctor_get(v___x_6245_, 3);
v_traceState_6252_ = lean_ctor_get(v___x_6245_, 4);
v_messages_6253_ = lean_ctor_get(v___x_6245_, 6);
v_infoState_6254_ = lean_ctor_get(v___x_6245_, 7);
v_snapshotTasks_6255_ = lean_ctor_get(v___x_6245_, 8);
v_isSharedCheck_6267_ = !lean_is_exclusive(v___x_6245_);
if (v_isSharedCheck_6267_ == 0)
{
lean_object* v_unused_6268_; 
v_unused_6268_ = lean_ctor_get(v___x_6245_, 5);
lean_dec(v_unused_6268_);
v___x_6257_ = v___x_6245_;
v_isShared_6258_ = v_isSharedCheck_6267_;
goto v_resetjp_6256_;
}
else
{
lean_inc(v_snapshotTasks_6255_);
lean_inc(v_infoState_6254_);
lean_inc(v_messages_6253_);
lean_inc(v_traceState_6252_);
lean_inc(v_auxDeclNGen_6251_);
lean_inc(v_ngen_6250_);
lean_inc(v_nextMacroScope_6249_);
lean_inc(v_env_6248_);
lean_dec(v___x_6245_);
v___x_6257_ = lean_box(0);
v_isShared_6258_ = v_isSharedCheck_6267_;
goto v_resetjp_6256_;
}
v_resetjp_6256_:
{
lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6262_; 
lean_inc(v___y_6241_);
v___x_6259_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6240_, v_funVals_6247_, v___y_6241_, v___y_6241_, v_env_6248_);
lean_dec_ref(v_funVals_6247_);
v___x_6260_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6258_ == 0)
{
lean_ctor_set(v___x_6257_, 5, v___x_6260_);
lean_ctor_set(v___x_6257_, 0, v___x_6259_);
v___x_6262_ = v___x_6257_;
goto v_reusejp_6261_;
}
else
{
lean_object* v_reuseFailAlloc_6266_; 
v_reuseFailAlloc_6266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6266_, 0, v___x_6259_);
lean_ctor_set(v_reuseFailAlloc_6266_, 1, v_nextMacroScope_6249_);
lean_ctor_set(v_reuseFailAlloc_6266_, 2, v_ngen_6250_);
lean_ctor_set(v_reuseFailAlloc_6266_, 3, v_auxDeclNGen_6251_);
lean_ctor_set(v_reuseFailAlloc_6266_, 4, v_traceState_6252_);
lean_ctor_set(v_reuseFailAlloc_6266_, 5, v___x_6260_);
lean_ctor_set(v_reuseFailAlloc_6266_, 6, v_messages_6253_);
lean_ctor_set(v_reuseFailAlloc_6266_, 7, v_infoState_6254_);
lean_ctor_set(v_reuseFailAlloc_6266_, 8, v_snapshotTasks_6255_);
v___x_6262_ = v_reuseFailAlloc_6266_;
goto v_reusejp_6261_;
}
v_reusejp_6261_:
{
lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; 
v___x_6263_ = lean_st_ref_set(v_a_6236_, v___x_6262_);
v___x_6264_ = lean_mk_empty_array_with_capacity(v___y_6241_);
v___x_6265_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6246_, v___y_6240_, v___y_6241_, v___x_6238_, v___x_6264_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_);
lean_dec_ref(v___y_6240_);
lean_dec_ref(v_assignments_6246_);
return v___x_6265_;
}
}
}
else
{
lean_object* v_a_6269_; lean_object* v___x_6271_; uint8_t v_isShared_6272_; uint8_t v_isSharedCheck_6276_; 
lean_dec(v___y_6242_);
lean_dec(v___y_6241_);
lean_dec_ref(v___y_6240_);
v_a_6269_ = lean_ctor_get(v___y_6243_, 0);
v_isSharedCheck_6276_ = !lean_is_exclusive(v___y_6243_);
if (v_isSharedCheck_6276_ == 0)
{
v___x_6271_ = v___y_6243_;
v_isShared_6272_ = v_isSharedCheck_6276_;
goto v_resetjp_6270_;
}
else
{
lean_inc(v_a_6269_);
lean_dec(v___y_6243_);
v___x_6271_ = lean_box(0);
v_isShared_6272_ = v_isSharedCheck_6276_;
goto v_resetjp_6270_;
}
v_resetjp_6270_:
{
lean_object* v___x_6274_; 
if (v_isShared_6272_ == 0)
{
v___x_6274_ = v___x_6271_;
goto v_reusejp_6273_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v_a_6269_);
v___x_6274_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6273_;
}
v_reusejp_6273_:
{
return v___x_6274_;
}
}
}
}
v___jp_6277_:
{
lean_object* v___x_6291_; double v___x_6292_; double v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v___x_6291_ = lean_io_get_num_heartbeats();
v___x_6292_ = lean_float_of_nat(v___y_6279_);
v___x_6293_ = lean_float_of_nat(v___x_6291_);
v___x_6294_ = lean_box_float(v___x_6292_);
v___x_6295_ = lean_box_float(v___x_6293_);
v___x_6296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6296_, 0, v___x_6294_);
lean_ctor_set(v___x_6296_, 1, v___x_6295_);
v___x_6297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6297_, 0, v_a_6290_);
lean_ctor_set(v___x_6297_, 1, v___x_6296_);
lean_inc_ref(v___y_6286_);
lean_inc(v___y_6285_);
v___x_6298_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6285_, v___y_6280_, v___y_6286_, v___y_6288_, v___y_6289_, v___y_6278_, v___y_6283_, v___x_6297_, v___y_6281_, v___y_6287_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_);
lean_dec_ref(v___y_6281_);
v___y_6240_ = v___y_6282_;
v___y_6241_ = v___y_6284_;
v___y_6242_ = v___y_6287_;
v___y_6243_ = v___x_6298_;
goto v___jp_6239_;
}
v___jp_6299_:
{
lean_object* v___x_6313_; double v___x_6314_; double v___x_6315_; double v___x_6316_; double v___x_6317_; double v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6313_ = lean_io_mono_nanos_now();
v___x_6314_ = lean_float_of_nat(v___y_6307_);
v___x_6315_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6316_ = lean_float_div(v___x_6314_, v___x_6315_);
v___x_6317_ = lean_float_of_nat(v___x_6313_);
v___x_6318_ = lean_float_div(v___x_6317_, v___x_6315_);
v___x_6319_ = lean_box_float(v___x_6316_);
v___x_6320_ = lean_box_float(v___x_6318_);
v___x_6321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6321_, 0, v___x_6319_);
lean_ctor_set(v___x_6321_, 1, v___x_6320_);
v___x_6322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6322_, 0, v_a_6312_);
lean_ctor_set(v___x_6322_, 1, v___x_6321_);
lean_inc_ref(v___y_6308_);
lean_inc(v___y_6306_);
v___x_6323_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6306_, v___y_6301_, v___y_6308_, v___y_6310_, v___y_6311_, v___y_6300_, v___y_6304_, v___x_6322_, v___y_6302_, v___y_6309_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_);
lean_dec_ref(v___y_6302_);
v___y_6240_ = v___y_6303_;
v___y_6241_ = v___y_6305_;
v___y_6242_ = v___y_6309_;
v___y_6243_ = v___x_6323_;
goto v___jp_6239_;
}
v___jp_6324_:
{
lean_object* v___x_6335_; lean_object* v_a_6336_; lean_object* v___x_6337_; uint8_t v___x_6338_; 
v___x_6335_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6236_);
v_a_6336_ = lean_ctor_get(v___x_6335_, 0);
lean_inc(v_a_6336_);
lean_dec_ref(v___x_6335_);
v___x_6337_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6338_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6333_, v___x_6337_);
if (v___x_6338_ == 0)
{
lean_object* v___x_6339_; lean_object* v___x_6340_; 
v___x_6339_ = lean_io_mono_nanos_now();
v___x_6340_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6238_, v___y_6326_, v___y_6332_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_);
if (lean_obj_tag(v___x_6340_) == 0)
{
lean_object* v_a_6341_; lean_object* v___x_6343_; uint8_t v_isShared_6344_; uint8_t v_isSharedCheck_6348_; 
v_a_6341_ = lean_ctor_get(v___x_6340_, 0);
v_isSharedCheck_6348_ = !lean_is_exclusive(v___x_6340_);
if (v_isSharedCheck_6348_ == 0)
{
v___x_6343_ = v___x_6340_;
v_isShared_6344_ = v_isSharedCheck_6348_;
goto v_resetjp_6342_;
}
else
{
lean_inc(v_a_6341_);
lean_dec(v___x_6340_);
v___x_6343_ = lean_box(0);
v_isShared_6344_ = v_isSharedCheck_6348_;
goto v_resetjp_6342_;
}
v_resetjp_6342_:
{
lean_object* v___x_6346_; 
if (v_isShared_6344_ == 0)
{
lean_ctor_set_tag(v___x_6343_, 1);
v___x_6346_ = v___x_6343_;
goto v_reusejp_6345_;
}
else
{
lean_object* v_reuseFailAlloc_6347_; 
v_reuseFailAlloc_6347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6347_, 0, v_a_6341_);
v___x_6346_ = v_reuseFailAlloc_6347_;
goto v_reusejp_6345_;
}
v_reusejp_6345_:
{
v___y_6300_ = v_a_6336_;
v___y_6301_ = v___y_6325_;
v___y_6302_ = v___y_6326_;
v___y_6303_ = v___y_6328_;
v___y_6304_ = v___y_6327_;
v___y_6305_ = v___y_6330_;
v___y_6306_ = v___y_6329_;
v___y_6307_ = v___x_6339_;
v___y_6308_ = v___y_6331_;
v___y_6309_ = v___y_6332_;
v___y_6310_ = v___y_6333_;
v___y_6311_ = v___y_6334_;
v_a_6312_ = v___x_6346_;
goto v___jp_6299_;
}
}
}
else
{
lean_object* v_a_6349_; lean_object* v___x_6351_; uint8_t v_isShared_6352_; uint8_t v_isSharedCheck_6356_; 
v_a_6349_ = lean_ctor_get(v___x_6340_, 0);
v_isSharedCheck_6356_ = !lean_is_exclusive(v___x_6340_);
if (v_isSharedCheck_6356_ == 0)
{
v___x_6351_ = v___x_6340_;
v_isShared_6352_ = v_isSharedCheck_6356_;
goto v_resetjp_6350_;
}
else
{
lean_inc(v_a_6349_);
lean_dec(v___x_6340_);
v___x_6351_ = lean_box(0);
v_isShared_6352_ = v_isSharedCheck_6356_;
goto v_resetjp_6350_;
}
v_resetjp_6350_:
{
lean_object* v___x_6354_; 
if (v_isShared_6352_ == 0)
{
lean_ctor_set_tag(v___x_6351_, 0);
v___x_6354_ = v___x_6351_;
goto v_reusejp_6353_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_a_6349_);
v___x_6354_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6353_;
}
v_reusejp_6353_:
{
v___y_6300_ = v_a_6336_;
v___y_6301_ = v___y_6325_;
v___y_6302_ = v___y_6326_;
v___y_6303_ = v___y_6328_;
v___y_6304_ = v___y_6327_;
v___y_6305_ = v___y_6330_;
v___y_6306_ = v___y_6329_;
v___y_6307_ = v___x_6339_;
v___y_6308_ = v___y_6331_;
v___y_6309_ = v___y_6332_;
v___y_6310_ = v___y_6333_;
v___y_6311_ = v___y_6334_;
v_a_6312_ = v___x_6354_;
goto v___jp_6299_;
}
}
}
}
else
{
lean_object* v___x_6357_; lean_object* v___x_6358_; 
v___x_6357_ = lean_io_get_num_heartbeats();
v___x_6358_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6238_, v___y_6326_, v___y_6332_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_);
if (lean_obj_tag(v___x_6358_) == 0)
{
lean_object* v_a_6359_; lean_object* v___x_6361_; uint8_t v_isShared_6362_; uint8_t v_isSharedCheck_6366_; 
v_a_6359_ = lean_ctor_get(v___x_6358_, 0);
v_isSharedCheck_6366_ = !lean_is_exclusive(v___x_6358_);
if (v_isSharedCheck_6366_ == 0)
{
v___x_6361_ = v___x_6358_;
v_isShared_6362_ = v_isSharedCheck_6366_;
goto v_resetjp_6360_;
}
else
{
lean_inc(v_a_6359_);
lean_dec(v___x_6358_);
v___x_6361_ = lean_box(0);
v_isShared_6362_ = v_isSharedCheck_6366_;
goto v_resetjp_6360_;
}
v_resetjp_6360_:
{
lean_object* v___x_6364_; 
if (v_isShared_6362_ == 0)
{
lean_ctor_set_tag(v___x_6361_, 1);
v___x_6364_ = v___x_6361_;
goto v_reusejp_6363_;
}
else
{
lean_object* v_reuseFailAlloc_6365_; 
v_reuseFailAlloc_6365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6365_, 0, v_a_6359_);
v___x_6364_ = v_reuseFailAlloc_6365_;
goto v_reusejp_6363_;
}
v_reusejp_6363_:
{
v___y_6278_ = v_a_6336_;
v___y_6279_ = v___x_6357_;
v___y_6280_ = v___y_6325_;
v___y_6281_ = v___y_6326_;
v___y_6282_ = v___y_6328_;
v___y_6283_ = v___y_6327_;
v___y_6284_ = v___y_6330_;
v___y_6285_ = v___y_6329_;
v___y_6286_ = v___y_6331_;
v___y_6287_ = v___y_6332_;
v___y_6288_ = v___y_6333_;
v___y_6289_ = v___y_6334_;
v_a_6290_ = v___x_6364_;
goto v___jp_6277_;
}
}
}
else
{
lean_object* v_a_6367_; lean_object* v___x_6369_; uint8_t v_isShared_6370_; uint8_t v_isSharedCheck_6374_; 
v_a_6367_ = lean_ctor_get(v___x_6358_, 0);
v_isSharedCheck_6374_ = !lean_is_exclusive(v___x_6358_);
if (v_isSharedCheck_6374_ == 0)
{
v___x_6369_ = v___x_6358_;
v_isShared_6370_ = v_isSharedCheck_6374_;
goto v_resetjp_6368_;
}
else
{
lean_inc(v_a_6367_);
lean_dec(v___x_6358_);
v___x_6369_ = lean_box(0);
v_isShared_6370_ = v_isSharedCheck_6374_;
goto v_resetjp_6368_;
}
v_resetjp_6368_:
{
lean_object* v___x_6372_; 
if (v_isShared_6370_ == 0)
{
lean_ctor_set_tag(v___x_6369_, 0);
v___x_6372_ = v___x_6369_;
goto v_reusejp_6371_;
}
else
{
lean_object* v_reuseFailAlloc_6373_; 
v_reuseFailAlloc_6373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_a_6367_);
v___x_6372_ = v_reuseFailAlloc_6373_;
goto v_reusejp_6371_;
}
v_reusejp_6371_:
{
v___y_6278_ = v_a_6336_;
v___y_6279_ = v___x_6357_;
v___y_6280_ = v___y_6325_;
v___y_6281_ = v___y_6326_;
v___y_6282_ = v___y_6328_;
v___y_6283_ = v___y_6327_;
v___y_6284_ = v___y_6330_;
v___y_6285_ = v___y_6329_;
v___y_6286_ = v___y_6331_;
v___y_6287_ = v___y_6332_;
v___y_6288_ = v___y_6333_;
v___y_6289_ = v___y_6334_;
v_a_6290_ = v___x_6372_;
goto v___jp_6277_;
}
}
}
}
}
v___jp_6375_:
{
size_t v_sz_6377_; size_t v___x_6378_; lean_object* v_assignments_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v_funVals_6382_; lean_object* v_state_6383_; lean_object* v___x_6384_; lean_object* v_options_6385_; lean_object* v_inheritedTraceOptions_6386_; uint8_t v_hasTrace_6387_; lean_object* v_ctx_6388_; 
v_sz_6377_ = lean_array_size(v___y_6376_);
v___x_6378_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6376_, 2);
v_assignments_6379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6377_, v___x_6378_, v___y_6376_);
v___x_6380_ = lean_array_get_size(v___y_6376_);
v___x_6381_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6382_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6376_, v___x_6380_, v___x_6380_, v___x_6381_);
v_state_6383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6383_, 0, v_assignments_6379_);
lean_ctor_set(v_state_6383_, 1, v_funVals_6382_);
v___x_6384_ = lean_st_mk_ref(v_state_6383_);
v_options_6385_ = lean_ctor_get(v_a_6235_, 2);
v_inheritedTraceOptions_6386_ = lean_ctor_get(v_a_6235_, 13);
v_hasTrace_6387_ = lean_ctor_get_uint8(v_options_6385_, sizeof(void*)*1);
v_ctx_6388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6388_, 0, v___y_6376_);
lean_ctor_set(v_ctx_6388_, 1, v___x_6238_);
if (v_hasTrace_6387_ == 0)
{
lean_object* v___x_6389_; 
v___x_6389_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6238_, v_ctx_6388_, v___x_6384_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_);
lean_dec_ref(v_ctx_6388_);
v___y_6240_ = v___y_6376_;
v___y_6241_ = v___x_6380_;
v___y_6242_ = v___x_6384_;
v___y_6243_ = v___x_6389_;
goto v___jp_6239_;
}
else
{
lean_object* v___f_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; uint8_t v___x_6394_; 
lean_inc_ref(v___y_6376_);
v___f_6390_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6390_, 0, v___y_6376_);
v___x_6391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6392_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6393_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6394_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6386_, v_options_6385_, v___x_6393_);
if (v___x_6394_ == 0)
{
lean_object* v___x_6395_; uint8_t v___x_6396_; 
v___x_6395_ = l_Lean_trace_profiler;
v___x_6396_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6385_, v___x_6395_);
if (v___x_6396_ == 0)
{
lean_object* v___x_6397_; 
lean_dec_ref(v___f_6390_);
v___x_6397_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6238_, v_ctx_6388_, v___x_6384_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_);
lean_dec_ref(v_ctx_6388_);
v___y_6240_ = v___y_6376_;
v___y_6241_ = v___x_6380_;
v___y_6242_ = v___x_6384_;
v___y_6243_ = v___x_6397_;
goto v___jp_6239_;
}
else
{
v___y_6325_ = v_hasTrace_6387_;
v___y_6326_ = v_ctx_6388_;
v___y_6327_ = v___f_6390_;
v___y_6328_ = v___y_6376_;
v___y_6329_ = v___x_6391_;
v___y_6330_ = v___x_6380_;
v___y_6331_ = v___x_6392_;
v___y_6332_ = v___x_6384_;
v___y_6333_ = v_options_6385_;
v___y_6334_ = v___x_6394_;
goto v___jp_6324_;
}
}
else
{
v___y_6325_ = v_hasTrace_6387_;
v___y_6326_ = v_ctx_6388_;
v___y_6327_ = v___f_6390_;
v___y_6328_ = v___y_6376_;
v___y_6329_ = v___x_6391_;
v___y_6330_ = v___x_6380_;
v___y_6331_ = v___x_6392_;
v___y_6332_ = v___x_6384_;
v___y_6333_ = v_options_6385_;
v___y_6334_ = v___x_6394_;
goto v___jp_6324_;
}
}
}
v___jp_6398_:
{
lean_object* v___x_6401_; 
v___x_6401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_decls_6232_, v___y_6399_, v___y_6400_);
lean_dec(v___y_6400_);
v___y_6376_ = v___x_6401_;
goto v___jp_6375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6410_, lean_object* v_a_6411_, lean_object* v_a_6412_, lean_object* v_a_6413_, lean_object* v_a_6414_, lean_object* v_a_6415_){
_start:
{
lean_object* v_res_6416_; 
v_res_6416_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6410_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
lean_dec(v_a_6414_);
lean_dec_ref(v_a_6413_);
lean_dec(v_a_6412_);
lean_dec_ref(v_a_6411_);
return v_res_6416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6417_, lean_object* v_n_6418_, lean_object* v_j_6419_, lean_object* v_a_6420_, lean_object* v_a_6421_){
_start:
{
lean_object* v___x_6422_; 
v___x_6422_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6417_, v_n_6418_, v_j_6419_, v_a_6421_);
return v___x_6422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6423_, lean_object* v_n_6424_, lean_object* v_j_6425_, lean_object* v_a_6426_, lean_object* v_a_6427_){
_start:
{
lean_object* v_res_6428_; 
v_res_6428_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6423_, v_n_6424_, v_j_6425_, v_a_6426_, v_a_6427_);
lean_dec(v_n_6424_);
lean_dec_ref(v___y_6423_);
return v_res_6428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6429_, lean_object* v___x_6430_, lean_object* v_n_6431_, lean_object* v_j_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_){
_start:
{
lean_object* v___x_6435_; 
v___x_6435_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6429_, v___x_6430_, v_n_6431_, v_j_6432_, v_a_6434_);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6436_, lean_object* v___x_6437_, lean_object* v_n_6438_, lean_object* v_j_6439_, lean_object* v_a_6440_, lean_object* v_a_6441_){
_start:
{
lean_object* v_res_6442_; 
v_res_6442_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6436_, v___x_6437_, v_n_6438_, v_j_6439_, v_a_6440_, v_a_6441_);
lean_dec(v_n_6438_);
lean_dec_ref(v___x_6437_);
lean_dec_ref(v___y_6436_);
return v_res_6442_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6443_, lean_object* v_as_6444_, lean_object* v_i_6445_, lean_object* v_j_6446_, lean_object* v_inv_6447_, lean_object* v_bs_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_){
_start:
{
lean_object* v___x_6454_; 
v___x_6454_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6443_, v_as_6444_, v_i_6445_, v_j_6446_, v_bs_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_);
return v___x_6454_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6455_, lean_object* v_as_6456_, lean_object* v_i_6457_, lean_object* v_j_6458_, lean_object* v_inv_6459_, lean_object* v_bs_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_){
_start:
{
lean_object* v_res_6466_; 
v_res_6466_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6455_, v_as_6456_, v_i_6457_, v_j_6458_, v_inv_6459_, v_bs_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_);
lean_dec(v___y_6464_);
lean_dec_ref(v___y_6463_);
lean_dec(v___y_6462_);
lean_dec_ref(v___y_6461_);
lean_dec_ref(v_as_6456_);
lean_dec_ref(v___x_6455_);
return v_res_6466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6467_, lean_object* v_as_6468_, lean_object* v_lo_6469_, lean_object* v_hi_6470_, lean_object* v_w_6471_, lean_object* v_hlo_6472_, lean_object* v_hhi_6473_){
_start:
{
lean_object* v___x_6474_; 
v___x_6474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_as_6468_, v_lo_6469_, v_hi_6470_);
return v___x_6474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6475_, lean_object* v_as_6476_, lean_object* v_lo_6477_, lean_object* v_hi_6478_, lean_object* v_w_6479_, lean_object* v_hlo_6480_, lean_object* v_hhi_6481_){
_start:
{
lean_object* v_res_6482_; 
v_res_6482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6475_, v_as_6476_, v_lo_6477_, v_hi_6478_, v_w_6479_, v_hlo_6480_, v_hhi_6481_);
lean_dec(v_hi_6478_);
lean_dec(v_n_6475_);
return v_res_6482_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6542_ = lean_unsigned_to_nat(3955956072u);
v___x_6543_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6544_ = l_Lean_Name_num___override(v___x_6543_, v___x_6542_);
return v___x_6544_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; 
v___x_6546_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6547_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6548_ = l_Lean_Name_str___override(v___x_6547_, v___x_6546_);
return v___x_6548_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; 
v___x_6550_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6551_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6552_ = l_Lean_Name_str___override(v___x_6551_, v___x_6550_);
return v___x_6552_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; 
v___x_6553_ = lean_unsigned_to_nat(2u);
v___x_6554_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6555_ = l_Lean_Name_num___override(v___x_6554_, v___x_6553_);
return v___x_6555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6557_; uint8_t v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; 
v___x_6557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6558_ = 1;
v___x_6559_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6560_ = l_Lean_registerTraceClass(v___x_6557_, v___x_6558_, v___x_6559_);
return v___x_6560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6561_){
_start:
{
lean_object* v_res_6562_; 
v_res_6562_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6562_;
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
res = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
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
