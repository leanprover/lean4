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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Prod_lexLtDec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "_private.Lean.Compiler.LCNF.ElimDeadBranches.0.Lean.Compiler.LCNF.UnreachableBranches.Value.merge.cleanup"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1;
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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_8_, 2);
v___x_12_ = lean_apply_2(v_k_9_, v_i_10_, v_vs_11_);
return v___x_12_;
}
case 3:
{
lean_object* v_vs_13_; lean_object* v___x_14_; 
v_vs_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_vs_13_);
lean_dec_ref_known(v_t_8_, 1);
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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(lean_object* v_xs_62_, lean_object* v_ys_63_, lean_object* v_x_64_){
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
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
switch(lean_obj_tag(v_x_73_))
{
case 0:
{
if (lean_obj_tag(v_x_74_) == 0)
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
case 1:
{
if (lean_obj_tag(v_x_74_) == 1)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
case 2:
{
if (lean_obj_tag(v_x_74_) == 2)
{
lean_object* v_i_79_; lean_object* v_vs_80_; lean_object* v_i_81_; lean_object* v_vs_82_; uint8_t v___x_83_; 
v_i_79_ = lean_ctor_get(v_x_73_, 0);
v_vs_80_ = lean_ctor_get(v_x_73_, 1);
v_i_81_ = lean_ctor_get(v_x_74_, 0);
v_vs_82_ = lean_ctor_get(v_x_74_, 1);
v___x_83_ = lean_name_eq(v_i_79_, v_i_81_);
if (v___x_83_ == 0)
{
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_array_get_size(v_vs_80_);
v___x_85_ = lean_array_get_size(v_vs_82_);
v___x_86_ = lean_nat_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(v_vs_80_, v_vs_82_, v___x_84_);
return v___x_87_;
}
}
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
default: 
{
if (lean_obj_tag(v_x_74_) == 3)
{
lean_object* v_vs_89_; lean_object* v_vs_90_; uint8_t v___x_91_; 
v_vs_89_ = lean_ctor_get(v_x_73_, 0);
v_vs_90_ = lean_ctor_get(v_x_74_, 0);
v___x_91_ = l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(v_vs_90_, v_vs_89_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(v_vs_89_, v_vs_90_);
return v___x_92_;
}
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(lean_object* v_a_94_, lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
else
{
lean_object* v_head_97_; lean_object* v_tail_98_; uint8_t v___x_99_; 
v_head_97_ = lean_ctor_get(v_x_95_, 0);
v_tail_98_ = lean_ctor_get(v_x_95_, 1);
v___x_99_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_94_, v_head_97_);
if (v___x_99_ == 0)
{
v_x_95_ = v_tail_98_;
goto _start;
}
else
{
return v___x_99_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(lean_object* v_bs_101_, lean_object* v_x_102_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
else
{
lean_object* v_head_104_; lean_object* v_tail_105_; uint8_t v___x_106_; 
v_head_104_ = lean_ctor_get(v_x_102_, 0);
v_tail_105_ = lean_ctor_get(v_x_102_, 1);
v___x_106_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(v_head_104_, v_bs_101_);
if (v___x_106_ == 0)
{
return v___x_106_;
}
else
{
v_x_102_ = v_tail_105_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1___boxed(lean_object* v_bs_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(v_bs_108_, v_x_109_);
lean_dec(v_x_109_);
lean_dec(v_bs_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___boxed(lean_object* v_a_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(v_a_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec(v_a_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg___boxed(lean_object* v_xs_116_, lean_object* v_ys_117_, lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(v_xs_116_, v_ys_117_, v_x_118_);
lean_dec_ref(v_ys_117_);
lean_dec_ref(v_xs_116_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___boxed(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_x_121_, v_x_122_);
lean_dec(v_x_122_);
lean_dec(v_x_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2(lean_object* v_xs_125_, lean_object* v_ys_126_, lean_object* v_hsz_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(v_xs_125_, v_ys_126_, v_x_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___boxed(lean_object* v_xs_131_, lean_object* v_ys_132_, lean_object* v_hsz_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2(v_xs_131_, v_ys_132_, v_hsz_133_, v_x_134_, v_x_135_);
lean_dec_ref(v_ys_132_);
lean_dec_ref(v_xs_131_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__1(lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_nat_to_int(v_a_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3_spec__3(lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_dec(v_x_142_);
return v_x_143_;
}
else
{
lean_object* v_head_145_; lean_object* v_tail_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_155_; 
v_head_145_ = lean_ctor_get(v_x_144_, 0);
v_tail_146_ = lean_ctor_get(v_x_144_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_155_ == 0)
{
v___x_148_ = v_x_144_;
v_isShared_149_ = v_isSharedCheck_155_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_tail_146_);
lean_inc(v_head_145_);
lean_dec(v_x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_155_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
lean_inc(v_x_142_);
if (v_isShared_149_ == 0)
{
lean_ctor_set_tag(v___x_148_, 5);
lean_ctor_set(v___x_148_, 1, v_x_142_);
lean_ctor_set(v___x_148_, 0, v_x_143_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_x_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_x_142_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_head_145_);
v_x_143_ = v___x_152_;
v_x_144_ = v_tail_146_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v___x_158_; 
lean_dec(v_x_157_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v_tail_159_; 
v_tail_159_ = lean_ctor_get(v_x_156_, 1);
if (lean_obj_tag(v_tail_159_) == 0)
{
lean_object* v_head_160_; 
lean_dec(v_x_157_);
v_head_160_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_head_160_);
lean_dec_ref_known(v_x_156_, 2);
return v_head_160_;
}
else
{
lean_object* v_head_161_; lean_object* v___x_162_; 
lean_inc(v_tail_159_);
v_head_161_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_head_161_);
lean_dec_ref_known(v_x_156_, 2);
v___x_162_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3_spec__3(v_x_157_, v_head_161_, v_tail_159_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0(lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
if (lean_obj_tag(v_a_172_) == 0)
{
lean_object* v___x_174_; 
v___x_174_ = l_List_reverse___redArg(v_a_173_);
return v___x_174_;
}
else
{
lean_object* v_head_175_; lean_object* v_tail_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_187_; 
v_head_175_ = lean_ctor_get(v_a_172_, 0);
v_tail_176_ = lean_ctor_get(v_a_172_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_172_);
if (v_isSharedCheck_187_ == 0)
{
v___x_178_ = v_a_172_;
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_tail_176_);
lean_inc(v_head_175_);
lean_dec(v_a_172_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_180_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__1));
v___x_181_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_175_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_a_173_);
lean_ctor_set(v___x_178_, 0, v___x_182_);
v___x_184_ = v___x_178_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_a_173_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
v_a_172_ = v_tail_176_;
v_a_173_ = v___x_184_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__4));
v___x_190_ = lean_string_length(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6);
v___x_192_ = lean_nat_to_int(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(lean_object* v_x_201_){
_start:
{
switch(lean_obj_tag(v_x_201_))
{
case 0:
{
lean_object* v___x_202_; 
v___x_202_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__1));
return v___x_202_;
}
case 1:
{
lean_object* v___x_203_; 
v___x_203_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__3));
return v___x_203_;
}
case 2:
{
lean_object* v_i_204_; lean_object* v_vs_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_232_; 
v_i_204_ = lean_ctor_get(v_x_201_, 0);
v_vs_205_ = lean_ctor_get(v_x_201_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_232_ == 0)
{
v___x_207_ = v_x_201_;
v_isShared_208_ = v_isSharedCheck_232_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_vs_205_);
lean_inc(v_i_204_);
lean_dec(v_x_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_232_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_array_get_size(v_vs_205_);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_nat_dec_eq(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_212_ = 1;
v___x_213_ = l_Lean_Name_toString(v_i_204_, v___x_212_);
v___x_214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___x_215_ = lean_array_to_list(v_vs_205_);
v___x_216_ = lean_box(0);
v___x_217_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0(v___x_215_, v___x_216_);
v___x_218_ = l_Std_Format_join(v___x_217_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 5);
lean_ctor_set(v___x_207_, 1, v___x_218_);
lean_ctor_set(v___x_207_, 0, v___x_214_);
v___x_220_ = v___x_207_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_229_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; 
v___x_221_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_222_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_220_);
v___x_224_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_221_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = 0;
v___x_228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_227_);
return v___x_228_;
}
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_del_object(v___x_207_);
lean_dec_ref(v_vs_205_);
v___x_230_ = l_Lean_Name_toString(v_i_204_, v___x_211_);
v___x_231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
default: 
{
lean_object* v_vs_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; 
v_vs_233_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_vs_233_);
lean_dec_ref_known(v_x_201_, 1);
v___x_234_ = lean_box(0);
v___x_235_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__2(v_vs_233_, v___x_234_);
v___x_236_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__11));
v___x_237_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_235_, v___x_236_);
v___x_238_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_239_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_237_);
v___x_241_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_238_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = 0;
v___x_245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_244_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__2(lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
if (lean_obj_tag(v_a_246_) == 0)
{
lean_object* v___x_248_; 
v___x_248_ = l_List_reverse___redArg(v_a_247_);
return v___x_248_;
}
else
{
lean_object* v_head_249_; lean_object* v_tail_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_259_; 
v_head_249_ = lean_ctor_get(v_a_246_, 0);
v_tail_250_ = lean_ctor_get(v_a_246_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_a_246_);
if (v_isSharedCheck_259_ == 0)
{
v___x_252_ = v_a_246_;
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_tail_250_);
lean_inc(v_head_249_);
lean_dec(v_a_246_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_249_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_a_247_);
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_a_247_);
v___x_256_ = v_reuseFailAlloc_258_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
v_a_246_ = v_tail_250_;
v_a_247_ = v___x_256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0(lean_object* v_v_260_, lean_object* v_x_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0___boxed(lean_object* v_v_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0(v_v_263_, v_x_264_);
lean_dec(v_x_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(lean_object* v_msg_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___f_276_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_277_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_278_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_279_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_280_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_281_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_282_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___f_276_);
lean_ctor_set(v___x_283_, 1, v___f_277_);
v___x_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___f_278_);
lean_ctor_set(v___x_284_, 2, v___f_279_);
lean_ctor_set(v___x_284_, 3, v___f_280_);
lean_ctor_set(v___x_284_, 4, v___f_281_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___f_282_);
v___x_286_ = l_Lean_instInhabitedInductiveVal_default;
v___x_287_ = l_instInhabitedOfMonad___redArg(v___x_285_, v___x_286_);
v___x_288_ = lean_panic_fn_borrowed(v___x_287_, v_msg_275_);
lean_dec(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_292_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_293_ = lean_unsigned_to_nat(51u);
v___x_294_ = lean_unsigned_to_nat(72u);
v___x_295_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1));
v___x_296_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_297_ = l_mkPanicMessageWithDecl(v___x_296_, v___x_295_, v___x_294_, v___x_293_, v___x_292_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_298_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_299_ = lean_unsigned_to_nat(56u);
v___x_300_ = lean_unsigned_to_nat(73u);
v___x_301_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1));
v___x_302_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_303_ = l_mkPanicMessageWithDecl(v___x_302_, v___x_301_, v___x_300_, v___x_299_, v___x_298_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(lean_object* v_ctorName_304_, lean_object* v_env_305_){
_start:
{
uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_312_ = 0;
lean_inc_ref(v_env_305_);
v___x_313_ = l_Lean_Environment_find_x3f(v_env_305_, v_ctorName_304_, v___x_312_);
if (lean_obj_tag(v___x_313_) == 1)
{
lean_object* v_val_314_; 
v_val_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_314_);
lean_dec_ref_known(v___x_313_, 1);
if (lean_obj_tag(v_val_314_) == 6)
{
lean_object* v_val_315_; lean_object* v_induct_316_; lean_object* v___x_317_; 
v_val_315_ = lean_ctor_get(v_val_314_, 0);
lean_inc_ref(v_val_315_);
lean_dec_ref_known(v_val_314_, 1);
v_induct_316_ = lean_ctor_get(v_val_315_, 1);
lean_inc(v_induct_316_);
lean_dec_ref(v_val_315_);
v___x_317_ = l_Lean_Environment_find_x3f(v_env_305_, v_induct_316_, v___x_312_);
if (lean_obj_tag(v___x_317_) == 1)
{
lean_object* v_val_318_; 
v_val_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___x_317_, 1);
if (lean_obj_tag(v_val_318_) == 5)
{
lean_object* v_val_319_; 
v_val_319_ = lean_ctor_get(v_val_318_, 0);
lean_inc_ref(v_val_319_);
lean_dec_ref_known(v_val_318_, 1);
return v_val_319_;
}
else
{
lean_dec(v_val_318_);
goto v___jp_309_;
}
}
else
{
lean_dec(v___x_317_);
goto v___jp_309_;
}
}
else
{
lean_dec(v_val_314_);
lean_dec_ref(v_env_305_);
goto v___jp_306_;
}
}
else
{
lean_dec(v___x_313_);
lean_dec_ref(v_env_305_);
goto v___jp_306_;
}
v___jp_306_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3);
v___x_308_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(v___x_307_);
return v___x_308_;
}
v___jp_309_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4);
v___x_311_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(lean_object* v_ctorName_320_, lean_object* v_env_321_, lean_object* v_n_322_){
_start:
{
lean_object* v_induct_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_induct_323_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_ctorName_320_, v_env_321_);
v___x_324_ = l_Lean_InductiveVal_numCtors(v_induct_323_);
lean_dec_ref(v_induct_323_);
v___x_325_ = lean_nat_dec_eq(v_n_322_, v___x_324_);
lean_dec(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___boxed(lean_object* v_ctorName_326_, lean_object* v_env_327_, lean_object* v_n_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_ctorName_326_, v_env_327_, v_n_328_);
lean_dec(v_n_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(uint8_t v___x_331_, lean_object* v_v_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_box(1);
v___x_334_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_v_332_, v___x_333_);
if (v___x_334_ == 0)
{
return v___x_331_;
}
else
{
uint8_t v___x_335_; 
v___x_335_ = 0;
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed(lean_object* v___x_336_, lean_object* v_v_337_){
_start:
{
uint8_t v___x_150__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v___x_150__boxed_338_ = lean_unbox(v___x_336_);
v_res_339_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(v___x_150__boxed_338_, v_v_337_);
lean_dec(v_v_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(lean_object* v_value_341_){
_start:
{
if (lean_obj_tag(v_value_341_) == 2)
{
lean_object* v_vs_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_369_; 
v_vs_342_ = lean_ctor_get(v_value_341_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_value_341_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v_value_341_, 0);
lean_dec(v_unused_370_);
v___x_344_ = v_value_341_;
v_isShared_345_ = v_isSharedCheck_369_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_vs_342_);
lean_dec(v_value_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_369_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___f_353_; lean_object* v___f_354_; lean_object* v___x_356_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_array_get_size(v_vs_342_);
v___f_348_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_349_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_350_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_351_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_352_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_353_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_354_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 0);
lean_ctor_set(v___x_344_, 1, v___f_349_);
lean_ctor_set(v___x_344_, 0, v___f_348_);
v___x_356_ = v___x_344_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___f_348_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___f_349_);
v___x_356_ = v_reuseFailAlloc_368_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___f_350_);
lean_ctor_set(v___x_357_, 2, v___f_351_);
lean_ctor_set(v___x_357_, 3, v___f_352_);
lean_ctor_set(v___x_357_, 4, v___f_353_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___f_354_);
v___x_359_ = lean_nat_dec_lt(v___x_346_, v___x_347_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
lean_dec_ref_known(v___x_358_, 2);
lean_dec_ref(v_vs_342_);
v___x_360_ = 1;
return v___x_360_;
}
else
{
if (v___x_359_ == 0)
{
lean_dec_ref_known(v___x_358_, 2);
lean_dec_ref(v_vs_342_);
return v___x_359_;
}
else
{
lean_object* v___x_361_; lean_object* v___f_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_361_ = lean_box(v___x_359_);
v___f_362_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed), 2, 1);
lean_closure_set(v___f_362_, 0, v___x_361_);
v___x_363_ = ((size_t)0ULL);
v___x_364_ = lean_usize_of_nat(v___x_347_);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_358_, v___f_362_, v_vs_342_, v___x_363_, v___x_364_);
v___x_366_ = lean_unbox(v___x_365_);
lean_dec(v___x_365_);
if (v___x_366_ == 0)
{
return v___x_359_;
}
else
{
uint8_t v___x_367_; 
v___x_367_ = 0;
return v___x_367_;
}
}
}
}
}
}
else
{
uint8_t v___x_371_; 
lean_dec(v_value_341_);
v___x_371_ = 0;
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___boxed(lean_object* v_value_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(v_value_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(lean_object* v_msg_375_){
_start:
{
lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_379_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_380_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_381_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_382_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___f_376_);
lean_ctor_set(v___x_383_, 1, v___f_377_);
v___x_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___f_378_);
lean_ctor_set(v___x_384_, 2, v___f_379_);
lean_ctor_set(v___x_384_, 3, v___f_380_);
lean_ctor_set(v___x_384_, 4, v___f_381_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___f_382_);
v___x_386_ = lean_box(0);
v___x_387_ = l_instInhabitedOfMonad___redArg(v___x_385_, v___x_386_);
v___x_388_ = lean_panic_fn_borrowed(v___x_387_, v_msg_375_);
lean_dec(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(lean_object* v_as_389_, size_t v_i_390_, size_t v_stop_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_eq(v_i_390_, v_stop_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_array_uget_borrowed(v_as_389_, v_i_390_);
v___x_394_ = lean_box(1);
v___x_395_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
uint8_t v___x_396_; 
v___x_396_ = 1;
return v___x_396_;
}
else
{
size_t v___x_397_; size_t v___x_398_; 
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_390_, v___x_397_);
v_i_390_ = v___x_398_;
goto _start;
}
}
else
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0___boxed(lean_object* v_as_401_, lean_object* v_i_402_, lean_object* v_stop_403_){
_start:
{
size_t v_i_boxed_404_; size_t v_stop_boxed_405_; uint8_t v_res_406_; lean_object* v_r_407_; 
v_i_boxed_404_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_stop_boxed_405_ = lean_unbox_usize(v_stop_403_);
lean_dec(v_stop_403_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_as_401_, v_i_boxed_404_, v_stop_boxed_405_);
lean_dec_ref(v_as_401_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(lean_object* v_x_408_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
uint8_t v___x_409_; 
v___x_409_ = 1;
return v___x_409_;
}
else
{
lean_object* v_head_410_; 
v_head_410_ = lean_ctor_get(v_x_408_, 0);
if (lean_obj_tag(v_head_410_) == 2)
{
lean_object* v_tail_411_; lean_object* v_vs_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_tail_411_ = lean_ctor_get(v_x_408_, 1);
v_vs_412_ = lean_ctor_get(v_head_410_, 1);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_array_get_size(v_vs_412_);
v___x_415_ = lean_nat_dec_lt(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
v_x_408_ = v_tail_411_;
goto _start;
}
else
{
if (v___x_415_ == 0)
{
v_x_408_ = v_tail_411_;
goto _start;
}
else
{
size_t v___x_418_; size_t v___x_419_; uint8_t v___x_420_; 
v___x_418_ = ((size_t)0ULL);
v___x_419_ = lean_usize_of_nat(v___x_414_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_412_, v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
v_x_408_ = v_tail_411_;
goto _start;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
}
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1___boxed(lean_object* v_x_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_x_424_);
lean_dec(v_x_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_428_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_429_ = lean_unsigned_to_nat(42u);
v___x_430_ = lean_unsigned_to_nat(122u);
v___x_431_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0));
v___x_432_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_433_ = l_mkPanicMessageWithDecl(v___x_432_, v___x_431_, v___x_430_, v___x_429_, v___x_428_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(lean_object* v_env_434_, lean_object* v_vs_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_vs_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
lean_dec_ref(v_env_434_);
v___x_437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_437_, 0, v_vs_435_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
v___x_439_ = l_List_head_x21___redArg(v___x_438_, v_vs_435_);
if (lean_obj_tag(v___x_439_) == 2)
{
lean_object* v_i_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_i_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_i_440_);
lean_dec_ref_known(v___x_439_, 2);
v___x_441_ = l_List_lengthTR___redArg(v_vs_435_);
v___x_442_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_i_440_, v_env_434_, v___x_441_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_443_, 0, v_vs_435_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
lean_dec(v_vs_435_);
v___x_444_ = lean_box(1);
return v___x_444_;
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v___x_439_);
lean_dec(v_vs_435_);
lean_dec_ref(v_env_434_);
v___x_445_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1);
v___x_446_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(lean_object* v_msg_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_panic_fn_borrowed(v___x_448_, v_msg_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
lean_dec(v_x_450_);
return v_x_451_;
}
else
{
lean_object* v_head_453_; lean_object* v_tail_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_464_; 
v_head_453_ = lean_ctor_get(v_x_452_, 0);
v_tail_454_ = lean_ctor_get(v_x_452_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_464_ == 0)
{
v___x_456_ = v_x_452_;
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_tail_454_);
lean_inc(v_head_453_);
lean_dec(v_x_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
lean_inc(v_x_450_);
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 5);
lean_ctor_set(v___x_456_, 1, v_x_450_);
lean_ctor_set(v___x_456_, 0, v_x_451_);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_x_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_x_450_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_453_);
v___x_461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v_x_451_ = v___x_461_;
v_x_452_ = v_tail_454_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v___x_467_; 
lean_dec(v_x_466_);
v___x_467_ = lean_box(0);
return v___x_467_;
}
else
{
lean_object* v_tail_468_; 
v_tail_468_ = lean_ctor_get(v_x_465_, 1);
if (lean_obj_tag(v_tail_468_) == 0)
{
lean_object* v_head_469_; lean_object* v___x_470_; 
lean_dec(v_x_466_);
v_head_469_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_head_469_);
lean_dec_ref_known(v_x_465_, 2);
v___x_470_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_469_);
return v___x_470_;
}
else
{
lean_object* v_head_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_inc(v_tail_468_);
v_head_471_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_head_471_);
lean_dec_ref_known(v_x_465_, 2);
v___x_472_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_471_);
v___x_473_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(v_x_466_, v___x_472_, v_tail_468_);
return v___x_473_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2));
v___x_486_ = lean_string_length(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7);
v___x_488_ = lean_nat_to_int(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(lean_object* v_a_493_){
_start:
{
if (lean_obj_tag(v_a_493_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1));
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; 
v___x_495_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_496_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(v_a_493_, v___x_495_);
v___x_497_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8);
v___x_498_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9));
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_496_);
v___x_500_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_497_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = 0;
v___x_504_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*1, v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(lean_object* v_env_510_, lean_object* v_v1_511_, lean_object* v_v2_512_){
_start:
{
lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_520_; lean_object* v_i_521_; lean_object* v_vs_522_; 
switch(lean_obj_tag(v_v1_511_))
{
case 0:
{
switch(lean_obj_tag(v_v2_512_))
{
case 2:
{
lean_object* v_i_529_; lean_object* v_vs_530_; 
v_i_529_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_i_529_);
v_vs_530_ = lean_ctor_get(v_v2_512_, 1);
lean_inc_ref(v_vs_530_);
v___y_520_ = v_v2_512_;
v_i_521_ = v_i_529_;
v_vs_522_ = v_vs_530_;
goto v___jp_519_;
}
case 3:
{
lean_object* v_vs_531_; lean_object* v___x_532_; 
v_vs_531_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_vs_531_);
lean_dec_ref_known(v_v2_512_, 1);
v___x_532_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v_vs_531_);
return v___x_532_;
}
default: 
{
lean_dec_ref(v_env_510_);
return v_v2_512_;
}
}
}
case 1:
{
lean_dec_ref(v_env_510_);
switch(lean_obj_tag(v_v2_512_))
{
case 0:
{
return v_v1_511_;
}
case 1:
{
return v_v2_512_;
}
case 3:
{
lean_dec_ref_known(v_v2_512_, 1);
return v_v1_511_;
}
default: 
{
lean_dec(v_v2_512_);
return v_v1_511_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_v2_512_))
{
case 0:
{
lean_object* v_i_533_; lean_object* v_vs_534_; 
v_i_533_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_i_533_);
v_vs_534_ = lean_ctor_get(v_v1_511_, 1);
lean_inc_ref(v_vs_534_);
v___y_520_ = v_v1_511_;
v_i_521_ = v_i_533_;
v_vs_522_ = v_vs_534_;
goto v___jp_519_;
}
case 1:
{
lean_dec_ref_known(v_v1_511_, 2);
lean_dec_ref(v_env_510_);
return v_v2_512_;
}
case 2:
{
lean_object* v_i_535_; lean_object* v_vs_536_; lean_object* v_i_537_; lean_object* v_vs_538_; uint8_t v___x_539_; 
v_i_535_ = lean_ctor_get(v_v1_511_, 0);
v_vs_536_ = lean_ctor_get(v_v1_511_, 1);
v_i_537_ = lean_ctor_get(v_v2_512_, 0);
v_vs_538_ = lean_ctor_get(v_v2_512_, 1);
v___x_539_ = lean_name_eq(v_i_535_, v_i_537_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_540_ = lean_box(0);
v___x_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_541_, 0, v_v2_512_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v_v1_511_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_542_);
return v___x_543_;
}
else
{
lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_553_; 
lean_inc_ref(v_vs_538_);
lean_inc_ref(v_vs_536_);
lean_inc(v_i_535_);
lean_dec_ref_known(v_v1_511_, 2);
v_isSharedCheck_553_ = !lean_is_exclusive(v_v2_512_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; lean_object* v_unused_555_; 
v_unused_554_ = lean_ctor_get(v_v2_512_, 1);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_v2_512_, 0);
lean_dec(v_unused_555_);
v___x_545_ = v_v2_512_;
v_isShared_546_ = v_isSharedCheck_553_;
goto v_resetjp_544_;
}
else
{
lean_dec(v_v2_512_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_553_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
lean_inc_ref(v_env_510_);
v___x_549_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_510_, v_vs_536_, v_vs_538_, v___x_547_, v___x_548_);
lean_dec_ref(v_vs_538_);
lean_dec_ref(v_vs_536_);
lean_inc_ref(v___x_549_);
lean_inc(v_i_535_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_549_);
lean_ctor_set(v___x_545_, 0, v_i_535_);
v___x_551_ = v___x_545_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_i_535_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v___y_520_ = v___x_551_;
v_i_521_ = v_i_535_;
v_vs_522_ = v___x_549_;
goto v___jp_519_;
}
}
}
}
default: 
{
lean_object* v_vs_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_vs_556_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_vs_556_);
lean_dec_ref_known(v_v2_512_, 1);
lean_inc_ref(v_env_510_);
v___x_557_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_510_, v_vs_556_, v_v1_511_);
v___x_558_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_557_);
return v___x_558_;
}
}
}
default: 
{
switch(lean_obj_tag(v_v2_512_))
{
case 0:
{
lean_object* v_vs_559_; lean_object* v___x_560_; 
v_vs_559_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_vs_559_);
lean_dec_ref_known(v_v1_511_, 1);
v___x_560_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v_vs_559_);
return v___x_560_;
}
case 1:
{
lean_dec_ref_known(v_v1_511_, 1);
lean_dec_ref(v_env_510_);
return v_v2_512_;
}
case 3:
{
lean_object* v_vs_561_; lean_object* v_vs_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_vs_561_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_vs_561_);
lean_dec_ref_known(v_v1_511_, 1);
v_vs_562_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_vs_562_);
lean_dec_ref_known(v_v2_512_, 1);
lean_inc_ref(v_env_510_);
v___x_563_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(v_env_510_, v_vs_562_, v_vs_561_);
v___x_564_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_563_);
return v___x_564_;
}
default: 
{
lean_object* v_vs_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_vs_565_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_vs_565_);
lean_dec_ref_known(v_v1_511_, 1);
lean_inc_ref(v_env_510_);
v___x_566_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_510_, v_vs_565_, v_v2_512_);
v___x_567_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_566_);
return v___x_567_;
}
}
}
}
v___jp_513_:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v___y_514_, v_env_510_, v___x_516_);
if (v___x_517_ == 0)
{
return v___y_515_;
}
else
{
lean_object* v___x_518_; 
lean_dec(v___y_515_);
v___x_518_ = lean_box(1);
return v___x_518_;
}
}
v___jp_519_:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_array_get_size(v_vs_522_);
v___x_525_ = lean_nat_dec_lt(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec_ref(v_vs_522_);
v___y_514_ = v_i_521_;
v___y_515_ = v___y_520_;
goto v___jp_513_;
}
else
{
if (v___x_525_ == 0)
{
lean_dec_ref(v_vs_522_);
v___y_514_ = v_i_521_;
v___y_515_ = v___y_520_;
goto v___jp_513_;
}
else
{
size_t v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = ((size_t)0ULL);
v___x_527_ = lean_usize_of_nat(v___x_524_);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_522_, v___x_526_, v___x_527_);
lean_dec_ref(v_vs_522_);
if (v___x_528_ == 0)
{
v___y_514_ = v_i_521_;
v___y_515_ = v___y_520_;
goto v___jp_513_;
}
else
{
lean_dec(v_i_521_);
lean_dec_ref(v_env_510_);
return v___y_520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(lean_object* v_env_568_, lean_object* v_as_569_, lean_object* v_bs_570_, lean_object* v_i_571_, lean_object* v_cs_572_){
_start:
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_array_get_size(v_as_569_);
v___x_574_ = lean_nat_dec_lt(v_i_571_, v___x_573_);
if (v___x_574_ == 0)
{
lean_dec(v_i_571_);
lean_dec_ref(v_env_568_);
return v_cs_572_;
}
else
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_array_get_size(v_bs_570_);
v___x_576_ = lean_nat_dec_lt(v_i_571_, v___x_575_);
if (v___x_576_ == 0)
{
lean_dec(v_i_571_);
lean_dec_ref(v_env_568_);
return v_cs_572_;
}
else
{
lean_object* v_a_577_; lean_object* v_b_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_577_ = lean_array_fget_borrowed(v_as_569_, v_i_571_);
v_b_578_ = lean_array_fget_borrowed(v_bs_570_, v_i_571_);
lean_inc(v_b_578_);
lean_inc(v_a_577_);
lean_inc_ref(v_env_568_);
v___x_579_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_568_, v_a_577_, v_b_578_);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_i_571_, v___x_580_);
lean_dec(v_i_571_);
v___x_582_ = lean_array_push(v_cs_572_, v___x_579_);
v_i_571_ = v___x_581_;
v_cs_572_ = v___x_582_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(lean_object* v_env_584_, lean_object* v_vs_585_, lean_object* v_v_586_){
_start:
{
if (lean_obj_tag(v_vs_585_) == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_env_584_);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v_v_586_);
lean_ctor_set(v___x_605_, 1, v_vs_585_);
return v___x_605_;
}
else
{
lean_object* v_head_606_; 
v_head_606_ = lean_ctor_get(v_vs_585_, 0);
if (lean_obj_tag(v_head_606_) == 2)
{
if (lean_obj_tag(v_v_586_) == 2)
{
lean_object* v_tail_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_635_; 
lean_inc_ref(v_head_606_);
v_tail_607_ = lean_ctor_get(v_vs_585_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_vs_585_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_vs_585_, 0);
lean_dec(v_unused_636_);
v___x_609_ = v_vs_585_;
v_isShared_610_ = v_isSharedCheck_635_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_tail_607_);
lean_dec(v_vs_585_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_635_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_i_611_; lean_object* v_vs_612_; lean_object* v_i_613_; lean_object* v_vs_614_; uint8_t v___x_615_; 
v_i_611_ = lean_ctor_get(v_head_606_, 0);
v_vs_612_ = lean_ctor_get(v_head_606_, 1);
v_i_613_ = lean_ctor_get(v_v_586_, 0);
v_vs_614_ = lean_ctor_get(v_v_586_, 1);
v___x_615_ = lean_name_eq(v_i_611_, v_i_613_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_584_, v_tail_607_, v_v_586_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v___x_616_);
v___x_618_ = v___x_609_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_head_606_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_632_; 
lean_inc_ref(v_vs_614_);
lean_inc_ref(v_vs_612_);
lean_inc(v_i_611_);
lean_dec_ref_known(v_head_606_, 2);
v_isSharedCheck_632_ = !lean_is_exclusive(v_v_586_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; lean_object* v_unused_634_; 
v_unused_633_ = lean_ctor_get(v_v_586_, 1);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_v_586_, 0);
lean_dec(v_unused_634_);
v___x_621_ = v_v_586_;
v_isShared_622_ = v_isSharedCheck_632_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_v_586_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_632_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
v___x_625_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_584_, v_vs_612_, v_vs_614_, v___x_623_, v___x_624_);
lean_dec_ref(v_vs_614_);
lean_dec_ref(v_vs_612_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_625_);
lean_ctor_set(v___x_621_, 0, v_i_611_);
v___x_627_ = v___x_621_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_i_611_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_627_);
v___x_629_ = v___x_609_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_tail_607_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_584_);
goto v___jp_587_;
}
}
else
{
lean_dec_ref(v_env_584_);
goto v___jp_587_;
}
}
v___jp_587_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_588_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_589_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0));
v___x_590_ = lean_unsigned_to_nat(92u);
v___x_591_ = lean_unsigned_to_nat(12u);
v___x_592_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1));
v___x_593_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_586_);
v___x_594_ = l_Std_Format_defWidth;
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l_Std_Format_pretty(v___x_593_, v___x_594_, v___x_595_, v___x_595_);
v___x_597_ = lean_string_append(v___x_592_, v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
v___x_600_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_vs_585_);
v___x_601_ = l_Std_Format_pretty(v___x_600_, v___x_594_, v___x_595_, v___x_595_);
v___x_602_ = lean_string_append(v___x_599_, v___x_601_);
lean_dec_ref(v___x_601_);
v___x_603_ = l_mkPanicMessageWithDecl(v___x_588_, v___x_589_, v___x_590_, v___x_591_, v___x_602_);
lean_dec_ref(v___x_602_);
v___x_604_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(v___x_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(lean_object* v_env_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
lean_dec_ref(v_env_637_);
return v_x_638_;
}
else
{
lean_object* v_head_640_; lean_object* v_tail_641_; lean_object* v___x_642_; 
v_head_640_ = lean_ctor_get(v_x_639_, 0);
lean_inc(v_head_640_);
v_tail_641_ = lean_ctor_get(v_x_639_, 1);
lean_inc(v_tail_641_);
lean_dec_ref_known(v_x_639_, 2);
lean_inc_ref(v_env_637_);
v___x_642_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_637_, v_x_638_, v_head_640_);
v_x_638_ = v___x_642_;
v_x_639_ = v_tail_641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2___boxed(lean_object* v_env_644_, lean_object* v_as_645_, lean_object* v_bs_646_, lean_object* v_i_647_, lean_object* v_cs_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_644_, v_as_645_, v_bs_646_, v_i_647_, v_cs_648_);
lean_dec_ref(v_bs_646_);
lean_dec_ref(v_as_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(lean_object* v_a_650_, lean_object* v_n_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_a_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___boxed(lean_object* v_a_653_, lean_object* v_n_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(v_a_653_, v_n_654_);
lean_dec(v_n_654_);
return v_res_655_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(lean_object* v_a_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
else
{
lean_object* v_head_659_; lean_object* v_tail_660_; uint8_t v___x_661_; 
v_head_659_ = lean_ctor_get(v_x_657_, 0);
v_tail_660_ = lean_ctor_get(v_x_657_, 1);
v___x_661_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_656_, v_head_659_);
if (v___x_661_ == 0)
{
v_x_657_ = v_tail_660_;
goto _start;
}
else
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object* v_a_663_, lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v_a_663_, v_x_664_);
lean_dec(v_x_664_);
lean_dec(v_a_663_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(lean_object* v_env_667_, lean_object* v_forbiddenTypes_x27_668_, lean_object* v_n_669_, size_t v_sz_670_, size_t v_i_671_, lean_object* v_bs_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_673_ == 0)
{
lean_dec(v_forbiddenTypes_x27_668_);
lean_dec_ref(v_env_667_);
return v_bs_672_;
}
else
{
lean_object* v_v_674_; lean_object* v___x_675_; lean_object* v_bs_x27_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v_v_674_ = lean_array_uget(v_bs_672_, v_i_671_);
v___x_675_ = lean_unsigned_to_nat(0u);
v_bs_x27_676_ = lean_array_uset(v_bs_672_, v_i_671_, v___x_675_);
lean_inc(v_forbiddenTypes_x27_668_);
lean_inc_ref(v_env_667_);
v___x_677_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_667_, v_v_674_, v_forbiddenTypes_x27_668_, v_n_669_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_671_, v___x_678_);
v___x_680_ = lean_array_uset(v_bs_x27_676_, v_i_671_, v___x_677_);
v_i_671_ = v___x_679_;
v_bs_672_ = v___x_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(lean_object* v_env_682_, lean_object* v_v_683_, lean_object* v_forbiddenTypes_684_, lean_object* v_remainingDepth_685_){
_start:
{
lean_object* v_zero_686_; uint8_t v_isZero_687_; 
v_zero_686_ = lean_unsigned_to_nat(0u);
v_isZero_687_ = lean_nat_dec_eq(v_remainingDepth_685_, v_zero_686_);
if (v_isZero_687_ == 1)
{
lean_object* v___x_688_; 
lean_dec(v_forbiddenTypes_684_);
lean_dec(v_v_683_);
lean_dec_ref(v_env_682_);
v___x_688_ = lean_box(1);
return v___x_688_;
}
else
{
lean_object* v_one_689_; lean_object* v_n_690_; 
v_one_689_ = lean_unsigned_to_nat(1u);
v_n_690_ = lean_nat_sub(v_remainingDepth_685_, v_one_689_);
switch(lean_obj_tag(v_v_683_))
{
case 2:
{
lean_object* v_i_691_; lean_object* v_vs_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_711_; 
v_i_691_ = lean_ctor_get(v_v_683_, 0);
v_vs_692_ = lean_ctor_get(v_v_683_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_v_683_);
if (v_isSharedCheck_711_ == 0)
{
v___x_694_ = v_v_683_;
v_isShared_695_ = v_isSharedCheck_711_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_vs_692_);
lean_inc(v_i_691_);
lean_dec(v_v_683_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_711_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_forbiddenTypes_x27_697_; lean_object* v_induct_704_; lean_object* v_toConstantVal_705_; uint8_t v_isRec_706_; lean_object* v_name_707_; uint8_t v___x_708_; 
lean_inc_ref(v_env_682_);
lean_inc(v_i_691_);
v_induct_704_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_i_691_, v_env_682_);
v_toConstantVal_705_ = lean_ctor_get(v_induct_704_, 0);
lean_inc_ref(v_toConstantVal_705_);
v_isRec_706_ = lean_ctor_get_uint8(v_induct_704_, sizeof(void*)*6);
lean_dec_ref(v_induct_704_);
v_name_707_ = lean_ctor_get(v_toConstantVal_705_, 0);
lean_inc(v_name_707_);
lean_dec_ref(v_toConstantVal_705_);
v___x_708_ = l_Lean_NameSet_contains(v_forbiddenTypes_684_, v_name_707_);
if (v___x_708_ == 0)
{
if (v_isRec_706_ == 0)
{
lean_dec(v_name_707_);
v_forbiddenTypes_x27_697_ = v_forbiddenTypes_684_;
goto v___jp_696_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_NameSet_insert(v_forbiddenTypes_684_, v_name_707_);
v_forbiddenTypes_x27_697_ = v___x_709_;
goto v___jp_696_;
}
}
else
{
lean_object* v___x_710_; 
lean_dec(v_name_707_);
lean_del_object(v___x_694_);
lean_dec_ref(v_vs_692_);
lean_dec(v_i_691_);
lean_dec(v_n_690_);
lean_dec(v_forbiddenTypes_684_);
lean_dec_ref(v_env_682_);
v___x_710_ = lean_box(1);
return v___x_710_;
}
v___jp_696_:
{
size_t v_sz_698_; size_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v_sz_698_ = lean_array_size(v_vs_692_);
v___x_699_ = ((size_t)0ULL);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_682_, v_forbiddenTypes_x27_697_, v_n_690_, v_sz_698_, v___x_699_, v_vs_692_);
lean_dec(v_n_690_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_700_);
v___x_702_ = v___x_694_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_i_691_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
case 3:
{
lean_object* v_vs_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_723_; 
v_vs_712_ = lean_ctor_get(v_v_683_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_v_683_);
if (v_isSharedCheck_723_ == 0)
{
v___x_714_ = v_v_683_;
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_vs_712_);
lean_dec(v_v_683_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v_vs_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_716_ = lean_box(0);
v_vs_717_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_682_, v_forbiddenTypes_684_, v_n_690_, v_vs_712_, v___x_716_);
lean_dec(v_n_690_);
v___x_718_ = lean_box(1);
v___x_719_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v___x_718_, v_vs_717_);
if (v___x_719_ == 0)
{
lean_object* v___x_721_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_vs_717_);
v___x_721_ = v___x_714_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_vs_717_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
else
{
lean_dec(v_vs_717_);
lean_del_object(v___x_714_);
return v___x_718_;
}
}
}
default: 
{
lean_dec(v_n_690_);
lean_dec(v_forbiddenTypes_684_);
lean_dec_ref(v_env_682_);
return v_v_683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(lean_object* v_env_724_, lean_object* v_forbiddenTypes_725_, lean_object* v_n_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
if (lean_obj_tag(v_a_727_) == 0)
{
lean_object* v___x_729_; 
lean_dec(v_forbiddenTypes_725_);
lean_dec_ref(v_env_724_);
v___x_729_ = l_List_reverse___redArg(v_a_728_);
return v___x_729_;
}
else
{
lean_object* v_head_730_; lean_object* v_tail_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_740_; 
v_head_730_ = lean_ctor_get(v_a_727_, 0);
v_tail_731_ = lean_ctor_get(v_a_727_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_a_727_);
if (v_isSharedCheck_740_ == 0)
{
v___x_733_ = v_a_727_;
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_tail_731_);
lean_inc(v_head_730_);
lean_dec(v_a_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc(v_forbiddenTypes_725_);
lean_inc_ref(v_env_724_);
v___x_735_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_724_, v_head_730_, v_forbiddenTypes_725_, v_n_726_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_a_728_);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_a_728_);
v___x_737_ = v_reuseFailAlloc_739_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
v_a_727_ = v_tail_731_;
v_a_728_ = v___x_737_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object* v_env_741_, lean_object* v_forbiddenTypes_742_, lean_object* v_n_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_741_, v_forbiddenTypes_742_, v_n_743_, v_a_744_, v_a_745_);
lean_dec(v_n_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object* v_env_747_, lean_object* v_forbiddenTypes_x27_748_, lean_object* v_n_749_, lean_object* v_sz_750_, lean_object* v_i_751_, lean_object* v_bs_752_){
_start:
{
size_t v_sz_boxed_753_; size_t v_i_boxed_754_; lean_object* v_res_755_; 
v_sz_boxed_753_ = lean_unbox_usize(v_sz_750_);
lean_dec(v_sz_750_);
v_i_boxed_754_ = lean_unbox_usize(v_i_751_);
lean_dec(v_i_751_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_747_, v_forbiddenTypes_x27_748_, v_n_749_, v_sz_boxed_753_, v_i_boxed_754_, v_bs_752_);
lean_dec(v_n_749_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___boxed(lean_object* v_env_756_, lean_object* v_v_757_, lean_object* v_forbiddenTypes_758_, lean_object* v_remainingDepth_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_756_, v_v_757_, v_forbiddenTypes_758_, v_remainingDepth_759_);
lean_dec(v_remainingDepth_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(lean_object* v_env_761_, lean_object* v_v_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = l_Lean_NameSet_empty;
v___x_764_ = lean_unsigned_to_nat(8u);
v___x_765_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_761_, v_v_762_, v___x_763_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(lean_object* v_env_766_, lean_object* v_v1_767_, lean_object* v_v2_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_inc_ref(v_env_766_);
v___x_769_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_766_, v_v1_767_, v_v2_768_);
v___x_770_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(v_env_766_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
uint8_t v___x_773_; 
v___x_773_ = 0;
return v___x_773_;
}
else
{
lean_object* v_head_774_; lean_object* v_tail_775_; uint8_t v___x_776_; 
v_head_774_ = lean_ctor_get(v_x_772_, 0);
v_tail_775_ = lean_ctor_get(v_x_772_, 1);
v___x_776_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_head_774_, v_x_771_);
if (v___x_776_ == 0)
{
v_x_772_ = v_tail_775_;
goto _start;
}
else
{
return v___x_776_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
switch(lean_obj_tag(v_x_778_))
{
case 2:
{
lean_object* v_i_780_; uint8_t v___x_781_; 
v_i_780_ = lean_ctor_get(v_x_778_, 0);
v___x_781_ = lean_name_eq(v_i_780_, v_x_779_);
return v___x_781_;
}
case 3:
{
lean_object* v_vs_782_; uint8_t v___x_783_; 
v_vs_782_ = lean_ctor_get(v_x_778_, 0);
v___x_783_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_779_, v_vs_782_);
return v___x_783_;
}
default: 
{
uint8_t v___x_784_; 
v___x_784_ = 1;
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_x_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec(v_x_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0___boxed(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec(v_x_789_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(lean_object* v_x_796_, lean_object* v_as_x27_797_, lean_object* v_b_798_){
_start:
{
if (lean_obj_tag(v_as_x27_797_) == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_798_);
return v___x_799_;
}
else
{
lean_object* v_head_800_; lean_object* v_tail_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v_b_798_);
v_head_800_ = lean_ctor_get(v_as_x27_797_, 0);
v_tail_801_ = lean_ctor_get(v_as_x27_797_, 1);
v___x_802_ = lean_box(0);
v___x_803_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_800_) == 2)
{
lean_object* v_i_804_; lean_object* v_vs_805_; uint8_t v___x_806_; 
v_i_804_ = lean_ctor_get(v_head_800_, 0);
v_vs_805_ = lean_ctor_get(v_head_800_, 1);
v___x_806_ = lean_name_eq(v_i_804_, v_x_796_);
if (v___x_806_ == 0)
{
v_as_x27_797_ = v_tail_801_;
v_b_798_ = v___x_803_;
goto _start;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref(v_vs_805_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_vs_805_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_802_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
else
{
v_as_x27_797_ = v_tail_801_;
v_b_798_ = v___x_803_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___boxed(lean_object* v_x_812_, lean_object* v_as_x27_813_, lean_object* v_b_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_812_, v_as_x27_813_, v_b_814_);
lean_dec(v_as_x27_813_);
lean_dec(v_x_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
switch(lean_obj_tag(v_x_816_))
{
case 2:
{
lean_object* v_i_818_; lean_object* v_vs_819_; uint8_t v___x_820_; 
v_i_818_ = lean_ctor_get(v_x_816_, 0);
v_vs_819_ = lean_ctor_get(v_x_816_, 1);
v___x_820_ = lean_name_eq(v_i_818_, v_x_817_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
v___x_821_ = lean_box(0);
return v___x_821_;
}
else
{
lean_object* v___x_822_; 
lean_inc_ref(v_vs_819_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_vs_819_);
return v___x_822_;
}
}
case 3:
{
lean_object* v_vs_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_val_827_; lean_object* v_fst_828_; 
v_vs_823_ = lean_ctor_get(v_x_816_, 0);
v___x_824_ = lean_box(0);
v___x_825_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
v___x_826_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_817_, v_vs_823_, v___x_825_);
v_val_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_827_);
lean_dec(v___x_826_);
v_fst_828_ = lean_ctor_get(v_val_827_, 0);
lean_inc(v_fst_828_);
lean_dec(v_val_827_);
if (lean_obj_tag(v_fst_828_) == 0)
{
return v___x_824_;
}
else
{
return v_fst_828_;
}
}
default: 
{
lean_object* v___x_829_; 
v___x_829_ = lean_box(0);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs___boxed(lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_x_830_, v_x_831_);
lean_dec(v_x_831_);
lean_dec(v_x_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(lean_object* v_x_833_, lean_object* v_as_834_, lean_object* v_as_x27_835_, lean_object* v_b_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_833_, v_as_x27_835_, v_b_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___boxed(lean_object* v_x_839_, lean_object* v_as_840_, lean_object* v_as_x27_841_, lean_object* v_b_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(v_x_839_, v_as_840_, v_as_x27_841_, v_b_842_, v_a_843_);
lean_dec(v_as_x27_841_);
lean_dec(v_as_840_);
lean_dec(v_x_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(lean_object* v_a_857_){
_start:
{
lean_object* v_zero_858_; uint8_t v_isZero_859_; 
v_zero_858_ = lean_unsigned_to_nat(0u);
v_isZero_859_ = lean_nat_dec_eq(v_a_857_, v_zero_858_);
if (v_isZero_859_ == 1)
{
lean_object* v___x_860_; 
v___x_860_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3));
return v___x_860_;
}
else
{
lean_object* v_one_861_; lean_object* v_n_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_one_861_ = lean_unsigned_to_nat(1u);
v_n_862_ = lean_nat_sub(v_a_857_, v_one_861_);
v___x_863_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5));
v___x_864_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_862_);
lean_dec(v_n_862_);
v___x_865_ = lean_mk_empty_array_with_capacity(v_one_861_);
v___x_866_ = lean_array_push(v___x_865_, v___x_864_);
v___x_867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_863_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___boxed(lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_a_868_);
lean_dec(v_a_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(lean_object* v_n_870_){
_start:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(8u);
v___x_872_ = lean_nat_dec_lt(v___x_871_, v_n_870_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_870_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; 
v___x_874_ = lean_box(1);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat___boxed(lean_object* v_n_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_n_875_);
lean_dec(v_n_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_object* v_val_878_; lean_object* v___x_879_; 
v_val_878_ = lean_ctor_get(v_x_877_, 0);
v___x_879_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_val_878_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = lean_box(1);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit___boxed(lean_object* v_x_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_x_881_);
lean_dec_ref(v_x_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(lean_object* v_env_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
switch(lean_obj_tag(v_x_884_))
{
case 2:
{
lean_object* v_vs_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
lean_dec_ref(v_env_883_);
v_vs_886_ = lean_ctor_get(v_x_884_, 1);
v___x_887_ = lean_array_get_size(v_vs_886_);
v___x_888_ = lean_nat_dec_lt(v_x_885_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_box(0);
return v___x_889_;
}
else
{
lean_object* v___x_890_; 
v___x_890_ = lean_array_fget_borrowed(v_vs_886_, v_x_885_);
lean_inc(v___x_890_);
return v___x_890_;
}
}
case 3:
{
lean_object* v_vs_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_vs_891_ = lean_ctor_get(v_x_884_, 0);
v___x_892_ = lean_box(0);
v___x_893_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_883_, v_x_885_, v___x_892_, v_vs_891_);
return v___x_893_;
}
default: 
{
lean_dec_ref(v_env_883_);
lean_inc(v_x_884_);
return v_x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(lean_object* v_env_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_dec_ref(v_env_894_);
return v_x_896_;
}
else
{
lean_object* v_head_898_; lean_object* v_tail_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_head_898_ = lean_ctor_get(v_x_897_, 0);
v_tail_899_ = lean_ctor_get(v_x_897_, 1);
lean_inc_ref_n(v_env_894_, 2);
v___x_900_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_894_, v_head_898_, v_x_895_);
v___x_901_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_894_, v_x_896_, v___x_900_);
v_x_896_ = v___x_901_;
v_x_897_ = v_tail_899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0___boxed(lean_object* v_env_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_903_, v_x_904_, v_x_905_, v_x_906_);
lean_dec(v_x_906_);
lean_dec(v_x_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj___boxed(lean_object* v_env_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_908_, v_x_909_, v_x_910_);
lean_dec(v_x_910_);
lean_dec(v_x_909_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_912_) == 2)
{
lean_object* v_vs_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_vs_913_ = lean_ctor_get(v_x_912_, 1);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_array_get_size(v_vs_913_);
v___x_916_ = lean_nat_dec_lt(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
uint8_t v___x_917_; 
v___x_917_ = 1;
return v___x_917_;
}
else
{
if (v___x_916_ == 0)
{
return v___x_916_;
}
else
{
size_t v___x_918_; size_t v___x_919_; uint8_t v___x_920_; 
v___x_918_ = ((size_t)0ULL);
v___x_919_ = lean_usize_of_nat(v___x_915_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_vs_913_, v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
return v___x_916_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = 0;
return v___x_921_;
}
}
}
}
else
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(lean_object* v_as_923_, size_t v_i_924_, size_t v_stop_925_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = lean_usize_dec_eq(v_i_924_, v_stop_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_array_uget_borrowed(v_as_923_, v_i_924_);
v___x_928_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v___x_927_);
if (v___x_928_ == 0)
{
uint8_t v___x_929_; 
v___x_929_ = 1;
return v___x_929_;
}
else
{
size_t v___x_930_; size_t v___x_931_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_924_, v___x_930_);
v_i_924_ = v___x_931_;
goto _start;
}
}
else
{
uint8_t v___x_933_; 
v___x_933_ = 0;
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0___boxed(lean_object* v_as_934_, lean_object* v_i_935_, lean_object* v_stop_936_){
_start:
{
size_t v_i_boxed_937_; size_t v_stop_boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v_i_boxed_937_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_stop_boxed_938_ = lean_unbox_usize(v_stop_936_);
lean_dec(v_stop_936_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_as_934_, v_i_boxed_937_, v_stop_boxed_938_);
lean_dec_ref(v_as_934_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral___boxed(lean_object* v_x_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_x_941_);
lean_dec(v_x_941_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(lean_object* v_msg_944_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_panic_fn_borrowed(v___x_945_, v_msg_944_);
return v___x_946_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_949_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1));
v___x_950_ = lean_unsigned_to_nat(9u);
v___x_951_ = lean_unsigned_to_nat(271u);
v___x_952_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0));
v___x_953_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_954_ = l_mkPanicMessageWithDecl(v___x_953_, v___x_952_, v___x_951_, v___x_950_, v___x_949_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(lean_object* v_a_955_){
_start:
{
if (lean_obj_tag(v_a_955_) == 2)
{
lean_object* v_i_959_; 
v_i_959_ = lean_ctor_get(v_a_955_, 0);
if (lean_obj_tag(v_i_959_) == 1)
{
lean_object* v_pre_960_; 
v_pre_960_ = lean_ctor_get(v_i_959_, 0);
if (lean_obj_tag(v_pre_960_) == 1)
{
lean_object* v_pre_961_; 
v_pre_961_ = lean_ctor_get(v_pre_960_, 0);
if (lean_obj_tag(v_pre_961_) == 0)
{
lean_object* v_vs_962_; lean_object* v_str_963_; lean_object* v_str_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_vs_962_ = lean_ctor_get(v_a_955_, 1);
v_str_963_ = lean_ctor_get(v_i_959_, 1);
v_str_964_ = lean_ctor_get(v_pre_960_, 1);
v___x_965_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_966_ = lean_string_dec_eq(v_str_964_, v___x_965_);
if (v___x_966_ == 0)
{
goto v___jp_956_;
}
else
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_968_ = lean_string_dec_eq(v_str_963_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_970_ = lean_string_dec_eq(v_str_963_, v___x_969_);
if (v___x_970_ == 0)
{
goto v___jp_956_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_array_get_size(v_vs_962_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_dec_eq(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
goto v___jp_956_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_array_fget_borrowed(v_vs_962_, v___x_974_);
v___x_976_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_975_);
v___x_977_ = lean_nat_add(v___x_976_, v___x_972_);
lean_dec(v___x_976_);
return v___x_977_;
}
}
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_978_ = lean_array_get_size(v_vs_962_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_nat_dec_eq(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
goto v___jp_956_;
}
else
{
return v___x_979_;
}
}
}
}
else
{
goto v___jp_956_;
}
}
else
{
goto v___jp_956_;
}
}
else
{
goto v___jp_956_;
}
}
else
{
goto v___jp_956_;
}
v___jp_956_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2);
v___x_958_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(v___x_957_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___boxed(lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v_a_981_);
lean_dec(v_a_981_);
return v_res_982_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_instMonadEIO(lean_box(0));
return v___x_983_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Array_instInhabited(lean_box(0));
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(lean_object* v_msg_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_toApplicative_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1030_; 
v___x_993_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0);
v___x_994_ = l_StateRefT_x27_instMonad___redArg(v___x_993_);
v_toApplicative_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v___x_994_, 1);
lean_dec(v_unused_1031_);
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1030_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_toApplicative_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1030_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_toFunctor_999_; lean_object* v_toSeq_1000_; lean_object* v_toSeqLeft_1001_; lean_object* v_toSeqRight_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1028_; 
v_toFunctor_999_ = lean_ctor_get(v_toApplicative_995_, 0);
v_toSeq_1000_ = lean_ctor_get(v_toApplicative_995_, 2);
v_toSeqLeft_1001_ = lean_ctor_get(v_toApplicative_995_, 3);
v_toSeqRight_1002_ = lean_ctor_get(v_toApplicative_995_, 4);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_toApplicative_995_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_toApplicative_995_, 1);
lean_dec(v_unused_1029_);
v___x_1004_ = v_toApplicative_995_;
v_isShared_1005_ = v_isSharedCheck_1028_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_toSeqRight_1002_);
lean_inc(v_toSeqLeft_1001_);
lean_inc(v_toSeq_1000_);
lean_inc(v_toFunctor_999_);
lean_dec(v_toApplicative_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1028_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1015_; 
v___f_1006_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1));
v___f_1007_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2));
lean_inc_ref(v_toFunctor_999_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toFunctor_999_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toFunctor_999_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___f_1008_);
lean_ctor_set(v___x_1010_, 1, v___f_1009_);
v___f_1011_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1011_, 0, v_toSeqRight_1002_);
v___f_1012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1012_, 0, v_toSeqLeft_1001_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toSeq_1000_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 4, v___f_1011_);
lean_ctor_set(v___x_1004_, 3, v___f_1012_);
lean_ctor_set(v___x_1004_, 2, v___f_1013_);
lean_ctor_set(v___x_1004_, 1, v___f_1006_);
lean_ctor_set(v___x_1004_, 0, v___x_1010_);
v___x_1015_ = v___x_1004_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___f_1006_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v___f_1013_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v___f_1012_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v___f_1011_);
v___x_1015_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___f_1007_);
lean_ctor_set(v___x_997_, 0, v___x_1015_);
v___x_1017_ = v___x_997_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___f_1007_);
v___x_1017_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; lean_object* v___x_1968__overap_1024_; lean_object* v___x_1025_; 
v___x_1018_ = l_StateRefT_x27_instMonad___redArg(v___x_1017_);
v___x_1019_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_instInhabitedOfMonad___redArg(v___x_1018_, v___x_1021_);
v___f_1023_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1023_, 0, v___x_1022_);
v___x_1968__overap_1024_ = lean_panic_fn_borrowed(v___f_1023_, v_msg_987_);
lean_dec_ref(v___f_1023_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
v___x_1025_ = lean_apply_5(v___x_1968__overap_1024_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
return v___x_1025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object* v_as_1039_, size_t v_i_1040_, size_t v_stop_1041_, lean_object* v_b_1042_){
_start:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_usize_dec_eq(v_i_1040_, v_stop_1041_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v_fst_1047_; lean_object* v_snd_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1061_; 
v___x_1044_ = lean_array_uget_borrowed(v_as_1039_, v_i_1040_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
v_fst_1047_ = lean_ctor_get(v_b_1042_, 0);
v_snd_1048_ = lean_ctor_get(v_b_1042_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_b_1042_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1050_ = v_b_1042_;
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snd_1048_);
lean_inc(v_fst_1047_);
lean_dec(v_b_1042_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1052_ = l_Array_append___redArg(v_fst_1047_, v_fst_1045_);
lean_inc(v_snd_1046_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_snd_1046_);
v___x_1054_ = lean_array_push(v_snd_1048_, v___x_1053_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1054_);
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1040_, v___x_1057_);
v_i_1040_ = v___x_1058_;
v_b_1042_ = v___x_1056_;
goto _start;
}
}
}
else
{
return v_b_1042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object* v_as_1062_, lean_object* v_i_1063_, lean_object* v_stop_1064_, lean_object* v_b_1065_){
_start:
{
size_t v_i_boxed_1066_; size_t v_stop_boxed_1067_; lean_object* v_res_1068_; 
v_i_boxed_1066_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_stop_boxed_1067_ = lean_unbox_usize(v_stop_1064_);
lean_dec(v_stop_1064_);
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_as_1062_, v_i_boxed_1066_, v_stop_boxed_1067_, v_b_1065_);
lean_dec_ref(v_as_1062_);
return v_res_1068_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1073_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1074_ = lean_unsigned_to_nat(65u);
v___x_1075_ = lean_unsigned_to_nat(258u);
v___x_1076_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1077_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1078_ = l_mkPanicMessageWithDecl(v___x_1077_, v___x_1076_, v___x_1075_, v___x_1074_, v___x_1073_);
return v___x_1078_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1085_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1086_ = lean_unsigned_to_nat(9u);
v___x_1087_ = lean_unsigned_to_nat(266u);
v___x_1088_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1089_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1090_ = l_mkPanicMessageWithDecl(v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_, v___x_1085_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; 
if (lean_obj_tag(v_a_1091_) == 2)
{
lean_object* v_i_1146_; lean_object* v_vs_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1268_; 
v_i_1146_ = lean_ctor_get(v_a_1091_, 0);
v_vs_1147_ = lean_ctor_get(v_a_1091_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_a_1091_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1149_ = v_a_1091_;
v_isShared_1150_ = v_isSharedCheck_1268_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_vs_1147_);
lean_inc(v_i_1146_);
lean_dec(v_a_1091_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1268_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_ctorName_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; 
if (lean_obj_tag(v_i_1146_) == 1)
{
lean_object* v_pre_1190_; 
v_pre_1190_ = lean_ctor_get(v_i_1146_, 0);
if (lean_obj_tag(v_pre_1190_) == 1)
{
lean_object* v_pre_1191_; 
v_pre_1191_ = lean_ctor_get(v_pre_1190_, 0);
if (lean_obj_tag(v_pre_1191_) == 0)
{
lean_object* v_str_1192_; lean_object* v_str_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_str_1192_ = lean_ctor_get(v_i_1146_, 1);
v_str_1193_ = lean_ctor_get(v_pre_1190_, 1);
v___x_1194_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_1195_ = lean_string_dec_eq(v_str_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
v_ctorName_1152_ = v_i_1146_;
v___y_1153_ = v_a_1092_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
lean_inc(v_pre_1191_);
lean_inc_ref(v_str_1192_);
lean_dec_ref_known(v_i_1146_, 2);
v___x_1196_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_1197_ = lean_string_dec_eq(v_str_1192_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_1199_ = lean_string_dec_eq(v_str_1192_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = l_Lean_Name_str___override(v_pre_1191_, v___x_1194_);
v___x_1201_ = l_Lean_Name_str___override(v___x_1200_, v_str_1192_);
v_ctorName_1152_ = v___x_1201_;
v___y_1153_ = v_a_1092_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
lean_dec_ref(v_str_1192_);
v___x_1202_ = lean_array_get_size(v_vs_1147_);
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = lean_nat_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = l_Lean_Name_str___override(v_pre_1191_, v___x_1194_);
v___x_1206_ = l_Lean_Name_str___override(v___x_1205_, v___x_1198_);
v_ctorName_1152_ = v___x_1206_;
v___y_1153_ = v_a_1092_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_val_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_del_object(v___x_1149_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_array_fget(v_vs_1147_, v___x_1207_);
lean_dec_ref(v_vs_1147_);
v___x_1209_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_1208_);
lean_dec(v___x_1208_);
v_val_1210_ = lean_nat_add(v___x_1209_, v___x_1203_);
lean_dec(v___x_1209_);
v___x_1211_ = 0;
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_val_1210_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1215_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1211_, v___x_1213_, v___x_1214_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1228_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1228_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1228_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v_fvarId_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v_fvarId_1220_ = lean_ctor_get(v_a_1216_, 0);
lean_inc(v_fvarId_1220_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_a_1216_);
v___x_1222_ = lean_mk_empty_array_with_capacity(v___x_1203_);
v___x_1223_ = lean_array_push(v___x_1222_, v___x_1221_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v_fvarId_1220_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1224_);
v___x_1226_ = v___x_1218_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1229_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1215_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1215_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
lean_dec_ref(v_str_1192_);
v___x_1237_ = lean_array_get_size(v_vs_1147_);
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_nat_dec_eq(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = l_Lean_Name_str___override(v_pre_1191_, v___x_1194_);
v___x_1241_ = l_Lean_Name_str___override(v___x_1240_, v___x_1196_);
v_ctorName_1152_ = v___x_1241_;
v___y_1153_ = v_a_1092_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
goto v___jp_1151_;
}
else
{
uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_del_object(v___x_1149_);
lean_dec_ref(v_vs_1147_);
v___x_1242_ = 0;
v___x_1243_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6));
v___x_1244_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1245_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1242_, v___x_1243_, v___x_1244_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1259_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1259_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1259_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_fvarId_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_fvarId_1250_ = lean_ctor_get(v_a_1246_, 0);
lean_inc(v_fvarId_1250_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1246_);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_mk_empty_array_with_capacity(v___x_1252_);
v___x_1254_ = lean_array_push(v___x_1253_, v___x_1251_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v_fvarId_1250_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1255_);
v___x_1257_ = v___x_1248_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
v_a_1260_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1245_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1245_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
}
else
{
v_ctorName_1152_ = v_i_1146_;
v___y_1153_ = v_a_1092_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
goto v___jp_1151_;
}
}
else
{
v_ctorName_1152_ = v_i_1146_;
v___y_1153_ = v_a_1092_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
goto v___jp_1151_;
}
}
else
{
v_ctorName_1152_ = v_i_1146_;
v___y_1153_ = v_a_1092_;
v___y_1154_ = v_a_1093_;
v___y_1155_ = v_a_1094_;
v___y_1156_ = v_a_1095_;
goto v___jp_1151_;
}
v___jp_1151_:
{
lean_object* v___x_1157_; lean_object* v_env_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1157_ = lean_st_ref_get(v___y_1156_);
v_env_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc_ref(v_env_1158_);
lean_dec(v___x_1157_);
v___x_1159_ = 0;
lean_inc(v_ctorName_1152_);
v___x_1160_ = l_Lean_Environment_find_x3f(v_env_1158_, v_ctorName_1152_, v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 1)
{
lean_object* v_val_1161_; 
v_val_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v___x_1160_, 1);
if (lean_obj_tag(v_val_1161_) == 6)
{
lean_object* v_val_1162_; size_t v_sz_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v_val_1162_ = lean_ctor_get(v_val_1161_, 0);
lean_inc_ref(v_val_1162_);
lean_dec_ref_known(v_val_1161_, 1);
v_sz_1163_ = lean_array_size(v_vs_1147_);
v___x_1164_ = ((size_t)0ULL);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_1163_, v___x_1164_, v_vs_1147_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_numParams_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v_numParams_1167_ = lean_ctor_get(v_val_1162_, 3);
lean_inc(v_numParams_1167_);
lean_dec_ref(v_val_1162_);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4));
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_mk_array(v_numParams_1167_, v___x_1170_);
v___x_1172_ = lean_array_get_size(v_a_1166_);
v___x_1173_ = lean_nat_dec_lt(v___x_1168_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v_a_1166_);
lean_del_object(v___x_1149_);
v___y_1098_ = v___y_1155_;
v___y_1099_ = v___y_1154_;
v___y_1100_ = v___y_1153_;
v___y_1101_ = v___y_1156_;
v___y_1102_ = v_ctorName_1152_;
v_fst_1103_ = v___x_1169_;
v_snd_1104_ = v___x_1171_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1175_; 
lean_inc_ref(v___x_1171_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 0);
lean_ctor_set(v___x_1149_, 1, v___x_1171_);
lean_ctor_set(v___x_1149_, 0, v___x_1169_);
v___x_1175_ = v___x_1149_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1171_);
v___x_1175_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_nat_dec_le(v___x_1172_, v___x_1172_);
if (v___x_1176_ == 0)
{
if (v___x_1173_ == 0)
{
lean_dec_ref(v___x_1175_);
lean_dec(v_a_1166_);
v___y_1098_ = v___y_1155_;
v___y_1099_ = v___y_1154_;
v___y_1100_ = v___y_1153_;
v___y_1101_ = v___y_1156_;
v___y_1102_ = v_ctorName_1152_;
v_fst_1103_ = v___x_1169_;
v_snd_1104_ = v___x_1171_;
goto v___jp_1097_;
}
else
{
size_t v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v___x_1171_);
v___x_1177_ = lean_usize_of_nat(v___x_1172_);
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1166_, v___x_1164_, v___x_1177_, v___x_1175_);
lean_dec(v_a_1166_);
v___y_1131_ = v___y_1155_;
v___y_1132_ = v___y_1154_;
v___y_1133_ = v___y_1153_;
v___y_1134_ = v___y_1156_;
v___y_1135_ = v_ctorName_1152_;
v___y_1136_ = v___x_1178_;
goto v___jp_1130_;
}
}
else
{
size_t v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v___x_1171_);
v___x_1179_ = lean_usize_of_nat(v___x_1172_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1166_, v___x_1164_, v___x_1179_, v___x_1175_);
lean_dec(v_a_1166_);
v___y_1131_ = v___y_1155_;
v___y_1132_ = v___y_1154_;
v___y_1133_ = v___y_1153_;
v___y_1134_ = v___y_1156_;
v___y_1135_ = v_ctorName_1152_;
v___y_1136_ = v___x_1180_;
goto v___jp_1130_;
}
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_val_1162_);
lean_dec(v_ctorName_1152_);
lean_del_object(v___x_1149_);
v_a_1182_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1165_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1165_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_dec(v_val_1161_);
lean_dec(v_ctorName_1152_);
lean_del_object(v___x_1149_);
lean_dec_ref(v_vs_1147_);
v___y_1140_ = v___y_1153_;
v___y_1141_ = v___y_1154_;
v___y_1142_ = v___y_1155_;
v___y_1143_ = v___y_1156_;
goto v___jp_1139_;
}
}
else
{
lean_dec(v___x_1160_);
lean_dec(v_ctorName_1152_);
lean_del_object(v___x_1149_);
lean_dec_ref(v_vs_1147_);
v___y_1140_ = v___y_1153_;
v___y_1141_ = v___y_1154_;
v___y_1142_ = v___y_1155_;
v___y_1143_ = v___y_1156_;
goto v___jp_1139_;
}
}
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec(v_a_1091_);
v___x_1269_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7);
v___x_1270_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1269_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
return v___x_1270_;
}
v___jp_1097_:
{
uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1105_ = 0;
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1102_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
lean_ctor_set(v___x_1107_, 2, v_snd_1104_);
v___x_1108_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1109_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1105_, v___x_1107_, v___x_1108_, v___y_1100_, v___y_1099_, v___y_1098_, v___y_1101_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1121_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1121_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1121_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_fvarId_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v_fvarId_1114_ = lean_ctor_get(v_a_1110_, 0);
lean_inc(v_fvarId_1114_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_a_1110_);
v___x_1116_ = lean_array_push(v_fst_1103_, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_fvarId_1114_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1117_);
v___x_1119_ = v___x_1112_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_fst_1103_);
v_a_1122_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1109_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1109_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
v___jp_1130_:
{
lean_object* v_fst_1137_; lean_object* v_snd_1138_; 
v_fst_1137_ = lean_ctor_get(v___y_1136_, 0);
lean_inc(v_fst_1137_);
v_snd_1138_ = lean_ctor_get(v___y_1136_, 1);
lean_inc(v_snd_1138_);
lean_dec_ref(v___y_1136_);
v___y_1098_ = v___y_1131_;
v___y_1099_ = v___y_1132_;
v___y_1100_ = v___y_1133_;
v___y_1101_ = v___y_1134_;
v___y_1102_ = v___y_1135_;
v_fst_1103_ = v_fst_1137_;
v_snd_1104_ = v_snd_1138_;
goto v___jp_1097_;
}
v___jp_1139_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3);
v___x_1145_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1144_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(size_t v_sz_1271_, size_t v_i_1272_, lean_object* v_bs_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_lt(v_i_1272_, v_sz_1271_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_bs_1273_);
return v___x_1280_;
}
else
{
lean_object* v_v_1281_; lean_object* v___x_1282_; 
v_v_1281_ = lean_array_uget_borrowed(v_bs_1273_, v_i_1272_);
lean_inc(v_v_1281_);
v___x_1282_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1281_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; lean_object* v_bs_x27_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = lean_unsigned_to_nat(0u);
v_bs_x27_1285_ = lean_array_uset(v_bs_1273_, v_i_1272_, v___x_1284_);
v___x_1286_ = ((size_t)1ULL);
v___x_1287_ = lean_usize_add(v_i_1272_, v___x_1286_);
v___x_1288_ = lean_array_uset(v_bs_x27_1285_, v_i_1272_, v_a_1283_);
v_i_1272_ = v___x_1287_;
v_bs_1273_ = v___x_1288_;
goto _start;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_bs_1273_);
v_a_1290_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1282_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1282_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_bs_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
size_t v_sz_boxed_1306_; size_t v_i_boxed_1307_; lean_object* v_res_1308_; 
v_sz_boxed_1306_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1307_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_boxed_1306_, v_i_boxed_1307_, v_bs_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(lean_object* v_v_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_v_1316_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_v_1316_);
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; 
v___x_1325_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1335_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1325_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1325_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral___boxed(lean_object* v_v_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_v_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
return v_res_1349_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(lean_object* v_a_1350_, lean_object* v_b_1351_){
_start:
{
lean_object* v_fst_1352_; lean_object* v_fst_1353_; uint8_t v___x_1354_; 
v_fst_1352_ = lean_ctor_get(v_a_1350_, 0);
v_fst_1353_ = lean_ctor_get(v_b_1351_, 0);
v___x_1354_ = l_Lean_Name_quickLt(v_fst_1352_, v_fst_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed(lean_object* v_a_1355_, lean_object* v_b_1356_){
_start:
{
uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_res_1357_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(v_a_1355_, v_b_1356_);
lean_dec_ref(v_b_1356_);
lean_dec_ref(v_a_1355_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(lean_object* v_entries_1361_, lean_object* v_fid_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_array_get_size(v_entries_1361_);
v___x_1365_ = lean_nat_dec_lt(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec(v_fid_1362_);
v___x_1366_ = lean_box(0);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_sub(v___x_1364_, v___x_1367_);
v___x_1369_ = lean_nat_dec_le(v___x_1363_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v___x_1368_);
lean_dec(v_fid_1362_);
v___x_1370_ = lean_box(0);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_fid_1362_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0));
v___x_1374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1));
v___x_1375_ = l_Array_binSearchAux___redArg(v___x_1373_, v___x_1374_, v_entries_1361_, v___x_1372_, v___x_1363_, v___x_1368_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
else
{
lean_object* v_val_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1385_; 
v_val_1377_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_val_1377_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_snd_1381_; lean_object* v___x_1383_; 
v_snd_1381_ = lean_ctor_get(v_val_1377_, 1);
lean_inc(v_snd_1381_);
lean_dec(v_val_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_snd_1381_);
v___x_1383_ = v___x_1379_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_snd_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___boxed(lean_object* v_entries_1386_, lean_object* v_fid_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(v_entries_1386_, v_fid_1387_);
lean_dec_ref(v_entries_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_es_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_array_mk(v_es_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1391_, lean_object* v_i_1392_, lean_object* v_k_1393_){
_start:
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_array_get_size(v_keys_1391_);
v___x_1395_ = lean_nat_dec_lt(v_i_1392_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec(v_i_1392_);
return v___x_1395_;
}
else
{
lean_object* v_k_x27_1396_; uint8_t v___x_1397_; 
v_k_x27_1396_ = lean_array_fget_borrowed(v_keys_1391_, v_i_1392_);
v___x_1397_ = lean_name_eq(v_k_1393_, v_k_x27_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v_i_1392_, v___x_1398_);
lean_dec(v_i_1392_);
v_i_1392_ = v___x_1399_;
goto _start;
}
else
{
lean_dec(v_i_1392_);
return v___x_1395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1401_, lean_object* v_i_1402_, lean_object* v_k_1403_){
_start:
{
uint8_t v_res_1404_; lean_object* v_r_1405_; 
v_res_1404_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1401_, v_i_1402_, v_k_1403_);
lean_dec(v_k_1403_);
lean_dec_ref(v_keys_1401_);
v_r_1405_ = lean_box(v_res_1404_);
return v_r_1405_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1406_, size_t v_x_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 0)
{
lean_object* v_es_1409_; lean_object* v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; lean_object* v_j_1413_; lean_object* v___x_1414_; 
v_es_1409_ = lean_ctor_get(v_x_1406_, 0);
v___x_1410_ = lean_box(2);
v___x_1411_ = ((size_t)31ULL);
v___x_1412_ = lean_usize_land(v_x_1407_, v___x_1411_);
v_j_1413_ = lean_usize_to_nat(v___x_1412_);
v___x_1414_ = lean_array_get_borrowed(v___x_1410_, v_es_1409_, v_j_1413_);
lean_dec(v_j_1413_);
switch(lean_obj_tag(v___x_1414_))
{
case 0:
{
lean_object* v_key_1415_; uint8_t v___x_1416_; 
v_key_1415_ = lean_ctor_get(v___x_1414_, 0);
v___x_1416_ = lean_name_eq(v_x_1408_, v_key_1415_);
return v___x_1416_;
}
case 1:
{
lean_object* v_node_1417_; size_t v___x_1418_; size_t v___x_1419_; 
v_node_1417_ = lean_ctor_get(v___x_1414_, 0);
v___x_1418_ = ((size_t)5ULL);
v___x_1419_ = lean_usize_shift_right(v_x_1407_, v___x_1418_);
v_x_1406_ = v_node_1417_;
v_x_1407_ = v___x_1419_;
goto _start;
}
default: 
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
}
}
else
{
lean_object* v_ks_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_ks_1422_ = lean_ctor_get(v_x_1406_, 0);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1422_, v___x_1423_, v_x_1408_);
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
size_t v_x_1138__boxed_1428_; uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_x_1138__boxed_1428_ = lean_unbox_usize(v_x_1426_);
lean_dec(v_x_1426_);
v_res_1429_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1425_, v_x_1138__boxed_1428_, v_x_1427_);
lean_dec(v_x_1427_);
lean_dec_ref(v_x_1425_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
uint64_t v___y_1434_; 
if (lean_obj_tag(v_x_1432_) == 0)
{
uint64_t v___x_1437_; 
v___x_1437_ = 1723ULL;
v___y_1434_ = v___x_1437_;
goto v___jp_1433_;
}
else
{
uint64_t v_hash_1438_; 
v_hash_1438_ = lean_ctor_get_uint64(v_x_1432_, sizeof(void*)*2);
v___y_1434_ = v_hash_1438_;
goto v___jp_1433_;
}
v___jp_1433_:
{
size_t v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_uint64_to_usize(v___y_1434_);
v___x_1436_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1431_, v___x_1435_, v_x_1432_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_res_1441_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1439_, v_x_1440_);
lean_dec(v_x_1440_);
lean_dec_ref(v_x_1439_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x1_1443_, lean_object* v_x2_1444_){
_start:
{
lean_object* v_fst_1445_; uint8_t v___x_1446_; 
v_fst_1445_ = lean_ctor_get(v_x2_1444_, 0);
v___x_1446_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x1_1443_, v_fst_1445_);
if (v___x_1446_ == 0)
{
uint8_t v___x_1447_; 
v___x_1447_ = 1;
return v___x_1447_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = 0;
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x1_1449_, lean_object* v_x2_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x1_1449_, v_x2_1450_);
lean_dec_ref(v_x2_1450_);
lean_dec_ref(v_x1_1449_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_f_1453_, lean_object* v_keys_1454_, lean_object* v_vals_1455_, lean_object* v_i_1456_, lean_object* v_acc_1457_){
_start:
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = lean_array_get_size(v_keys_1454_);
v___x_1459_ = lean_nat_dec_lt(v_i_1456_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_dec(v_i_1456_);
lean_dec(v_f_1453_);
return v_acc_1457_;
}
else
{
lean_object* v_k_1460_; lean_object* v_v_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_k_1460_ = lean_array_fget_borrowed(v_keys_1454_, v_i_1456_);
v_v_1461_ = lean_array_fget_borrowed(v_vals_1455_, v_i_1456_);
lean_inc(v_f_1453_);
lean_inc(v_v_1461_);
lean_inc(v_k_1460_);
v___x_1462_ = lean_apply_3(v_f_1453_, v_acc_1457_, v_k_1460_, v_v_1461_);
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = lean_nat_add(v_i_1456_, v___x_1463_);
lean_dec(v_i_1456_);
v_i_1456_ = v___x_1464_;
v_acc_1457_ = v___x_1462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_f_1466_, lean_object* v_keys_1467_, lean_object* v_vals_1468_, lean_object* v_i_1469_, lean_object* v_acc_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1466_, v_keys_1467_, v_vals_1468_, v_i_1469_, v_acc_1470_);
lean_dec_ref(v_vals_1468_);
lean_dec_ref(v_keys_1467_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1472_, lean_object* v_as_1473_, size_t v_i_1474_, size_t v_stop_1475_, lean_object* v_b_1476_){
_start:
{
lean_object* v___y_1478_; uint8_t v___x_1482_; 
v___x_1482_ = lean_usize_dec_eq(v_i_1474_, v_stop_1475_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_array_uget_borrowed(v_as_1473_, v_i_1474_);
switch(lean_obj_tag(v___x_1483_))
{
case 0:
{
lean_object* v_key_1484_; lean_object* v_val_1485_; lean_object* v___x_1486_; 
v_key_1484_ = lean_ctor_get(v___x_1483_, 0);
v_val_1485_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_f_1472_);
lean_inc(v_val_1485_);
lean_inc(v_key_1484_);
v___x_1486_ = lean_apply_3(v_f_1472_, v_b_1476_, v_key_1484_, v_val_1485_);
v___y_1478_ = v___x_1486_;
goto v___jp_1477_;
}
case 1:
{
lean_object* v_node_1487_; lean_object* v___x_1488_; 
v_node_1487_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_f_1472_);
v___x_1488_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1472_, v_node_1487_, v_b_1476_);
v___y_1478_ = v___x_1488_;
goto v___jp_1477_;
}
default: 
{
v___y_1478_ = v_b_1476_;
goto v___jp_1477_;
}
}
}
else
{
lean_dec(v_f_1472_);
return v_b_1476_;
}
v___jp_1477_:
{
size_t v___x_1479_; size_t v___x_1480_; 
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1474_, v___x_1479_);
v_i_1474_ = v___x_1480_;
v_b_1476_ = v___y_1478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
lean_object* v_es_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_es_1492_ = lean_ctor_get(v_x_1490_, 0);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = lean_array_get_size(v_es_1492_);
v___x_1495_ = lean_nat_dec_lt(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_dec(v_f_1489_);
return v_x_1491_;
}
else
{
size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = lean_usize_of_nat(v___x_1494_);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1489_, v_es_1492_, v___x_1496_, v___x_1497_, v_x_1491_);
return v___x_1498_;
}
}
else
{
lean_object* v_ks_1499_; lean_object* v_vs_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_ks_1499_ = lean_ctor_get(v_x_1490_, 0);
v_vs_1500_ = lean_ctor_get(v_x_1490_, 1);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1489_, v_ks_1499_, v_vs_1500_, v___x_1501_, v_x_1491_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1503_, v_x_1504_, v_x_1505_);
lean_dec_ref(v_x_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1507_, lean_object* v_as_1508_, lean_object* v_i_1509_, lean_object* v_stop_1510_, lean_object* v_b_1511_){
_start:
{
size_t v_i_boxed_1512_; size_t v_stop_boxed_1513_; lean_object* v_res_1514_; 
v_i_boxed_1512_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_stop_boxed_1513_ = lean_unbox_usize(v_stop_1510_);
lean_dec(v_stop_1510_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1507_, v_as_1508_, v_i_boxed_1512_, v_stop_boxed_1513_, v_b_1511_);
lean_dec_ref(v_as_1508_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1515_, lean_object* v_x1_1516_, lean_object* v_x2_1517_, lean_object* v_x3_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_apply_3(v_f_1515_, v_x1_1516_, v_x2_1517_, v_x3_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1520_, lean_object* v_f_1521_, lean_object* v_init_1522_){
_start:
{
lean_object* v___f_1523_; lean_object* v___x_1524_; 
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1523_, 0, v_f_1521_);
v___x_1524_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1523_, v_map_1520_, v_init_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1525_, lean_object* v_f_1526_, lean_object* v_init_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1525_, v_f_1526_, v_init_1527_);
lean_dec_ref(v_map_1525_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1529_, lean_object* v_k_1530_, lean_object* v_v_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_k_1530_);
lean_ctor_set(v___x_1532_, 1, v_v_1531_);
v___x_1533_ = lean_array_push(v_ps_1529_, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1537_){
_start:
{
lean_object* v___f_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___f_1538_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1539_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1540_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1537_, v___f_1538_, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1541_);
lean_dec_ref(v_m_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_fst_1545_; lean_object* v_fst_1546_; uint8_t v___x_1547_; 
v_fst_1545_ = lean_ctor_get(v___y_1543_, 0);
v_fst_1546_ = lean_ctor_get(v___y_1544_, 0);
v___x_1547_ = l_Lean_Name_quickLt(v_fst_1545_, v_fst_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_res_1550_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1548_, v___y_1549_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v___y_1548_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_hi_1552_, lean_object* v_pivot_1553_, lean_object* v_as_1554_, lean_object* v_i_1555_, lean_object* v_k_1556_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_lt(v_k_1556_, v_hi_1552_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec(v_k_1556_);
v___x_1558_ = lean_array_fswap(v_as_1554_, v_i_1555_, v_hi_1552_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_i_1555_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; lean_object* v_fst_1561_; lean_object* v_fst_1562_; uint8_t v___x_1563_; 
v___x_1560_ = lean_array_fget_borrowed(v_as_1554_, v_k_1556_);
v_fst_1561_ = lean_ctor_get(v___x_1560_, 0);
v_fst_1562_ = lean_ctor_get(v_pivot_1553_, 0);
v___x_1563_ = l_Lean_Name_quickLt(v_fst_1561_, v_fst_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_add(v_k_1556_, v___x_1564_);
lean_dec(v_k_1556_);
v_k_1556_ = v___x_1565_;
goto _start;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1567_ = lean_array_fswap(v_as_1554_, v_i_1555_, v_k_1556_);
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_add(v_i_1555_, v___x_1568_);
lean_dec(v_i_1555_);
v___x_1570_ = lean_nat_add(v_k_1556_, v___x_1568_);
lean_dec(v_k_1556_);
v_as_1554_ = v___x_1567_;
v_i_1555_ = v___x_1569_;
v_k_1556_ = v___x_1570_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_hi_1572_, lean_object* v_pivot_1573_, lean_object* v_as_1574_, lean_object* v_i_1575_, lean_object* v_k_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1572_, v_pivot_1573_, v_as_1574_, v_i_1575_, v_k_1576_);
lean_dec_ref(v_pivot_1573_);
lean_dec(v_hi_1572_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_1578_, lean_object* v_as_1579_, lean_object* v_lo_1580_, lean_object* v_hi_1581_){
_start:
{
lean_object* v___y_1583_; uint8_t v___x_1593_; 
v___x_1593_ = lean_nat_dec_lt(v_lo_1580_, v_hi_1581_);
if (v___x_1593_ == 0)
{
lean_dec(v_lo_1580_);
return v_as_1579_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_mid_1596_; lean_object* v___y_1598_; lean_object* v___y_1604_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1594_ = lean_nat_add(v_lo_1580_, v_hi_1581_);
v___x_1595_ = lean_unsigned_to_nat(1u);
v_mid_1596_ = lean_nat_shiftr(v___x_1594_, v___x_1595_);
lean_dec(v___x_1594_);
v___x_1609_ = lean_array_fget_borrowed(v_as_1579_, v_mid_1596_);
v___x_1610_ = lean_array_fget_borrowed(v_as_1579_, v_lo_1580_);
v___x_1611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
v___y_1604_ = v_as_1579_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_array_fswap(v_as_1579_, v_lo_1580_, v_mid_1596_);
v___y_1604_ = v___x_1612_;
goto v___jp_1603_;
}
v___jp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1599_ = lean_array_fget_borrowed(v___y_1598_, v_mid_1596_);
v___x_1600_ = lean_array_fget_borrowed(v___y_1598_, v_hi_1581_);
v___x_1601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1599_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_dec(v_mid_1596_);
v___y_1583_ = v___y_1598_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_array_fswap(v___y_1598_, v_mid_1596_, v_hi_1581_);
lean_dec(v_mid_1596_);
v___y_1583_ = v___x_1602_;
goto v___jp_1582_;
}
}
v___jp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = lean_array_fget_borrowed(v___y_1604_, v_hi_1581_);
v___x_1606_ = lean_array_fget_borrowed(v___y_1604_, v_lo_1580_);
v___x_1607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
v___y_1598_ = v___y_1604_;
goto v___jp_1597_;
}
else
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_array_fswap(v___y_1604_, v_lo_1580_, v_hi_1581_);
v___y_1598_ = v___x_1608_;
goto v___jp_1597_;
}
}
}
v___jp_1582_:
{
lean_object* v_pivot_1584_; lean_object* v___x_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; uint8_t v___x_1588_; 
v_pivot_1584_ = lean_array_fget(v___y_1583_, v_hi_1581_);
lean_inc_n(v_lo_1580_, 2);
v___x_1585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1581_, v_pivot_1584_, v___y_1583_, v_lo_1580_, v_lo_1580_);
lean_dec(v_pivot_1584_);
v_fst_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_fst_1586_);
v_snd_1587_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_snd_1587_);
lean_dec_ref(v___x_1585_);
v___x_1588_ = lean_nat_dec_le(v_hi_1581_, v_fst_1586_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1578_, v_snd_1587_, v_lo_1580_, v_fst_1586_);
v___x_1590_ = lean_unsigned_to_nat(1u);
v___x_1591_ = lean_nat_add(v_fst_1586_, v___x_1590_);
lean_dec(v_fst_1586_);
v_as_1579_ = v___x_1589_;
v_lo_1580_ = v___x_1591_;
goto _start;
}
else
{
lean_dec(v_fst_1586_);
lean_dec(v_lo_1580_);
return v_snd_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_1613_, lean_object* v_as_1614_, lean_object* v_lo_1615_, lean_object* v_hi_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1613_, v_as_1614_, v_lo_1615_, v_hi_1616_);
lean_dec(v_hi_1616_);
lean_dec(v_n_1613_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1620_, lean_object* v_s_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___y_1628_; lean_object* v___y_1629_; uint8_t v___x_1632_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1625_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1621_);
v___x_1626_ = lean_array_get_size(v___x_1625_);
v___x_1632_ = lean_nat_dec_eq(v___x_1626_, v___x_1623_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___y_1636_; uint8_t v___x_1638_; 
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_sub(v___x_1626_, v___x_1633_);
v___x_1638_ = lean_nat_dec_le(v___x_1623_, v___x_1634_);
if (v___x_1638_ == 0)
{
lean_inc(v___x_1634_);
v___y_1636_ = v___x_1634_;
goto v___jp_1635_;
}
else
{
v___y_1636_ = v___x_1623_;
goto v___jp_1635_;
}
v___jp_1635_:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_nat_dec_le(v___y_1636_, v___x_1634_);
if (v___x_1637_ == 0)
{
lean_dec(v___x_1634_);
lean_inc(v___y_1636_);
v___y_1628_ = v___y_1636_;
v___y_1629_ = v___y_1636_;
goto v___jp_1627_;
}
else
{
v___y_1628_ = v___y_1636_;
v___y_1629_ = v___x_1634_;
goto v___jp_1627_;
}
}
}
else
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1624_);
lean_ctor_set(v___x_1639_, 1, v___x_1624_);
lean_ctor_set(v___x_1639_, 2, v___x_1625_);
return v___x_1639_;
}
v___jp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1626_, v___x_1625_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
v___x_1631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1624_);
lean_ctor_set(v___x_1631_, 1, v___x_1624_);
lean_ctor_set(v___x_1631_, 2, v___x_1630_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1640_, lean_object* v_s_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1640_, v_s_1641_, v_x_1642_);
lean_dec(v_x_1642_);
lean_dec_ref(v_s_1641_);
lean_dec_ref(v_x_1640_);
return v_res_1643_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1644_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1649_);
lean_dec_ref(v_x_1649_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v_ks_1655_; lean_object* v_vs_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1680_; 
v_ks_1655_ = lean_ctor_get(v_x_1651_, 0);
v_vs_1656_ = lean_ctor_get(v_x_1651_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_x_1651_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1658_ = v_x_1651_;
v_isShared_1659_ = v_isSharedCheck_1680_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_vs_1656_);
lean_inc(v_ks_1655_);
lean_dec(v_x_1651_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1680_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = lean_array_get_size(v_ks_1655_);
v___x_1661_ = lean_nat_dec_lt(v_x_1652_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_dec(v_x_1652_);
v___x_1662_ = lean_array_push(v_ks_1655_, v_x_1653_);
v___x_1663_ = lean_array_push(v_vs_1656_, v_x_1654_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v___x_1663_);
lean_ctor_set(v___x_1658_, 0, v___x_1662_);
v___x_1665_ = v___x_1658_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
else
{
lean_object* v_k_x27_1667_; uint8_t v___x_1668_; 
v_k_x27_1667_ = lean_array_fget_borrowed(v_ks_1655_, v_x_1652_);
v___x_1668_ = lean_name_eq(v_x_1653_, v_k_x27_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1670_; 
if (v_isShared_1659_ == 0)
{
v___x_1670_ = v___x_1658_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_ks_1655_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_vs_1656_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_add(v_x_1652_, v___x_1671_);
lean_dec(v_x_1652_);
v_x_1651_ = v___x_1670_;
v_x_1652_ = v___x_1672_;
goto _start;
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = lean_array_fset(v_ks_1655_, v_x_1652_, v_x_1653_);
v___x_1676_ = lean_array_fset(v_vs_1656_, v_x_1652_, v_x_1654_);
lean_dec(v_x_1652_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v___x_1676_);
lean_ctor_set(v___x_1658_, 0, v___x_1675_);
v___x_1678_ = v___x_1658_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_n_1681_, lean_object* v_k_1682_, lean_object* v_v_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_n_1681_, v___x_1684_, v_k_1682_, v_v_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_x_1687_, size_t v_x_1688_, size_t v_x_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
lean_object* v_es_1692_; size_t v___x_1693_; size_t v___x_1694_; lean_object* v_j_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_es_1692_ = lean_ctor_get(v_x_1687_, 0);
v___x_1693_ = ((size_t)31ULL);
v___x_1694_ = lean_usize_land(v_x_1688_, v___x_1693_);
v_j_1695_ = lean_usize_to_nat(v___x_1694_);
v___x_1696_ = lean_array_get_size(v_es_1692_);
v___x_1697_ = lean_nat_dec_lt(v_j_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_dec(v_j_1695_);
lean_dec(v_x_1691_);
lean_dec(v_x_1690_);
return v_x_1687_;
}
else
{
lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1736_; 
lean_inc_ref(v_es_1692_);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1737_);
v___x_1699_ = v_x_1687_;
v_isShared_1700_ = v_isSharedCheck_1736_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v_x_1687_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1736_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_v_1701_; lean_object* v___x_1702_; lean_object* v_xs_x27_1703_; lean_object* v___y_1705_; 
v_v_1701_ = lean_array_fget(v_es_1692_, v_j_1695_);
v___x_1702_ = lean_box(0);
v_xs_x27_1703_ = lean_array_fset(v_es_1692_, v_j_1695_, v___x_1702_);
switch(lean_obj_tag(v_v_1701_))
{
case 0:
{
lean_object* v_key_1710_; lean_object* v_val_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1721_; 
v_key_1710_ = lean_ctor_get(v_v_1701_, 0);
v_val_1711_ = lean_ctor_get(v_v_1701_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_v_1701_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1713_ = v_v_1701_;
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_val_1711_);
lean_inc(v_key_1710_);
lean_dec(v_v_1701_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_name_eq(v_x_1690_, v_key_1710_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_del_object(v___x_1713_);
v___x_1716_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1710_, v_val_1711_, v_x_1690_, v_x_1691_);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
v___y_1705_ = v___x_1717_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1719_; 
lean_dec(v_val_1711_);
lean_dec(v_key_1710_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v_x_1691_);
lean_ctor_set(v___x_1713_, 0, v_x_1690_);
v___x_1719_ = v___x_1713_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_x_1690_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_x_1691_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
v___y_1705_ = v___x_1719_;
goto v___jp_1704_;
}
}
}
}
case 1:
{
lean_object* v_node_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1734_; 
v_node_1722_ = lean_ctor_get(v_v_1701_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_v_1701_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1724_ = v_v_1701_;
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_node_1722_);
lean_dec(v_v_1701_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1726_ = ((size_t)5ULL);
v___x_1727_ = lean_usize_shift_right(v_x_1688_, v___x_1726_);
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_x_1689_, v___x_1728_);
v___x_1730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_node_1722_, v___x_1727_, v___x_1729_, v_x_1690_, v_x_1691_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1730_);
v___x_1732_ = v___x_1724_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
v___y_1705_ = v___x_1732_;
goto v___jp_1704_;
}
}
}
default: 
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v_x_1690_);
lean_ctor_set(v___x_1735_, 1, v_x_1691_);
v___y_1705_ = v___x_1735_;
goto v___jp_1704_;
}
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = lean_array_fset(v_xs_x27_1703_, v_j_1695_, v___y_1705_);
lean_dec(v_j_1695_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1706_);
v___x_1708_ = v___x_1699_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
lean_object* v_ks_1738_; lean_object* v_vs_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1757_; 
v_ks_1738_ = lean_ctor_get(v_x_1687_, 0);
v_vs_1739_ = lean_ctor_get(v_x_1687_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1741_ = v_x_1687_;
v_isShared_1742_ = v_isSharedCheck_1757_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_vs_1739_);
lean_inc(v_ks_1738_);
lean_dec(v_x_1687_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1757_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_ks_1738_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_vs_1739_);
v___x_1744_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v_newNode_1745_; size_t v___x_1746_; uint8_t v___x_1747_; 
v_newNode_1745_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v___x_1744_, v_x_1690_, v_x_1691_);
v___x_1746_ = ((size_t)7ULL);
v___x_1747_ = lean_usize_dec_le(v___x_1746_, v_x_1689_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1748_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1745_);
v___x_1749_ = lean_unsigned_to_nat(4u);
v___x_1750_ = lean_nat_dec_lt(v___x_1748_, v___x_1749_);
lean_dec(v___x_1748_);
if (v___x_1750_ == 0)
{
lean_object* v_ks_1751_; lean_object* v_vs_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_ks_1751_ = lean_ctor_get(v_newNode_1745_, 0);
lean_inc_ref(v_ks_1751_);
v_vs_1752_ = lean_ctor_get(v_newNode_1745_, 1);
lean_inc_ref(v_vs_1752_);
lean_dec_ref(v_newNode_1745_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0);
v___x_1755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_x_1689_, v_ks_1751_, v_vs_1752_, v___x_1753_, v___x_1754_);
lean_dec_ref(v_vs_1752_);
lean_dec_ref(v_ks_1751_);
return v___x_1755_;
}
else
{
return v_newNode_1745_;
}
}
else
{
return v_newNode_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t v_depth_1758_, lean_object* v_keys_1759_, lean_object* v_vals_1760_, lean_object* v_i_1761_, lean_object* v_entries_1762_){
_start:
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_array_get_size(v_keys_1759_);
v___x_1764_ = lean_nat_dec_lt(v_i_1761_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec(v_i_1761_);
return v_entries_1762_;
}
else
{
lean_object* v_k_1765_; lean_object* v_v_1766_; uint64_t v___y_1768_; 
v_k_1765_ = lean_array_fget_borrowed(v_keys_1759_, v_i_1761_);
v_v_1766_ = lean_array_fget_borrowed(v_vals_1760_, v_i_1761_);
if (lean_obj_tag(v_k_1765_) == 0)
{
uint64_t v___x_1779_; 
v___x_1779_ = 1723ULL;
v___y_1768_ = v___x_1779_;
goto v___jp_1767_;
}
else
{
uint64_t v_hash_1780_; 
v_hash_1780_ = lean_ctor_get_uint64(v_k_1765_, sizeof(void*)*2);
v___y_1768_ = v_hash_1780_;
goto v___jp_1767_;
}
v___jp_1767_:
{
size_t v_h_1769_; size_t v___x_1770_; lean_object* v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; size_t v___x_1774_; size_t v_h_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_h_1769_ = lean_uint64_to_usize(v___y_1768_);
v___x_1770_ = ((size_t)5ULL);
v___x_1771_ = lean_unsigned_to_nat(1u);
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_sub(v_depth_1758_, v___x_1772_);
v___x_1774_ = lean_usize_mul(v___x_1770_, v___x_1773_);
v_h_1775_ = lean_usize_shift_right(v_h_1769_, v___x_1774_);
v___x_1776_ = lean_nat_add(v_i_1761_, v___x_1771_);
lean_dec(v_i_1761_);
lean_inc(v_v_1766_);
lean_inc(v_k_1765_);
v___x_1777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_entries_1762_, v_h_1775_, v_depth_1758_, v_k_1765_, v_v_1766_);
v_i_1761_ = v___x_1776_;
v_entries_1762_ = v___x_1777_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_1781_, lean_object* v_keys_1782_, lean_object* v_vals_1783_, lean_object* v_i_1784_, lean_object* v_entries_1785_){
_start:
{
size_t v_depth_boxed_1786_; lean_object* v_res_1787_; 
v_depth_boxed_1786_ = lean_unbox_usize(v_depth_1781_);
lean_dec(v_depth_1781_);
v_res_1787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_boxed_1786_, v_keys_1782_, v_vals_1783_, v_i_1784_, v_entries_1785_);
lean_dec_ref(v_vals_1783_);
lean_dec_ref(v_keys_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
size_t v_x_1532__boxed_1793_; size_t v_x_1533__boxed_1794_; lean_object* v_res_1795_; 
v_x_1532__boxed_1793_ = lean_unbox_usize(v_x_1789_);
lean_dec(v_x_1789_);
v_x_1533__boxed_1794_ = lean_unbox_usize(v_x_1790_);
lean_dec(v_x_1790_);
v_res_1795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1788_, v_x_1532__boxed_1793_, v_x_1533__boxed_1794_, v_x_1791_, v_x_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
uint64_t v___y_1800_; 
if (lean_obj_tag(v_x_1797_) == 0)
{
uint64_t v___x_1804_; 
v___x_1804_ = 1723ULL;
v___y_1800_ = v___x_1804_;
goto v___jp_1799_;
}
else
{
uint64_t v_hash_1805_; 
v_hash_1805_ = lean_ctor_get_uint64(v_x_1797_, sizeof(void*)*2);
v___y_1800_ = v_hash_1805_;
goto v___jp_1799_;
}
v___jp_1799_:
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_uint64_to_usize(v___y_1800_);
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1796_, v___x_1801_, v___x_1802_, v_x_1797_, v_x_1798_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v_fst_1808_; lean_object* v_snd_1809_; lean_object* v___x_1810_; 
v_fst_1808_ = lean_ctor_get(v_x_1807_, 0);
lean_inc(v_fst_1808_);
v_snd_1809_ = lean_ctor_get(v_x_1807_, 1);
lean_inc(v_snd_1809_);
lean_dec_ref(v_x_1807_);
v___x_1810_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1806_, v_fst_1808_, v_snd_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1844_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1846_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
uint8_t v___x_1850_; 
v___x_1850_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1848_, v_x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_){
_start:
{
uint8_t v_res_1854_; lean_object* v_r_1855_; 
v_res_1854_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1851_, v_x_1852_, v_x_1853_);
lean_dec(v_x_1853_);
lean_dec_ref(v_x_1852_);
v_r_1855_ = lean_box(v_res_1854_);
return v_r_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1856_, lean_object* v_m_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_m_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1859_, v_m_1860_);
lean_dec_ref(v_m_1860_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1862_, lean_object* v_as_1863_, lean_object* v_lo_1864_, lean_object* v_hi_1865_, lean_object* v_w_1866_, lean_object* v_hlo_1867_, lean_object* v_hhi_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1862_, v_as_1863_, v_lo_1864_, v_hi_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1870_, lean_object* v_as_1871_, lean_object* v_lo_1872_, lean_object* v_hi_1873_, lean_object* v_w_1874_, lean_object* v_hlo_1875_, lean_object* v_hhi_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1870_, v_as_1871_, v_lo_1872_, v_hi_1873_, v_w_1874_, v_hlo_1875_, v_hhi_1876_);
lean_dec(v_hi_1873_);
lean_dec(v_n_1870_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1879_, v_x_1880_, v_x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1883_, lean_object* v_x_1884_, size_t v_x_1885_, lean_object* v_x_1886_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1884_, v_x_1885_, v_x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
size_t v_x_1832__boxed_1892_; uint8_t v_res_1893_; lean_object* v_r_1894_; 
v_x_1832__boxed_1892_ = lean_unbox_usize(v_x_1890_);
lean_dec(v_x_1890_);
v_res_1893_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1888_, v_x_1889_, v_x_1832__boxed_1892_, v_x_1891_);
lean_dec(v_x_1891_);
lean_dec_ref(v_x_1889_);
v_r_1894_ = lean_box(v_res_1893_);
return v_r_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_map_1897_, lean_object* v_f_1898_, lean_object* v_init_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1897_, v_f_1898_, v_init_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_map_1903_, lean_object* v_f_1904_, lean_object* v_init_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1901_, v_00_u03b2_1902_, v_map_1903_, v_f_1904_, v_init_1905_);
lean_dec_ref(v_map_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_n_1907_, lean_object* v_lo_1908_, lean_object* v_hi_1909_, lean_object* v_hhi_1910_, lean_object* v_pivot_1911_, lean_object* v_as_1912_, lean_object* v_i_1913_, lean_object* v_k_1914_, lean_object* v_ilo_1915_, lean_object* v_ik_1916_, lean_object* v_w_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1909_, v_pivot_1911_, v_as_1912_, v_i_1913_, v_k_1914_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_n_1919_, lean_object* v_lo_1920_, lean_object* v_hi_1921_, lean_object* v_hhi_1922_, lean_object* v_pivot_1923_, lean_object* v_as_1924_, lean_object* v_i_1925_, lean_object* v_k_1926_, lean_object* v_ilo_1927_, lean_object* v_ik_1928_, lean_object* v_w_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(v_n_1919_, v_lo_1920_, v_hi_1921_, v_hhi_1922_, v_pivot_1923_, v_as_1924_, v_i_1925_, v_k_1926_, v_ilo_1927_, v_ik_1928_, v_w_1929_);
lean_dec_ref(v_pivot_1923_);
lean_dec(v_hi_1921_);
lean_dec(v_lo_1920_);
lean_dec(v_n_1919_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1931_, lean_object* v_x_1932_, size_t v_x_1933_, size_t v_x_1934_, lean_object* v_x_1935_, lean_object* v_x_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1932_, v_x_1933_, v_x_1934_, v_x_1935_, v_x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_, lean_object* v_x_1943_){
_start:
{
size_t v_x_1847__boxed_1944_; size_t v_x_1848__boxed_1945_; lean_object* v_res_1946_; 
v_x_1847__boxed_1944_ = lean_unbox_usize(v_x_1940_);
lean_dec(v_x_1940_);
v_x_1848__boxed_1945_ = lean_unbox_usize(v_x_1941_);
lean_dec(v_x_1941_);
v_res_1946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1938_, v_x_1939_, v_x_1847__boxed_1944_, v_x_1848__boxed_1945_, v_x_1942_, v_x_1943_);
return v_res_1946_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1947_, lean_object* v_keys_1948_, lean_object* v_vals_1949_, lean_object* v_heq_1950_, lean_object* v_i_1951_, lean_object* v_k_1952_){
_start:
{
uint8_t v___x_1953_; 
v___x_1953_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1948_, v_i_1951_, v_k_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1954_, lean_object* v_keys_1955_, lean_object* v_vals_1956_, lean_object* v_heq_1957_, lean_object* v_i_1958_, lean_object* v_k_1959_){
_start:
{
uint8_t v_res_1960_; lean_object* v_r_1961_; 
v_res_1960_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1954_, v_keys_1955_, v_vals_1956_, v_heq_1957_, v_i_1958_, v_k_1959_);
lean_dec(v_k_1959_);
lean_dec_ref(v_vals_1956_);
lean_dec_ref(v_keys_1955_);
v_r_1961_ = lean_box(v_res_1960_);
return v_r_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1962_, lean_object* v_f_1963_, lean_object* v_init_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1963_, v_map_1962_, v_init_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1966_, lean_object* v_f_1967_, lean_object* v_init_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1966_, v_f_1967_, v_init_1968_);
lean_dec_ref(v_map_1966_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1970_, lean_object* v_00_u03b2_1971_, lean_object* v_map_1972_, lean_object* v_f_1973_, lean_object* v_init_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1973_, v_map_1972_, v_init_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1976_, lean_object* v_00_u03b2_1977_, lean_object* v_map_1978_, lean_object* v_f_1979_, lean_object* v_init_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1976_, v_00_u03b2_1977_, v_map_1978_, v_f_1979_, v_init_1980_);
lean_dec_ref(v_map_1978_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1982_, lean_object* v_n_1983_, lean_object* v_k_1984_, lean_object* v_v_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_n_1983_, v_k_1984_, v_v_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1987_, size_t v_depth_1988_, lean_object* v_keys_1989_, lean_object* v_vals_1990_, lean_object* v_heq_1991_, lean_object* v_i_1992_, lean_object* v_entries_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_1988_, v_keys_1989_, v_vals_1990_, v_i_1992_, v_entries_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1995_, lean_object* v_depth_1996_, lean_object* v_keys_1997_, lean_object* v_vals_1998_, lean_object* v_heq_1999_, lean_object* v_i_2000_, lean_object* v_entries_2001_){
_start:
{
size_t v_depth_boxed_2002_; lean_object* v_res_2003_; 
v_depth_boxed_2002_ = lean_unbox_usize(v_depth_1996_);
lean_dec(v_depth_1996_);
v_res_2003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(v_00_u03b2_1995_, v_depth_boxed_2002_, v_keys_1997_, v_vals_1998_, v_heq_1999_, v_i_2000_, v_entries_2001_);
lean_dec_ref(v_vals_1998_);
lean_dec_ref(v_keys_1997_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2004_, lean_object* v_00_u03b1_2005_, lean_object* v_00_u03b2_2006_, lean_object* v_f_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2007_, v_x_2008_, v_x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2011_, lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_f_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_2011_, v_00_u03b1_2012_, v_00_u03b2_2013_, v_f_2014_, v_x_2015_, v_x_2016_);
lean_dec_ref(v_x_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_x_2019_, v_x_2020_, v_x_2021_, v_x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_00_u03c3_2026_, lean_object* v_f_2027_, lean_object* v_as_2028_, size_t v_i_2029_, size_t v_stop_2030_, lean_object* v_b_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_2027_, v_as_2028_, v_i_2029_, v_stop_2030_, v_b_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_00_u03c3_2035_, lean_object* v_f_2036_, lean_object* v_as_2037_, lean_object* v_i_2038_, lean_object* v_stop_2039_, lean_object* v_b_2040_){
_start:
{
size_t v_i_boxed_2041_; size_t v_stop_boxed_2042_; lean_object* v_res_2043_; 
v_i_boxed_2041_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_stop_boxed_2042_ = lean_unbox_usize(v_stop_2039_);
lean_dec(v_stop_2039_);
v_res_2043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_2033_, v_00_u03b2_2034_, v_00_u03c3_2035_, v_f_2036_, v_as_2037_, v_i_boxed_2041_, v_stop_boxed_2042_, v_b_2040_);
lean_dec_ref(v_as_2037_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03c3_2044_, lean_object* v_00_u03b1_2045_, lean_object* v_00_u03b2_2046_, lean_object* v_f_2047_, lean_object* v_keys_2048_, lean_object* v_vals_2049_, lean_object* v_heq_2050_, lean_object* v_i_2051_, lean_object* v_acc_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_2047_, v_keys_2048_, v_vals_2049_, v_i_2051_, v_acc_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03c3_2054_, lean_object* v_00_u03b1_2055_, lean_object* v_00_u03b2_2056_, lean_object* v_f_2057_, lean_object* v_keys_2058_, lean_object* v_vals_2059_, lean_object* v_heq_2060_, lean_object* v_i_2061_, lean_object* v_acc_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(v_00_u03c3_2054_, v_00_u03b1_2055_, v_00_u03b2_2056_, v_f_2057_, v_keys_2058_, v_vals_2059_, v_heq_2060_, v_i_2061_, v_acc_2062_);
lean_dec_ref(v_vals_2059_);
lean_dec_ref(v_keys_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2064_, lean_object* v_fid_2065_, lean_object* v_v_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v_toEnvExtension_2068_; lean_object* v_asyncMode_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2067_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2068_ = lean_ctor_get(v___x_2067_, 0);
v_asyncMode_2069_ = lean_ctor_get(v_toEnvExtension_2068_, 2);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_fid_2065_);
lean_ctor_set(v___x_2070_, 1, v_v_2066_);
v___x_2071_ = lean_box(0);
v___x_2072_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2067_, v_env_2064_, v___x_2070_, v_asyncMode_2069_, v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2073_, lean_object* v_vals_2074_, lean_object* v_i_2075_, lean_object* v_k_2076_){
_start:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_array_get_size(v_keys_2073_);
v___x_2078_ = lean_nat_dec_lt(v_i_2075_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
lean_dec(v_i_2075_);
v___x_2079_ = lean_box(0);
return v___x_2079_;
}
else
{
lean_object* v_k_x27_2080_; uint8_t v___x_2081_; 
v_k_x27_2080_ = lean_array_fget_borrowed(v_keys_2073_, v_i_2075_);
v___x_2081_ = lean_name_eq(v_k_2076_, v_k_x27_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = lean_nat_add(v_i_2075_, v___x_2082_);
lean_dec(v_i_2075_);
v_i_2075_ = v___x_2083_;
goto _start;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_array_fget_borrowed(v_vals_2074_, v_i_2075_);
lean_dec(v_i_2075_);
lean_inc(v___x_2085_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2087_, lean_object* v_vals_2088_, lean_object* v_i_2089_, lean_object* v_k_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2087_, v_vals_2088_, v_i_2089_, v_k_2090_);
lean_dec(v_k_2090_);
lean_dec_ref(v_vals_2088_);
lean_dec_ref(v_keys_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2092_, size_t v_x_2093_, lean_object* v_x_2094_){
_start:
{
if (lean_obj_tag(v_x_2092_) == 0)
{
lean_object* v_es_2095_; lean_object* v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; lean_object* v_j_2099_; lean_object* v___x_2100_; 
v_es_2095_ = lean_ctor_get(v_x_2092_, 0);
v___x_2096_ = lean_box(2);
v___x_2097_ = ((size_t)31ULL);
v___x_2098_ = lean_usize_land(v_x_2093_, v___x_2097_);
v_j_2099_ = lean_usize_to_nat(v___x_2098_);
v___x_2100_ = lean_array_get_borrowed(v___x_2096_, v_es_2095_, v_j_2099_);
lean_dec(v_j_2099_);
switch(lean_obj_tag(v___x_2100_))
{
case 0:
{
lean_object* v_key_2101_; lean_object* v_val_2102_; uint8_t v___x_2103_; 
v_key_2101_ = lean_ctor_get(v___x_2100_, 0);
v_val_2102_ = lean_ctor_get(v___x_2100_, 1);
v___x_2103_ = lean_name_eq(v_x_2094_, v_key_2101_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_box(0);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; 
lean_inc(v_val_2102_);
v___x_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_val_2102_);
return v___x_2105_;
}
}
case 1:
{
lean_object* v_node_2106_; size_t v___x_2107_; size_t v___x_2108_; 
v_node_2106_ = lean_ctor_get(v___x_2100_, 0);
v___x_2107_ = ((size_t)5ULL);
v___x_2108_ = lean_usize_shift_right(v_x_2093_, v___x_2107_);
v_x_2092_ = v_node_2106_;
v_x_2093_ = v___x_2108_;
goto _start;
}
default: 
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_box(0);
return v___x_2110_;
}
}
}
else
{
lean_object* v_ks_2111_; lean_object* v_vs_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_ks_2111_ = lean_ctor_get(v_x_2092_, 0);
v_vs_2112_ = lean_ctor_get(v_x_2092_, 1);
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2111_, v_vs_2112_, v___x_2113_, v_x_2094_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
size_t v_x_408__boxed_2118_; lean_object* v_res_2119_; 
v_x_408__boxed_2118_ = lean_unbox_usize(v_x_2116_);
lean_dec(v_x_2116_);
v_res_2119_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2115_, v_x_408__boxed_2118_, v_x_2117_);
lean_dec(v_x_2117_);
lean_dec_ref(v_x_2115_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2120_, lean_object* v_x_2121_){
_start:
{
uint64_t v___y_2123_; 
if (lean_obj_tag(v_x_2121_) == 0)
{
uint64_t v___x_2126_; 
v___x_2126_ = 1723ULL;
v___y_2123_ = v___x_2126_;
goto v___jp_2122_;
}
else
{
uint64_t v_hash_2127_; 
v_hash_2127_ = lean_ctor_get_uint64(v_x_2121_, sizeof(void*)*2);
v___y_2123_ = v_hash_2127_;
goto v___jp_2122_;
}
v___jp_2122_:
{
size_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_uint64_to_usize(v___y_2123_);
v___x_2125_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2120_, v___x_2124_, v_x_2121_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2128_, lean_object* v_x_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2128_, v_x_2129_);
lean_dec(v_x_2129_);
lean_dec_ref(v_x_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2131_, lean_object* v_k_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_m_2137_; lean_object* v_a_2138_; uint8_t v___x_2139_; 
v___x_2135_ = lean_nat_add(v_x_2133_, v_x_2134_);
v___x_2136_ = lean_unsigned_to_nat(1u);
v_m_2137_ = lean_nat_shiftr(v___x_2135_, v___x_2136_);
lean_dec(v___x_2135_);
v_a_2138_ = lean_array_fget_borrowed(v_as_2131_, v_m_2137_);
v___x_2139_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2138_, v_k_2132_);
if (v___x_2139_ == 0)
{
uint8_t v___x_2140_; 
lean_dec(v_x_2134_);
v___x_2140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2132_, v_a_2138_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec(v_m_2137_);
lean_dec(v_x_2133_);
lean_inc(v_a_2138_);
v___x_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_a_2138_);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; uint8_t v___y_2146_; 
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_nat_dec_eq(v_m_2137_, v___x_2142_);
v___x_2144_ = lean_nat_sub(v_m_2137_, v___x_2136_);
lean_dec(v_m_2137_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_nat_dec_lt(v___x_2144_, v_x_2133_);
v___y_2146_ = v___x_2149_;
goto v___jp_2145_;
}
else
{
v___y_2146_ = v___x_2143_;
goto v___jp_2145_;
}
v___jp_2145_:
{
if (v___y_2146_ == 0)
{
v_x_2134_ = v___x_2144_;
goto _start;
}
else
{
lean_object* v___x_2148_; 
lean_dec(v___x_2144_);
lean_dec(v_x_2133_);
v___x_2148_ = lean_box(0);
return v___x_2148_;
}
}
}
}
else
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
lean_dec(v_x_2133_);
v___x_2150_ = lean_nat_add(v_m_2137_, v___x_2136_);
lean_dec(v_m_2137_);
v___x_2151_ = lean_nat_dec_le(v___x_2150_, v_x_2134_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_dec(v___x_2150_);
lean_dec(v_x_2134_);
v___x_2152_ = lean_box(0);
return v___x_2152_;
}
else
{
v_x_2133_ = v___x_2150_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2154_, lean_object* v_k_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2154_, v_k_2155_, v_x_2156_, v_x_2157_);
lean_dec_ref(v_k_2155_);
lean_dec_ref(v_as_2154_);
return v_res_2158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2162_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2163_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2162_, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2167_, lean_object* v_fid_2168_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2178_; 
v___x_2169_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2170_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2178_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2167_, v_fid_2168_);
if (lean_obj_tag(v___x_2178_) == 0)
{
goto v___jp_2171_;
}
else
{
lean_object* v_val_2179_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_val_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2201_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_2169_, v___x_2170_, v_env_2167_, v_val_2179_);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = lean_array_get_size(v___x_2201_);
v___x_2204_ = lean_nat_dec_lt(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_dec_ref(v___x_2201_);
goto v___jp_2180_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_nat_sub(v___x_2203_, v___x_2205_);
v___x_2207_ = lean_nat_dec_le(v___x_2202_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_dec(v___x_2206_);
lean_dec_ref(v___x_2201_);
goto v___jp_2180_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_box(0);
lean_inc(v_fid_2168_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_fid_2168_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2201_, v___x_2209_, v___x_2202_, v___x_2206_);
lean_dec_ref_known(v___x_2209_, 2);
lean_dec_ref(v___x_2201_);
if (lean_obj_tag(v___x_2210_) == 0)
{
goto v___jp_2180_;
}
else
{
lean_object* v_val_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_val_2179_);
lean_dec(v_fid_2168_);
lean_dec_ref(v_env_2167_);
v_val_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2219_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_val_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2219_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_snd_2215_; lean_object* v___x_2217_; 
v_snd_2215_ = lean_ctor_get(v_val_2211_, 1);
lean_inc(v_snd_2215_);
lean_dec(v_val_2211_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_snd_2215_);
v___x_2217_ = v___x_2213_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_snd_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
v___jp_2180_:
{
uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2181_ = 0;
v___x_2182_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2169_, v___x_2170_, v_env_2167_, v_val_2179_, v___x_2181_);
lean_dec(v_val_2179_);
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = lean_array_get_size(v___x_2182_);
v___x_2185_ = lean_nat_dec_lt(v___x_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_dec_ref(v___x_2182_);
goto v___jp_2171_;
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_sub(v___x_2184_, v___x_2186_);
v___x_2188_ = lean_nat_dec_le(v___x_2183_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_dec(v___x_2187_);
lean_dec_ref(v___x_2182_);
goto v___jp_2171_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = lean_box(0);
lean_inc(v_fid_2168_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_fid_2168_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2182_, v___x_2190_, v___x_2183_, v___x_2187_);
lean_dec_ref_known(v___x_2190_, 2);
lean_dec_ref(v___x_2182_);
if (lean_obj_tag(v___x_2191_) == 0)
{
goto v___jp_2171_;
}
else
{
lean_object* v_val_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_fid_2168_);
lean_dec_ref(v_env_2167_);
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_val_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_snd_2196_; lean_object* v___x_2198_; 
v_snd_2196_ = lean_ctor_get(v_val_2192_, 1);
lean_inc(v_snd_2196_);
lean_dec(v_val_2192_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_snd_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_snd_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
}
v___jp_2171_:
{
lean_object* v_toEnvExtension_2172_; lean_object* v_asyncMode_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_snd_2176_; lean_object* v___x_2177_; 
v_toEnvExtension_2172_ = lean_ctor_get(v___x_2170_, 0);
v_asyncMode_2173_ = lean_ctor_get(v_toEnvExtension_2172_, 2);
v___x_2174_ = lean_box(0);
v___x_2175_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2169_, v___x_2170_, v_env_2167_, v_asyncMode_2173_, v___x_2174_);
v_snd_2176_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_snd_2176_);
lean_dec(v___x_2175_);
v___x_2177_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2176_, v_fid_2168_);
lean_dec(v_fid_2168_);
lean_dec(v_snd_2176_);
return v___x_2177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2221_, v_x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2224_, v_x_2225_, v_x_2226_);
lean_dec(v_x_2226_);
lean_dec_ref(v_x_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2228_, lean_object* v_k_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2228_, v_k_2229_, v_x_2230_, v_x_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2234_, lean_object* v_k_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2234_, v_k_2235_, v_x_2236_, v_x_2237_, v_x_2238_);
lean_dec_ref(v_k_2235_);
lean_dec_ref(v_as_2234_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2240_, lean_object* v_x_2241_, size_t v_x_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2241_, v_x_2242_, v_x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2245_, lean_object* v_x_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
size_t v_x_646__boxed_2249_; lean_object* v_res_2250_; 
v_x_646__boxed_2249_ = lean_unbox_usize(v_x_2247_);
lean_dec(v_x_2247_);
v_res_2250_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2245_, v_x_2246_, v_x_646__boxed_2249_, v_x_2248_);
lean_dec(v_x_2248_);
lean_dec_ref(v_x_2246_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2251_, lean_object* v_keys_2252_, lean_object* v_vals_2253_, lean_object* v_heq_2254_, lean_object* v_i_2255_, lean_object* v_k_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2252_, v_vals_2253_, v_i_2255_, v_k_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2258_, lean_object* v_keys_2259_, lean_object* v_vals_2260_, lean_object* v_heq_2261_, lean_object* v_i_2262_, lean_object* v_k_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2258_, v_keys_2259_, v_vals_2260_, v_heq_2261_, v_i_2262_, v_k_2263_);
lean_dec(v_k_2263_);
lean_dec_ref(v_vals_2260_);
lean_dec_ref(v_keys_2259_);
return v_res_2264_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2268_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2269_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2268_, v___x_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v_assignments_2274_; lean_object* v_currFnIdx_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2273_ = lean_st_ref_get(v_a_2271_);
v_assignments_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc_ref(v_assignments_2274_);
lean_dec(v___x_2273_);
v_currFnIdx_2275_ = lean_ctor_get(v_a_2270_, 1);
v___x_2276_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2277_ = lean_array_get(v___x_2276_, v_assignments_2274_, v_currFnIdx_2275_);
lean_dec_ref(v_assignments_2274_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2279_, v_a_2280_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2283_, v_a_2284_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; lean_object* v_funVals_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2302_ = lean_st_ref_get(v_a_2300_);
v_funVals_2303_ = lean_ctor_get(v___x_2302_, 1);
lean_inc_ref(v_funVals_2303_);
lean_dec(v___x_2302_);
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_array_get(v___x_2304_, v_funVals_2303_, v_funIdx_2299_);
lean_dec_ref(v_funVals_2303_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2307_, v_a_2308_);
lean_dec(v_a_2308_);
lean_dec(v_funIdx_2307_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2311_, v_a_2313_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_funIdx_2320_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2329_, lean_object* v_as_2330_, lean_object* v_j_2331_){
_start:
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = lean_array_get_size(v_as_2330_);
v___x_2333_ = lean_nat_dec_lt(v_j_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; 
lean_dec(v_j_2331_);
v___x_2334_ = lean_box(0);
return v___x_2334_;
}
else
{
lean_object* v___x_2335_; lean_object* v_toSignature_2336_; lean_object* v_name_2337_; uint8_t v___x_2338_; 
v___x_2335_ = lean_array_fget_borrowed(v_as_2330_, v_j_2331_);
v_toSignature_2336_ = lean_ctor_get(v___x_2335_, 0);
v_name_2337_ = lean_ctor_get(v_toSignature_2336_, 0);
v___x_2338_ = lean_name_eq(v_name_2337_, v_declName_2329_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = lean_nat_add(v_j_2331_, v___x_2339_);
lean_dec(v_j_2331_);
v_j_2331_ = v___x_2340_;
goto _start;
}
else
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2342_, 0, v_j_2331_);
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2343_, lean_object* v_as_2344_, lean_object* v_j_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2343_, v_as_2344_, v_j_2345_);
lean_dec_ref(v_as_2344_);
lean_dec(v_declName_2343_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_decls_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_decls_2351_ = lean_ctor_get(v_a_2348_, 0);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2347_, v_decls_2351_, v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
else
{
lean_object* v_val_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2372_; 
v_val_2356_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2358_ = v___x_2353_;
v_isShared_2359_ = v_isSharedCheck_2372_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_val_2356_);
lean_dec(v___x_2353_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2372_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2371_; 
v___x_2360_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2356_, v_a_2349_);
lean_dec(v_val_2356_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2371_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2371_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v_a_2361_);
v___x_2366_ = v___x_2358_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2366_);
v___x_2368_ = v___x_2363_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_declName_2373_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2378_, v_a_2379_, v_a_2380_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_declName_2387_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v_currFnIdx_2401_; lean_object* v_assignments_2402_; lean_object* v_funVals_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2421_; 
v___x_2400_ = lean_st_ref_take(v_a_2398_);
v_currFnIdx_2401_ = lean_ctor_get(v_a_2397_, 1);
v_assignments_2402_ = lean_ctor_get(v___x_2400_, 0);
v_funVals_2403_ = lean_ctor_get(v___x_2400_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2405_ = v___x_2400_;
v_isShared_2406_ = v_isSharedCheck_2421_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_funVals_2403_);
lean_inc(v_assignments_2402_);
lean_dec(v___x_2400_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2421_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___y_2409_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2407_ = lean_box(0);
v___x_2415_ = lean_array_get_size(v_assignments_2402_);
v___x_2416_ = lean_nat_dec_lt(v_currFnIdx_2401_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_dec_ref(v_f_2396_);
v___y_2409_ = v_assignments_2402_;
goto v___jp_2408_;
}
else
{
lean_object* v_v_2417_; lean_object* v_xs_x27_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_v_2417_ = lean_array_fget(v_assignments_2402_, v_currFnIdx_2401_);
v_xs_x27_2418_ = lean_array_fset(v_assignments_2402_, v_currFnIdx_2401_, v___x_2407_);
v___x_2419_ = lean_apply_1(v_f_2396_, v_v_2417_);
v___x_2420_ = lean_array_fset(v_xs_x27_2418_, v_currFnIdx_2401_, v___x_2419_);
v___y_2409_ = v___x_2420_;
goto v___jp_2408_;
}
v___jp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___y_2409_);
v___x_2411_ = v___x_2405_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___y_2409_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_funVals_2403_);
v___x_2411_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_st_ref_put(v_a_2398_, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2407_);
return v___x_2413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2427_, v_a_2428_, v_a_2429_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2445_, lean_object* v_fallback_2446_, lean_object* v_x_2447_){
_start:
{
if (lean_obj_tag(v_x_2447_) == 0)
{
lean_inc(v_fallback_2446_);
return v_fallback_2446_;
}
else
{
lean_object* v_key_2448_; lean_object* v_value_2449_; lean_object* v_tail_2450_; uint8_t v___x_2451_; 
v_key_2448_ = lean_ctor_get(v_x_2447_, 0);
v_value_2449_ = lean_ctor_get(v_x_2447_, 1);
v_tail_2450_ = lean_ctor_get(v_x_2447_, 2);
v___x_2451_ = l_Lean_instBEqFVarId_beq(v_key_2448_, v_a_2445_);
if (v___x_2451_ == 0)
{
v_x_2447_ = v_tail_2450_;
goto _start;
}
else
{
lean_inc(v_value_2449_);
return v_value_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2453_, lean_object* v_fallback_2454_, lean_object* v_x_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2453_, v_fallback_2454_, v_x_2455_);
lean_dec(v_x_2455_);
lean_dec(v_fallback_2454_);
lean_dec(v_a_2453_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2457_, lean_object* v_a_2458_, lean_object* v_fallback_2459_){
_start:
{
lean_object* v_buckets_2460_; lean_object* v___x_2461_; uint64_t v___x_2462_; uint64_t v___x_2463_; uint64_t v___x_2464_; uint64_t v_fold_2465_; uint64_t v___x_2466_; uint64_t v___x_2467_; uint64_t v___x_2468_; size_t v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; size_t v___x_2472_; size_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_buckets_2460_ = lean_ctor_get(v_m_2457_, 1);
v___x_2461_ = lean_array_get_size(v_buckets_2460_);
v___x_2462_ = l_Lean_instHashableFVarId_hash(v_a_2458_);
v___x_2463_ = 32ULL;
v___x_2464_ = lean_uint64_shift_right(v___x_2462_, v___x_2463_);
v_fold_2465_ = lean_uint64_xor(v___x_2462_, v___x_2464_);
v___x_2466_ = 16ULL;
v___x_2467_ = lean_uint64_shift_right(v_fold_2465_, v___x_2466_);
v___x_2468_ = lean_uint64_xor(v_fold_2465_, v___x_2467_);
v___x_2469_ = lean_uint64_to_usize(v___x_2468_);
v___x_2470_ = lean_usize_of_nat(v___x_2461_);
v___x_2471_ = ((size_t)1ULL);
v___x_2472_ = lean_usize_sub(v___x_2470_, v___x_2471_);
v___x_2473_ = lean_usize_land(v___x_2469_, v___x_2472_);
v___x_2474_ = lean_array_uget_borrowed(v_buckets_2460_, v___x_2473_);
v___x_2475_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2458_, v_fallback_2459_, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2476_, lean_object* v_a_2477_, lean_object* v_fallback_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2476_, v_a_2477_, v_fallback_2478_);
lean_dec(v_fallback_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_m_2476_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2494_; 
v___x_2484_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2481_, v_a_2482_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = lean_box(0);
v___x_2490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2485_, v_var_2480_, v___x_2489_);
lean_dec(v_a_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2490_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_var_2495_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2500_, v_a_2501_, v_a_2502_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_var_2509_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2518_, lean_object* v_m_2519_, lean_object* v_a_2520_, lean_object* v_fallback_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2519_, v_a_2520_, v_fallback_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2523_, lean_object* v_m_2524_, lean_object* v_a_2525_, lean_object* v_fallback_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2523_, v_m_2524_, v_a_2525_, v_fallback_2526_);
lean_dec(v_fallback_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_m_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2528_, lean_object* v_a_2529_, lean_object* v_fallback_2530_, lean_object* v_x_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2529_, v_fallback_2530_, v_x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2533_, lean_object* v_a_2534_, lean_object* v_fallback_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2533_, v_a_2534_, v_fallback_2535_, v_x_2536_);
lean_dec(v_x_2536_);
lean_dec(v_fallback_2535_);
lean_dec(v_a_2534_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
if (lean_obj_tag(v_arg_2538_) == 1)
{
lean_object* v_fvarId_2542_; lean_object* v___x_2543_; 
v_fvarId_2542_ = lean_ctor_get(v_arg_2538_, 0);
v___x_2543_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2542_, v_a_2539_, v_a_2540_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_box(1);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_arg_2546_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2551_, v_a_2552_, v_a_2553_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_arg_2560_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2569_, lean_object* v_b_2570_, lean_object* v_x_2571_){
_start:
{
if (lean_obj_tag(v_x_2571_) == 0)
{
lean_dec(v_b_2570_);
lean_dec(v_a_2569_);
return v_x_2571_;
}
else
{
lean_object* v_key_2572_; lean_object* v_value_2573_; lean_object* v_tail_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2586_; 
v_key_2572_ = lean_ctor_get(v_x_2571_, 0);
v_value_2573_ = lean_ctor_get(v_x_2571_, 1);
v_tail_2574_ = lean_ctor_get(v_x_2571_, 2);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_x_2571_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2576_ = v_x_2571_;
v_isShared_2577_ = v_isSharedCheck_2586_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_tail_2574_);
lean_inc(v_value_2573_);
lean_inc(v_key_2572_);
lean_dec(v_x_2571_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2586_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
uint8_t v___x_2578_; 
v___x_2578_ = l_Lean_instBEqFVarId_beq(v_key_2572_, v_a_2569_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2569_, v_b_2570_, v_tail_2574_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 2, v___x_2579_);
v___x_2581_ = v___x_2576_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_key_2572_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_value_2573_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
else
{
lean_object* v___x_2584_; 
lean_dec(v_value_2573_);
lean_dec(v_key_2572_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v_b_2570_);
lean_ctor_set(v___x_2576_, 0, v_a_2569_);
v___x_2584_ = v___x_2576_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2569_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_b_2570_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_tail_2574_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2587_, lean_object* v_x_2588_){
_start:
{
if (lean_obj_tag(v_x_2588_) == 0)
{
return v_x_2587_;
}
else
{
lean_object* v_key_2589_; lean_object* v_value_2590_; lean_object* v_tail_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2614_; 
v_key_2589_ = lean_ctor_get(v_x_2588_, 0);
v_value_2590_ = lean_ctor_get(v_x_2588_, 1);
v_tail_2591_ = lean_ctor_get(v_x_2588_, 2);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_x_2588_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2593_ = v_x_2588_;
v_isShared_2594_ = v_isSharedCheck_2614_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_tail_2591_);
lean_inc(v_value_2590_);
lean_inc(v_key_2589_);
lean_dec(v_x_2588_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2614_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; uint64_t v___x_2596_; uint64_t v___x_2597_; uint64_t v___x_2598_; uint64_t v_fold_2599_; uint64_t v___x_2600_; uint64_t v___x_2601_; uint64_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2595_ = lean_array_get_size(v_x_2587_);
v___x_2596_ = l_Lean_instHashableFVarId_hash(v_key_2589_);
v___x_2597_ = 32ULL;
v___x_2598_ = lean_uint64_shift_right(v___x_2596_, v___x_2597_);
v_fold_2599_ = lean_uint64_xor(v___x_2596_, v___x_2598_);
v___x_2600_ = 16ULL;
v___x_2601_ = lean_uint64_shift_right(v_fold_2599_, v___x_2600_);
v___x_2602_ = lean_uint64_xor(v_fold_2599_, v___x_2601_);
v___x_2603_ = lean_uint64_to_usize(v___x_2602_);
v___x_2604_ = lean_usize_of_nat(v___x_2595_);
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_sub(v___x_2604_, v___x_2605_);
v___x_2607_ = lean_usize_land(v___x_2603_, v___x_2606_);
v___x_2608_ = lean_array_uget_borrowed(v_x_2587_, v___x_2607_);
lean_inc(v___x_2608_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 2, v___x_2608_);
v___x_2610_ = v___x_2593_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_key_2589_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_value_2590_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_array_uset(v_x_2587_, v___x_2607_, v___x_2610_);
v_x_2587_ = v___x_2611_;
v_x_2588_ = v_tail_2591_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2615_, lean_object* v_source_2616_, lean_object* v_target_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = lean_array_get_size(v_source_2616_);
v___x_2619_ = lean_nat_dec_lt(v_i_2615_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_dec_ref(v_source_2616_);
lean_dec(v_i_2615_);
return v_target_2617_;
}
else
{
lean_object* v_es_2620_; lean_object* v___x_2621_; lean_object* v_source_2622_; lean_object* v_target_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_es_2620_ = lean_array_fget(v_source_2616_, v_i_2615_);
v___x_2621_ = lean_box(0);
v_source_2622_ = lean_array_fset(v_source_2616_, v_i_2615_, v___x_2621_);
v_target_2623_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2617_, v_es_2620_);
v___x_2624_ = lean_unsigned_to_nat(1u);
v___x_2625_ = lean_nat_add(v_i_2615_, v___x_2624_);
lean_dec(v_i_2615_);
v_i_2615_ = v___x_2625_;
v_source_2616_ = v_source_2622_;
v_target_2617_ = v_target_2623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2627_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_nbuckets_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2628_ = lean_array_get_size(v_data_2627_);
v___x_2629_ = lean_unsigned_to_nat(2u);
v_nbuckets_2630_ = lean_nat_mul(v___x_2628_, v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_mk_array(v_nbuckets_2630_, v___x_2632_);
v___x_2634_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2631_, v_data_2627_, v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2635_, lean_object* v_x_2636_){
_start:
{
if (lean_obj_tag(v_x_2636_) == 0)
{
uint8_t v___x_2637_; 
v___x_2637_ = 0;
return v___x_2637_;
}
else
{
lean_object* v_key_2638_; lean_object* v_tail_2639_; uint8_t v___x_2640_; 
v_key_2638_ = lean_ctor_get(v_x_2636_, 0);
v_tail_2639_ = lean_ctor_get(v_x_2636_, 2);
v___x_2640_ = l_Lean_instBEqFVarId_beq(v_key_2638_, v_a_2635_);
if (v___x_2640_ == 0)
{
v_x_2636_ = v_tail_2639_;
goto _start;
}
else
{
return v___x_2640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2642_, lean_object* v_x_2643_){
_start:
{
uint8_t v_res_2644_; lean_object* v_r_2645_; 
v_res_2644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2642_, v_x_2643_);
lean_dec(v_x_2643_);
lean_dec(v_a_2642_);
v_r_2645_ = lean_box(v_res_2644_);
return v_r_2645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2646_, lean_object* v_a_2647_, lean_object* v_b_2648_){
_start:
{
lean_object* v_size_2649_; lean_object* v_buckets_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2693_; 
v_size_2649_ = lean_ctor_get(v_m_2646_, 0);
v_buckets_2650_ = lean_ctor_get(v_m_2646_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_m_2646_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2652_ = v_m_2646_;
v_isShared_2653_ = v_isSharedCheck_2693_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_buckets_2650_);
lean_inc(v_size_2649_);
lean_dec(v_m_2646_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2693_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; uint64_t v___x_2655_; uint64_t v___x_2656_; uint64_t v___x_2657_; uint64_t v_fold_2658_; uint64_t v___x_2659_; uint64_t v___x_2660_; uint64_t v___x_2661_; size_t v___x_2662_; size_t v___x_2663_; size_t v___x_2664_; size_t v___x_2665_; size_t v___x_2666_; lean_object* v_bkt_2667_; uint8_t v___x_2668_; 
v___x_2654_ = lean_array_get_size(v_buckets_2650_);
v___x_2655_ = l_Lean_instHashableFVarId_hash(v_a_2647_);
v___x_2656_ = 32ULL;
v___x_2657_ = lean_uint64_shift_right(v___x_2655_, v___x_2656_);
v_fold_2658_ = lean_uint64_xor(v___x_2655_, v___x_2657_);
v___x_2659_ = 16ULL;
v___x_2660_ = lean_uint64_shift_right(v_fold_2658_, v___x_2659_);
v___x_2661_ = lean_uint64_xor(v_fold_2658_, v___x_2660_);
v___x_2662_ = lean_uint64_to_usize(v___x_2661_);
v___x_2663_ = lean_usize_of_nat(v___x_2654_);
v___x_2664_ = ((size_t)1ULL);
v___x_2665_ = lean_usize_sub(v___x_2663_, v___x_2664_);
v___x_2666_ = lean_usize_land(v___x_2662_, v___x_2665_);
v_bkt_2667_ = lean_array_uget_borrowed(v_buckets_2650_, v___x_2666_);
v___x_2668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2647_, v_bkt_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v_size_x27_2670_; lean_object* v___x_2671_; lean_object* v_buckets_x27_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2669_ = lean_unsigned_to_nat(1u);
v_size_x27_2670_ = lean_nat_add(v_size_2649_, v___x_2669_);
lean_dec(v_size_2649_);
lean_inc(v_bkt_2667_);
v___x_2671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2671_, 0, v_a_2647_);
lean_ctor_set(v___x_2671_, 1, v_b_2648_);
lean_ctor_set(v___x_2671_, 2, v_bkt_2667_);
v_buckets_x27_2672_ = lean_array_uset(v_buckets_2650_, v___x_2666_, v___x_2671_);
v___x_2673_ = lean_unsigned_to_nat(4u);
v___x_2674_ = lean_nat_mul(v_size_x27_2670_, v___x_2673_);
v___x_2675_ = lean_unsigned_to_nat(3u);
v___x_2676_ = lean_nat_div(v___x_2674_, v___x_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_array_get_size(v_buckets_x27_2672_);
v___x_2678_ = lean_nat_dec_le(v___x_2676_, v___x_2677_);
lean_dec(v___x_2676_);
if (v___x_2678_ == 0)
{
lean_object* v_val_2679_; lean_object* v___x_2681_; 
v_val_2679_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2672_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v_val_2679_);
lean_ctor_set(v___x_2652_, 0, v_size_x27_2670_);
v___x_2681_ = v___x_2652_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_size_x27_2670_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_val_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
else
{
lean_object* v___x_2684_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v_buckets_x27_2672_);
lean_ctor_set(v___x_2652_, 0, v_size_x27_2670_);
v___x_2684_ = v___x_2652_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_size_x27_2670_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_buckets_x27_2672_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v_buckets_x27_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
lean_inc(v_bkt_2667_);
v___x_2686_ = lean_box(0);
v_buckets_x27_2687_ = lean_array_uset(v_buckets_2650_, v___x_2666_, v___x_2686_);
v___x_2688_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2647_, v_b_2648_, v_bkt_2667_);
v___x_2689_ = lean_array_uset(v_buckets_x27_2687_, v___x_2666_, v___x_2688_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v___x_2689_);
v___x_2691_ = v___x_2652_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_size_2649_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2694_, lean_object* v___x_2695_, lean_object* v_x_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2696_, v_var_2694_, v___x_2695_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2698_, lean_object* v_newVal_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_st_ref_get(v_a_2702_);
v___x_2705_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2698_, v_a_2700_, v_a_2701_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v_env_2707_; lean_object* v___x_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v_env_2707_ = lean_ctor_get(v___x_2704_, 0);
lean_inc_ref(v_env_2707_);
lean_dec(v___x_2704_);
v___x_2708_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2707_, v_a_2706_, v_newVal_2699_);
v___f_2709_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2709_, 0, v_var_2698_);
lean_closure_set(v___f_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2709_, v_a_2700_, v_a_2701_);
return v___x_2710_;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v___x_2704_);
lean_dec(v_newVal_2699_);
lean_dec(v_var_2698_);
v_a_2711_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2705_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2705_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2719_, lean_object* v_newVal_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2719_, v_newVal_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2726_, lean_object* v_newVal_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2726_, v_newVal_2727_, v_a_2728_, v_a_2729_, v_a_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2736_, lean_object* v_newVal_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2736_, v_newVal_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2746_, lean_object* v_m_2747_, lean_object* v_a_2748_, lean_object* v_b_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2747_, v_a_2748_, v_b_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2751_, lean_object* v_a_2752_, lean_object* v_x_2753_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2752_, v_x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2755_, lean_object* v_a_2756_, lean_object* v_x_2757_){
_start:
{
uint8_t v_res_2758_; lean_object* v_r_2759_; 
v_res_2758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2755_, v_a_2756_, v_x_2757_);
lean_dec(v_x_2757_);
lean_dec(v_a_2756_);
v_r_2759_ = lean_box(v_res_2758_);
return v_r_2759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2760_, lean_object* v_data_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2763_, lean_object* v_a_2764_, lean_object* v_b_2765_, lean_object* v_x_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2764_, v_b_2765_, v_x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2768_, lean_object* v_i_2769_, lean_object* v_source_2770_, lean_object* v_target_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2769_, v_source_2770_, v_target_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2774_, v_x_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_box(0);
v___x_2780_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2778_, v_var_2777_, v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___f_2785_; lean_object* v___x_2786_; 
v___f_2785_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2785_, 0, v_var_2781_);
v___x_2786_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2785_, v_a_2782_, v_a_2783_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2787_, v_a_2788_, v_a_2789_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2792_, v_a_2793_, v_a_2794_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v_fst_2818_; lean_object* v_snd_2819_; lean_object* v_currFnIdx_2822_; lean_object* v_assignments_2823_; lean_object* v_funVals_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2815_ = lean_st_ref_get(v_a_2813_);
v___x_2816_ = lean_st_ref_take(v_a_2812_);
v_currFnIdx_2822_ = lean_ctor_get(v_a_2811_, 1);
v_assignments_2823_ = lean_ctor_get(v___x_2816_, 0);
lean_inc_ref(v_assignments_2823_);
v_funVals_2824_ = lean_ctor_get(v___x_2816_, 1);
lean_inc_ref(v_funVals_2824_);
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_array_get_size(v_funVals_2824_);
v___x_2827_ = lean_nat_dec_lt(v_currFnIdx_2822_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_dec_ref(v_funVals_2824_);
lean_dec_ref(v_assignments_2823_);
lean_dec(v___x_2815_);
lean_dec(v_v_2810_);
v_fst_2818_ = v___x_2825_;
v_snd_2819_ = v___x_2816_;
goto v___jp_2817_;
}
else
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2839_; 
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; lean_object* v_unused_2841_; 
v_unused_2840_ = lean_ctor_get(v___x_2816_, 1);
lean_dec(v_unused_2840_);
v_unused_2841_ = lean_ctor_get(v___x_2816_, 0);
lean_dec(v_unused_2841_);
v___x_2829_ = v___x_2816_;
v_isShared_2830_ = v_isSharedCheck_2839_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v___x_2816_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2839_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_env_2831_; lean_object* v_v_2832_; lean_object* v_xs_x27_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v_env_2831_ = lean_ctor_get(v___x_2815_, 0);
lean_inc_ref(v_env_2831_);
lean_dec(v___x_2815_);
v_v_2832_ = lean_array_fget(v_funVals_2824_, v_currFnIdx_2822_);
v_xs_x27_2833_ = lean_array_fset(v_funVals_2824_, v_currFnIdx_2822_, v___x_2825_);
v___x_2834_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2831_, v_v_2810_, v_v_2832_);
v___x_2835_ = lean_array_fset(v_xs_x27_2833_, v_currFnIdx_2822_, v___x_2834_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v___x_2835_);
v___x_2837_ = v___x_2829_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_assignments_2823_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v___x_2835_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
v_fst_2818_ = v___x_2825_;
v_snd_2819_ = v___x_2837_;
goto v___jp_2817_;
}
}
}
v___jp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_st_ref_put(v_a_2812_, v_snd_2819_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_fst_2818_);
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2848_, v_a_2849_, v_a_2850_, v_a_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2866_, uint8_t v_b_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_array_2872_; lean_object* v_start_2873_; lean_object* v_stop_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2911_; 
v_array_2872_ = lean_ctor_get(v_a_2866_, 0);
v_start_2873_ = lean_ctor_get(v_a_2866_, 1);
v_stop_2874_ = lean_ctor_get(v_a_2866_, 2);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2876_ = v_a_2866_;
v_isShared_2877_ = v_isSharedCheck_2911_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_stop_2874_);
lean_inc(v_start_2873_);
lean_inc(v_array_2872_);
lean_dec(v_a_2866_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2911_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
uint8_t v___x_2878_; 
v___x_2878_ = lean_nat_dec_lt(v_start_2873_, v_stop_2874_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_del_object(v___x_2876_);
lean_dec(v_stop_2874_);
lean_dec(v_start_2873_);
lean_dec_ref(v_array_2872_);
v___x_2879_ = lean_box(v_b_2867_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
else
{
lean_object* v___x_2881_; lean_object* v_fvarId_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_array_fget_borrowed(v_array_2872_, v_start_2873_);
v_fvarId_2882_ = lean_ctor_get(v___x_2881_, 0);
v___x_2883_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2882_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = lean_box(1);
lean_inc(v_fvarId_2882_);
v___x_2886_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2882_, v___x_2885_, v___y_2868_, v___y_2869_, v___y_2870_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
lean_dec_ref_known(v___x_2886_, 1);
v___x_2887_ = lean_unsigned_to_nat(1u);
v___x_2888_ = lean_nat_add(v_start_2873_, v___x_2887_);
lean_dec(v_start_2873_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v___x_2888_);
v___x_2890_ = v___x_2876_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_array_2872_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_stop_2874_);
v___x_2890_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = lean_box(0);
v___x_2892_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2884_, v___x_2891_);
lean_dec(v_a_2884_);
v_a_2866_ = v___x_2890_;
v_b_2867_ = v___x_2892_;
goto _start;
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_a_2884_);
lean_del_object(v___x_2876_);
lean_dec(v_stop_2874_);
lean_dec(v_start_2873_);
lean_dec_ref(v_array_2872_);
v_a_2895_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2886_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2886_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_del_object(v___x_2876_);
lean_dec(v_stop_2874_);
lean_dec(v_start_2873_);
lean_dec_ref(v_array_2872_);
v_a_2903_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2883_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2883_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2912_, lean_object* v_b_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v_b_boxed_2918_; lean_object* v_res_2919_; 
v_b_boxed_2918_ = lean_unbox(v_b_2913_);
v_res_2919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2912_, v_b_boxed_2918_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2920_, lean_object* v___x_2921_, lean_object* v_x_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2922_, v_fvarId_2920_, v___x_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2924_, lean_object* v_as_2925_, size_t v_sz_2926_, size_t v_i_2927_, lean_object* v_b_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_a_2933_; uint8_t v___x_2937_; 
v___x_2937_ = lean_usize_dec_lt(v_i_2927_, v_sz_2926_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_dec_ref(v___x_2924_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_b_2928_);
return v___x_2938_;
}
else
{
lean_object* v_snd_2939_; lean_object* v_fst_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_3006_; 
v_snd_2939_ = lean_ctor_get(v_b_2928_, 1);
v_fst_2940_ = lean_ctor_get(v_b_2928_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_b_2928_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2942_ = v_b_2928_;
v_isShared_2943_ = v_isSharedCheck_3006_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snd_2939_);
lean_inc(v_fst_2940_);
lean_dec(v_b_2928_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_3006_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v_array_2944_; lean_object* v_start_2945_; lean_object* v_stop_2946_; uint8_t v___x_2947_; 
v_array_2944_ = lean_ctor_get(v_snd_2939_, 0);
v_start_2945_ = lean_ctor_get(v_snd_2939_, 1);
v_stop_2946_ = lean_ctor_get(v_snd_2939_, 2);
v___x_2947_ = lean_nat_dec_lt(v_start_2945_, v_stop_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref(v___x_2924_);
if (v_isShared_2943_ == 0)
{
v___x_2949_ = v___x_2942_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_fst_2940_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_snd_2939_);
v___x_2949_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
else
{
lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3002_; 
lean_inc(v_stop_2946_);
lean_inc(v_start_2945_);
lean_inc_ref(v_array_2944_);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_snd_2939_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; lean_object* v_unused_3004_; lean_object* v_unused_3005_; 
v_unused_3003_ = lean_ctor_get(v_snd_2939_, 2);
lean_dec(v_unused_3003_);
v_unused_3004_ = lean_ctor_get(v_snd_2939_, 1);
lean_dec(v_unused_3004_);
v_unused_3005_ = lean_ctor_get(v_snd_2939_, 0);
lean_dec(v_unused_3005_);
v___x_2953_ = v_snd_2939_;
v_isShared_2954_ = v_isSharedCheck_3002_;
goto v_resetjp_2952_;
}
else
{
lean_dec(v_snd_2939_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3002_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_a_2955_; lean_object* v_fvarId_2956_; lean_object* v___x_2957_; 
v_a_2955_ = lean_array_uget_borrowed(v_as_2925_, v_i_2927_);
v_fvarId_2956_ = lean_ctor_get(v_a_2955_, 0);
v___x_2957_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2956_, v___y_2929_, v___y_2930_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = lean_array_fget_borrowed(v_array_2944_, v_start_2945_);
v___x_2960_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2959_, v___y_2929_, v___y_2930_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_start_2945_, v___x_2962_);
lean_dec(v_start_2945_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2963_);
v___x_2965_ = v___x_2953_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_array_2944_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_stop_2946_);
v___x_2965_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
lean_inc(v_a_2958_);
lean_inc_ref(v___x_2924_);
v___x_2966_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2924_, v_a_2958_, v_a_2961_);
v___x_2967_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2966_, v_a_2958_);
lean_dec(v_a_2958_);
if (v___x_2967_ == 0)
{
lean_object* v___f_2968_; lean_object* v___x_2969_; 
lean_dec(v_fst_2940_);
lean_inc(v_fvarId_2956_);
v___f_2968_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2968_, 0, v_fvarId_2956_);
lean_closure_set(v___f_2968_, 1, v___x_2966_);
v___x_2969_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2968_, v___y_2929_, v___y_2930_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = lean_box(v___x_2947_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v___x_2965_);
lean_ctor_set(v___x_2942_, 0, v___x_2970_);
v___x_2972_ = v___x_2942_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___x_2965_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v_a_2933_ = v___x_2972_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v___x_2965_);
lean_del_object(v___x_2942_);
lean_dec_ref(v___x_2924_);
v_a_2974_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2969_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2969_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v___x_2983_; 
lean_dec(v___x_2966_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v___x_2965_);
v___x_2983_ = v___x_2942_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_fst_2940_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___x_2965_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
v_a_2933_ = v___x_2983_;
goto v___jp_2932_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_a_2958_);
lean_del_object(v___x_2953_);
lean_dec(v_stop_2946_);
lean_dec(v_start_2945_);
lean_dec_ref(v_array_2944_);
lean_del_object(v___x_2942_);
lean_dec(v_fst_2940_);
lean_dec_ref(v___x_2924_);
v_a_2986_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2960_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2960_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_del_object(v___x_2953_);
lean_dec(v_stop_2946_);
lean_dec(v_start_2945_);
lean_dec_ref(v_array_2944_);
lean_del_object(v___x_2942_);
lean_dec(v_fst_2940_);
lean_dec_ref(v___x_2924_);
v_a_2994_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2957_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2957_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
}
}
v___jp_2932_:
{
size_t v___x_2934_; size_t v___x_2935_; 
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_add(v_i_2927_, v___x_2934_);
v_i_2927_ = v___x_2935_;
v_b_2928_ = v_a_2933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3007_, lean_object* v_as_3008_, lean_object* v_sz_3009_, lean_object* v_i_3010_, lean_object* v_b_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
size_t v_sz_boxed_3015_; size_t v_i_boxed_3016_; lean_object* v_res_3017_; 
v_sz_boxed_3015_ = lean_unbox_usize(v_sz_3009_);
lean_dec(v_sz_3009_);
v_i_boxed_3016_ = lean_unbox_usize(v_i_3010_);
lean_dec(v_i_3010_);
v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3007_, v_as_3008_, v_sz_boxed_3015_, v_i_boxed_3016_, v_b_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec_ref(v_as_3008_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3018_, lean_object* v_args_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v_env_3028_; uint8_t v_ret_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; size_t v_sz_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
v___x_3027_ = lean_st_ref_get(v_a_3025_);
v_env_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc_ref(v_env_3028_);
lean_dec(v___x_3027_);
v_ret_3029_ = 0;
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_array_get_size(v_args_3019_);
v___x_3032_ = l_Array_toSubarray___redArg(v_args_3019_, v___x_3030_, v___x_3031_);
v___x_3033_ = lean_box(v_ret_3029_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___x_3032_);
v_sz_3035_ = lean_array_size(v_params_3018_);
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3028_, v_params_3018_, v_sz_3035_, v___x_3036_, v___x_3034_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3055_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3055_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3055_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_fst_3042_; lean_object* v_lower_3044_; lean_object* v_upper_3045_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v_fst_3042_ = lean_ctor_get(v_a_3038_, 0);
lean_inc(v_fst_3042_);
lean_dec(v_a_3038_);
v___x_3049_ = lean_array_get_size(v_params_3018_);
v___x_3050_ = lean_nat_dec_eq(v___x_3049_, v___x_3031_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
lean_del_object(v___x_3040_);
v___x_3051_ = lean_nat_dec_le(v___x_3031_, v___x_3030_);
if (v___x_3051_ == 0)
{
v_lower_3044_ = v___x_3031_;
v_upper_3045_ = v___x_3049_;
goto v___jp_3043_;
}
else
{
v_lower_3044_ = v___x_3030_;
v_upper_3045_ = v___x_3049_;
goto v___jp_3043_;
}
}
else
{
lean_object* v___x_3053_; 
lean_dec_ref(v_params_3018_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v_fst_3042_);
v___x_3053_ = v___x_3040_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_fst_3042_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
v___jp_3043_:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = l_Array_toSubarray___redArg(v_params_3018_, v_lower_3044_, v_upper_3045_);
v___x_3047_ = lean_unbox(v_fst_3042_);
lean_dec(v_fst_3042_);
v___x_3048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3046_, v___x_3047_, v_a_3020_, v_a_3021_, v_a_3025_);
return v___x_3048_;
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_params_3018_);
v_a_3056_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3037_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3037_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3064_, lean_object* v_args_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3064_, v_args_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3074_, lean_object* v_as_3075_, size_t v_sz_3076_, size_t v_i_3077_, lean_object* v_b_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3074_, v_as_3075_, v_sz_3076_, v_i_3077_, v_b_3078_, v___y_3079_, v___y_3080_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3087_, lean_object* v_as_3088_, lean_object* v_sz_3089_, lean_object* v_i_3090_, lean_object* v_b_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
size_t v_sz_boxed_3099_; size_t v_i_boxed_3100_; lean_object* v_res_3101_; 
v_sz_boxed_3099_ = lean_unbox_usize(v_sz_3089_);
lean_dec(v_sz_3089_);
v_i_boxed_3100_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3087_, v_as_3088_, v_sz_boxed_3099_, v_i_boxed_3100_, v_b_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v_as_3088_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3102_, lean_object* v_R_3103_, lean_object* v_a_3104_, uint8_t v_b_3105_, lean_object* v_c_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3104_, v_b_3105_, v___y_3107_, v___y_3108_, v___y_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3115_, lean_object* v_R_3116_, lean_object* v_a_3117_, lean_object* v_b_3118_, lean_object* v_c_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
uint8_t v_b_boxed_3127_; lean_object* v_res_3128_; 
v_b_boxed_3127_ = lean_unbox(v_b_3118_);
v_res_3128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3115_, v_R_3116_, v_a_3117_, v_b_boxed_3127_, v_c_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3129_, size_t v_sz_3130_, size_t v_i_3131_, uint8_t v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
uint8_t v_a_3137_; uint8_t v___x_3141_; 
v___x_3141_ = lean_usize_dec_lt(v_i_3131_, v_sz_3130_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_box(v_b_3132_);
v___x_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
else
{
lean_object* v_a_3144_; lean_object* v_fvarId_3145_; lean_object* v___x_3146_; 
v_a_3144_ = lean_array_uget_borrowed(v_as_3129_, v_i_3131_);
v_fvarId_3145_ = lean_ctor_get(v_a_3144_, 0);
v___x_3146_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3145_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = lean_box(1);
v___x_3149_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3148_, v_a_3147_);
lean_dec(v_a_3147_);
if (v___x_3149_ == 0)
{
lean_object* v___f_3150_; lean_object* v___x_3151_; 
lean_inc(v_fvarId_3145_);
v___f_3150_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3150_, 0, v_fvarId_3145_);
lean_closure_set(v___f_3150_, 1, v___x_3148_);
v___x_3151_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3150_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_dec_ref_known(v___x_3151_, 1);
v_a_3137_ = v___x_3141_;
goto v___jp_3136_;
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
v_a_3137_ = v_b_3132_;
goto v___jp_3136_;
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3146_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3146_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
v___jp_3136_:
{
size_t v___x_3138_; size_t v___x_3139_; 
v___x_3138_ = ((size_t)1ULL);
v___x_3139_ = lean_usize_add(v_i_3131_, v___x_3138_);
v_i_3131_ = v___x_3139_;
v_b_3132_ = v_a_3137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3168_, lean_object* v_sz_3169_, lean_object* v_i_3170_, lean_object* v_b_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
size_t v_sz_boxed_3175_; size_t v_i_boxed_3176_; uint8_t v_b_boxed_3177_; lean_object* v_res_3178_; 
v_sz_boxed_3175_ = lean_unbox_usize(v_sz_3169_);
lean_dec(v_sz_3169_);
v_i_boxed_3176_ = lean_unbox_usize(v_i_3170_);
lean_dec(v_i_3170_);
v_b_boxed_3177_ = lean_unbox(v_b_3171_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3168_, v_sz_boxed_3175_, v_i_boxed_3176_, v_b_boxed_3177_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v_as_3168_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
uint8_t v_ret_3187_; size_t v_sz_3188_; size_t v___x_3189_; lean_object* v___x_3190_; 
v_ret_3187_ = 0;
v_sz_3188_ = lean_array_size(v_params_3179_);
v___x_3189_ = ((size_t)0ULL);
v___x_3190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3179_, v_sz_3188_, v___x_3189_, v_ret_3187_, v_a_3180_, v_a_3181_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec_ref(v_params_3191_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3200_, size_t v_sz_3201_, size_t v_i_3202_, uint8_t v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3200_, v_sz_3201_, v_i_3202_, v_b_3203_, v___y_3204_, v___y_3205_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3212_, lean_object* v_sz_3213_, lean_object* v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
size_t v_sz_boxed_3223_; size_t v_i_boxed_3224_; uint8_t v_b_boxed_3225_; lean_object* v_res_3226_; 
v_sz_boxed_3223_ = lean_unbox_usize(v_sz_3213_);
lean_dec(v_sz_3213_);
v_i_boxed_3224_ = lean_unbox_usize(v_i_3214_);
lean_dec(v_i_3214_);
v_b_boxed_3225_ = lean_unbox(v_b_3215_);
v_res_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3212_, v_sz_boxed_3223_, v_i_boxed_3224_, v_b_boxed_3225_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec_ref(v_as_3212_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3227_, size_t v_i_3228_, size_t v_stop_3229_, lean_object* v_b_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_usize_dec_eq(v_i_3228_, v_stop_3229_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v_fvarId_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_array_uget_borrowed(v_as_3227_, v_i_3228_);
v_fvarId_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_fvarId_3236_);
v___x_3237_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3236_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; size_t v___x_3239_; size_t v___x_3240_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = ((size_t)1ULL);
v___x_3240_ = lean_usize_add(v_i_3228_, v___x_3239_);
v_i_3228_ = v___x_3240_;
v_b_3230_ = v_a_3238_;
goto _start;
}
else
{
return v___x_3237_;
}
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3242_, 0, v_b_3230_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3243_, lean_object* v_i_3244_, lean_object* v_stop_3245_, lean_object* v_b_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
size_t v_i_boxed_3250_; size_t v_stop_boxed_3251_; lean_object* v_res_3252_; 
v_i_boxed_3250_ = lean_unbox_usize(v_i_3244_);
lean_dec(v_i_3244_);
v_stop_boxed_3251_ = lean_unbox_usize(v_stop_3245_);
lean_dec(v_stop_3245_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3243_, v_i_boxed_3250_, v_stop_boxed_3251_, v_b_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v_as_3243_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v_decl_3272_; lean_object* v_k_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; 
switch(lean_obj_tag(v_x_3253_))
{
case 0:
{
lean_object* v_k_3294_; 
v_k_3294_ = lean_ctor_get(v_x_3253_, 1);
lean_inc_ref(v_k_3294_);
lean_dec_ref_known(v_x_3253_, 2);
v_x_3253_ = v_k_3294_;
goto _start;
}
case 3:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_dec_ref_known(v_x_3253_, 2);
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
return v___x_3297_;
}
case 4:
{
lean_object* v_cases_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3320_; 
v_cases_3298_ = lean_ctor_get(v_x_3253_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_x_3253_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3300_ = v_x_3253_;
v_isShared_3301_ = v_isSharedCheck_3320_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_cases_3298_);
lean_dec(v_x_3253_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3320_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v_alts_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
v_alts_3302_ = lean_ctor_get(v_cases_3298_, 3);
lean_inc_ref(v_alts_3302_);
lean_dec_ref(v_cases_3298_);
v___x_3303_ = lean_unsigned_to_nat(0u);
v___x_3304_ = lean_array_get_size(v_alts_3302_);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_nat_dec_lt(v___x_3303_, v___x_3304_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3308_; 
lean_dec_ref(v_alts_3302_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3305_);
v___x_3308_ = v___x_3300_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3305_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
else
{
uint8_t v___x_3310_; 
v___x_3310_ = lean_nat_dec_le(v___x_3304_, v___x_3304_);
if (v___x_3310_ == 0)
{
if (v___x_3306_ == 0)
{
lean_object* v___x_3312_; 
lean_dec_ref(v_alts_3302_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3305_);
v___x_3312_ = v___x_3300_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3305_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
else
{
size_t v___x_3314_; size_t v___x_3315_; lean_object* v___x_3316_; 
lean_del_object(v___x_3300_);
v___x_3314_ = ((size_t)0ULL);
v___x_3315_ = lean_usize_of_nat(v___x_3304_);
v___x_3316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3302_, v___x_3314_, v___x_3315_, v___x_3305_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
lean_dec_ref(v_alts_3302_);
return v___x_3316_;
}
}
else
{
size_t v___x_3317_; size_t v___x_3318_; lean_object* v___x_3319_; 
lean_del_object(v___x_3300_);
v___x_3317_ = ((size_t)0ULL);
v___x_3318_ = lean_usize_of_nat(v___x_3304_);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3302_, v___x_3317_, v___x_3318_, v___x_3305_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
lean_dec_ref(v_alts_3302_);
return v___x_3319_;
}
}
}
}
case 5:
{
lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3328_; 
v_isSharedCheck_3328_ = !lean_is_exclusive(v_x_3253_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v_x_3253_, 0);
lean_dec(v_unused_3329_);
v___x_3322_ = v_x_3253_;
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v_x_3253_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3324_ = lean_box(0);
if (v_isShared_3323_ == 0)
{
lean_ctor_set_tag(v___x_3322_, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3324_);
v___x_3326_ = v___x_3322_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
case 6:
{
lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v_isSharedCheck_3337_ = !lean_is_exclusive(v_x_3253_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v_x_3253_, 0);
lean_dec(v_unused_3338_);
v___x_3331_ = v_x_3253_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_dec(v_x_3253_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = lean_box(0);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
default: 
{
lean_object* v_decl_3339_; lean_object* v_k_3340_; 
v_decl_3339_ = lean_ctor_get(v_x_3253_, 0);
lean_inc_ref(v_decl_3339_);
v_k_3340_ = lean_ctor_get(v_x_3253_, 1);
lean_inc_ref(v_k_3340_);
lean_dec_ref(v_x_3253_);
v_decl_3272_ = v_decl_3339_;
v_k_3273_ = v_k_3340_;
v___y_3274_ = v_a_3254_;
v___y_3275_ = v_a_3255_;
v___y_3276_ = v_a_3256_;
v___y_3277_ = v_a_3257_;
v___y_3278_ = v_a_3258_;
v___y_3279_ = v_a_3259_;
goto v___jp_3271_;
}
}
v___jp_3261_:
{
if (lean_obj_tag(v___y_3269_) == 0)
{
lean_dec_ref_known(v___y_3269_, 1);
v_x_3253_ = v___y_3263_;
v_a_3254_ = v___y_3267_;
v_a_3255_ = v___y_3265_;
v_a_3256_ = v___y_3266_;
v_a_3257_ = v___y_3264_;
v_a_3258_ = v___y_3268_;
v_a_3259_ = v___y_3262_;
goto _start;
}
else
{
lean_dec_ref(v___y_3263_);
return v___y_3269_;
}
}
v___jp_3271_:
{
lean_object* v_params_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v_params_3280_ = lean_ctor_get(v_decl_3272_, 2);
lean_inc_ref(v_params_3280_);
lean_dec_ref(v_decl_3272_);
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = lean_array_get_size(v_params_3280_);
v___x_3283_ = lean_nat_dec_lt(v___x_3281_, v___x_3282_);
if (v___x_3283_ == 0)
{
lean_dec_ref(v_params_3280_);
v_x_3253_ = v_k_3273_;
v_a_3254_ = v___y_3274_;
v_a_3255_ = v___y_3275_;
v_a_3256_ = v___y_3276_;
v_a_3257_ = v___y_3277_;
v_a_3258_ = v___y_3278_;
v_a_3259_ = v___y_3279_;
goto _start;
}
else
{
lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_nat_dec_le(v___x_3282_, v___x_3282_);
if (v___x_3286_ == 0)
{
if (v___x_3283_ == 0)
{
lean_dec_ref(v_params_3280_);
v_x_3253_ = v_k_3273_;
v_a_3254_ = v___y_3274_;
v_a_3255_ = v___y_3275_;
v_a_3256_ = v___y_3276_;
v_a_3257_ = v___y_3277_;
v_a_3258_ = v___y_3278_;
v_a_3259_ = v___y_3279_;
goto _start;
}
else
{
size_t v___x_3288_; size_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = ((size_t)0ULL);
v___x_3289_ = lean_usize_of_nat(v___x_3282_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3280_, v___x_3288_, v___x_3289_, v___x_3285_, v___y_3274_, v___y_3275_);
lean_dec_ref(v_params_3280_);
v___y_3262_ = v___y_3279_;
v___y_3263_ = v_k_3273_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3275_;
v___y_3266_ = v___y_3276_;
v___y_3267_ = v___y_3274_;
v___y_3268_ = v___y_3278_;
v___y_3269_ = v___x_3290_;
goto v___jp_3261_;
}
}
else
{
size_t v___x_3291_; size_t v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = ((size_t)0ULL);
v___x_3292_ = lean_usize_of_nat(v___x_3282_);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3280_, v___x_3291_, v___x_3292_, v___x_3285_, v___y_3274_, v___y_3275_);
lean_dec_ref(v_params_3280_);
v___y_3262_ = v___y_3279_;
v___y_3263_ = v_k_3273_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3275_;
v___y_3266_ = v___y_3276_;
v___y_3267_ = v___y_3274_;
v___y_3268_ = v___y_3278_;
v___y_3269_ = v___x_3293_;
goto v___jp_3261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3341_, size_t v_i_3342_, size_t v_stop_3343_, lean_object* v_b_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___y_3353_; uint8_t v___x_3359_; 
v___x_3359_ = lean_usize_dec_eq(v_i_3342_, v_stop_3343_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_array_uget_borrowed(v_as_3341_, v_i_3342_);
switch(lean_obj_tag(v___x_3360_))
{
case 0:
{
lean_object* v_code_3361_; 
v_code_3361_ = lean_ctor_get(v___x_3360_, 2);
lean_inc_ref(v_code_3361_);
v___y_3353_ = v_code_3361_;
goto v___jp_3352_;
}
case 1:
{
lean_object* v_code_3362_; 
v_code_3362_ = lean_ctor_get(v___x_3360_, 1);
lean_inc_ref(v_code_3362_);
v___y_3353_ = v_code_3362_;
goto v___jp_3352_;
}
default: 
{
lean_object* v_code_3363_; 
v_code_3363_ = lean_ctor_get(v___x_3360_, 0);
lean_inc_ref(v_code_3363_);
v___y_3353_ = v_code_3363_;
goto v___jp_3352_;
}
}
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_b_3344_);
return v___x_3364_;
}
v___jp_3352_:
{
lean_object* v___x_3354_; 
v___x_3354_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3353_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; size_t v___x_3356_; size_t v___x_3357_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = ((size_t)1ULL);
v___x_3357_ = lean_usize_add(v_i_3342_, v___x_3356_);
v_i_3342_ = v___x_3357_;
v_b_3344_ = v_a_3355_;
goto _start;
}
else
{
return v___x_3354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3365_, lean_object* v_i_3366_, lean_object* v_stop_3367_, lean_object* v_b_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
size_t v_i_boxed_3376_; size_t v_stop_boxed_3377_; lean_object* v_res_3378_; 
v_i_boxed_3376_ = lean_unbox_usize(v_i_3366_);
lean_dec(v_i_3366_);
v_stop_boxed_3377_ = lean_unbox_usize(v_stop_3367_);
lean_dec(v_stop_3367_);
v_res_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3365_, v_i_boxed_3376_, v_stop_boxed_3377_, v_b_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec_ref(v_as_3365_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3388_, size_t v_i_3389_, size_t v_stop_3390_, lean_object* v_b_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3388_, v_i_3389_, v_stop_3390_, v_b_3391_, v___y_3392_, v___y_3393_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3400_, lean_object* v_i_3401_, lean_object* v_stop_3402_, lean_object* v_b_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
size_t v_i_boxed_3411_; size_t v_stop_boxed_3412_; lean_object* v_res_3413_; 
v_i_boxed_3411_ = lean_unbox_usize(v_i_3401_);
lean_dec(v_i_3401_);
v_stop_boxed_3412_ = lean_unbox_usize(v_stop_3402_);
lean_dec(v_stop_3402_);
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3400_, v_i_boxed_3411_, v_stop_boxed_3412_, v_b_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec_ref(v_as_3400_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3414_, lean_object* v_b_3415_){
_start:
{
lean_object* v_array_3416_; lean_object* v_start_3417_; lean_object* v_stop_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3431_; 
v_array_3416_ = lean_ctor_get(v_a_3414_, 0);
v_start_3417_ = lean_ctor_get(v_a_3414_, 1);
v_stop_3418_ = lean_ctor_get(v_a_3414_, 2);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_a_3414_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3420_ = v_a_3414_;
v_isShared_3421_ = v_isSharedCheck_3431_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_stop_3418_);
lean_inc(v_start_3417_);
lean_inc(v_array_3416_);
lean_dec(v_a_3414_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3431_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
uint8_t v___x_3422_; 
v___x_3422_ = lean_nat_dec_lt(v_start_3417_, v_stop_3418_);
if (v___x_3422_ == 0)
{
lean_del_object(v___x_3420_);
lean_dec(v_stop_3418_);
lean_dec(v_start_3417_);
lean_dec_ref(v_array_3416_);
return v_b_3415_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3423_ = lean_unsigned_to_nat(1u);
v___x_3424_ = lean_nat_add(v_start_3417_, v___x_3423_);
lean_inc_ref(v_array_3416_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v___x_3424_);
v___x_3426_ = v___x_3420_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_array_3416_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3430_, 2, v_stop_3418_);
v___x_3426_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_array_fget(v_array_3416_, v_start_3417_);
lean_dec(v_start_3417_);
lean_dec_ref(v_array_3416_);
v___x_3428_ = lean_array_push(v_b_3415_, v___x_3427_);
v_a_3414_ = v___x_3426_;
v_b_3415_ = v___x_3428_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3432_, size_t v_i_3433_, lean_object* v_bs_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_usize_dec_lt(v_i_3433_, v_sz_3432_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_bs_3434_);
return v___x_3439_;
}
else
{
lean_object* v_v_3440_; lean_object* v___x_3441_; 
v_v_3440_ = lean_array_uget_borrowed(v_bs_3434_, v_i_3433_);
v___x_3441_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3440_, v___y_3435_, v___y_3436_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; lean_object* v_bs_x27_3444_; size_t v___x_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
v___x_3443_ = lean_unsigned_to_nat(0u);
v_bs_x27_3444_ = lean_array_uset(v_bs_3434_, v_i_3433_, v___x_3443_);
v___x_3445_ = ((size_t)1ULL);
v___x_3446_ = lean_usize_add(v_i_3433_, v___x_3445_);
v___x_3447_ = lean_array_uset(v_bs_x27_3444_, v_i_3433_, v_a_3442_);
v_i_3433_ = v___x_3446_;
v_bs_3434_ = v___x_3447_;
goto _start;
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v_bs_3434_);
v_a_3449_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3441_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3441_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3457_, lean_object* v_i_3458_, lean_object* v_bs_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
size_t v_sz_boxed_3463_; size_t v_i_boxed_3464_; lean_object* v_res_3465_; 
v_sz_boxed_3463_ = lean_unbox_usize(v_sz_3457_);
lean_dec(v_sz_3457_);
v_i_boxed_3464_ = lean_unbox_usize(v_i_3458_);
lean_dec(v_i_3458_);
v_res_3465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3463_, v_i_boxed_3464_, v_bs_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3466_, size_t v_i_3467_, size_t v_stop_3468_, lean_object* v_b_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
uint8_t v___x_3474_; 
v___x_3474_ = lean_usize_dec_eq(v_i_3467_, v_stop_3468_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v_fvarId_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3475_ = lean_array_uget_borrowed(v_as_3466_, v_i_3467_);
v_fvarId_3476_ = lean_ctor_get(v___x_3475_, 0);
v___x_3477_ = lean_box(1);
lean_inc(v_fvarId_3476_);
v___x_3478_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3476_, v___x_3477_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; size_t v___x_3480_; size_t v___x_3481_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = ((size_t)1ULL);
v___x_3481_ = lean_usize_add(v_i_3467_, v___x_3480_);
v_i_3467_ = v___x_3481_;
v_b_3469_ = v_a_3479_;
goto _start;
}
else
{
return v___x_3478_;
}
}
else
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v_b_3469_);
return v___x_3483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3484_, lean_object* v_i_3485_, lean_object* v_stop_3486_, lean_object* v_b_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
size_t v_i_boxed_3492_; size_t v_stop_boxed_3493_; lean_object* v_res_3494_; 
v_i_boxed_3492_ = lean_unbox_usize(v_i_3485_);
lean_dec(v_i_3485_);
v_stop_boxed_3493_ = lean_unbox_usize(v_stop_3486_);
lean_dec(v_stop_3486_);
v_res_3494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3484_, v_i_boxed_3492_, v_stop_boxed_3493_, v_b_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v_as_3484_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3495_, size_t v_i_3496_, size_t v_stop_3497_, lean_object* v_b_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_usize_dec_eq(v_i_3496_, v_stop_3497_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v_fst_3505_; lean_object* v_snd_3506_; lean_object* v_fvarId_3507_; lean_object* v___x_3508_; 
v___x_3504_ = lean_array_uget_borrowed(v_as_3495_, v_i_3496_);
v_fst_3505_ = lean_ctor_get(v___x_3504_, 0);
v_snd_3506_ = lean_ctor_get(v___x_3504_, 1);
v_fvarId_3507_ = lean_ctor_get(v_fst_3505_, 0);
lean_inc(v_snd_3506_);
lean_inc(v_fvarId_3507_);
v___x_3508_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3507_, v_snd_3506_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; size_t v___x_3510_; size_t v___x_3511_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_add(v_i_3496_, v___x_3510_);
v_i_3496_ = v___x_3511_;
v_b_3498_ = v_a_3509_;
goto _start;
}
else
{
return v___x_3508_;
}
}
else
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_b_3498_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3514_, lean_object* v_i_3515_, lean_object* v_stop_3516_, lean_object* v_b_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
size_t v_i_boxed_3522_; size_t v_stop_boxed_3523_; lean_object* v_res_3524_; 
v_i_boxed_3522_ = lean_unbox_usize(v_i_3515_);
lean_dec(v_i_3515_);
v_stop_boxed_3523_ = lean_unbox_usize(v_stop_3516_);
lean_dec(v_stop_3516_);
v_res_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3514_, v_i_boxed_3522_, v_stop_boxed_3523_, v_b_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v_as_3514_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3527_, size_t v_i_3528_, size_t v_stop_3529_, lean_object* v_b_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_usize_dec_eq(v_i_3528_, v_stop_3529_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_array_uget_borrowed(v_as_3527_, v_i_3528_);
v___x_3540_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3539_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; size_t v___x_3542_; size_t v___x_3543_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v___x_3542_ = ((size_t)1ULL);
v___x_3543_ = lean_usize_add(v_i_3528_, v___x_3542_);
v_i_3528_ = v___x_3543_;
v_b_3530_ = v_a_3541_;
goto _start;
}
else
{
return v___x_3540_;
}
}
else
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v_b_3530_);
return v___x_3545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v___y_3561_; 
switch(lean_obj_tag(v_letVal_3546_))
{
case 0:
{
lean_object* v_value_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3578_; 
v_value_3570_ = lean_ctor_get(v_letVal_3546_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_letVal_3546_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3572_ = v_letVal_3546_;
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_value_3570_);
lean_dec(v_letVal_3546_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3574_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3570_);
lean_dec_ref(v_value_3570_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v___x_3574_);
v___x_3576_ = v___x_3572_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
case 1:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = lean_box(1);
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
case 2:
{
lean_object* v_idx_3581_; lean_object* v_struct_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_idx_3581_ = lean_ctor_get(v_letVal_3546_, 1);
lean_inc(v_idx_3581_);
v_struct_3582_ = lean_ctor_get(v_letVal_3546_, 2);
lean_inc(v_struct_3582_);
lean_dec_ref_known(v_letVal_3546_, 3);
v___x_3583_ = lean_st_ref_get(v_a_3552_);
v___x_3584_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3582_, v_a_3547_, v_a_3548_);
lean_dec(v_struct_3582_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3594_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3587_ = v___x_3584_;
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v_env_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v_env_3589_ = lean_ctor_get(v___x_3583_, 0);
lean_inc_ref(v_env_3589_);
lean_dec(v___x_3583_);
v___x_3590_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3589_, v_a_3585_, v_idx_3581_);
lean_dec(v_idx_3581_);
lean_dec(v_a_3585_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3590_);
v___x_3592_ = v___x_3587_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
lean_dec(v___x_3583_);
lean_dec(v_idx_3581_);
return v___x_3584_;
}
}
case 3:
{
lean_object* v_declName_3595_; lean_object* v_args_3596_; lean_object* v___x_3597_; lean_object* v_env_3598_; lean_object* v___x_3599_; lean_object* v_numFields_3601_; lean_object* v_lower_3602_; lean_object* v_upper_3603_; lean_object* v___x_3631_; lean_object* v___y_3700_; uint8_t v___x_3709_; 
v_declName_3595_ = lean_ctor_get(v_letVal_3546_, 0);
lean_inc(v_declName_3595_);
v_args_3596_ = lean_ctor_get(v_letVal_3546_, 2);
lean_inc_ref(v_args_3596_);
lean_dec_ref_known(v_letVal_3546_, 3);
v___x_3597_ = lean_st_ref_get(v_a_3552_);
v_env_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc_ref(v_env_3598_);
lean_dec(v___x_3597_);
v___x_3599_ = lean_unsigned_to_nat(0u);
v___x_3631_ = lean_array_get_size(v_args_3596_);
v___x_3709_ = lean_nat_dec_lt(v___x_3599_, v___x_3631_);
if (v___x_3709_ == 0)
{
goto v___jp_3632_;
}
else
{
lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_nat_dec_le(v___x_3631_, v___x_3631_);
if (v___x_3711_ == 0)
{
if (v___x_3709_ == 0)
{
goto v___jp_3632_;
}
else
{
size_t v___x_3712_; size_t v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = ((size_t)0ULL);
v___x_3713_ = lean_usize_of_nat(v___x_3631_);
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3596_, v___x_3712_, v___x_3713_, v___x_3710_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
v___y_3700_ = v___x_3714_;
goto v___jp_3699_;
}
}
else
{
size_t v___x_3715_; size_t v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = ((size_t)0ULL);
v___x_3716_ = lean_usize_of_nat(v___x_3631_);
v___x_3717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3596_, v___x_3715_, v___x_3716_, v___x_3710_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
v___y_3700_ = v___x_3717_;
goto v___jp_3699_;
}
}
v___jp_3600_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3604_ = l_Array_toSubarray___redArg(v_args_3596_, v_lower_3602_, v_upper_3603_);
v___x_3605_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3606_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3604_, v___x_3605_);
v___x_3607_ = lean_array_get_size(v___x_3606_);
v___x_3608_ = lean_nat_dec_eq(v_numFields_3601_, v___x_3607_);
lean_dec(v_numFields_3601_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_dec_ref(v___x_3606_);
lean_dec(v_declName_3595_);
v___x_3609_ = lean_box(1);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
else
{
size_t v_sz_3611_; size_t v___x_3612_; lean_object* v___x_3613_; 
v_sz_3611_ = lean_array_size(v___x_3606_);
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3611_, v___x_3612_, v___x_3606_, v_a_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3622_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
v___x_3618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3618_, 0, v_declName_3595_);
lean_ctor_set(v___x_3618_, 1, v_a_3614_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3618_);
v___x_3620_ = v___x_3616_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v_declName_3595_);
v_a_3623_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3613_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3613_);
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
v___jp_3632_:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3549_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; uint8_t v___x_3635_; lean_object* v___x_3636_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = lean_unbox(v_a_3634_);
lean_dec(v_a_3634_);
lean_inc(v_declName_3595_);
v___x_3636_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3595_, v___x_3635_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3682_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3682_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3682_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
if (lean_obj_tag(v_a_3637_) == 1)
{
lean_object* v_val_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
lean_dec_ref(v_args_3596_);
v_val_3641_ = lean_ctor_get(v_a_3637_, 0);
lean_inc(v_val_3641_);
lean_dec_ref_known(v_a_3637_, 1);
v___x_3642_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3641_);
lean_dec(v_val_3641_);
v___x_3643_ = lean_nat_dec_eq(v___x_3642_, v___x_3631_);
lean_dec(v___x_3642_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
lean_dec_ref(v_env_3598_);
lean_dec(v_declName_3595_);
v___x_3644_ = lean_box(1);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3644_);
v___x_3646_ = v___x_3639_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
else
{
lean_object* v___x_3648_; 
lean_inc(v_declName_3595_);
v___x_3648_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3598_, v_declName_3595_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3649_; 
lean_del_object(v___x_3639_);
v___x_3649_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3595_, v_a_3547_, v_a_3548_);
lean_dec(v_declName_3595_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3662_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3662_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3662_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
if (lean_obj_tag(v_a_3650_) == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = lean_box(1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3654_);
v___x_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
else
{
lean_object* v_val_3658_; lean_object* v___x_3660_; 
v_val_3658_ = lean_ctor_get(v_a_3650_, 0);
lean_inc(v_val_3658_);
lean_dec_ref_known(v_a_3650_, 1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_val_3658_);
v___x_3660_ = v___x_3652_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_val_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v_a_3663_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3649_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3649_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v_val_3671_; lean_object* v___x_3673_; 
lean_dec(v_declName_3595_);
v_val_3671_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_val_3671_);
lean_dec_ref_known(v___x_3648_, 1);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v_val_3671_);
v___x_3673_ = v___x_3639_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_val_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
uint8_t v___x_3675_; lean_object* v___x_3676_; 
lean_del_object(v___x_3639_);
lean_dec(v_a_3637_);
v___x_3675_ = 0;
lean_inc(v_declName_3595_);
v___x_3676_ = l_Lean_Environment_find_x3f(v_env_3598_, v_declName_3595_, v___x_3675_);
if (lean_obj_tag(v___x_3676_) == 1)
{
lean_object* v_val_3677_; 
v_val_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_val_3677_);
lean_dec_ref_known(v___x_3676_, 1);
if (lean_obj_tag(v_val_3677_) == 6)
{
lean_object* v_val_3678_; lean_object* v_numParams_3679_; lean_object* v_numFields_3680_; uint8_t v___x_3681_; 
v_val_3678_ = lean_ctor_get(v_val_3677_, 0);
lean_inc_ref(v_val_3678_);
lean_dec_ref_known(v_val_3677_, 1);
v_numParams_3679_ = lean_ctor_get(v_val_3678_, 3);
lean_inc(v_numParams_3679_);
v_numFields_3680_ = lean_ctor_get(v_val_3678_, 4);
lean_inc(v_numFields_3680_);
lean_dec_ref(v_val_3678_);
v___x_3681_ = lean_nat_dec_le(v_numParams_3679_, v___x_3599_);
if (v___x_3681_ == 0)
{
v_numFields_3601_ = v_numFields_3680_;
v_lower_3602_ = v_numParams_3679_;
v_upper_3603_ = v___x_3631_;
goto v___jp_3600_;
}
else
{
lean_dec(v_numParams_3679_);
v_numFields_3601_ = v_numFields_3680_;
v_lower_3602_ = v___x_3599_;
v_upper_3603_ = v___x_3631_;
goto v___jp_3600_;
}
}
else
{
lean_dec(v_val_3677_);
lean_dec_ref(v_args_3596_);
lean_dec(v_declName_3595_);
goto v___jp_3554_;
}
}
else
{
lean_dec(v___x_3676_);
lean_dec_ref(v_args_3596_);
lean_dec(v_declName_3595_);
goto v___jp_3554_;
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v_env_3598_);
lean_dec_ref(v_args_3596_);
lean_dec(v_declName_3595_);
v_a_3683_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3636_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3636_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_env_3598_);
lean_dec_ref(v_args_3596_);
lean_dec(v_declName_3595_);
v_a_3691_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3633_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3633_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
v___jp_3699_:
{
if (lean_obj_tag(v___y_3700_) == 0)
{
lean_dec_ref_known(v___y_3700_, 1);
goto v___jp_3632_;
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v_env_3598_);
lean_dec_ref(v_args_3596_);
lean_dec(v_declName_3595_);
v_a_3701_ = lean_ctor_get(v___y_3700_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___y_3700_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___y_3700_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___y_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
default: 
{
lean_object* v_args_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v_args_3718_ = lean_ctor_get(v_letVal_3546_, 1);
lean_inc_ref(v_args_3718_);
lean_dec_ref_known(v_letVal_3546_, 2);
v___x_3719_ = lean_unsigned_to_nat(0u);
v___x_3720_ = lean_array_get_size(v_args_3718_);
v___x_3721_ = lean_nat_dec_lt(v___x_3719_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_dec_ref(v_args_3718_);
goto v___jp_3557_;
}
else
{
lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3722_ = lean_box(0);
v___x_3723_ = lean_nat_dec_le(v___x_3720_, v___x_3720_);
if (v___x_3723_ == 0)
{
if (v___x_3721_ == 0)
{
lean_dec_ref(v_args_3718_);
goto v___jp_3557_;
}
else
{
size_t v___x_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = ((size_t)0ULL);
v___x_3725_ = lean_usize_of_nat(v___x_3720_);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3718_, v___x_3724_, v___x_3725_, v___x_3722_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec_ref(v_args_3718_);
v___y_3561_ = v___x_3726_;
goto v___jp_3560_;
}
}
else
{
size_t v___x_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3727_ = ((size_t)0ULL);
v___x_3728_ = lean_usize_of_nat(v___x_3720_);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3718_, v___x_3727_, v___x_3728_, v___x_3722_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec_ref(v_args_3718_);
v___y_3561_ = v___x_3729_;
goto v___jp_3560_;
}
}
}
}
v___jp_3554_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_box(1);
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
return v___x_3556_;
}
v___jp_3557_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_box(1);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
return v___x_3559_;
}
v___jp_3560_:
{
if (lean_obj_tag(v___y_3561_) == 0)
{
lean_dec_ref_known(v___y_3561_, 1);
goto v___jp_3557_;
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_a_3562_ = lean_ctor_get(v___y_3561_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___y_3561_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___y_3561_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___y_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3730_, lean_object* v_args_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_params_3739_; lean_object* v_value_3740_; lean_object* v___x_3741_; 
v_params_3739_ = lean_ctor_get(v_funDecl_3730_, 2);
lean_inc_ref(v_params_3739_);
v_value_3740_ = lean_ctor_get(v_funDecl_3730_, 4);
lean_inc_ref(v_value_3740_);
lean_dec_ref(v_funDecl_3730_);
v___x_3741_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3739_, v_args_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3753_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3753_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3753_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
uint8_t v___x_3746_; 
v___x_3746_ = lean_unbox(v_a_3742_);
lean_dec(v_a_3742_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
lean_dec_ref(v_value_3740_);
v___x_3747_ = lean_box(0);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3747_);
v___x_3749_ = v___x_3744_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
else
{
lean_object* v___x_3751_; 
lean_del_object(v___x_3744_);
lean_inc_ref(v_value_3740_);
v___x_3751_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3740_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v___x_3752_; 
lean_dec_ref_known(v___x_3751_, 1);
v___x_3752_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3740_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
return v___x_3752_;
}
else
{
lean_dec_ref(v_value_3740_);
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref(v_value_3740_);
v_a_3754_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3741_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3741_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3762_, lean_object* v_as_3763_, size_t v_sz_3764_, size_t v_i_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_a_3775_; uint8_t v___x_3779_; 
v___x_3779_ = lean_usize_dec_lt(v_i_3765_, v_sz_3764_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v_b_3766_);
return v___x_3780_;
}
else
{
lean_object* v___x_3781_; lean_object* v_a_3782_; 
v___x_3781_ = lean_box(0);
v_a_3782_ = lean_array_uget_borrowed(v_as_3763_, v_i_3765_);
if (lean_obj_tag(v_a_3782_) == 0)
{
lean_object* v_ctorName_3783_; lean_object* v_params_3784_; lean_object* v_code_3785_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3795_; lean_object* v___y_3797_; lean_object* v___x_3798_; 
v_ctorName_3783_ = lean_ctor_get(v_a_3782_, 0);
v_params_3784_ = lean_ctor_get(v_a_3782_, 1);
v_code_3785_ = lean_ctor_get(v_a_3782_, 2);
v___x_3798_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3762_, v_ctorName_3783_);
if (lean_obj_tag(v___x_3798_) == 1)
{
lean_object* v_val_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
v_val_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_val_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v___x_3800_ = l_Array_zip___redArg(v_params_3784_, v_val_3799_);
lean_dec(v_val_3799_);
v___x_3801_ = lean_unsigned_to_nat(0u);
v___x_3802_ = lean_array_get_size(v___x_3800_);
v___x_3803_ = lean_nat_dec_lt(v___x_3801_, v___x_3802_);
if (v___x_3803_ == 0)
{
lean_dec_ref(v___x_3800_);
v___y_3787_ = v___y_3767_;
v___y_3788_ = v___y_3768_;
v___y_3789_ = v___y_3769_;
v___y_3790_ = v___y_3770_;
v___y_3791_ = v___y_3771_;
v___y_3792_ = v___y_3772_;
goto v___jp_3786_;
}
else
{
uint8_t v___x_3804_; 
v___x_3804_ = lean_nat_dec_le(v___x_3802_, v___x_3802_);
if (v___x_3804_ == 0)
{
if (v___x_3803_ == 0)
{
lean_dec_ref(v___x_3800_);
v___y_3787_ = v___y_3767_;
v___y_3788_ = v___y_3768_;
v___y_3789_ = v___y_3769_;
v___y_3790_ = v___y_3770_;
v___y_3791_ = v___y_3771_;
v___y_3792_ = v___y_3772_;
goto v___jp_3786_;
}
else
{
size_t v___x_3805_; size_t v___x_3806_; lean_object* v___x_3807_; 
v___x_3805_ = ((size_t)0ULL);
v___x_3806_ = lean_usize_of_nat(v___x_3802_);
v___x_3807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3800_, v___x_3805_, v___x_3806_, v___x_3781_, v___y_3767_, v___y_3768_, v___y_3772_);
lean_dec_ref(v___x_3800_);
v___y_3795_ = v___x_3807_;
goto v___jp_3794_;
}
}
else
{
size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = ((size_t)0ULL);
v___x_3809_ = lean_usize_of_nat(v___x_3802_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3800_, v___x_3808_, v___x_3809_, v___x_3781_, v___y_3767_, v___y_3768_, v___y_3772_);
lean_dec_ref(v___x_3800_);
v___y_3795_ = v___x_3810_;
goto v___jp_3794_;
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
lean_dec(v___x_3798_);
v___x_3811_ = lean_unsigned_to_nat(0u);
v___x_3812_ = lean_array_get_size(v_params_3784_);
v___x_3813_ = lean_nat_dec_lt(v___x_3811_, v___x_3812_);
if (v___x_3813_ == 0)
{
v___y_3787_ = v___y_3767_;
v___y_3788_ = v___y_3768_;
v___y_3789_ = v___y_3769_;
v___y_3790_ = v___y_3770_;
v___y_3791_ = v___y_3771_;
v___y_3792_ = v___y_3772_;
goto v___jp_3786_;
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_nat_dec_le(v___x_3812_, v___x_3812_);
if (v___x_3814_ == 0)
{
if (v___x_3813_ == 0)
{
v___y_3787_ = v___y_3767_;
v___y_3788_ = v___y_3768_;
v___y_3789_ = v___y_3769_;
v___y_3790_ = v___y_3770_;
v___y_3791_ = v___y_3771_;
v___y_3792_ = v___y_3772_;
goto v___jp_3786_;
}
else
{
size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; 
v___x_3815_ = ((size_t)0ULL);
v___x_3816_ = lean_usize_of_nat(v___x_3812_);
v___x_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3784_, v___x_3815_, v___x_3816_, v___x_3781_, v___y_3767_, v___y_3768_, v___y_3772_);
v___y_3797_ = v___x_3817_;
goto v___jp_3796_;
}
}
else
{
size_t v___x_3818_; size_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = lean_usize_of_nat(v___x_3812_);
v___x_3820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3784_, v___x_3818_, v___x_3819_, v___x_3781_, v___y_3767_, v___y_3768_, v___y_3772_);
v___y_3797_ = v___x_3820_;
goto v___jp_3796_;
}
}
}
v___jp_3786_:
{
lean_object* v___x_3793_; 
lean_inc_ref(v_code_3785_);
v___x_3793_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3785_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_dec_ref_known(v___x_3793_, 1);
v_a_3775_ = v___x_3781_;
goto v___jp_3774_;
}
else
{
return v___x_3793_;
}
}
v___jp_3794_:
{
if (lean_obj_tag(v___y_3795_) == 0)
{
lean_dec_ref_known(v___y_3795_, 1);
v___y_3787_ = v___y_3767_;
v___y_3788_ = v___y_3768_;
v___y_3789_ = v___y_3769_;
v___y_3790_ = v___y_3770_;
v___y_3791_ = v___y_3771_;
v___y_3792_ = v___y_3772_;
goto v___jp_3786_;
}
else
{
return v___y_3795_;
}
}
v___jp_3796_:
{
if (lean_obj_tag(v___y_3797_) == 0)
{
lean_dec_ref_known(v___y_3797_, 1);
v___y_3787_ = v___y_3767_;
v___y_3788_ = v___y_3768_;
v___y_3789_ = v___y_3769_;
v___y_3790_ = v___y_3770_;
v___y_3791_ = v___y_3771_;
v___y_3792_ = v___y_3772_;
goto v___jp_3786_;
}
else
{
return v___y_3797_;
}
}
}
else
{
lean_object* v_code_3821_; lean_object* v___x_3822_; 
v_code_3821_ = lean_ctor_get(v_a_3782_, 0);
lean_inc_ref(v_code_3821_);
v___x_3822_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3821_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_dec_ref_known(v___x_3822_, 1);
v_a_3775_ = v___x_3781_;
goto v___jp_3774_;
}
else
{
return v___x_3822_;
}
}
}
v___jp_3774_:
{
size_t v___x_3776_; size_t v___x_3777_; 
v___x_3776_ = ((size_t)1ULL);
v___x_3777_ = lean_usize_add(v_i_3765_, v___x_3776_);
v_i_3765_ = v___x_3777_;
v_b_3766_ = v_a_3775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v_decl_3832_; lean_object* v_k_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; 
switch(lean_obj_tag(v_x_3823_))
{
case 0:
{
lean_object* v_decl_3843_; lean_object* v_k_3844_; lean_object* v_fvarId_3845_; lean_object* v_value_3846_; lean_object* v___x_3847_; 
v_decl_3843_ = lean_ctor_get(v_x_3823_, 0);
lean_inc_ref(v_decl_3843_);
v_k_3844_ = lean_ctor_get(v_x_3823_, 1);
lean_inc_ref(v_k_3844_);
lean_dec_ref_known(v_x_3823_, 2);
v_fvarId_3845_ = lean_ctor_get(v_decl_3843_, 0);
lean_inc(v_fvarId_3845_);
v_value_3846_ = lean_ctor_get(v_decl_3843_, 3);
lean_inc_n(v_value_3846_, 2);
lean_dec_ref(v_decl_3843_);
v___x_3847_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3846_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3845_, v_a_3848_, v_a_3824_, v_a_3825_, v_a_3829_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_dec_ref_known(v___x_3849_, 1);
if (lean_obj_tag(v_value_3846_) == 4)
{
lean_object* v_fvarId_3850_; lean_object* v_args_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; 
v_fvarId_3850_ = lean_ctor_get(v_value_3846_, 0);
lean_inc(v_fvarId_3850_);
v_args_3851_ = lean_ctor_get(v_value_3846_, 1);
lean_inc_ref(v_args_3851_);
lean_dec_ref_known(v_value_3846_, 2);
v___x_3852_ = 0;
v___x_3853_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3852_, v_fvarId_3850_, v_a_3827_);
lean_dec(v_fvarId_3850_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
if (lean_obj_tag(v_a_3854_) == 1)
{
lean_object* v_val_3855_; lean_object* v___x_3856_; 
v_val_3855_ = lean_ctor_get(v_a_3854_, 0);
lean_inc(v_val_3855_);
lean_dec_ref_known(v_a_3854_, 1);
v___x_3856_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3855_, v_args_3851_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_dec_ref_known(v___x_3856_, 1);
v_x_3823_ = v_k_3844_;
goto _start;
}
else
{
lean_dec_ref(v_k_3844_);
return v___x_3856_;
}
}
else
{
lean_dec(v_a_3854_);
lean_dec_ref(v_args_3851_);
v_x_3823_ = v_k_3844_;
goto _start;
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec_ref(v_args_3851_);
lean_dec_ref(v_k_3844_);
v_a_3859_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3853_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3853_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_dec(v_value_3846_);
v_x_3823_ = v_k_3844_;
goto _start;
}
}
else
{
lean_dec(v_value_3846_);
lean_dec_ref(v_k_3844_);
return v___x_3849_;
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v_value_3846_);
lean_dec(v_fvarId_3845_);
lean_dec_ref(v_k_3844_);
v_a_3868_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3847_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3847_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3876_; lean_object* v_args_3877_; uint8_t v___x_3878_; lean_object* v___x_3879_; 
v_fvarId_3876_ = lean_ctor_get(v_x_3823_, 0);
lean_inc(v_fvarId_3876_);
v_args_3877_ = lean_ctor_get(v_x_3823_, 1);
lean_inc_ref(v_args_3877_);
lean_dec_ref_known(v_x_3823_, 2);
v___x_3878_ = 0;
v___x_3879_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3878_, v_fvarId_3876_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___y_3882_; lean_object* v___x_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3884_ = lean_unsigned_to_nat(0u);
v___x_3885_ = lean_array_get_size(v_args_3877_);
v___x_3886_ = lean_nat_dec_lt(v___x_3884_, v___x_3885_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; 
v___x_3887_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3880_, v_args_3877_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3887_;
}
else
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_nat_dec_le(v___x_3885_, v___x_3885_);
if (v___x_3889_ == 0)
{
if (v___x_3886_ == 0)
{
lean_object* v___x_3890_; 
v___x_3890_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3880_, v_args_3877_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3890_;
}
else
{
size_t v___x_3891_; size_t v___x_3892_; lean_object* v___x_3893_; 
v___x_3891_ = ((size_t)0ULL);
v___x_3892_ = lean_usize_of_nat(v___x_3885_);
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3877_, v___x_3891_, v___x_3892_, v___x_3888_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
v___y_3882_ = v___x_3893_;
goto v___jp_3881_;
}
}
else
{
size_t v___x_3894_; size_t v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = ((size_t)0ULL);
v___x_3895_ = lean_usize_of_nat(v___x_3885_);
v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3877_, v___x_3894_, v___x_3895_, v___x_3888_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
v___y_3882_ = v___x_3896_;
goto v___jp_3881_;
}
}
v___jp_3881_:
{
if (lean_obj_tag(v___y_3882_) == 0)
{
lean_object* v___x_3883_; 
lean_dec_ref_known(v___y_3882_, 1);
v___x_3883_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3880_, v_args_3877_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3883_;
}
else
{
lean_dec(v_a_3880_);
lean_dec_ref(v_args_3877_);
return v___y_3882_;
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec_ref(v_args_3877_);
v_a_3897_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3879_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3879_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
case 4:
{
lean_object* v_cases_3905_; lean_object* v_discr_3906_; lean_object* v_alts_3907_; lean_object* v___x_3908_; 
v_cases_3905_ = lean_ctor_get(v_x_3823_, 0);
lean_inc_ref(v_cases_3905_);
lean_dec_ref_known(v_x_3823_, 1);
v_discr_3906_ = lean_ctor_get(v_cases_3905_, 2);
lean_inc(v_discr_3906_);
v_alts_3907_ = lean_ctor_get(v_cases_3905_, 3);
lean_inc_ref(v_alts_3907_);
lean_dec_ref(v_cases_3905_);
v___x_3908_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3906_, v_a_3824_, v_a_3825_);
lean_dec(v_discr_3906_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; size_t v_sz_3911_; size_t v___x_3912_; lean_object* v___x_3913_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = lean_box(0);
v_sz_3911_ = lean_array_size(v_alts_3907_);
v___x_3912_ = ((size_t)0ULL);
v___x_3913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3909_, v_alts_3907_, v_sz_3911_, v___x_3912_, v___x_3910_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
lean_dec_ref(v_alts_3907_);
lean_dec(v_a_3909_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3920_ == 0)
{
lean_object* v_unused_3921_; 
v_unused_3921_ = lean_ctor_get(v___x_3913_, 0);
lean_dec(v_unused_3921_);
v___x_3915_ = v___x_3913_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_dec(v___x_3913_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3910_);
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3910_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
else
{
return v___x_3913_;
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec_ref(v_alts_3907_);
v_a_3922_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3908_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3908_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3930_; lean_object* v___x_3931_; 
v_fvarId_3930_ = lean_ctor_get(v_x_3823_, 0);
lean_inc(v_fvarId_3930_);
lean_dec_ref_known(v_x_3823_, 1);
v___x_3931_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3930_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v___x_3932_; 
lean_dec_ref_known(v___x_3931_, 1);
v___x_3932_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3930_, v_a_3824_, v_a_3825_);
lean_dec(v_fvarId_3930_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3934_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3934_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3933_, v_a_3824_, v_a_3825_, v_a_3829_);
return v___x_3934_;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
v_a_3935_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3932_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3932_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_dec(v_fvarId_3930_);
return v___x_3931_;
}
}
case 6:
{
lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3950_; 
v_isSharedCheck_3950_ = !lean_is_exclusive(v_x_3823_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; 
v_unused_3951_ = lean_ctor_get(v_x_3823_, 0);
lean_dec(v_unused_3951_);
v___x_3944_ = v_x_3823_;
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
else
{
lean_dec(v_x_3823_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_box(0);
if (v_isShared_3945_ == 0)
{
lean_ctor_set_tag(v___x_3944_, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3946_);
v___x_3948_ = v___x_3944_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
default: 
{
lean_object* v_decl_3952_; lean_object* v_k_3953_; 
v_decl_3952_ = lean_ctor_get(v_x_3823_, 0);
lean_inc_ref(v_decl_3952_);
v_k_3953_ = lean_ctor_get(v_x_3823_, 1);
lean_inc_ref(v_k_3953_);
lean_dec_ref(v_x_3823_);
v_decl_3832_ = v_decl_3952_;
v_k_3833_ = v_k_3953_;
v___y_3834_ = v_a_3824_;
v___y_3835_ = v_a_3825_;
v___y_3836_ = v_a_3826_;
v___y_3837_ = v_a_3827_;
v___y_3838_ = v_a_3828_;
v___y_3839_ = v_a_3829_;
goto v___jp_3831_;
}
}
v___jp_3831_:
{
lean_object* v_value_3840_; lean_object* v___x_3841_; 
v_value_3840_ = lean_ctor_get(v_decl_3832_, 4);
lean_inc_ref(v_value_3840_);
lean_dec_ref(v_decl_3832_);
v___x_3841_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3840_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_dec_ref_known(v___x_3841_, 1);
v_x_3823_ = v_k_3833_;
v_a_3824_ = v___y_3834_;
v_a_3825_ = v___y_3835_;
v_a_3826_ = v___y_3836_;
v_a_3827_ = v___y_3837_;
v_a_3828_ = v___y_3838_;
v_a_3829_ = v___y_3839_;
goto _start;
}
else
{
lean_dec_ref(v_k_3833_);
return v___x_3841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
uint8_t v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = 0;
v___x_3963_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3962_, v_var_3954_, v_a_3958_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3996_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3996_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3996_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
if (lean_obj_tag(v_a_3964_) == 1)
{
lean_object* v_val_3968_; lean_object* v_params_3969_; lean_object* v_value_3970_; lean_object* v___x_3971_; 
lean_del_object(v___x_3966_);
v_val_3968_ = lean_ctor_get(v_a_3964_, 0);
lean_inc(v_val_3968_);
lean_dec_ref_known(v_a_3964_, 1);
v_params_3969_ = lean_ctor_get(v_val_3968_, 2);
lean_inc_ref(v_params_3969_);
v_value_3970_ = lean_ctor_get(v_val_3968_, 4);
lean_inc_ref(v_value_3970_);
lean_dec(v_val_3968_);
v___x_3971_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3969_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
lean_dec_ref(v_params_3969_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3983_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3974_ = v___x_3971_;
v_isShared_3975_ = v_isSharedCheck_3983_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3983_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
uint8_t v___x_3976_; 
v___x_3976_ = lean_unbox(v_a_3972_);
lean_dec(v_a_3972_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3979_; 
lean_dec_ref(v_value_3970_);
v___x_3977_ = lean_box(0);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3977_);
v___x_3979_ = v___x_3974_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
else
{
lean_object* v___x_3981_; 
lean_del_object(v___x_3974_);
lean_inc_ref(v_value_3970_);
v___x_3981_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3970_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v___x_3982_; 
lean_dec_ref_known(v___x_3981_, 1);
v___x_3982_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3970_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
return v___x_3982_;
}
else
{
lean_dec_ref(v_value_3970_);
return v___x_3981_;
}
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec_ref(v_value_3970_);
v_a_3984_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3971_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3971_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
else
{
lean_object* v___x_3992_; lean_object* v___x_3994_; 
lean_dec(v_a_3964_);
v___x_3992_ = lean_box(0);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3992_);
v___x_3994_ = v___x_3966_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
v_a_3997_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3963_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3963_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
if (lean_obj_tag(v_arg_4005_) == 1)
{
lean_object* v_fvarId_4013_; lean_object* v___x_4014_; 
v_fvarId_4013_ = lean_ctor_get(v_arg_4005_, 0);
v___x_4014_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4013_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
return v___x_4014_;
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4015_ = lean_box(0);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_arg_4017_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_4026_, lean_object* v_i_4027_, lean_object* v_stop_4028_, lean_object* v_b_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
size_t v_i_boxed_4037_; size_t v_stop_boxed_4038_; lean_object* v_res_4039_; 
v_i_boxed_4037_ = lean_unbox_usize(v_i_4027_);
lean_dec(v_i_4027_);
v_stop_boxed_4038_ = lean_unbox_usize(v_stop_4028_);
lean_dec(v_stop_4028_);
v_res_4039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_4026_, v_i_boxed_4037_, v_stop_boxed_4038_, v_b_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec_ref(v_as_4026_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_4040_, lean_object* v_args_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_4040_, v_args_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_var_4050_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4059_, lean_object* v_as_4060_, lean_object* v_sz_4061_, lean_object* v_i_4062_, lean_object* v_b_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
size_t v_sz_boxed_4071_; size_t v_i_boxed_4072_; lean_object* v_res_4073_; 
v_sz_boxed_4071_ = lean_unbox_usize(v_sz_4061_);
lean_dec(v_sz_4061_);
v_i_boxed_4072_ = lean_unbox_usize(v_i_4062_);
lean_dec(v_i_4062_);
v_res_4073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4059_, v_as_4060_, v_sz_boxed_4071_, v_i_boxed_4072_, v_b_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec_ref(v_as_4060_);
lean_dec(v_a_4059_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4092_, lean_object* v_R_4093_, lean_object* v_a_4094_, lean_object* v_b_4095_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4094_, v_b_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4097_, size_t v_i_4098_, lean_object* v_bs_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4097_, v_i_4098_, v_bs_4099_, v___y_4100_, v___y_4101_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4108_, lean_object* v_i_4109_, lean_object* v_bs_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
size_t v_sz_boxed_4118_; size_t v_i_boxed_4119_; lean_object* v_res_4120_; 
v_sz_boxed_4118_ = lean_unbox_usize(v_sz_4108_);
lean_dec(v_sz_4108_);
v_i_boxed_4119_ = lean_unbox_usize(v_i_4109_);
lean_dec(v_i_4109_);
v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4118_, v_i_boxed_4119_, v_bs_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4121_, size_t v_i_4122_, size_t v_stop_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4121_, v_i_4122_, v_stop_4123_, v_b_4124_, v___y_4125_, v___y_4126_, v___y_4130_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4133_, lean_object* v_i_4134_, lean_object* v_stop_4135_, lean_object* v_b_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
size_t v_i_boxed_4144_; size_t v_stop_boxed_4145_; lean_object* v_res_4146_; 
v_i_boxed_4144_ = lean_unbox_usize(v_i_4134_);
lean_dec(v_i_4134_);
v_stop_boxed_4145_ = lean_unbox_usize(v_stop_4135_);
lean_dec(v_stop_4135_);
v_res_4146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4133_, v_i_boxed_4144_, v_stop_boxed_4145_, v_b_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec_ref(v_as_4133_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4147_, size_t v_i_4148_, size_t v_stop_4149_, lean_object* v_b_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4147_, v_i_4148_, v_stop_4149_, v_b_4150_, v___y_4151_, v___y_4152_, v___y_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4159_, lean_object* v_i_4160_, lean_object* v_stop_4161_, lean_object* v_b_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
size_t v_i_boxed_4170_; size_t v_stop_boxed_4171_; lean_object* v_res_4172_; 
v_i_boxed_4170_ = lean_unbox_usize(v_i_4160_);
lean_dec(v_i_4160_);
v_stop_boxed_4171_ = lean_unbox_usize(v_stop_4161_);
lean_dec(v_stop_4161_);
v_res_4172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4159_, v_i_boxed_4170_, v_stop_boxed_4171_, v_b_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec_ref(v_as_4159_);
return v_res_4172_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4173_ = lean_unsigned_to_nat(32u);
v___x_4174_ = lean_mk_empty_array_with_capacity(v___x_4173_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4176_ = ((size_t)5ULL);
v___x_4177_ = lean_unsigned_to_nat(0u);
v___x_4178_ = lean_unsigned_to_nat(32u);
v___x_4179_ = lean_mk_empty_array_with_capacity(v___x_4178_);
v___x_4180_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4181_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
lean_ctor_set(v___x_4181_, 1, v___x_4179_);
lean_ctor_set(v___x_4181_, 2, v___x_4177_);
lean_ctor_set(v___x_4181_, 3, v___x_4177_);
lean_ctor_set_usize(v___x_4181_, 4, v___x_4176_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4182_){
_start:
{
lean_object* v___x_4184_; lean_object* v_traceState_4185_; lean_object* v_traces_4186_; lean_object* v___x_4187_; lean_object* v_traceState_4188_; lean_object* v_env_4189_; lean_object* v_nextMacroScope_4190_; lean_object* v_ngen_4191_; lean_object* v_auxDeclNGen_4192_; lean_object* v_cache_4193_; lean_object* v_messages_4194_; lean_object* v_infoState_4195_; lean_object* v_snapshotTasks_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4215_; 
v___x_4184_ = lean_st_ref_get(v___y_4182_);
v_traceState_4185_ = lean_ctor_get(v___x_4184_, 4);
lean_inc_ref(v_traceState_4185_);
lean_dec(v___x_4184_);
v_traces_4186_ = lean_ctor_get(v_traceState_4185_, 0);
lean_inc_ref(v_traces_4186_);
lean_dec_ref(v_traceState_4185_);
v___x_4187_ = lean_st_ref_take(v___y_4182_);
v_traceState_4188_ = lean_ctor_get(v___x_4187_, 4);
v_env_4189_ = lean_ctor_get(v___x_4187_, 0);
v_nextMacroScope_4190_ = lean_ctor_get(v___x_4187_, 1);
v_ngen_4191_ = lean_ctor_get(v___x_4187_, 2);
v_auxDeclNGen_4192_ = lean_ctor_get(v___x_4187_, 3);
v_cache_4193_ = lean_ctor_get(v___x_4187_, 5);
v_messages_4194_ = lean_ctor_get(v___x_4187_, 6);
v_infoState_4195_ = lean_ctor_get(v___x_4187_, 7);
v_snapshotTasks_4196_ = lean_ctor_get(v___x_4187_, 8);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4198_ = v___x_4187_;
v_isShared_4199_ = v_isSharedCheck_4215_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_snapshotTasks_4196_);
lean_inc(v_infoState_4195_);
lean_inc(v_messages_4194_);
lean_inc(v_cache_4193_);
lean_inc(v_traceState_4188_);
lean_inc(v_auxDeclNGen_4192_);
lean_inc(v_ngen_4191_);
lean_inc(v_nextMacroScope_4190_);
lean_inc(v_env_4189_);
lean_dec(v___x_4187_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4215_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
uint64_t v_tid_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4213_; 
v_tid_4200_ = lean_ctor_get_uint64(v_traceState_4188_, sizeof(void*)*1);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_traceState_4188_);
if (v_isSharedCheck_4213_ == 0)
{
lean_object* v_unused_4214_; 
v_unused_4214_ = lean_ctor_get(v_traceState_4188_, 0);
lean_dec(v_unused_4214_);
v___x_4202_ = v_traceState_4188_;
v_isShared_4203_ = v_isSharedCheck_4213_;
goto v_resetjp_4201_;
}
else
{
lean_dec(v_traceState_4188_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4213_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; lean_object* v___x_4206_; 
v___x_4204_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4204_);
v___x_4206_ = v___x_4202_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4204_);
lean_ctor_set_uint64(v_reuseFailAlloc_4212_, sizeof(void*)*1, v_tid_4200_);
v___x_4206_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4208_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 4, v___x_4206_);
v___x_4208_ = v___x_4198_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_env_4189_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_nextMacroScope_4190_);
lean_ctor_set(v_reuseFailAlloc_4211_, 2, v_ngen_4191_);
lean_ctor_set(v_reuseFailAlloc_4211_, 3, v_auxDeclNGen_4192_);
lean_ctor_set(v_reuseFailAlloc_4211_, 4, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4211_, 5, v_cache_4193_);
lean_ctor_set(v_reuseFailAlloc_4211_, 6, v_messages_4194_);
lean_ctor_set(v_reuseFailAlloc_4211_, 7, v_infoState_4195_);
lean_ctor_set(v_reuseFailAlloc_4211_, 8, v_snapshotTasks_4196_);
v___x_4208_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4209_ = lean_st_ref_put(v___y_4182_, v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_traces_4186_);
return v___x_4210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4216_);
lean_dec(v___y_4216_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4224_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
return v_res_4234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4235_, lean_object* v_opt_4236_){
_start:
{
lean_object* v_name_4237_; lean_object* v_defValue_4238_; lean_object* v_map_4239_; lean_object* v___x_4240_; 
v_name_4237_ = lean_ctor_get(v_opt_4236_, 0);
v_defValue_4238_ = lean_ctor_get(v_opt_4236_, 1);
v_map_4239_ = lean_ctor_get(v_opts_4235_, 0);
v___x_4240_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4239_, v_name_4237_);
if (lean_obj_tag(v___x_4240_) == 0)
{
uint8_t v___x_4241_; 
v___x_4241_ = lean_unbox(v_defValue_4238_);
return v___x_4241_;
}
else
{
lean_object* v_val_4242_; 
v_val_4242_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_val_4242_);
lean_dec_ref_known(v___x_4240_, 1);
if (lean_obj_tag(v_val_4242_) == 1)
{
uint8_t v_v_4243_; 
v_v_4243_ = lean_ctor_get_uint8(v_val_4242_, 0);
lean_dec_ref_known(v_val_4242_, 0);
return v_v_4243_;
}
else
{
uint8_t v___x_4244_; 
lean_dec(v_val_4242_);
v___x_4244_ = lean_unbox(v_defValue_4238_);
return v___x_4244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4245_, lean_object* v_opt_4246_){
_start:
{
uint8_t v_res_4247_; lean_object* v_r_4248_; 
v_res_4247_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4245_, v_opt_4246_);
lean_dec_ref(v_opt_4246_);
lean_dec_ref(v_opts_4245_);
v_r_4248_ = lean_box(v_res_4247_);
return v_r_4248_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4251_ = l_Lean_stringToMessageData(v___x_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4252_, lean_object* v_x_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4261_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4262_ = l_Lean_MessageData_ofName(v_name_4252_);
v___x_4263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4261_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4265_, lean_object* v_x_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4265_, v_x_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec_ref(v_x_4266_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4275_, lean_object* v_opt_4276_){
_start:
{
lean_object* v_name_4277_; lean_object* v_defValue_4278_; lean_object* v_map_4279_; lean_object* v___x_4280_; 
v_name_4277_ = lean_ctor_get(v_opt_4276_, 0);
v_defValue_4278_ = lean_ctor_get(v_opt_4276_, 1);
v_map_4279_ = lean_ctor_get(v_opts_4275_, 0);
v___x_4280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4279_, v_name_4277_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_inc(v_defValue_4278_);
return v_defValue_4278_;
}
else
{
lean_object* v_val_4281_; 
v_val_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_val_4281_);
lean_dec_ref_known(v___x_4280_, 1);
if (lean_obj_tag(v_val_4281_) == 3)
{
lean_object* v_v_4282_; 
v_v_4282_ = lean_ctor_get(v_val_4281_, 0);
lean_inc(v_v_4282_);
lean_dec_ref_known(v_val_4281_, 1);
return v_v_4282_;
}
else
{
lean_dec(v_val_4281_);
lean_inc(v_defValue_4278_);
return v_defValue_4278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4283_, lean_object* v_opt_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4283_, v_opt_4284_);
lean_dec_ref(v_opt_4284_);
lean_dec_ref(v_opts_4283_);
return v_res_4285_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4286_){
_start:
{
if (lean_obj_tag(v_e_4286_) == 0)
{
uint8_t v___x_4287_; 
v___x_4287_ = 2;
return v___x_4287_;
}
else
{
uint8_t v___x_4288_; 
v___x_4288_ = 0;
return v___x_4288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4289_){
_start:
{
uint8_t v_res_4290_; lean_object* v_r_4291_; 
v_res_4290_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4289_);
lean_dec_ref(v_e_4289_);
v_r_4291_ = lean_box(v_res_4290_);
return v_r_4291_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4292_){
_start:
{
if (lean_obj_tag(v_x_4292_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
v_a_4294_ = lean_ctor_get(v_x_4292_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v_x_4292_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v_x_4292_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v_x_4292_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 1);
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_a_4302_ = lean_ctor_get(v_x_4292_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v_x_4292_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v_x_4292_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v_x_4292_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set_tag(v___x_4304_, 0);
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4310_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4313_, size_t v_i_4314_, lean_object* v_bs_4315_){
_start:
{
uint8_t v___x_4316_; 
v___x_4316_ = lean_usize_dec_lt(v_i_4314_, v_sz_4313_);
if (v___x_4316_ == 0)
{
return v_bs_4315_;
}
else
{
lean_object* v_v_4317_; lean_object* v_msg_4318_; lean_object* v___x_4319_; lean_object* v_bs_x27_4320_; size_t v___x_4321_; size_t v___x_4322_; lean_object* v___x_4323_; 
v_v_4317_ = lean_array_uget_borrowed(v_bs_4315_, v_i_4314_);
v_msg_4318_ = lean_ctor_get(v_v_4317_, 1);
lean_inc_ref(v_msg_4318_);
v___x_4319_ = lean_unsigned_to_nat(0u);
v_bs_x27_4320_ = lean_array_uset(v_bs_4315_, v_i_4314_, v___x_4319_);
v___x_4321_ = ((size_t)1ULL);
v___x_4322_ = lean_usize_add(v_i_4314_, v___x_4321_);
v___x_4323_ = lean_array_uset(v_bs_x27_4320_, v_i_4314_, v_msg_4318_);
v_i_4314_ = v___x_4322_;
v_bs_4315_ = v___x_4323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4325_, lean_object* v_i_4326_, lean_object* v_bs_4327_){
_start:
{
size_t v_sz_boxed_4328_; size_t v_i_boxed_4329_; lean_object* v_res_4330_; 
v_sz_boxed_4328_ = lean_unbox_usize(v_sz_4325_);
lean_dec(v_sz_4325_);
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4328_, v_i_boxed_4329_, v_bs_4327_);
return v_res_4330_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4331_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
return v___x_4333_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4335_ = lean_unsigned_to_nat(0u);
v___x_4336_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
lean_ctor_set(v___x_4336_, 2, v___x_4335_);
lean_ctor_set(v___x_4336_, 3, v___x_4335_);
lean_ctor_set(v___x_4336_, 4, v___x_4334_);
lean_ctor_set(v___x_4336_, 5, v___x_4334_);
lean_ctor_set(v___x_4336_, 6, v___x_4334_);
lean_ctor_set(v___x_4336_, 7, v___x_4334_);
lean_ctor_set(v___x_4336_, 8, v___x_4334_);
lean_ctor_set(v___x_4336_, 9, v___x_4334_);
lean_ctor_set(v___x_4336_, 10, v___x_4334_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4337_, lean_object* v_data_4338_, lean_object* v_ref_4339_, lean_object* v_msg_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_options_4346_; lean_object* v___x_4347_; lean_object* v_traceState_4348_; lean_object* v_traces_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_options_4346_ = lean_ctor_get(v___y_4343_, 2);
v___x_4347_ = lean_st_ref_get(v___y_4344_);
v_traceState_4348_ = lean_ctor_get(v___x_4347_, 4);
lean_inc_ref(v_traceState_4348_);
lean_dec(v___x_4347_);
v_traces_4349_ = lean_ctor_get(v_traceState_4348_, 0);
lean_inc_ref(v_traces_4349_);
lean_dec_ref(v_traceState_4348_);
v___x_4350_ = lean_st_ref_get(v___y_4344_);
v___x_4351_ = lean_st_ref_get(v___y_4342_);
v___x_4352_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4341_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4409_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4409_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4409_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v_env_4357_; lean_object* v_lctx_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4407_; 
v_env_4357_ = lean_ctor_get(v___x_4350_, 0);
lean_inc_ref(v_env_4357_);
lean_dec(v___x_4350_);
v_lctx_4358_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4407_ == 0)
{
lean_object* v_unused_4408_; 
v_unused_4408_ = lean_ctor_get(v___x_4351_, 1);
lean_dec(v_unused_4408_);
v___x_4360_ = v___x_4351_;
v_isShared_4361_ = v_isSharedCheck_4407_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_lctx_4358_);
lean_dec(v___x_4351_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4407_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v_traceState_4364_; lean_object* v_env_4365_; lean_object* v_nextMacroScope_4366_; lean_object* v_ngen_4367_; lean_object* v_auxDeclNGen_4368_; lean_object* v_cache_4369_; lean_object* v_messages_4370_; lean_object* v_infoState_4371_; lean_object* v_snapshotTasks_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4406_; 
v___x_4362_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4363_ = lean_st_ref_take(v___y_4344_);
v_traceState_4364_ = lean_ctor_get(v___x_4363_, 4);
v_env_4365_ = lean_ctor_get(v___x_4363_, 0);
v_nextMacroScope_4366_ = lean_ctor_get(v___x_4363_, 1);
v_ngen_4367_ = lean_ctor_get(v___x_4363_, 2);
v_auxDeclNGen_4368_ = lean_ctor_get(v___x_4363_, 3);
v_cache_4369_ = lean_ctor_get(v___x_4363_, 5);
v_messages_4370_ = lean_ctor_get(v___x_4363_, 6);
v_infoState_4371_ = lean_ctor_get(v___x_4363_, 7);
v_snapshotTasks_4372_ = lean_ctor_get(v___x_4363_, 8);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4374_ = v___x_4363_;
v_isShared_4375_ = v_isSharedCheck_4406_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_snapshotTasks_4372_);
lean_inc(v_infoState_4371_);
lean_inc(v_messages_4370_);
lean_inc(v_cache_4369_);
lean_inc(v_traceState_4364_);
lean_inc(v_auxDeclNGen_4368_);
lean_inc(v_ngen_4367_);
lean_inc(v_nextMacroScope_4366_);
lean_inc(v_env_4365_);
lean_dec(v___x_4363_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4406_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
uint64_t v_tid_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4404_; 
v_tid_4376_ = lean_ctor_get_uint64(v_traceState_4364_, sizeof(void*)*1);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_traceState_4364_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v_traceState_4364_, 0);
lean_dec(v_unused_4405_);
v___x_4378_ = v_traceState_4364_;
v_isShared_4379_ = v_isSharedCheck_4404_;
goto v_resetjp_4377_;
}
else
{
lean_dec(v_traceState_4364_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4404_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; size_t v_sz_4381_; size_t v___x_4382_; lean_object* v___x_4383_; lean_object* v_msg_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; 
v___x_4380_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4349_);
lean_dec_ref(v_traces_4349_);
v_sz_4381_ = lean_array_size(v___x_4380_);
v___x_4382_ = ((size_t)0ULL);
v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4381_, v___x_4382_, v___x_4380_);
v_msg_4384_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4384_, 0, v_data_4338_);
lean_ctor_set(v_msg_4384_, 1, v_msg_4340_);
lean_ctor_set(v_msg_4384_, 2, v___x_4383_);
v___x_4385_ = lean_unbox(v_a_4353_);
lean_dec(v_a_4353_);
v___x_4386_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4358_, v___x_4385_);
lean_dec_ref(v_lctx_4358_);
lean_inc_ref(v_options_4346_);
v___x_4387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4387_, 0, v_env_4357_);
lean_ctor_set(v___x_4387_, 1, v___x_4362_);
lean_ctor_set(v___x_4387_, 2, v___x_4386_);
lean_ctor_set(v___x_4387_, 3, v_options_4346_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set_tag(v___x_4360_, 3);
lean_ctor_set(v___x_4360_, 1, v_msg_4384_);
lean_ctor_set(v___x_4360_, 0, v___x_4387_);
v___x_4389_ = v___x_4360_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_msg_4384_);
v___x_4389_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v_ref_4339_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4337_, v___x_4390_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4391_);
v___x_4393_ = v___x_4378_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4391_);
lean_ctor_set_uint64(v_reuseFailAlloc_4402_, sizeof(void*)*1, v_tid_4376_);
v___x_4393_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4395_; 
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 4, v___x_4393_);
v___x_4395_ = v___x_4374_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_env_4365_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_nextMacroScope_4366_);
lean_ctor_set(v_reuseFailAlloc_4401_, 2, v_ngen_4367_);
lean_ctor_set(v_reuseFailAlloc_4401_, 3, v_auxDeclNGen_4368_);
lean_ctor_set(v_reuseFailAlloc_4401_, 4, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4401_, 5, v_cache_4369_);
lean_ctor_set(v_reuseFailAlloc_4401_, 6, v_messages_4370_);
lean_ctor_set(v_reuseFailAlloc_4401_, 7, v_infoState_4371_);
lean_ctor_set(v_reuseFailAlloc_4401_, 8, v_snapshotTasks_4372_);
v___x_4395_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4396_ = lean_st_ref_put(v___y_4344_, v___x_4395_);
v___x_4397_ = lean_box(0);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4397_);
v___x_4399_ = v___x_4355_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
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
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v___x_4351_);
lean_dec(v___x_4350_);
lean_dec_ref(v_traces_4349_);
lean_dec_ref(v_msg_4340_);
lean_dec(v_ref_4339_);
lean_dec_ref(v_data_4338_);
lean_dec_ref(v_oldTraces_4337_);
v_a_4410_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4352_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4352_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4418_, lean_object* v_data_4419_, lean_object* v_ref_4420_, lean_object* v_msg_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4418_, v_data_4419_, v_ref_4420_, v_msg_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
return v_res_4427_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4428_; double v___x_4429_; 
v___x_4428_ = lean_unsigned_to_nat(0u);
v___x_4429_ = lean_float_of_nat(v___x_4428_);
return v___x_4429_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4432_ = l_Lean_stringToMessageData(v___x_4431_);
return v___x_4432_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4433_; double v___x_4434_; 
v___x_4433_ = lean_unsigned_to_nat(1000u);
v___x_4434_ = lean_float_of_nat(v___x_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4435_, uint8_t v_collapsed_4436_, lean_object* v_tag_4437_, lean_object* v_opts_4438_, uint8_t v_clsEnabled_4439_, lean_object* v_oldTraces_4440_, lean_object* v_msg_4441_, lean_object* v_resStartStop_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v_fst_4450_; lean_object* v_snd_4451_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v_data_4455_; lean_object* v_fst_4458_; lean_object* v_snd_4459_; lean_object* v___x_4460_; uint8_t v___x_4461_; lean_object* v___y_4463_; lean_object* v_a_4464_; uint8_t v___y_4479_; double v___y_4510_; 
v_fst_4450_ = lean_ctor_get(v_resStartStop_4442_, 0);
lean_inc(v_fst_4450_);
v_snd_4451_ = lean_ctor_get(v_resStartStop_4442_, 1);
lean_inc(v_snd_4451_);
lean_dec_ref(v_resStartStop_4442_);
v_fst_4458_ = lean_ctor_get(v_snd_4451_, 0);
lean_inc(v_fst_4458_);
v_snd_4459_ = lean_ctor_get(v_snd_4451_, 1);
lean_inc(v_snd_4459_);
lean_dec(v_snd_4451_);
v___x_4460_ = l_Lean_trace_profiler;
v___x_4461_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4438_, v___x_4460_);
if (v___x_4461_ == 0)
{
v___y_4479_ = v___x_4461_;
goto v___jp_4478_;
}
else
{
lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4515_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4516_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4438_, v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; double v___x_4519_; double v___x_4520_; double v___x_4521_; 
v___x_4517_ = l_Lean_trace_profiler_threshold;
v___x_4518_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4438_, v___x_4517_);
v___x_4519_ = lean_float_of_nat(v___x_4518_);
v___x_4520_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4521_ = lean_float_div(v___x_4519_, v___x_4520_);
v___y_4510_ = v___x_4521_;
goto v___jp_4509_;
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4523_; double v___x_4524_; 
v___x_4522_ = l_Lean_trace_profiler_threshold;
v___x_4523_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4438_, v___x_4522_);
v___x_4524_ = lean_float_of_nat(v___x_4523_);
v___y_4510_ = v___x_4524_;
goto v___jp_4509_;
}
}
v___jp_4452_:
{
lean_object* v___x_4456_; 
lean_inc(v___y_4453_);
v___x_4456_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4440_, v_data_4455_, v___y_4453_, v___y_4454_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v___x_4457_; 
lean_dec_ref_known(v___x_4456_, 1);
v___x_4457_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4450_);
return v___x_4457_;
}
else
{
lean_dec(v_fst_4450_);
return v___x_4456_;
}
}
v___jp_4462_:
{
uint8_t v_result_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; double v___x_4468_; lean_object* v_data_4469_; 
v_result_4465_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4450_);
v___x_4466_ = lean_box(v_result_4465_);
v___x_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
v___x_4468_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4437_);
lean_inc_ref(v___x_4467_);
lean_inc(v_cls_4435_);
v_data_4469_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4469_, 0, v_cls_4435_);
lean_ctor_set(v_data_4469_, 1, v___x_4467_);
lean_ctor_set(v_data_4469_, 2, v_tag_4437_);
lean_ctor_set_float(v_data_4469_, sizeof(void*)*3, v___x_4468_);
lean_ctor_set_float(v_data_4469_, sizeof(void*)*3 + 8, v___x_4468_);
lean_ctor_set_uint8(v_data_4469_, sizeof(void*)*3 + 16, v_collapsed_4436_);
if (v___x_4461_ == 0)
{
lean_dec_ref_known(v___x_4467_, 1);
lean_dec(v_snd_4459_);
lean_dec(v_fst_4458_);
lean_dec_ref(v_tag_4437_);
lean_dec(v_cls_4435_);
v___y_4453_ = v___y_4463_;
v___y_4454_ = v_a_4464_;
v_data_4455_ = v_data_4469_;
goto v___jp_4452_;
}
else
{
lean_object* v_data_4470_; double v___x_4471_; double v___x_4472_; 
lean_dec_ref_known(v_data_4469_, 3);
v_data_4470_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4470_, 0, v_cls_4435_);
lean_ctor_set(v_data_4470_, 1, v___x_4467_);
lean_ctor_set(v_data_4470_, 2, v_tag_4437_);
v___x_4471_ = lean_unbox_float(v_fst_4458_);
lean_dec(v_fst_4458_);
lean_ctor_set_float(v_data_4470_, sizeof(void*)*3, v___x_4471_);
v___x_4472_ = lean_unbox_float(v_snd_4459_);
lean_dec(v_snd_4459_);
lean_ctor_set_float(v_data_4470_, sizeof(void*)*3 + 8, v___x_4472_);
lean_ctor_set_uint8(v_data_4470_, sizeof(void*)*3 + 16, v_collapsed_4436_);
v___y_4453_ = v___y_4463_;
v___y_4454_ = v_a_4464_;
v_data_4455_ = v_data_4470_;
goto v___jp_4452_;
}
}
v___jp_4473_:
{
lean_object* v_ref_4474_; lean_object* v___x_4475_; 
v_ref_4474_ = lean_ctor_get(v___y_4447_, 5);
lean_inc(v___y_4448_);
lean_inc_ref(v___y_4447_);
lean_inc(v___y_4446_);
lean_inc_ref(v___y_4445_);
lean_inc(v___y_4444_);
lean_inc_ref(v___y_4443_);
lean_inc(v_fst_4450_);
v___x_4475_ = lean_apply_8(v_msg_4441_, v_fst_4450_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, lean_box(0));
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4475_, 1);
v___y_4463_ = v_ref_4474_;
v_a_4464_ = v_a_4476_;
goto v___jp_4462_;
}
else
{
lean_object* v___x_4477_; 
lean_dec_ref_known(v___x_4475_, 1);
v___x_4477_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4463_ = v_ref_4474_;
v_a_4464_ = v___x_4477_;
goto v___jp_4462_;
}
}
v___jp_4478_:
{
if (v_clsEnabled_4439_ == 0)
{
if (v___y_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v_traceState_4481_; lean_object* v_env_4482_; lean_object* v_nextMacroScope_4483_; lean_object* v_ngen_4484_; lean_object* v_auxDeclNGen_4485_; lean_object* v_cache_4486_; lean_object* v_messages_4487_; lean_object* v_infoState_4488_; lean_object* v_snapshotTasks_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v_snd_4459_);
lean_dec(v_fst_4458_);
lean_dec_ref(v_msg_4441_);
lean_dec_ref(v_tag_4437_);
lean_dec(v_cls_4435_);
v___x_4480_ = lean_st_ref_take(v___y_4448_);
v_traceState_4481_ = lean_ctor_get(v___x_4480_, 4);
v_env_4482_ = lean_ctor_get(v___x_4480_, 0);
v_nextMacroScope_4483_ = lean_ctor_get(v___x_4480_, 1);
v_ngen_4484_ = lean_ctor_get(v___x_4480_, 2);
v_auxDeclNGen_4485_ = lean_ctor_get(v___x_4480_, 3);
v_cache_4486_ = lean_ctor_get(v___x_4480_, 5);
v_messages_4487_ = lean_ctor_get(v___x_4480_, 6);
v_infoState_4488_ = lean_ctor_get(v___x_4480_, 7);
v_snapshotTasks_4489_ = lean_ctor_get(v___x_4480_, 8);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4491_ = v___x_4480_;
v_isShared_4492_ = v_isSharedCheck_4508_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_snapshotTasks_4489_);
lean_inc(v_infoState_4488_);
lean_inc(v_messages_4487_);
lean_inc(v_cache_4486_);
lean_inc(v_traceState_4481_);
lean_inc(v_auxDeclNGen_4485_);
lean_inc(v_ngen_4484_);
lean_inc(v_nextMacroScope_4483_);
lean_inc(v_env_4482_);
lean_dec(v___x_4480_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4508_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
uint64_t v_tid_4493_; lean_object* v_traces_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4507_; 
v_tid_4493_ = lean_ctor_get_uint64(v_traceState_4481_, sizeof(void*)*1);
v_traces_4494_ = lean_ctor_get(v_traceState_4481_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v_traceState_4481_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4496_ = v_traceState_4481_;
v_isShared_4497_ = v_isSharedCheck_4507_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_traces_4494_);
lean_dec(v_traceState_4481_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4507_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; lean_object* v___x_4500_; 
v___x_4498_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4440_, v_traces_4494_);
lean_dec_ref(v_traces_4494_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v___x_4498_);
v___x_4500_ = v___x_4496_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4498_);
lean_ctor_set_uint64(v_reuseFailAlloc_4506_, sizeof(void*)*1, v_tid_4493_);
v___x_4500_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4502_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 4, v___x_4500_);
v___x_4502_ = v___x_4491_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_env_4482_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_nextMacroScope_4483_);
lean_ctor_set(v_reuseFailAlloc_4505_, 2, v_ngen_4484_);
lean_ctor_set(v_reuseFailAlloc_4505_, 3, v_auxDeclNGen_4485_);
lean_ctor_set(v_reuseFailAlloc_4505_, 4, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4505_, 5, v_cache_4486_);
lean_ctor_set(v_reuseFailAlloc_4505_, 6, v_messages_4487_);
lean_ctor_set(v_reuseFailAlloc_4505_, 7, v_infoState_4488_);
lean_ctor_set(v_reuseFailAlloc_4505_, 8, v_snapshotTasks_4489_);
v___x_4502_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = lean_st_ref_put(v___y_4448_, v___x_4502_);
v___x_4504_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4450_);
return v___x_4504_;
}
}
}
}
}
else
{
goto v___jp_4473_;
}
}
else
{
goto v___jp_4473_;
}
}
v___jp_4509_:
{
double v___x_4511_; double v___x_4512_; double v___x_4513_; uint8_t v___x_4514_; 
v___x_4511_ = lean_unbox_float(v_snd_4459_);
v___x_4512_ = lean_unbox_float(v_fst_4458_);
v___x_4513_ = lean_float_sub(v___x_4511_, v___x_4512_);
v___x_4514_ = lean_float_decLt(v___y_4510_, v___x_4513_);
v___y_4479_ = v___x_4514_;
goto v___jp_4478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4525_, lean_object* v_collapsed_4526_, lean_object* v_tag_4527_, lean_object* v_opts_4528_, lean_object* v_clsEnabled_4529_, lean_object* v_oldTraces_4530_, lean_object* v_msg_4531_, lean_object* v_resStartStop_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
uint8_t v_collapsed_boxed_4540_; uint8_t v_clsEnabled_boxed_4541_; lean_object* v_res_4542_; 
v_collapsed_boxed_4540_ = lean_unbox(v_collapsed_4526_);
v_clsEnabled_boxed_4541_ = lean_unbox(v_clsEnabled_4529_);
v_res_4542_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4525_, v_collapsed_boxed_4540_, v_tag_4527_, v_opts_4528_, v_clsEnabled_boxed_4541_, v_oldTraces_4530_, v_msg_4531_, v_resStartStop_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec_ref(v_opts_4528_);
return v_res_4542_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4546_; double v___x_4547_; 
v___x_4546_ = lean_unsigned_to_nat(1000000000u);
v___x_4547_ = lean_float_of_nat(v___x_4546_);
return v___x_4547_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4556_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4558_ = l_Lean_Name_append(v___x_4557_, v___x_4556_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4559_, lean_object* v___x_4560_, lean_object* v_a_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v_a_4571_; uint8_t v___x_4575_; 
v___x_4575_ = lean_nat_dec_lt(v_a_4561_, v_upperBound_4559_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; 
lean_dec(v_a_4561_);
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v_b_4562_);
return v___x_4576_;
}
else
{
lean_object* v___x_4577_; lean_object* v_toSignature_4578_; lean_object* v_value_4579_; lean_object* v_name_4580_; lean_object* v_params_4581_; uint8_t v_safe_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
lean_dec_ref(v_b_4562_);
v___x_4577_ = lean_array_fget_borrowed(v___x_4560_, v_a_4561_);
v_toSignature_4578_ = lean_ctor_get(v___x_4577_, 0);
v_value_4579_ = lean_ctor_get(v___x_4577_, 1);
v_name_4580_ = lean_ctor_get(v_toSignature_4578_, 0);
v_params_4581_ = lean_ctor_get(v_toSignature_4578_, 3);
v_safe_4582_ = lean_ctor_get_uint8(v_toSignature_4578_, sizeof(void*)*4);
v___x_4583_ = lean_box(0);
v___x_4584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4582_ == 0)
{
v_a_4571_ = v___x_4584_;
goto v___jp_4570_;
}
else
{
lean_object* v___x_4585_; 
v___x_4585_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4561_, v___y_4564_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v___y_4588_; lean_object* v_decls_4618_; lean_object* v___f_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; uint8_t v___y_4629_; lean_object* v_a_4630_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; uint8_t v___y_4648_; lean_object* v_a_4649_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; uint8_t v___y_4663_; lean_object* v___y_4729_; uint8_t v___x_4738_; 
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v___x_4585_, 1);
v_decls_4618_ = lean_ctor_get(v___y_4563_, 0);
lean_inc(v_name_4580_);
v___f_4619_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4619_, 0, v_name_4580_);
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = lean_array_get_size(v_params_4581_);
lean_inc(v_a_4561_);
lean_inc_ref(v_decls_4618_);
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v_decls_4618_);
lean_ctor_set(v___x_4622_, 1, v_a_4561_);
v___x_4738_ = lean_nat_dec_lt(v___x_4620_, v___x_4621_);
if (v___x_4738_ == 0)
{
goto v___jp_4712_;
}
else
{
uint8_t v___x_4739_; 
v___x_4739_ = lean_nat_dec_le(v___x_4621_, v___x_4621_);
if (v___x_4739_ == 0)
{
if (v___x_4738_ == 0)
{
goto v___jp_4712_;
}
else
{
size_t v___x_4740_; size_t v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = ((size_t)0ULL);
v___x_4741_ = lean_usize_of_nat(v___x_4621_);
v___x_4742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4581_, v___x_4740_, v___x_4741_, v___x_4583_, v___x_4622_, v___y_4564_, v___y_4568_);
v___y_4729_ = v___x_4742_;
goto v___jp_4728_;
}
}
else
{
size_t v___x_4743_; size_t v___x_4744_; lean_object* v___x_4745_; 
v___x_4743_ = ((size_t)0ULL);
v___x_4744_ = lean_usize_of_nat(v___x_4621_);
v___x_4745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4581_, v___x_4743_, v___x_4744_, v___x_4583_, v___x_4622_, v___y_4564_, v___y_4568_);
v___y_4729_ = v___x_4745_;
goto v___jp_4728_;
}
}
v___jp_4587_:
{
if (lean_obj_tag(v___y_4588_) == 0)
{
lean_object* v___x_4589_; 
lean_dec_ref_known(v___y_4588_, 1);
v___x_4589_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4561_, v___y_4564_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4601_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4601_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4601_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
uint8_t v___x_4594_; 
v___x_4594_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4586_, v_a_4590_);
lean_dec(v_a_4590_);
lean_dec(v_a_4586_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4599_; 
lean_dec(v_a_4561_);
v___x_4595_ = lean_box(v___x_4575_);
v___x_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
lean_ctor_set(v___x_4597_, 1, v___x_4583_);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4597_);
v___x_4599_ = v___x_4592_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4597_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
else
{
lean_del_object(v___x_4592_);
v_a_4571_ = v___x_4584_;
goto v___jp_4570_;
}
}
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4609_; 
lean_dec(v_a_4586_);
lean_dec(v_a_4561_);
v_a_4602_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4604_ = v___x_4589_;
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4589_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_dec(v_a_4586_);
lean_dec(v_a_4561_);
v_a_4610_ = lean_ctor_get(v___y_4588_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___y_4588_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___y_4588_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___y_4588_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
v___jp_4623_:
{
lean_object* v___x_4631_; double v___x_4632_; double v___x_4633_; double v___x_4634_; double v___x_4635_; double v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4631_ = lean_io_mono_nanos_now();
v___x_4632_ = lean_float_of_nat(v___y_4624_);
v___x_4633_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4634_ = lean_float_div(v___x_4632_, v___x_4633_);
v___x_4635_ = lean_float_of_nat(v___x_4631_);
v___x_4636_ = lean_float_div(v___x_4635_, v___x_4633_);
v___x_4637_ = lean_box_float(v___x_4634_);
v___x_4638_ = lean_box_float(v___x_4636_);
v___x_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4637_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v_a_4630_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
lean_inc_ref(v___y_4627_);
lean_inc(v___y_4625_);
v___x_4641_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4625_, v___x_4575_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4626_, v___f_4619_, v___x_4640_, v___x_4622_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec_ref_known(v___x_4622_, 2);
v___y_4588_ = v___x_4641_;
goto v___jp_4587_;
}
v___jp_4642_:
{
lean_object* v___x_4650_; double v___x_4651_; double v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4650_ = lean_io_get_num_heartbeats();
v___x_4651_ = lean_float_of_nat(v___y_4645_);
v___x_4652_ = lean_float_of_nat(v___x_4650_);
v___x_4653_ = lean_box_float(v___x_4651_);
v___x_4654_ = lean_box_float(v___x_4652_);
v___x_4655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4653_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v_a_4649_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
lean_inc_ref(v___y_4646_);
lean_inc(v___y_4643_);
v___x_4657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4643_, v___x_4575_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4644_, v___f_4619_, v___x_4656_, v___x_4622_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec_ref_known(v___x_4622_, 2);
v___y_4588_ = v___x_4657_;
goto v___jp_4587_;
}
v___jp_4658_:
{
lean_object* v___x_4664_; 
v___x_4664_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4568_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
v___x_4666_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4667_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4662_, v___x_4666_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = lean_io_mono_nanos_now();
v___x_4669_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4660_, v___x_4622_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4669_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4669_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
lean_ctor_set_tag(v___x_4672_, 1);
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
v___y_4624_ = v___x_4668_;
v___y_4625_ = v___y_4659_;
v___y_4626_ = v_a_4665_;
v___y_4627_ = v___y_4661_;
v___y_4628_ = v___y_4662_;
v___y_4629_ = v___y_4663_;
v_a_4630_ = v___x_4675_;
goto v___jp_4623_;
}
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
v_a_4678_ = lean_ctor_get(v___x_4669_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4669_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4669_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
lean_ctor_set_tag(v___x_4680_, 0);
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
v___y_4624_ = v___x_4668_;
v___y_4625_ = v___y_4659_;
v___y_4626_ = v_a_4665_;
v___y_4627_ = v___y_4661_;
v___y_4628_ = v___y_4662_;
v___y_4629_ = v___y_4663_;
v_a_4630_ = v___x_4683_;
goto v___jp_4623_;
}
}
}
}
else
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4686_ = lean_io_get_num_heartbeats();
v___x_4687_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4660_, v___x_4622_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4687_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4687_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
lean_ctor_set_tag(v___x_4690_, 1);
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
v___y_4643_ = v___y_4659_;
v___y_4644_ = v_a_4665_;
v___y_4645_ = v___x_4686_;
v___y_4646_ = v___y_4661_;
v___y_4647_ = v___y_4662_;
v___y_4648_ = v___y_4663_;
v_a_4649_ = v___x_4693_;
goto v___jp_4642_;
}
}
}
else
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4703_; 
v_a_4696_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4698_ = v___x_4687_;
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4687_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
lean_ctor_set_tag(v___x_4698_, 0);
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
v___y_4643_ = v___y_4659_;
v___y_4644_ = v_a_4665_;
v___y_4645_ = v___x_4686_;
v___y_4646_ = v___y_4661_;
v___y_4647_ = v___y_4662_;
v___y_4648_ = v___y_4663_;
v_a_4649_ = v___x_4701_;
goto v___jp_4642_;
}
}
}
}
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
lean_dec_ref(v___y_4660_);
lean_dec_ref_known(v___x_4622_, 2);
lean_dec_ref(v___f_4619_);
lean_dec(v_a_4586_);
lean_dec(v_a_4561_);
v_a_4704_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4664_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4664_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
v___jp_4712_:
{
if (lean_obj_tag(v_value_4579_) == 0)
{
lean_object* v_options_4713_; uint8_t v_hasTrace_4714_; 
v_options_4713_ = lean_ctor_get(v___y_4567_, 2);
v_hasTrace_4714_ = lean_ctor_get_uint8(v_options_4713_, sizeof(void*)*1);
if (v_hasTrace_4714_ == 0)
{
lean_object* v_code_4715_; lean_object* v___x_4716_; 
lean_dec_ref(v___f_4619_);
v_code_4715_ = lean_ctor_get(v_value_4579_, 0);
lean_inc_ref(v_code_4715_);
v___x_4716_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4715_, v___x_4622_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec_ref_known(v___x_4622_, 2);
v___y_4588_ = v___x_4716_;
goto v___jp_4587_;
}
else
{
lean_object* v_code_4717_; lean_object* v_inheritedTraceOptions_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; 
v_code_4717_ = lean_ctor_get(v_value_4579_, 0);
v_inheritedTraceOptions_4718_ = lean_ctor_get(v___y_4567_, 13);
v___x_4719_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4720_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4721_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4722_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4718_, v_options_4713_, v___x_4721_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; uint8_t v___x_4724_; 
v___x_4723_ = l_Lean_trace_profiler;
v___x_4724_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4713_, v___x_4723_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; 
lean_dec_ref(v___f_4619_);
lean_inc_ref(v_code_4717_);
v___x_4725_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4717_, v___x_4622_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec_ref_known(v___x_4622_, 2);
v___y_4588_ = v___x_4725_;
goto v___jp_4587_;
}
else
{
lean_inc_ref(v_code_4717_);
v___y_4659_ = v___x_4719_;
v___y_4660_ = v_code_4717_;
v___y_4661_ = v___x_4720_;
v___y_4662_ = v_options_4713_;
v___y_4663_ = v___x_4722_;
goto v___jp_4658_;
}
}
else
{
lean_inc_ref(v_code_4717_);
v___y_4659_ = v___x_4719_;
v___y_4660_ = v_code_4717_;
v___y_4661_ = v___x_4720_;
v___y_4662_ = v_options_4713_;
v___y_4663_ = v___x_4722_;
goto v___jp_4658_;
}
}
}
else
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
lean_dec_ref(v___f_4619_);
v___x_4726_ = lean_box(1);
v___x_4727_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4726_, v___x_4622_, v___y_4564_, v___y_4568_);
lean_dec_ref_known(v___x_4622_, 2);
v___y_4588_ = v___x_4727_;
goto v___jp_4587_;
}
}
v___jp_4728_:
{
if (lean_obj_tag(v___y_4729_) == 0)
{
lean_dec_ref_known(v___y_4729_, 1);
goto v___jp_4712_;
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec_ref_known(v___x_4622_, 2);
lean_dec_ref(v___f_4619_);
lean_dec(v_a_4586_);
lean_dec(v_a_4561_);
v_a_4730_ = lean_ctor_get(v___y_4729_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___y_4729_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___y_4729_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___y_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_dec(v_a_4561_);
v_a_4746_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4585_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4585_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
v___jp_4570_:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = lean_unsigned_to_nat(1u);
v___x_4573_ = lean_nat_add(v_a_4561_, v___x_4572_);
lean_dec(v_a_4561_);
lean_inc_ref(v_a_4571_);
v_a_4561_ = v___x_4573_;
v_b_4562_ = v_a_4571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4754_, lean_object* v___x_4755_, lean_object* v_a_4756_, lean_object* v_b_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4754_, v___x_4755_, v_a_4756_, v_b_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec_ref(v___x_4755_);
lean_dec(v_upperBound_4754_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_decls_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v_decls_4773_ = lean_ctor_get(v_a_4766_, 0);
v___x_4774_ = lean_array_get_size(v_decls_4773_);
v___x_4775_ = lean_unsigned_to_nat(0u);
v___x_4776_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4777_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4774_, v_decls_4773_, v___x_4775_, v___x_4776_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4792_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4792_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4792_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v_fst_4782_; 
v_fst_4782_ = lean_ctor_get(v_a_4778_, 0);
lean_inc(v_fst_4782_);
lean_dec(v_a_4778_);
if (lean_obj_tag(v_fst_4782_) == 0)
{
uint8_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4786_; 
v___x_4783_ = 0;
v___x_4784_ = lean_box(v___x_4783_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4784_);
v___x_4786_ = v___x_4780_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
else
{
lean_object* v_val_4788_; lean_object* v___x_4790_; 
v_val_4788_ = lean_ctor_get(v_fst_4782_, 0);
lean_inc(v_val_4788_);
lean_dec_ref_known(v_fst_4782_, 1);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v_val_4788_);
v___x_4790_ = v___x_4780_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_val_4788_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
v_a_4793_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4777_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4777_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4809_, lean_object* v_x_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4810_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4819_, lean_object* v_x_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4819_, v_x_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4829_, lean_object* v___x_4830_, lean_object* v_inst_4831_, lean_object* v_R_4832_, lean_object* v_a_4833_, lean_object* v_b_4834_, lean_object* v_c_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4829_, v___x_4830_, v_a_4833_, v_b_4834_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4844_, lean_object* v___x_4845_, lean_object* v_inst_4846_, lean_object* v_R_4847_, lean_object* v_a_4848_, lean_object* v_b_4849_, lean_object* v_c_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4844_, v___x_4845_, v_inst_4846_, v_R_4847_, v_a_4848_, v_b_4849_, v_c_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec_ref(v___x_4845_);
lean_dec(v_upperBound_4844_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4859_, lean_object* v_data_4860_, lean_object* v_ref_4861_, lean_object* v_msg_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4859_, v_data_4860_, v_ref_4861_, v_msg_4862_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4871_, lean_object* v_data_4872_, lean_object* v_ref_4873_, lean_object* v_msg_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4871_, v_data_4872_, v_ref_4873_, v_msg_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4885_, lean_object* v_msg_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v_options_4892_; lean_object* v_ref_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v_options_4892_ = lean_ctor_get(v___y_4889_, 2);
v_ref_4893_ = lean_ctor_get(v___y_4889_, 5);
v___x_4894_ = lean_st_ref_get(v___y_4890_);
v___x_4895_ = lean_st_ref_get(v___y_4888_);
v___x_4896_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4887_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4955_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4955_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4955_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v_env_4901_; lean_object* v_lctx_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4953_; 
v_env_4901_ = lean_ctor_get(v___x_4894_, 0);
lean_inc_ref(v_env_4901_);
lean_dec(v___x_4894_);
v_lctx_4902_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4953_ == 0)
{
lean_object* v_unused_4954_; 
v_unused_4954_ = lean_ctor_get(v___x_4895_, 1);
lean_dec(v_unused_4954_);
v___x_4904_ = v___x_4895_;
v_isShared_4905_ = v_isSharedCheck_4953_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_lctx_4902_);
lean_dec(v___x_4895_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4953_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v_traceState_4908_; lean_object* v_env_4909_; lean_object* v_nextMacroScope_4910_; lean_object* v_ngen_4911_; lean_object* v_auxDeclNGen_4912_; lean_object* v_cache_4913_; lean_object* v_messages_4914_; lean_object* v_infoState_4915_; lean_object* v_snapshotTasks_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4952_; 
v___x_4906_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4907_ = lean_st_ref_take(v___y_4890_);
v_traceState_4908_ = lean_ctor_get(v___x_4907_, 4);
v_env_4909_ = lean_ctor_get(v___x_4907_, 0);
v_nextMacroScope_4910_ = lean_ctor_get(v___x_4907_, 1);
v_ngen_4911_ = lean_ctor_get(v___x_4907_, 2);
v_auxDeclNGen_4912_ = lean_ctor_get(v___x_4907_, 3);
v_cache_4913_ = lean_ctor_get(v___x_4907_, 5);
v_messages_4914_ = lean_ctor_get(v___x_4907_, 6);
v_infoState_4915_ = lean_ctor_get(v___x_4907_, 7);
v_snapshotTasks_4916_ = lean_ctor_get(v___x_4907_, 8);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4918_ = v___x_4907_;
v_isShared_4919_ = v_isSharedCheck_4952_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_snapshotTasks_4916_);
lean_inc(v_infoState_4915_);
lean_inc(v_messages_4914_);
lean_inc(v_cache_4913_);
lean_inc(v_traceState_4908_);
lean_inc(v_auxDeclNGen_4912_);
lean_inc(v_ngen_4911_);
lean_inc(v_nextMacroScope_4910_);
lean_inc(v_env_4909_);
lean_dec(v___x_4907_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4952_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
uint64_t v_tid_4920_; lean_object* v_traces_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4951_; 
v_tid_4920_ = lean_ctor_get_uint64(v_traceState_4908_, sizeof(void*)*1);
v_traces_4921_ = lean_ctor_get(v_traceState_4908_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v_traceState_4908_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4923_ = v_traceState_4908_;
v_isShared_4924_ = v_isSharedCheck_4951_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_traces_4921_);
lean_dec(v_traceState_4908_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4951_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
uint8_t v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4929_; 
v___x_4925_ = lean_unbox(v_a_4897_);
lean_dec(v_a_4897_);
v___x_4926_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4902_, v___x_4925_);
lean_dec_ref(v_lctx_4902_);
lean_inc_ref(v_options_4892_);
v___x_4927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4927_, 0, v_env_4901_);
lean_ctor_set(v___x_4927_, 1, v___x_4906_);
lean_ctor_set(v___x_4927_, 2, v___x_4926_);
lean_ctor_set(v___x_4927_, 3, v_options_4892_);
if (v_isShared_4905_ == 0)
{
lean_ctor_set_tag(v___x_4904_, 3);
lean_ctor_set(v___x_4904_, 1, v_msg_4886_);
lean_ctor_set(v___x_4904_, 0, v___x_4927_);
v___x_4929_ = v___x_4904_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4927_);
lean_ctor_set(v_reuseFailAlloc_4950_, 1, v_msg_4886_);
v___x_4929_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4930_; double v___x_4931_; uint8_t v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4940_; 
v___x_4930_ = lean_box(0);
v___x_4931_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4932_ = 0;
v___x_4933_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4934_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4934_, 0, v_cls_4885_);
lean_ctor_set(v___x_4934_, 1, v___x_4930_);
lean_ctor_set(v___x_4934_, 2, v___x_4933_);
lean_ctor_set_float(v___x_4934_, sizeof(void*)*3, v___x_4931_);
lean_ctor_set_float(v___x_4934_, sizeof(void*)*3 + 8, v___x_4931_);
lean_ctor_set_uint8(v___x_4934_, sizeof(void*)*3 + 16, v___x_4932_);
v___x_4935_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4936_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4934_);
lean_ctor_set(v___x_4936_, 1, v___x_4929_);
lean_ctor_set(v___x_4936_, 2, v___x_4935_);
lean_inc(v_ref_4893_);
v___x_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4937_, 0, v_ref_4893_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = l_Lean_PersistentArray_push___redArg(v_traces_4921_, v___x_4937_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v___x_4938_);
v___x_4940_ = v___x_4923_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4938_);
lean_ctor_set_uint64(v_reuseFailAlloc_4949_, sizeof(void*)*1, v_tid_4920_);
v___x_4940_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
lean_object* v___x_4942_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 4, v___x_4940_);
v___x_4942_ = v___x_4918_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_env_4909_);
lean_ctor_set(v_reuseFailAlloc_4948_, 1, v_nextMacroScope_4910_);
lean_ctor_set(v_reuseFailAlloc_4948_, 2, v_ngen_4911_);
lean_ctor_set(v_reuseFailAlloc_4948_, 3, v_auxDeclNGen_4912_);
lean_ctor_set(v_reuseFailAlloc_4948_, 4, v___x_4940_);
lean_ctor_set(v_reuseFailAlloc_4948_, 5, v_cache_4913_);
lean_ctor_set(v_reuseFailAlloc_4948_, 6, v_messages_4914_);
lean_ctor_set(v_reuseFailAlloc_4948_, 7, v_infoState_4915_);
lean_ctor_set(v_reuseFailAlloc_4948_, 8, v_snapshotTasks_4916_);
v___x_4942_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4946_; 
v___x_4943_ = lean_st_ref_put(v___y_4890_, v___x_4942_);
v___x_4944_ = lean_box(0);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4944_);
v___x_4946_ = v___x_4899_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
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
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
lean_dec(v___x_4895_);
lean_dec(v___x_4894_);
lean_dec_ref(v_msg_4886_);
lean_dec(v_cls_4885_);
v_a_4956_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4896_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4896_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4964_, lean_object* v_msg_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4964_, v_msg_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
lean_dec(v___y_4969_);
lean_dec_ref(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4972_, lean_object* v_msg_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4972_, v_msg_4973_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4982_, lean_object* v_msg_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4982_, v_msg_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
lean_dec(v___y_4989_);
lean_dec_ref(v___y_4988_);
lean_dec(v___y_4987_);
lean_dec_ref(v___y_4986_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
return v_res_4991_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = lean_box(0);
v___x_4993_ = lean_unsigned_to_nat(16u);
v___x_4994_ = lean_mk_array(v___x_4993_, v___x_4992_);
return v___x_4994_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_4996_ = lean_unsigned_to_nat(0u);
v___x_4997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4996_);
lean_ctor_set(v___x_4997_, 1, v___x_4995_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_4998_, size_t v_i_4999_, lean_object* v_bs_5000_){
_start:
{
uint8_t v___x_5001_; 
v___x_5001_ = lean_usize_dec_lt(v_i_4999_, v_sz_4998_);
if (v___x_5001_ == 0)
{
return v_bs_5000_;
}
else
{
lean_object* v___x_5002_; lean_object* v_bs_x27_5003_; lean_object* v___x_5004_; size_t v___x_5005_; size_t v___x_5006_; lean_object* v___x_5007_; 
v___x_5002_ = lean_unsigned_to_nat(0u);
v_bs_x27_5003_ = lean_array_uset(v_bs_5000_, v_i_4999_, v___x_5002_);
v___x_5004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5005_ = ((size_t)1ULL);
v___x_5006_ = lean_usize_add(v_i_4999_, v___x_5005_);
v___x_5007_ = lean_array_uset(v_bs_x27_5003_, v_i_4999_, v___x_5004_);
v_i_4999_ = v___x_5006_;
v_bs_5000_ = v___x_5007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_5009_, lean_object* v_i_5010_, lean_object* v_bs_5011_){
_start:
{
size_t v_sz_boxed_5012_; size_t v_i_boxed_5013_; lean_object* v_res_5014_; 
v_sz_boxed_5012_ = lean_unbox_usize(v_sz_5009_);
lean_dec(v_sz_5009_);
v_i_boxed_5013_ = lean_unbox_usize(v_i_5010_);
lean_dec(v_i_5010_);
v_res_5014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_5012_, v_i_boxed_5013_, v_bs_5011_);
return v_res_5014_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5017_ = l_Lean_stringToMessageData(v___x_5016_);
return v___x_5017_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5019_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5020_ = l_Lean_stringToMessageData(v___x_5019_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v___x_5032_; lean_object* v_decls_5033_; lean_object* v_funVals_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5073_; 
v___x_5032_ = lean_st_ref_take(v_a_5023_);
v_decls_5033_ = lean_ctor_get(v_a_5022_, 0);
v_funVals_5034_ = lean_ctor_get(v___x_5032_, 1);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5073_ == 0)
{
lean_object* v_unused_5074_; 
v_unused_5074_ = lean_ctor_get(v___x_5032_, 0);
lean_dec(v_unused_5074_);
v___x_5036_ = v___x_5032_;
v_isShared_5037_ = v_isSharedCheck_5073_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_funVals_5034_);
lean_dec(v___x_5032_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5073_;
goto v_resetjp_5035_;
}
v___jp_5029_:
{
lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5030_ = lean_box(0);
v___x_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
return v___x_5031_;
}
v_resetjp_5035_:
{
size_t v_sz_5038_; size_t v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5042_; 
v_sz_5038_ = lean_array_size(v_decls_5033_);
v___x_5039_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5033_);
v___x_5040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5038_, v___x_5039_, v_decls_5033_);
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 0, v___x_5040_);
v___x_5042_ = v___x_5036_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5040_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v_funVals_5034_);
v___x_5042_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = lean_st_ref_put(v_a_5023_, v___x_5042_);
v___x_5044_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; uint8_t v___x_5046_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref_known(v___x_5044_, 1);
v___x_5046_ = lean_unbox(v_a_5045_);
lean_dec(v_a_5045_);
if (v___x_5046_ == 0)
{
lean_object* v_options_5047_; uint8_t v_hasTrace_5048_; 
v_options_5047_ = lean_ctor_get(v_a_5026_, 2);
v_hasTrace_5048_ = lean_ctor_get_uint8(v_options_5047_, sizeof(void*)*1);
if (v_hasTrace_5048_ == 0)
{
lean_dec(v_n_5021_);
goto v___jp_5029_;
}
else
{
lean_object* v_inheritedTraceOptions_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; 
v_inheritedTraceOptions_5049_ = lean_ctor_get(v_a_5026_, 13);
v___x_5050_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5051_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5052_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5049_, v_options_5047_, v___x_5051_);
if (v___x_5052_ == 0)
{
lean_dec(v_n_5021_);
goto v___jp_5029_;
}
else
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5053_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5054_ = l_Nat_reprFast(v_n_5021_);
v___x_5055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5054_);
v___x_5056_ = l_Lean_MessageData_ofFormat(v___x_5055_);
v___x_5057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5053_);
lean_ctor_set(v___x_5057_, 1, v___x_5056_);
v___x_5058_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5057_);
lean_ctor_set(v___x_5059_, 1, v___x_5058_);
v___x_5060_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5050_, v___x_5059_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_dec_ref_known(v___x_5060_, 1);
goto v___jp_5029_;
}
else
{
return v___x_5060_;
}
}
}
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5061_ = lean_unsigned_to_nat(1u);
v___x_5062_ = lean_nat_add(v_n_5021_, v___x_5061_);
lean_dec(v_n_5021_);
v_n_5021_ = v___x_5062_;
goto _start;
}
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
lean_dec(v_n_5021_);
v_a_5064_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_5044_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5044_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_a_5078_);
lean_dec(v_a_5077_);
lean_dec_ref(v_a_5076_);
return v_res_5083_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = 0;
v___x_5085_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5086_){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5087_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5088_ = lean_panic_fn_borrowed(v___x_5087_, v_msg_5086_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5089_, lean_object* v_msg_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_options_5096_; lean_object* v_ref_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v_options_5096_ = lean_ctor_get(v___y_5093_, 2);
v_ref_5097_ = lean_ctor_get(v___y_5093_, 5);
v___x_5098_ = lean_st_ref_get(v___y_5094_);
v___x_5099_ = lean_st_ref_get(v___y_5092_);
v___x_5100_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5091_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5159_; 
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5159_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5159_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v_env_5105_; lean_object* v_lctx_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5157_; 
v_env_5105_ = lean_ctor_get(v___x_5098_, 0);
lean_inc_ref(v_env_5105_);
lean_dec(v___x_5098_);
v_lctx_5106_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5157_ == 0)
{
lean_object* v_unused_5158_; 
v_unused_5158_ = lean_ctor_get(v___x_5099_, 1);
lean_dec(v_unused_5158_);
v___x_5108_ = v___x_5099_;
v_isShared_5109_ = v_isSharedCheck_5157_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_lctx_5106_);
lean_dec(v___x_5099_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5157_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v_traceState_5112_; lean_object* v_env_5113_; lean_object* v_nextMacroScope_5114_; lean_object* v_ngen_5115_; lean_object* v_auxDeclNGen_5116_; lean_object* v_cache_5117_; lean_object* v_messages_5118_; lean_object* v_infoState_5119_; lean_object* v_snapshotTasks_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5156_; 
v___x_5110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_5111_ = lean_st_ref_take(v___y_5094_);
v_traceState_5112_ = lean_ctor_get(v___x_5111_, 4);
v_env_5113_ = lean_ctor_get(v___x_5111_, 0);
v_nextMacroScope_5114_ = lean_ctor_get(v___x_5111_, 1);
v_ngen_5115_ = lean_ctor_get(v___x_5111_, 2);
v_auxDeclNGen_5116_ = lean_ctor_get(v___x_5111_, 3);
v_cache_5117_ = lean_ctor_get(v___x_5111_, 5);
v_messages_5118_ = lean_ctor_get(v___x_5111_, 6);
v_infoState_5119_ = lean_ctor_get(v___x_5111_, 7);
v_snapshotTasks_5120_ = lean_ctor_get(v___x_5111_, 8);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5122_ = v___x_5111_;
v_isShared_5123_ = v_isSharedCheck_5156_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_snapshotTasks_5120_);
lean_inc(v_infoState_5119_);
lean_inc(v_messages_5118_);
lean_inc(v_cache_5117_);
lean_inc(v_traceState_5112_);
lean_inc(v_auxDeclNGen_5116_);
lean_inc(v_ngen_5115_);
lean_inc(v_nextMacroScope_5114_);
lean_inc(v_env_5113_);
lean_dec(v___x_5111_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5156_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
uint64_t v_tid_5124_; lean_object* v_traces_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5155_; 
v_tid_5124_ = lean_ctor_get_uint64(v_traceState_5112_, sizeof(void*)*1);
v_traces_5125_ = lean_ctor_get(v_traceState_5112_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v_traceState_5112_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5127_ = v_traceState_5112_;
v_isShared_5128_ = v_isSharedCheck_5155_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_traces_5125_);
lean_dec(v_traceState_5112_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5155_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
uint8_t v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5133_; 
v___x_5129_ = lean_unbox(v_a_5101_);
lean_dec(v_a_5101_);
v___x_5130_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5106_, v___x_5129_);
lean_dec_ref(v_lctx_5106_);
lean_inc_ref(v_options_5096_);
v___x_5131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5131_, 0, v_env_5105_);
lean_ctor_set(v___x_5131_, 1, v___x_5110_);
lean_ctor_set(v___x_5131_, 2, v___x_5130_);
lean_ctor_set(v___x_5131_, 3, v_options_5096_);
if (v_isShared_5109_ == 0)
{
lean_ctor_set_tag(v___x_5108_, 3);
lean_ctor_set(v___x_5108_, 1, v_msg_5090_);
lean_ctor_set(v___x_5108_, 0, v___x_5131_);
v___x_5133_ = v___x_5108_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5131_);
lean_ctor_set(v_reuseFailAlloc_5154_, 1, v_msg_5090_);
v___x_5133_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
lean_object* v___x_5134_; double v___x_5135_; uint8_t v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5144_; 
v___x_5134_ = lean_box(0);
v___x_5135_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5136_ = 0;
v___x_5137_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5138_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5138_, 0, v_cls_5089_);
lean_ctor_set(v___x_5138_, 1, v___x_5134_);
lean_ctor_set(v___x_5138_, 2, v___x_5137_);
lean_ctor_set_float(v___x_5138_, sizeof(void*)*3, v___x_5135_);
lean_ctor_set_float(v___x_5138_, sizeof(void*)*3 + 8, v___x_5135_);
lean_ctor_set_uint8(v___x_5138_, sizeof(void*)*3 + 16, v___x_5136_);
v___x_5139_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5140_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5140_, 0, v___x_5138_);
lean_ctor_set(v___x_5140_, 1, v___x_5133_);
lean_ctor_set(v___x_5140_, 2, v___x_5139_);
lean_inc(v_ref_5097_);
v___x_5141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5141_, 0, v_ref_5097_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = l_Lean_PersistentArray_push___redArg(v_traces_5125_, v___x_5141_);
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 0, v___x_5142_);
v___x_5144_ = v___x_5127_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5142_);
lean_ctor_set_uint64(v_reuseFailAlloc_5153_, sizeof(void*)*1, v_tid_5124_);
v___x_5144_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
lean_object* v___x_5146_; 
if (v_isShared_5123_ == 0)
{
lean_ctor_set(v___x_5122_, 4, v___x_5144_);
v___x_5146_ = v___x_5122_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_env_5113_);
lean_ctor_set(v_reuseFailAlloc_5152_, 1, v_nextMacroScope_5114_);
lean_ctor_set(v_reuseFailAlloc_5152_, 2, v_ngen_5115_);
lean_ctor_set(v_reuseFailAlloc_5152_, 3, v_auxDeclNGen_5116_);
lean_ctor_set(v_reuseFailAlloc_5152_, 4, v___x_5144_);
lean_ctor_set(v_reuseFailAlloc_5152_, 5, v_cache_5117_);
lean_ctor_set(v_reuseFailAlloc_5152_, 6, v_messages_5118_);
lean_ctor_set(v_reuseFailAlloc_5152_, 7, v_infoState_5119_);
lean_ctor_set(v_reuseFailAlloc_5152_, 8, v_snapshotTasks_5120_);
v___x_5146_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5150_; 
v___x_5147_ = lean_st_ref_put(v___y_5094_, v___x_5146_);
v___x_5148_ = lean_box(0);
if (v_isShared_5104_ == 0)
{
lean_ctor_set(v___x_5103_, 0, v___x_5148_);
v___x_5150_ = v___x_5103_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v___x_5148_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
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
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5167_; 
lean_dec(v___x_5099_);
lean_dec(v___x_5098_);
lean_dec_ref(v_msg_5090_);
lean_dec(v_cls_5089_);
v_a_5160_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5162_ = v___x_5100_;
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v___x_5100_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5165_; 
if (v_isShared_5163_ == 0)
{
v___x_5165_ = v___x_5162_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5168_, lean_object* v_msg_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5168_, v_msg_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5176_, size_t v_i_5177_, size_t v_stop_5178_, lean_object* v_b_5179_){
_start:
{
uint8_t v___x_5181_; 
v___x_5181_ = lean_usize_dec_eq(v_i_5177_, v_stop_5178_);
if (v___x_5181_ == 0)
{
lean_object* v_fst_5182_; lean_object* v_snd_5183_; lean_object* v___x_5184_; lean_object* v_snd_5185_; lean_object* v_fst_5186_; lean_object* v_fst_5187_; lean_object* v_snd_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5203_; 
v_fst_5182_ = lean_ctor_get(v_b_5179_, 0);
lean_inc(v_fst_5182_);
v_snd_5183_ = lean_ctor_get(v_b_5179_, 1);
lean_inc(v_snd_5183_);
lean_dec_ref(v_b_5179_);
v___x_5184_ = lean_array_uget_borrowed(v_as_5176_, v_i_5177_);
v_snd_5185_ = lean_ctor_get(v___x_5184_, 1);
lean_inc(v_snd_5185_);
v_fst_5186_ = lean_ctor_get(v___x_5184_, 0);
v_fst_5187_ = lean_ctor_get(v_snd_5185_, 0);
v_snd_5188_ = lean_ctor_get(v_snd_5185_, 1);
v_isSharedCheck_5203_ = !lean_is_exclusive(v_snd_5185_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5190_ = v_snd_5185_;
v_isShared_5191_ = v_isSharedCheck_5203_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_snd_5188_);
lean_inc(v_fst_5187_);
lean_dec(v_snd_5185_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5203_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v_fvarId_5192_; uint8_t v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5198_; 
v_fvarId_5192_ = lean_ctor_get(v_fst_5186_, 0);
v___x_5193_ = 0;
v___x_5194_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5193_, v_fst_5187_, v_fst_5182_);
lean_dec(v_fst_5187_);
v___x_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5195_, 0, v_snd_5188_);
lean_inc(v_fvarId_5192_);
v___x_5196_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5183_, v_fvarId_5192_, v___x_5195_);
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 1, v___x_5196_);
lean_ctor_set(v___x_5190_, 0, v___x_5194_);
v___x_5198_ = v___x_5190_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5194_);
lean_ctor_set(v_reuseFailAlloc_5202_, 1, v___x_5196_);
v___x_5198_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
size_t v___x_5199_; size_t v___x_5200_; 
v___x_5199_ = ((size_t)1ULL);
v___x_5200_ = lean_usize_add(v_i_5177_, v___x_5199_);
v_i_5177_ = v___x_5200_;
v_b_5179_ = v___x_5198_;
goto _start;
}
}
}
else
{
lean_object* v___x_5204_; 
v___x_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5204_, 0, v_b_5179_);
return v___x_5204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5205_, lean_object* v_i_5206_, lean_object* v_stop_5207_, lean_object* v_b_5208_, lean_object* v___y_5209_){
_start:
{
size_t v_i_boxed_5210_; size_t v_stop_boxed_5211_; lean_object* v_res_5212_; 
v_i_boxed_5210_ = lean_unbox_usize(v_i_5206_);
lean_dec(v_i_5206_);
v_stop_boxed_5211_ = lean_unbox_usize(v_stop_5207_);
lean_dec(v_stop_5207_);
v_res_5212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5205_, v_i_boxed_5210_, v_stop_boxed_5211_, v_b_5208_);
lean_dec_ref(v_as_5205_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5213_, lean_object* v_x_5214_){
_start:
{
if (lean_obj_tag(v_x_5214_) == 0)
{
lean_object* v___x_5215_; 
v___x_5215_ = lean_box(0);
return v___x_5215_;
}
else
{
lean_object* v_key_5216_; lean_object* v_value_5217_; lean_object* v_tail_5218_; uint8_t v___x_5219_; 
v_key_5216_ = lean_ctor_get(v_x_5214_, 0);
v_value_5217_ = lean_ctor_get(v_x_5214_, 1);
v_tail_5218_ = lean_ctor_get(v_x_5214_, 2);
v___x_5219_ = l_Lean_instBEqFVarId_beq(v_key_5216_, v_a_5213_);
if (v___x_5219_ == 0)
{
v_x_5214_ = v_tail_5218_;
goto _start;
}
else
{
lean_object* v___x_5221_; 
lean_inc(v_value_5217_);
v___x_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5221_, 0, v_value_5217_);
return v___x_5221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5222_, lean_object* v_x_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5222_, v_x_5223_);
lean_dec(v_x_5223_);
lean_dec(v_a_5222_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v_buckets_5227_; lean_object* v___x_5228_; uint64_t v___x_5229_; uint64_t v___x_5230_; uint64_t v___x_5231_; uint64_t v_fold_5232_; uint64_t v___x_5233_; uint64_t v___x_5234_; uint64_t v___x_5235_; size_t v___x_5236_; size_t v___x_5237_; size_t v___x_5238_; size_t v___x_5239_; size_t v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v_buckets_5227_ = lean_ctor_get(v_m_5225_, 1);
v___x_5228_ = lean_array_get_size(v_buckets_5227_);
v___x_5229_ = l_Lean_instHashableFVarId_hash(v_a_5226_);
v___x_5230_ = 32ULL;
v___x_5231_ = lean_uint64_shift_right(v___x_5229_, v___x_5230_);
v_fold_5232_ = lean_uint64_xor(v___x_5229_, v___x_5231_);
v___x_5233_ = 16ULL;
v___x_5234_ = lean_uint64_shift_right(v_fold_5232_, v___x_5233_);
v___x_5235_ = lean_uint64_xor(v_fold_5232_, v___x_5234_);
v___x_5236_ = lean_uint64_to_usize(v___x_5235_);
v___x_5237_ = lean_usize_of_nat(v___x_5228_);
v___x_5238_ = ((size_t)1ULL);
v___x_5239_ = lean_usize_sub(v___x_5237_, v___x_5238_);
v___x_5240_ = lean_usize_land(v___x_5236_, v___x_5239_);
v___x_5241_ = lean_array_uget_borrowed(v_buckets_5227_, v___x_5240_);
v___x_5242_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5226_, v___x_5241_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5243_, lean_object* v_a_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5243_, v_a_5244_);
lean_dec(v_a_5244_);
lean_dec_ref(v_m_5243_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5246_, lean_object* v_as_5247_, size_t v_i_5248_, size_t v_stop_5249_, lean_object* v_b_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_a_5257_; uint8_t v___x_5261_; 
v___x_5261_ = lean_usize_dec_eq(v_i_5248_, v_stop_5249_);
if (v___x_5261_ == 0)
{
lean_object* v___x_5262_; lean_object* v_fvarId_5263_; lean_object* v___x_5264_; 
v___x_5262_ = lean_array_uget_borrowed(v_as_5247_, v_i_5248_);
v_fvarId_5263_ = lean_ctor_get(v___x_5262_, 0);
v___x_5264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5246_, v_fvarId_5263_);
if (lean_obj_tag(v___x_5264_) == 1)
{
lean_object* v_val_5265_; lean_object* v___x_5266_; 
v_val_5265_ = lean_ctor_get(v___x_5264_, 0);
lean_inc(v_val_5265_);
lean_dec_ref_known(v___x_5264_, 1);
v___x_5266_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5265_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
if (lean_obj_tag(v___x_5266_) == 0)
{
lean_object* v_a_5267_; 
v_a_5267_ = lean_ctor_get(v___x_5266_, 0);
lean_inc(v_a_5267_);
lean_dec_ref_known(v___x_5266_, 1);
if (lean_obj_tag(v_a_5267_) == 1)
{
lean_object* v_val_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v_val_5268_ = lean_ctor_get(v_a_5267_, 0);
lean_inc(v_val_5268_);
lean_dec_ref_known(v_a_5267_, 1);
lean_inc(v___x_5262_);
v___x_5269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5262_);
lean_ctor_set(v___x_5269_, 1, v_val_5268_);
v___x_5270_ = lean_array_push(v_b_5250_, v___x_5269_);
v_a_5257_ = v___x_5270_;
goto v___jp_5256_;
}
else
{
lean_dec(v_a_5267_);
v_a_5257_ = v_b_5250_;
goto v___jp_5256_;
}
}
else
{
lean_object* v_a_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5278_; 
lean_dec_ref(v_b_5250_);
v_a_5271_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5278_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5273_ = v___x_5266_;
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_a_5271_);
lean_dec(v___x_5266_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5276_; 
if (v_isShared_5274_ == 0)
{
v___x_5276_ = v___x_5273_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
v___x_5276_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
return v___x_5276_;
}
}
}
}
else
{
lean_dec(v___x_5264_);
v_a_5257_ = v_b_5250_;
goto v___jp_5256_;
}
}
else
{
lean_object* v___x_5279_; 
v___x_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5279_, 0, v_b_5250_);
return v___x_5279_;
}
v___jp_5256_:
{
size_t v___x_5258_; size_t v___x_5259_; 
v___x_5258_ = ((size_t)1ULL);
v___x_5259_ = lean_usize_add(v_i_5248_, v___x_5258_);
v_i_5248_ = v___x_5259_;
v_b_5250_ = v_a_5257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5280_, lean_object* v_as_5281_, lean_object* v_i_5282_, lean_object* v_stop_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
size_t v_i_boxed_5290_; size_t v_stop_boxed_5291_; lean_object* v_res_5292_; 
v_i_boxed_5290_ = lean_unbox_usize(v_i_5282_);
lean_dec(v_i_5282_);
v_stop_boxed_5291_ = lean_unbox_usize(v_stop_5283_);
lean_dec(v_stop_5283_);
v_res_5292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5280_, v_as_5281_, v_i_boxed_5290_, v_stop_boxed_5291_, v_b_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec_ref(v_as_5281_);
lean_dec_ref(v_assignment_5280_);
return v_res_5292_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5295_, lean_object* v_as_5296_, lean_object* v_start_5297_, lean_object* v_stop_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v___x_5304_; uint8_t v___x_5305_; 
v___x_5304_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5305_ = lean_nat_dec_lt(v_start_5297_, v_stop_5298_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; 
v___x_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5304_);
return v___x_5306_;
}
else
{
lean_object* v___x_5307_; uint8_t v___x_5308_; 
v___x_5307_ = lean_array_get_size(v_as_5296_);
v___x_5308_ = lean_nat_dec_le(v_stop_5298_, v___x_5307_);
if (v___x_5308_ == 0)
{
uint8_t v___x_5309_; 
v___x_5309_ = lean_nat_dec_lt(v_start_5297_, v___x_5307_);
if (v___x_5309_ == 0)
{
lean_object* v___x_5310_; 
v___x_5310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5304_);
return v___x_5310_;
}
else
{
size_t v___x_5311_; size_t v___x_5312_; lean_object* v___x_5313_; 
v___x_5311_ = lean_usize_of_nat(v_start_5297_);
v___x_5312_ = lean_usize_of_nat(v___x_5307_);
v___x_5313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5295_, v_as_5296_, v___x_5311_, v___x_5312_, v___x_5304_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
return v___x_5313_;
}
}
else
{
size_t v___x_5314_; size_t v___x_5315_; lean_object* v___x_5316_; 
v___x_5314_ = lean_usize_of_nat(v_start_5297_);
v___x_5315_ = lean_usize_of_nat(v_stop_5298_);
v___x_5316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5295_, v_as_5296_, v___x_5314_, v___x_5315_, v___x_5304_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
return v___x_5316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5317_, lean_object* v_as_5318_, lean_object* v_start_5319_, lean_object* v_stop_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v_res_5326_; 
v_res_5326_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5317_, v_as_5318_, v_start_5319_, v_stop_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v_stop_5320_);
lean_dec(v_start_5319_);
lean_dec_ref(v_as_5318_);
lean_dec_ref(v_assignment_5317_);
return v_res_5326_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5329_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5330_ = lean_unsigned_to_nat(9u);
v___x_5331_ = lean_unsigned_to_nat(641u);
v___x_5332_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5333_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5334_ = l_mkPanicMessageWithDecl(v___x_5333_, v___x_5332_, v___x_5331_, v___x_5330_, v___x_5329_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5337_, lean_object* v_discrVal_5338_, lean_object* v_discr_5339_, lean_object* v_assignment_5340_, lean_object* v_i_5341_, lean_object* v_as_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v___x_5348_; uint8_t v___x_5349_; 
v___x_5348_ = lean_array_get_size(v_as_5342_);
v___x_5349_ = lean_nat_dec_lt(v_i_5341_, v___x_5348_);
if (v___x_5349_ == 0)
{
lean_object* v___x_5350_; 
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v___x_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5350_, 0, v_as_5342_);
return v___x_5350_;
}
else
{
lean_object* v_a_5351_; lean_object* v_a_5353_; 
v_a_5351_ = lean_array_fget_borrowed(v_as_5342_, v_i_5341_);
if (lean_obj_tag(v_a_5351_) == 0)
{
lean_object* v_ctorName_5364_; lean_object* v_params_5365_; lean_object* v_code_5366_; uint8_t v___x_5367_; lean_object* v___y_5369_; lean_object* v___y_5370_; lean_object* v___y_5383_; uint8_t v___x_5387_; 
v_ctorName_5364_ = lean_ctor_get(v_a_5351_, 0);
v_params_5365_ = lean_ctor_get(v_a_5351_, 1);
v_code_5366_ = lean_ctor_get(v_a_5351_, 2);
v___x_5367_ = 0;
v___x_5387_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5338_, v_ctorName_5364_);
if (v___x_5387_ == 0)
{
lean_object* v_options_5388_; uint8_t v_hasTrace_5389_; 
v_options_5388_ = lean_ctor_get(v___y_5345_, 2);
v_hasTrace_5389_ = lean_ctor_get_uint8(v_options_5388_, sizeof(void*)*1);
if (v_hasTrace_5389_ == 0)
{
v___y_5383_ = v___y_5344_;
goto v___jp_5382_;
}
else
{
lean_object* v_inheritedTraceOptions_5390_; lean_object* v_cls_5391_; lean_object* v___x_5392_; uint8_t v___x_5393_; 
v_inheritedTraceOptions_5390_ = lean_ctor_get(v___y_5345_, 13);
v_cls_5391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5392_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5390_, v_options_5388_, v___x_5392_);
if (v___x_5393_ == 0)
{
v___y_5383_ = v___y_5344_;
goto v___jp_5382_;
}
else
{
lean_object* v___x_5394_; 
lean_inc(v_discr_5339_);
v___x_5394_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5339_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
if (lean_obj_tag(v___x_5394_) == 0)
{
lean_object* v_a_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v_a_5395_ = lean_ctor_get(v___x_5394_, 0);
lean_inc(v_a_5395_);
lean_dec_ref_known(v___x_5394_, 1);
v___x_5396_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5397_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5395_, v___x_5393_);
v___x_5398_ = lean_string_append(v___x_5396_, v___x_5397_);
lean_dec_ref(v___x_5397_);
v___x_5399_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5400_ = lean_string_append(v___x_5398_, v___x_5399_);
lean_inc(v_ctorName_5364_);
v___x_5401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5364_, v___x_5393_);
v___x_5402_ = lean_string_append(v___x_5400_, v___x_5401_);
lean_dec_ref(v___x_5401_);
v___x_5403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5403_, 0, v___x_5402_);
v___x_5404_ = l_Lean_MessageData_ofFormat(v___x_5403_);
v___x_5405_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5391_, v___x_5404_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
if (lean_obj_tag(v___x_5405_) == 0)
{
lean_dec_ref_known(v___x_5405_, 1);
v___y_5383_ = v___y_5344_;
goto v___jp_5382_;
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5413_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5408_ = v___x_5405_;
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5405_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5411_; 
if (v_isShared_5409_ == 0)
{
v___x_5411_ = v___x_5408_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5406_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
else
{
lean_object* v_a_5414_; lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5421_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5414_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5421_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5421_ == 0)
{
v___x_5416_ = v___x_5394_;
v_isShared_5417_ = v_isSharedCheck_5421_;
goto v_resetjp_5415_;
}
else
{
lean_inc(v_a_5414_);
lean_dec(v___x_5394_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5421_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
lean_object* v___x_5419_; 
if (v_isShared_5417_ == 0)
{
v___x_5419_ = v___x_5416_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_a_5414_);
v___x_5419_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
return v___x_5419_;
}
}
}
}
}
}
else
{
lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5422_ = lean_unsigned_to_nat(0u);
v___x_5423_ = lean_array_get_size(v_params_5365_);
v___x_5424_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5340_, v_params_5365_, v___x_5422_, v___x_5423_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
if (lean_obj_tag(v___x_5424_) == 0)
{
lean_object* v_a_5425_; lean_object* v___x_5438_; uint8_t v___x_5439_; lean_object* v_fst_5441_; lean_object* v_snd_5442_; lean_object* v___y_5455_; 
v_a_5425_ = lean_ctor_get(v___x_5424_, 0);
lean_inc(v_a_5425_);
lean_dec_ref_known(v___x_5424_, 1);
v___x_5438_ = lean_array_get_size(v_a_5425_);
v___x_5439_ = lean_nat_dec_eq(v___x_5438_, v___x_5422_);
if (v___x_5439_ == 0)
{
if (v___x_5387_ == 0)
{
lean_dec(v_a_5425_);
goto v___jp_5426_;
}
else
{
lean_object* v___x_5467_; 
lean_inc_ref(v_code_5366_);
v___x_5467_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5340_, v_code_5366_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
if (lean_obj_tag(v___x_5467_) == 0)
{
lean_object* v_a_5468_; lean_object* v___x_5469_; uint8_t v___x_5470_; 
v_a_5468_ = lean_ctor_get(v___x_5467_, 0);
lean_inc(v_a_5468_);
lean_dec_ref_known(v___x_5467_, 1);
v___x_5469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5470_ = lean_nat_dec_lt(v___x_5422_, v___x_5438_);
if (v___x_5470_ == 0)
{
lean_dec(v_a_5425_);
v_fst_5441_ = v_a_5468_;
v_snd_5442_ = v___x_5469_;
goto v___jp_5440_;
}
else
{
lean_object* v___x_5471_; uint8_t v___x_5472_; 
lean_inc(v_a_5468_);
v___x_5471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5471_, 0, v_a_5468_);
lean_ctor_set(v___x_5471_, 1, v___x_5469_);
v___x_5472_ = lean_nat_dec_le(v___x_5438_, v___x_5438_);
if (v___x_5472_ == 0)
{
if (v___x_5470_ == 0)
{
lean_dec_ref_known(v___x_5471_, 2);
lean_dec(v_a_5425_);
v_fst_5441_ = v_a_5468_;
v_snd_5442_ = v___x_5469_;
goto v___jp_5440_;
}
else
{
size_t v___x_5473_; size_t v___x_5474_; lean_object* v___x_5475_; 
lean_dec(v_a_5468_);
v___x_5473_ = ((size_t)0ULL);
v___x_5474_ = lean_usize_of_nat(v___x_5438_);
v___x_5475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5425_, v___x_5473_, v___x_5474_, v___x_5471_);
lean_dec(v_a_5425_);
v___y_5455_ = v___x_5475_;
goto v___jp_5454_;
}
}
else
{
size_t v___x_5476_; size_t v___x_5477_; lean_object* v___x_5478_; 
lean_dec(v_a_5468_);
v___x_5476_ = ((size_t)0ULL);
v___x_5477_ = lean_usize_of_nat(v___x_5438_);
v___x_5478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5425_, v___x_5476_, v___x_5477_, v___x_5471_);
lean_dec(v_a_5425_);
v___y_5455_ = v___x_5478_;
goto v___jp_5454_;
}
}
}
else
{
lean_object* v_a_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5486_; 
lean_dec(v_a_5425_);
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5479_ = lean_ctor_get(v___x_5467_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5481_ = v___x_5467_;
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___x_5467_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5484_; 
if (v_isShared_5482_ == 0)
{
v___x_5484_ = v___x_5481_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_a_5479_);
v___x_5484_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
return v___x_5484_;
}
}
}
}
}
else
{
lean_dec(v_a_5425_);
goto v___jp_5426_;
}
v___jp_5426_:
{
lean_object* v___x_5427_; 
lean_inc_ref(v_code_5366_);
v___x_5427_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5340_, v_code_5366_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
if (lean_obj_tag(v___x_5427_) == 0)
{
lean_object* v_a_5428_; lean_object* v___x_5429_; 
v_a_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_a_5428_);
lean_dec_ref_known(v___x_5427_, 1);
lean_inc_ref(v_a_5351_);
v___x_5429_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5351_, v_a_5428_);
v_a_5353_ = v___x_5429_;
goto v___jp_5352_;
}
else
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5437_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5430_ = lean_ctor_get(v___x_5427_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5427_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5432_ = v___x_5427_;
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5427_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5435_; 
if (v_isShared_5433_ == 0)
{
v___x_5435_ = v___x_5432_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5430_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
}
v___jp_5440_:
{
lean_object* v___x_5443_; 
v___x_5443_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5367_, v_fst_5441_, v_snd_5442_, v___x_5439_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec_ref(v_snd_5442_);
if (lean_obj_tag(v___x_5443_) == 0)
{
lean_object* v_a_5444_; lean_object* v___x_5445_; 
v_a_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc(v_a_5444_);
lean_dec_ref_known(v___x_5443_, 1);
lean_inc_ref(v_a_5351_);
v___x_5445_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5351_, v_a_5444_);
v_a_5353_ = v___x_5445_;
goto v___jp_5352_;
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5453_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5446_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5448_ = v___x_5443_;
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___x_5443_);
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
v___jp_5454_:
{
if (lean_obj_tag(v___y_5455_) == 0)
{
lean_object* v_a_5456_; lean_object* v_fst_5457_; lean_object* v_snd_5458_; 
v_a_5456_ = lean_ctor_get(v___y_5455_, 0);
lean_inc(v_a_5456_);
lean_dec_ref_known(v___y_5455_, 1);
v_fst_5457_ = lean_ctor_get(v_a_5456_, 0);
lean_inc(v_fst_5457_);
v_snd_5458_ = lean_ctor_get(v_a_5456_, 1);
lean_inc(v_snd_5458_);
lean_dec(v_a_5456_);
v_fst_5441_ = v_fst_5457_;
v_snd_5442_ = v_snd_5458_;
goto v___jp_5440_;
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5459_ = lean_ctor_get(v___y_5455_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___y_5455_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___y_5455_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___y_5455_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5464_; 
if (v_isShared_5462_ == 0)
{
v___x_5464_ = v___x_5461_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_a_5459_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5487_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5424_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5424_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
v___jp_5368_:
{
lean_object* v___x_5371_; 
v___x_5371_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5367_, v___y_5370_, v___y_5369_);
lean_dec_ref(v___y_5370_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v___x_5372_; lean_object* v___x_5373_; 
lean_dec_ref_known(v___x_5371_, 1);
lean_inc_ref(v_resultType_5337_);
v___x_5372_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5372_, 0, v_resultType_5337_);
lean_inc_ref(v_a_5351_);
v___x_5373_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5351_, v___x_5372_);
v_a_5353_ = v___x_5373_;
goto v___jp_5352_;
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5374_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5371_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5371_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
v___jp_5382_:
{
switch(lean_obj_tag(v_a_5351_))
{
case 0:
{
lean_object* v_code_5384_; 
v_code_5384_ = lean_ctor_get(v_a_5351_, 2);
lean_inc_ref(v_code_5384_);
v___y_5369_ = v___y_5383_;
v___y_5370_ = v_code_5384_;
goto v___jp_5368_;
}
case 1:
{
lean_object* v_code_5385_; 
v_code_5385_ = lean_ctor_get(v_a_5351_, 1);
lean_inc_ref(v_code_5385_);
v___y_5369_ = v___y_5383_;
v___y_5370_ = v_code_5385_;
goto v___jp_5368_;
}
default: 
{
lean_object* v_code_5386_; 
v_code_5386_ = lean_ctor_get(v_a_5351_, 0);
lean_inc_ref(v_code_5386_);
v___y_5369_ = v___y_5383_;
v___y_5370_ = v_code_5386_;
goto v___jp_5368_;
}
}
}
}
else
{
lean_object* v_code_5495_; lean_object* v___x_5496_; 
v_code_5495_ = lean_ctor_get(v_a_5351_, 0);
lean_inc_ref(v_code_5495_);
v___x_5496_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5340_, v_code_5495_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
if (lean_obj_tag(v___x_5496_) == 0)
{
lean_object* v_a_5497_; lean_object* v___x_5498_; 
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
lean_inc(v_a_5497_);
lean_dec_ref_known(v___x_5496_, 1);
lean_inc_ref(v_a_5351_);
v___x_5498_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5351_, v_a_5497_);
v_a_5353_ = v___x_5498_;
goto v___jp_5352_;
}
else
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
lean_dec_ref(v_as_5342_);
lean_dec(v_i_5341_);
lean_dec(v_discr_5339_);
lean_dec_ref(v_resultType_5337_);
v_a_5499_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5501_ = v___x_5496_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5496_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
v___jp_5352_:
{
size_t v___x_5354_; size_t v___x_5355_; uint8_t v___x_5356_; 
v___x_5354_ = lean_ptr_addr(v_a_5351_);
v___x_5355_ = lean_ptr_addr(v_a_5353_);
v___x_5356_ = lean_usize_dec_eq(v___x_5354_, v___x_5355_);
if (v___x_5356_ == 0)
{
lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5357_ = lean_unsigned_to_nat(1u);
v___x_5358_ = lean_nat_add(v_i_5341_, v___x_5357_);
v___x_5359_ = lean_array_fset(v_as_5342_, v_i_5341_, v_a_5353_);
lean_dec(v_i_5341_);
v_i_5341_ = v___x_5358_;
v_as_5342_ = v___x_5359_;
goto _start;
}
else
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
lean_dec_ref(v_a_5353_);
v___x_5361_ = lean_unsigned_to_nat(1u);
v___x_5362_ = lean_nat_add(v_i_5341_, v___x_5361_);
lean_dec(v_i_5341_);
v_i_5341_ = v___x_5362_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5507_, lean_object* v_code_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_){
_start:
{
lean_object* v_decl_5515_; lean_object* v_k_5516_; lean_object* v___y_5517_; lean_object* v___y_5518_; lean_object* v___y_5519_; lean_object* v___y_5520_; 
switch(lean_obj_tag(v_code_5508_))
{
case 0:
{
lean_object* v_decl_5628_; lean_object* v_k_5629_; lean_object* v___x_5630_; 
v_decl_5628_ = lean_ctor_get(v_code_5508_, 0);
v_k_5629_ = lean_ctor_get(v_code_5508_, 1);
lean_inc_ref(v_k_5629_);
v___x_5630_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5507_, v_k_5629_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v_a_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5667_; 
v_a_5631_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5667_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5667_ == 0)
{
v___x_5633_ = v___x_5630_;
v_isShared_5634_ = v_isSharedCheck_5667_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_a_5631_);
lean_dec(v___x_5630_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5667_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
size_t v___x_5635_; size_t v___x_5636_; uint8_t v___x_5637_; 
v___x_5635_ = lean_ptr_addr(v_k_5629_);
v___x_5636_ = lean_ptr_addr(v_a_5631_);
v___x_5637_ = lean_usize_dec_eq(v___x_5635_, v___x_5636_);
if (v___x_5637_ == 0)
{
lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5647_; 
lean_inc_ref(v_decl_5628_);
v_isSharedCheck_5647_ = !lean_is_exclusive(v_code_5508_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; lean_object* v_unused_5649_; 
v_unused_5648_ = lean_ctor_get(v_code_5508_, 1);
lean_dec(v_unused_5648_);
v_unused_5649_ = lean_ctor_get(v_code_5508_, 0);
lean_dec(v_unused_5649_);
v___x_5639_ = v_code_5508_;
v_isShared_5640_ = v_isSharedCheck_5647_;
goto v_resetjp_5638_;
}
else
{
lean_dec(v_code_5508_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5647_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 1, v_a_5631_);
v___x_5642_ = v___x_5639_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_decl_5628_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_a_5631_);
v___x_5642_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
lean_object* v___x_5644_; 
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v___x_5642_);
v___x_5644_ = v___x_5633_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v___x_5642_);
v___x_5644_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
return v___x_5644_;
}
}
}
}
else
{
size_t v___x_5650_; uint8_t v___x_5651_; 
v___x_5650_ = lean_ptr_addr(v_decl_5628_);
v___x_5651_ = lean_usize_dec_eq(v___x_5650_, v___x_5650_);
if (v___x_5651_ == 0)
{
lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5661_; 
lean_inc_ref(v_decl_5628_);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_code_5508_);
if (v_isSharedCheck_5661_ == 0)
{
lean_object* v_unused_5662_; lean_object* v_unused_5663_; 
v_unused_5662_ = lean_ctor_get(v_code_5508_, 1);
lean_dec(v_unused_5662_);
v_unused_5663_ = lean_ctor_get(v_code_5508_, 0);
lean_dec(v_unused_5663_);
v___x_5653_ = v_code_5508_;
v_isShared_5654_ = v_isSharedCheck_5661_;
goto v_resetjp_5652_;
}
else
{
lean_dec(v_code_5508_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5661_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
lean_ctor_set(v___x_5653_, 1, v_a_5631_);
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_decl_5628_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v_a_5631_);
v___x_5656_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5658_; 
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v___x_5656_);
v___x_5658_ = v___x_5633_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v___x_5656_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
}
else
{
lean_object* v___x_5665_; 
lean_dec(v_a_5631_);
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v_code_5508_);
v___x_5665_ = v___x_5633_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_code_5508_);
v___x_5665_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
return v___x_5665_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_5508_, 2);
return v___x_5630_;
}
}
case 1:
{
lean_object* v_decl_5668_; lean_object* v_k_5669_; 
v_decl_5668_ = lean_ctor_get(v_code_5508_, 0);
v_k_5669_ = lean_ctor_get(v_code_5508_, 1);
lean_inc_ref(v_k_5669_);
lean_inc_ref(v_decl_5668_);
v_decl_5515_ = v_decl_5668_;
v_k_5516_ = v_k_5669_;
v___y_5517_ = v_a_5509_;
v___y_5518_ = v_a_5510_;
v___y_5519_ = v_a_5511_;
v___y_5520_ = v_a_5512_;
goto v___jp_5514_;
}
case 2:
{
lean_object* v_decl_5670_; lean_object* v_k_5671_; 
v_decl_5670_ = lean_ctor_get(v_code_5508_, 0);
v_k_5671_ = lean_ctor_get(v_code_5508_, 1);
lean_inc_ref(v_k_5671_);
lean_inc_ref(v_decl_5670_);
v_decl_5515_ = v_decl_5670_;
v_k_5516_ = v_k_5671_;
v___y_5517_ = v_a_5509_;
v___y_5518_ = v_a_5510_;
v___y_5519_ = v_a_5511_;
v___y_5520_ = v_a_5512_;
goto v___jp_5514_;
}
case 4:
{
lean_object* v_cases_5672_; lean_object* v_typeName_5673_; lean_object* v_resultType_5674_; lean_object* v_discr_5675_; lean_object* v_alts_5676_; lean_object* v___x_5678_; uint8_t v_isShared_5679_; uint8_t v_isSharedCheck_5717_; 
v_cases_5672_ = lean_ctor_get(v_code_5508_, 0);
lean_inc_ref(v_cases_5672_);
v_typeName_5673_ = lean_ctor_get(v_cases_5672_, 0);
v_resultType_5674_ = lean_ctor_get(v_cases_5672_, 1);
v_discr_5675_ = lean_ctor_get(v_cases_5672_, 2);
v_alts_5676_ = lean_ctor_get(v_cases_5672_, 3);
v_isSharedCheck_5717_ = !lean_is_exclusive(v_cases_5672_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5678_ = v_cases_5672_;
v_isShared_5679_ = v_isSharedCheck_5717_;
goto v_resetjp_5677_;
}
else
{
lean_inc(v_alts_5676_);
lean_inc(v_discr_5675_);
lean_inc(v_resultType_5674_);
lean_inc(v_typeName_5673_);
lean_dec(v_cases_5672_);
v___x_5678_ = lean_box(0);
v_isShared_5679_ = v_isSharedCheck_5717_;
goto v_resetjp_5677_;
}
v_resetjp_5677_:
{
lean_object* v___x_5680_; lean_object* v_discrVal_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; 
v___x_5680_ = lean_box(0);
v_discrVal_5681_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5507_, v_discr_5675_, v___x_5680_);
v___x_5682_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5676_);
lean_inc(v_discr_5675_);
lean_inc_ref(v_resultType_5674_);
v___x_5683_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5674_, v_discrVal_5681_, v_discr_5675_, v_assignment_5507_, v___x_5682_, v_alts_5676_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
lean_dec(v_discrVal_5681_);
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5708_; 
v_a_5684_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5686_ = v___x_5683_;
v_isShared_5687_ = v_isSharedCheck_5708_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___x_5683_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5708_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
size_t v___x_5688_; size_t v___x_5689_; uint8_t v___x_5690_; 
v___x_5688_ = lean_ptr_addr(v_alts_5676_);
lean_dec_ref(v_alts_5676_);
v___x_5689_ = lean_ptr_addr(v_a_5684_);
v___x_5690_ = lean_usize_dec_eq(v___x_5688_, v___x_5689_);
if (v___x_5690_ == 0)
{
lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5703_; 
v_isSharedCheck_5703_ = !lean_is_exclusive(v_code_5508_);
if (v_isSharedCheck_5703_ == 0)
{
lean_object* v_unused_5704_; 
v_unused_5704_ = lean_ctor_get(v_code_5508_, 0);
lean_dec(v_unused_5704_);
v___x_5692_ = v_code_5508_;
v_isShared_5693_ = v_isSharedCheck_5703_;
goto v_resetjp_5691_;
}
else
{
lean_dec(v_code_5508_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5703_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 3, v_a_5684_);
v___x_5695_ = v___x_5678_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_typeName_5673_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v_resultType_5674_);
lean_ctor_set(v_reuseFailAlloc_5702_, 2, v_discr_5675_);
lean_ctor_set(v_reuseFailAlloc_5702_, 3, v_a_5684_);
v___x_5695_ = v_reuseFailAlloc_5702_;
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
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
lean_object* v___x_5699_; 
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 0, v___x_5697_);
v___x_5699_ = v___x_5686_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5697_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
}
else
{
lean_object* v___x_5706_; 
lean_dec(v_a_5684_);
lean_del_object(v___x_5678_);
lean_dec(v_discr_5675_);
lean_dec_ref(v_resultType_5674_);
lean_dec(v_typeName_5673_);
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 0, v_code_5508_);
v___x_5706_ = v___x_5686_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v_code_5508_);
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
else
{
lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5716_; 
lean_del_object(v___x_5678_);
lean_dec_ref(v_alts_5676_);
lean_dec(v_discr_5675_);
lean_dec_ref(v_resultType_5674_);
lean_dec(v_typeName_5673_);
lean_dec_ref_known(v_code_5508_, 1);
v_a_5709_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5716_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5711_ = v___x_5683_;
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_dec(v___x_5683_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5714_; 
if (v_isShared_5712_ == 0)
{
v___x_5714_ = v___x_5711_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
}
}
}
default: 
{
lean_object* v___x_5718_; 
v___x_5718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5718_, 0, v_code_5508_);
return v___x_5718_;
}
}
v___jp_5514_:
{
lean_object* v_params_5521_; lean_object* v_type_5522_; lean_object* v_value_5523_; lean_object* v___x_5524_; 
v_params_5521_ = lean_ctor_get(v_decl_5515_, 2);
lean_inc_ref(v_params_5521_);
v_type_5522_ = lean_ctor_get(v_decl_5515_, 3);
lean_inc_ref(v_type_5522_);
v_value_5523_ = lean_ctor_get(v_decl_5515_, 4);
lean_inc_ref(v_value_5523_);
v___x_5524_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5507_, v_value_5523_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_);
if (lean_obj_tag(v___x_5524_) == 0)
{
lean_object* v_a_5525_; uint8_t v___x_5526_; lean_object* v___x_5527_; 
v_a_5525_ = lean_ctor_get(v___x_5524_, 0);
lean_inc(v_a_5525_);
lean_dec_ref_known(v___x_5524_, 1);
v___x_5526_ = 0;
v___x_5527_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5526_, v_decl_5515_, v_type_5522_, v_params_5521_, v_a_5525_, v___y_5518_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5529_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
lean_inc(v_a_5528_);
lean_dec_ref_known(v___x_5527_, 1);
v___x_5529_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5507_, v_k_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_);
if (lean_obj_tag(v___x_5529_) == 0)
{
switch(lean_obj_tag(v_code_5508_))
{
case 1:
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5569_; 
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5532_ = v___x_5529_;
v_isShared_5533_ = v_isSharedCheck_5569_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5529_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5569_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v_decl_5534_; lean_object* v_k_5535_; size_t v___x_5536_; size_t v___x_5537_; uint8_t v___x_5538_; 
v_decl_5534_ = lean_ctor_get(v_code_5508_, 0);
v_k_5535_ = lean_ctor_get(v_code_5508_, 1);
v___x_5536_ = lean_ptr_addr(v_k_5535_);
v___x_5537_ = lean_ptr_addr(v_a_5530_);
v___x_5538_ = lean_usize_dec_eq(v___x_5536_, v___x_5537_);
if (v___x_5538_ == 0)
{
lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5548_; 
v_isSharedCheck_5548_ = !lean_is_exclusive(v_code_5508_);
if (v_isSharedCheck_5548_ == 0)
{
lean_object* v_unused_5549_; lean_object* v_unused_5550_; 
v_unused_5549_ = lean_ctor_get(v_code_5508_, 1);
lean_dec(v_unused_5549_);
v_unused_5550_ = lean_ctor_get(v_code_5508_, 0);
lean_dec(v_unused_5550_);
v___x_5540_ = v_code_5508_;
v_isShared_5541_ = v_isSharedCheck_5548_;
goto v_resetjp_5539_;
}
else
{
lean_dec(v_code_5508_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5548_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5543_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 1, v_a_5530_);
lean_ctor_set(v___x_5540_, 0, v_a_5528_);
v___x_5543_ = v___x_5540_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5528_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_a_5530_);
v___x_5543_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5545_; 
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v___x_5543_);
v___x_5545_ = v___x_5532_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5543_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
else
{
size_t v___x_5551_; size_t v___x_5552_; uint8_t v___x_5553_; 
v___x_5551_ = lean_ptr_addr(v_decl_5534_);
v___x_5552_ = lean_ptr_addr(v_a_5528_);
v___x_5553_ = lean_usize_dec_eq(v___x_5551_, v___x_5552_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5563_; 
v_isSharedCheck_5563_ = !lean_is_exclusive(v_code_5508_);
if (v_isSharedCheck_5563_ == 0)
{
lean_object* v_unused_5564_; lean_object* v_unused_5565_; 
v_unused_5564_ = lean_ctor_get(v_code_5508_, 1);
lean_dec(v_unused_5564_);
v_unused_5565_ = lean_ctor_get(v_code_5508_, 0);
lean_dec(v_unused_5565_);
v___x_5555_ = v_code_5508_;
v_isShared_5556_ = v_isSharedCheck_5563_;
goto v_resetjp_5554_;
}
else
{
lean_dec(v_code_5508_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5563_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5558_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 1, v_a_5530_);
lean_ctor_set(v___x_5555_, 0, v_a_5528_);
v___x_5558_ = v___x_5555_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5528_);
lean_ctor_set(v_reuseFailAlloc_5562_, 1, v_a_5530_);
v___x_5558_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
lean_object* v___x_5560_; 
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v___x_5558_);
v___x_5560_ = v___x_5532_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v___x_5558_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
else
{
lean_object* v___x_5567_; 
lean_dec(v_a_5530_);
lean_dec(v_a_5528_);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v_code_5508_);
v___x_5567_ = v___x_5532_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_code_5508_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
}
case 2:
{
lean_object* v_a_5570_; lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5609_; 
v_a_5570_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5572_ = v___x_5529_;
v_isShared_5573_ = v_isSharedCheck_5609_;
goto v_resetjp_5571_;
}
else
{
lean_inc(v_a_5570_);
lean_dec(v___x_5529_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5609_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v_decl_5574_; lean_object* v_k_5575_; size_t v___x_5576_; size_t v___x_5577_; uint8_t v___x_5578_; 
v_decl_5574_ = lean_ctor_get(v_code_5508_, 0);
v_k_5575_ = lean_ctor_get(v_code_5508_, 1);
v___x_5576_ = lean_ptr_addr(v_k_5575_);
v___x_5577_ = lean_ptr_addr(v_a_5570_);
v___x_5578_ = lean_usize_dec_eq(v___x_5576_, v___x_5577_);
if (v___x_5578_ == 0)
{
lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5588_; 
v_isSharedCheck_5588_ = !lean_is_exclusive(v_code_5508_);
if (v_isSharedCheck_5588_ == 0)
{
lean_object* v_unused_5589_; lean_object* v_unused_5590_; 
v_unused_5589_ = lean_ctor_get(v_code_5508_, 1);
lean_dec(v_unused_5589_);
v_unused_5590_ = lean_ctor_get(v_code_5508_, 0);
lean_dec(v_unused_5590_);
v___x_5580_ = v_code_5508_;
v_isShared_5581_ = v_isSharedCheck_5588_;
goto v_resetjp_5579_;
}
else
{
lean_dec(v_code_5508_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5588_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
lean_ctor_set(v___x_5580_, 1, v_a_5570_);
lean_ctor_set(v___x_5580_, 0, v_a_5528_);
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5528_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v_a_5570_);
v___x_5583_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5585_; 
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 0, v___x_5583_);
v___x_5585_ = v___x_5572_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
return v___x_5585_;
}
}
}
}
else
{
size_t v___x_5591_; size_t v___x_5592_; uint8_t v___x_5593_; 
v___x_5591_ = lean_ptr_addr(v_decl_5574_);
v___x_5592_ = lean_ptr_addr(v_a_5528_);
v___x_5593_ = lean_usize_dec_eq(v___x_5591_, v___x_5592_);
if (v___x_5593_ == 0)
{
lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5603_; 
v_isSharedCheck_5603_ = !lean_is_exclusive(v_code_5508_);
if (v_isSharedCheck_5603_ == 0)
{
lean_object* v_unused_5604_; lean_object* v_unused_5605_; 
v_unused_5604_ = lean_ctor_get(v_code_5508_, 1);
lean_dec(v_unused_5604_);
v_unused_5605_ = lean_ctor_get(v_code_5508_, 0);
lean_dec(v_unused_5605_);
v___x_5595_ = v_code_5508_;
v_isShared_5596_ = v_isSharedCheck_5603_;
goto v_resetjp_5594_;
}
else
{
lean_dec(v_code_5508_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5603_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 1, v_a_5570_);
lean_ctor_set(v___x_5595_, 0, v_a_5528_);
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5528_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v_a_5570_);
v___x_5598_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5600_; 
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 0, v___x_5598_);
v___x_5600_ = v___x_5572_;
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
else
{
lean_object* v___x_5607_; 
lean_dec(v_a_5570_);
lean_dec(v_a_5528_);
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 0, v_code_5508_);
v___x_5607_ = v___x_5572_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_code_5508_);
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
}
default: 
{
lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5618_; 
lean_dec(v_a_5528_);
lean_dec_ref(v_code_5508_);
v_isSharedCheck_5618_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5618_ == 0)
{
lean_object* v_unused_5619_; 
v_unused_5619_ = lean_ctor_get(v___x_5529_, 0);
lean_dec(v_unused_5619_);
v___x_5611_ = v___x_5529_;
v_isShared_5612_ = v_isSharedCheck_5618_;
goto v_resetjp_5610_;
}
else
{
lean_dec(v___x_5529_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5618_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5616_; 
v___x_5613_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5614_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5613_);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 0, v___x_5614_);
v___x_5616_ = v___x_5611_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v___x_5614_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
}
}
}
else
{
lean_dec(v_a_5528_);
lean_dec_ref(v_code_5508_);
return v___x_5529_;
}
}
else
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5627_; 
lean_dec_ref(v_k_5516_);
lean_dec_ref(v_code_5508_);
v_a_5620_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5622_ = v___x_5527_;
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5527_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5625_; 
if (v_isShared_5623_ == 0)
{
v___x_5625_ = v___x_5622_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_a_5620_);
v___x_5625_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
return v___x_5625_;
}
}
}
}
else
{
lean_dec_ref(v_type_5522_);
lean_dec_ref(v_params_5521_);
lean_dec_ref(v_k_5516_);
lean_dec_ref(v_decl_5515_);
lean_dec_ref(v_code_5508_);
return v___x_5524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5719_, lean_object* v_code_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_){
_start:
{
lean_object* v_res_5726_; 
v_res_5726_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5719_, v_code_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
lean_dec(v_a_5724_);
lean_dec_ref(v_a_5723_);
lean_dec(v_a_5722_);
lean_dec_ref(v_a_5721_);
lean_dec_ref(v_assignment_5719_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5727_, lean_object* v_discrVal_5728_, lean_object* v_discr_5729_, lean_object* v_assignment_5730_, lean_object* v_i_5731_, lean_object* v_as_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_){
_start:
{
lean_object* v_res_5738_; 
v_res_5738_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5727_, v_discrVal_5728_, v_discr_5729_, v_assignment_5730_, v_i_5731_, v_as_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_);
lean_dec(v___y_5736_);
lean_dec_ref(v___y_5735_);
lean_dec(v___y_5734_);
lean_dec_ref(v___y_5733_);
lean_dec_ref(v_assignment_5730_);
lean_dec(v_discrVal_5728_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5739_, lean_object* v_m_5740_, lean_object* v_a_5741_){
_start:
{
lean_object* v___x_5742_; 
v___x_5742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5740_, v_a_5741_);
return v___x_5742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5743_, lean_object* v_m_5744_, lean_object* v_a_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5743_, v_m_5744_, v_a_5745_);
lean_dec(v_a_5745_);
lean_dec_ref(v_m_5744_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5747_, size_t v_i_5748_, size_t v_stop_5749_, lean_object* v_b_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_){
_start:
{
lean_object* v___x_5756_; 
v___x_5756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5747_, v_i_5748_, v_stop_5749_, v_b_5750_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5757_, lean_object* v_i_5758_, lean_object* v_stop_5759_, lean_object* v_b_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_){
_start:
{
size_t v_i_boxed_5766_; size_t v_stop_boxed_5767_; lean_object* v_res_5768_; 
v_i_boxed_5766_ = lean_unbox_usize(v_i_5758_);
lean_dec(v_i_5758_);
v_stop_boxed_5767_ = lean_unbox_usize(v_stop_5759_);
lean_dec(v_stop_5759_);
v_res_5768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5757_, v_i_boxed_5766_, v_stop_boxed_5767_, v_b_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
lean_dec(v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec_ref(v_as_5757_);
return v_res_5768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5769_, lean_object* v_a_5770_, lean_object* v_x_5771_){
_start:
{
lean_object* v___x_5772_; 
v___x_5772_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5770_, v_x_5771_);
return v___x_5772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5773_, lean_object* v_a_5774_, lean_object* v_x_5775_){
_start:
{
lean_object* v_res_5776_; 
v_res_5776_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5773_, v_a_5774_, v_x_5775_);
lean_dec(v_x_5775_);
lean_dec(v_a_5774_);
return v_res_5776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5777_, lean_object* v_v_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
if (lean_obj_tag(v_v_5778_) == 0)
{
lean_object* v_code_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5808_; 
v_code_5784_ = lean_ctor_get(v_v_5778_, 0);
v_isSharedCheck_5808_ = !lean_is_exclusive(v_v_5778_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5786_ = v_v_5778_;
v_isShared_5787_ = v_isSharedCheck_5808_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_code_5784_);
lean_dec(v_v_5778_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5808_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5788_; 
lean_inc(v___y_5782_);
lean_inc_ref(v___y_5781_);
lean_inc(v___y_5780_);
lean_inc_ref(v___y_5779_);
v___x_5788_ = lean_apply_6(v_f_5777_, v_code_5784_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_, lean_box(0));
if (lean_obj_tag(v___x_5788_) == 0)
{
lean_object* v_a_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5799_; 
v_a_5789_ = lean_ctor_get(v___x_5788_, 0);
v_isSharedCheck_5799_ = !lean_is_exclusive(v___x_5788_);
if (v_isSharedCheck_5799_ == 0)
{
v___x_5791_ = v___x_5788_;
v_isShared_5792_ = v_isSharedCheck_5799_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_a_5789_);
lean_dec(v___x_5788_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5799_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
lean_object* v___x_5794_; 
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 0, v_a_5789_);
v___x_5794_ = v___x_5786_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_a_5789_);
v___x_5794_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
lean_object* v___x_5796_; 
if (v_isShared_5792_ == 0)
{
lean_ctor_set(v___x_5791_, 0, v___x_5794_);
v___x_5796_ = v___x_5791_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5794_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
}
else
{
lean_object* v_a_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5807_; 
lean_del_object(v___x_5786_);
v_a_5800_ = lean_ctor_get(v___x_5788_, 0);
v_isSharedCheck_5807_ = !lean_is_exclusive(v___x_5788_);
if (v_isSharedCheck_5807_ == 0)
{
v___x_5802_ = v___x_5788_;
v_isShared_5803_ = v_isSharedCheck_5807_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_a_5800_);
lean_dec(v___x_5788_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5807_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
lean_object* v___x_5805_; 
if (v_isShared_5803_ == 0)
{
v___x_5805_ = v___x_5802_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
v___x_5805_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
return v___x_5805_;
}
}
}
}
}
else
{
lean_object* v___x_5809_; 
lean_dec_ref(v_f_5777_);
v___x_5809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5809_, 0, v_v_5778_);
return v___x_5809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5810_, lean_object* v_v_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5810_, v_v_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
lean_dec(v___y_5815_);
lean_dec_ref(v___y_5814_);
lean_dec(v___y_5813_);
lean_dec_ref(v___y_5812_);
return v_res_5817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5818_, lean_object* v_f_5819_, lean_object* v_v_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_){
_start:
{
lean_object* v___x_5826_; 
v___x_5826_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5819_, v_v_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_);
return v___x_5826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5827_, lean_object* v_f_5828_, lean_object* v_v_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_){
_start:
{
uint8_t v_pu_boxed_5835_; lean_object* v_res_5836_; 
v_pu_boxed_5835_ = lean_unbox(v_pu_5827_);
v_res_5836_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5835_, v_f_5828_, v_v_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
lean_dec(v___y_5833_);
lean_dec_ref(v___y_5832_);
lean_dec(v___y_5831_);
lean_dec_ref(v___y_5830_);
return v_res_5836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5837_, lean_object* v_x_5838_){
_start:
{
if (lean_obj_tag(v_x_5838_) == 0)
{
return v_x_5837_;
}
else
{
lean_object* v_key_5839_; lean_object* v_value_5840_; lean_object* v_tail_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; 
v_key_5839_ = lean_ctor_get(v_x_5838_, 0);
v_value_5840_ = lean_ctor_get(v_x_5838_, 1);
v_tail_5841_ = lean_ctor_get(v_x_5838_, 2);
lean_inc(v_value_5840_);
lean_inc(v_key_5839_);
v___x_5842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5842_, 0, v_key_5839_);
lean_ctor_set(v___x_5842_, 1, v_value_5840_);
v___x_5843_ = lean_array_push(v_x_5837_, v___x_5842_);
v_x_5837_ = v___x_5843_;
v_x_5838_ = v_tail_5841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5845_, lean_object* v_x_5846_){
_start:
{
lean_object* v_res_5847_; 
v_res_5847_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5845_, v_x_5846_);
lean_dec(v_x_5846_);
return v_res_5847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5848_, size_t v_i_5849_, size_t v_stop_5850_, lean_object* v_b_5851_){
_start:
{
uint8_t v___x_5852_; 
v___x_5852_ = lean_usize_dec_eq(v_i_5849_, v_stop_5850_);
if (v___x_5852_ == 0)
{
lean_object* v___x_5853_; lean_object* v___x_5854_; size_t v___x_5855_; size_t v___x_5856_; 
v___x_5853_ = lean_array_uget_borrowed(v_as_5848_, v_i_5849_);
v___x_5854_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5851_, v___x_5853_);
v___x_5855_ = ((size_t)1ULL);
v___x_5856_ = lean_usize_add(v_i_5849_, v___x_5855_);
v_i_5849_ = v___x_5856_;
v_b_5851_ = v___x_5854_;
goto _start;
}
else
{
return v_b_5851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5858_, lean_object* v_i_5859_, lean_object* v_stop_5860_, lean_object* v_b_5861_){
_start:
{
size_t v_i_boxed_5862_; size_t v_stop_boxed_5863_; lean_object* v_res_5864_; 
v_i_boxed_5862_ = lean_unbox_usize(v_i_5859_);
lean_dec(v_i_5859_);
v_stop_boxed_5863_ = lean_unbox_usize(v_stop_5860_);
lean_dec(v_stop_5860_);
v_res_5864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5858_, v_i_boxed_5862_, v_stop_boxed_5863_, v_b_5861_);
lean_dec_ref(v_as_5858_);
return v_res_5864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5865_, size_t v_sz_5866_, size_t v_i_5867_, lean_object* v_bs_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_){
_start:
{
uint8_t v___x_5874_; 
v___x_5874_ = lean_usize_dec_lt(v_i_5867_, v_sz_5866_);
if (v___x_5874_ == 0)
{
lean_object* v___x_5875_; 
v___x_5875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5875_, 0, v_bs_5868_);
return v___x_5875_;
}
else
{
lean_object* v_v_5876_; lean_object* v_fst_5877_; lean_object* v_snd_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5902_; 
v_v_5876_ = lean_array_uget(v_bs_5868_, v_i_5867_);
v_fst_5877_ = lean_ctor_get(v_v_5876_, 0);
v_snd_5878_ = lean_ctor_get(v_v_5876_, 1);
v_isSharedCheck_5902_ = !lean_is_exclusive(v_v_5876_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5880_ = v_v_5876_;
v_isShared_5881_ = v_isSharedCheck_5902_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_snd_5878_);
lean_inc(v_fst_5877_);
lean_dec(v_v_5876_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5902_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___x_5882_; 
v___x_5882_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5877_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_);
if (lean_obj_tag(v___x_5882_) == 0)
{
lean_object* v_a_5883_; lean_object* v___x_5884_; lean_object* v_bs_x27_5885_; lean_object* v___x_5886_; lean_object* v___x_5888_; 
v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
lean_inc(v_a_5883_);
lean_dec_ref_known(v___x_5882_, 1);
v___x_5884_ = lean_unsigned_to_nat(0u);
v_bs_x27_5885_ = lean_array_uset(v_bs_5868_, v_i_5867_, v___x_5884_);
v___x_5886_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5883_, v_a_5865_);
if (v_isShared_5881_ == 0)
{
lean_ctor_set(v___x_5880_, 0, v___x_5886_);
v___x_5888_ = v___x_5880_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5886_);
lean_ctor_set(v_reuseFailAlloc_5893_, 1, v_snd_5878_);
v___x_5888_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
size_t v___x_5889_; size_t v___x_5890_; lean_object* v___x_5891_; 
v___x_5889_ = ((size_t)1ULL);
v___x_5890_ = lean_usize_add(v_i_5867_, v___x_5889_);
v___x_5891_ = lean_array_uset(v_bs_x27_5885_, v_i_5867_, v___x_5888_);
v_i_5867_ = v___x_5890_;
v_bs_5868_ = v___x_5891_;
goto _start;
}
}
else
{
lean_object* v_a_5894_; lean_object* v___x_5896_; uint8_t v_isShared_5897_; uint8_t v_isSharedCheck_5901_; 
lean_del_object(v___x_5880_);
lean_dec(v_snd_5878_);
lean_dec_ref(v_bs_5868_);
v_a_5894_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5901_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5901_ == 0)
{
v___x_5896_ = v___x_5882_;
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
else
{
lean_inc(v_a_5894_);
lean_dec(v___x_5882_);
v___x_5896_ = lean_box(0);
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
v_resetjp_5895_:
{
lean_object* v___x_5899_; 
if (v_isShared_5897_ == 0)
{
v___x_5899_ = v___x_5896_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_a_5894_);
v___x_5899_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
return v___x_5899_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5903_, lean_object* v_sz_5904_, lean_object* v_i_5905_, lean_object* v_bs_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_){
_start:
{
uint8_t v_a_2392__boxed_5912_; size_t v_sz_boxed_5913_; size_t v_i_boxed_5914_; lean_object* v_res_5915_; 
v_a_2392__boxed_5912_ = lean_unbox(v_a_5903_);
v_sz_boxed_5913_ = lean_unbox_usize(v_sz_5904_);
lean_dec(v_sz_5904_);
v_i_boxed_5914_ = lean_unbox_usize(v_i_5905_);
lean_dec(v_i_5905_);
v_res_5915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2392__boxed_5912_, v_sz_boxed_5913_, v_i_boxed_5914_, v_bs_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
lean_dec(v___y_5910_);
lean_dec_ref(v___y_5909_);
lean_dec(v___y_5908_);
lean_dec_ref(v___y_5907_);
return v_res_5915_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5916_){
_start:
{
lean_object* v_fst_5917_; lean_object* v_snd_5918_; lean_object* v___x_5920_; uint8_t v_isShared_5921_; uint8_t v_isSharedCheck_5941_; 
v_fst_5917_ = lean_ctor_get(v_x_5916_, 0);
v_snd_5918_ = lean_ctor_get(v_x_5916_, 1);
v_isSharedCheck_5941_ = !lean_is_exclusive(v_x_5916_);
if (v_isSharedCheck_5941_ == 0)
{
v___x_5920_ = v_x_5916_;
v_isShared_5921_ = v_isSharedCheck_5941_;
goto v_resetjp_5919_;
}
else
{
lean_inc(v_snd_5918_);
lean_inc(v_fst_5917_);
lean_dec(v_x_5916_);
v___x_5920_ = lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5941_;
goto v_resetjp_5919_;
}
v_resetjp_5919_:
{
lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5926_; 
v___x_5922_ = l_String_quote(v_fst_5917_);
v___x_5923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5922_);
v___x_5924_ = lean_box(0);
if (v_isShared_5921_ == 0)
{
lean_ctor_set_tag(v___x_5920_, 1);
lean_ctor_set(v___x_5920_, 1, v___x_5924_);
lean_ctor_set(v___x_5920_, 0, v___x_5923_);
v___x_5926_ = v___x_5920_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v___x_5924_);
v___x_5926_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; uint8_t v___x_5938_; lean_object* v___x_5939_; 
v___x_5927_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5918_);
v___x_5928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5927_);
lean_ctor_set(v___x_5928_, 1, v___x_5926_);
v___x_5929_ = l_List_reverse___redArg(v___x_5928_);
v___x_5930_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5931_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5929_, v___x_5930_);
v___x_5932_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5933_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
lean_ctor_set(v___x_5934_, 1, v___x_5931_);
v___x_5935_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5932_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
v___x_5938_ = 0;
v___x_5939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5939_, 0, v___x_5937_);
lean_ctor_set_uint8(v___x_5939_, sizeof(void*)*1, v___x_5938_);
return v___x_5939_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5942_, lean_object* v_x_5943_, lean_object* v_x_5944_){
_start:
{
if (lean_obj_tag(v_x_5944_) == 0)
{
lean_dec(v_x_5942_);
return v_x_5943_;
}
else
{
lean_object* v_head_5945_; lean_object* v_tail_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5956_; 
v_head_5945_ = lean_ctor_get(v_x_5944_, 0);
v_tail_5946_ = lean_ctor_get(v_x_5944_, 1);
v_isSharedCheck_5956_ = !lean_is_exclusive(v_x_5944_);
if (v_isSharedCheck_5956_ == 0)
{
v___x_5948_ = v_x_5944_;
v_isShared_5949_ = v_isSharedCheck_5956_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_tail_5946_);
lean_inc(v_head_5945_);
lean_dec(v_x_5944_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5956_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
lean_inc(v_x_5942_);
if (v_isShared_5949_ == 0)
{
lean_ctor_set_tag(v___x_5948_, 5);
lean_ctor_set(v___x_5948_, 1, v_x_5942_);
lean_ctor_set(v___x_5948_, 0, v_x_5943_);
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5955_; 
v_reuseFailAlloc_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5955_, 0, v_x_5943_);
lean_ctor_set(v_reuseFailAlloc_5955_, 1, v_x_5942_);
v___x_5951_ = v_reuseFailAlloc_5955_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
lean_object* v___x_5952_; lean_object* v___x_5953_; 
v___x_5952_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5945_);
v___x_5953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5951_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v_x_5943_ = v___x_5953_;
v_x_5944_ = v_tail_5946_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5957_, lean_object* v_x_5958_, lean_object* v_x_5959_){
_start:
{
if (lean_obj_tag(v_x_5959_) == 0)
{
lean_dec(v_x_5957_);
return v_x_5958_;
}
else
{
lean_object* v_head_5960_; lean_object* v_tail_5961_; lean_object* v___x_5963_; uint8_t v_isShared_5964_; uint8_t v_isSharedCheck_5971_; 
v_head_5960_ = lean_ctor_get(v_x_5959_, 0);
v_tail_5961_ = lean_ctor_get(v_x_5959_, 1);
v_isSharedCheck_5971_ = !lean_is_exclusive(v_x_5959_);
if (v_isSharedCheck_5971_ == 0)
{
v___x_5963_ = v_x_5959_;
v_isShared_5964_ = v_isSharedCheck_5971_;
goto v_resetjp_5962_;
}
else
{
lean_inc(v_tail_5961_);
lean_inc(v_head_5960_);
lean_dec(v_x_5959_);
v___x_5963_ = lean_box(0);
v_isShared_5964_ = v_isSharedCheck_5971_;
goto v_resetjp_5962_;
}
v_resetjp_5962_:
{
lean_object* v___x_5966_; 
lean_inc(v_x_5957_);
if (v_isShared_5964_ == 0)
{
lean_ctor_set_tag(v___x_5963_, 5);
lean_ctor_set(v___x_5963_, 1, v_x_5957_);
lean_ctor_set(v___x_5963_, 0, v_x_5958_);
v___x_5966_ = v___x_5963_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_x_5958_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v_x_5957_);
v___x_5966_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; 
v___x_5967_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5960_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5966_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5957_, v___x_5968_, v_tail_5961_);
return v___x_5969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5972_, lean_object* v_x_5973_){
_start:
{
if (lean_obj_tag(v_x_5972_) == 0)
{
lean_object* v___x_5974_; 
lean_dec(v_x_5973_);
v___x_5974_ = lean_box(0);
return v___x_5974_;
}
else
{
lean_object* v_tail_5975_; 
v_tail_5975_ = lean_ctor_get(v_x_5972_, 1);
if (lean_obj_tag(v_tail_5975_) == 0)
{
lean_object* v_head_5976_; lean_object* v___x_5977_; 
lean_dec(v_x_5973_);
v_head_5976_ = lean_ctor_get(v_x_5972_, 0);
lean_inc(v_head_5976_);
lean_dec_ref_known(v_x_5972_, 2);
v___x_5977_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5976_);
return v___x_5977_;
}
else
{
lean_object* v_head_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; 
lean_inc(v_tail_5975_);
v_head_5978_ = lean_ctor_get(v_x_5972_, 0);
lean_inc(v_head_5978_);
lean_dec_ref_known(v_x_5972_, 2);
v___x_5979_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5978_);
v___x_5980_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5973_, v___x_5979_, v_tail_5975_);
return v___x_5980_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5983_ = lean_string_length(v___x_5982_);
return v___x_5983_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5984_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5985_ = lean_nat_to_int(v___x_5984_);
return v___x_5985_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5991_){
_start:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; uint8_t v___x_5994_; 
v___x_5992_ = lean_array_get_size(v_xs_5991_);
v___x_5993_ = lean_unsigned_to_nat(0u);
v___x_5994_ = lean_nat_dec_eq(v___x_5992_, v___x_5993_);
if (v___x_5994_ == 0)
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; 
v___x_5995_ = lean_array_to_list(v_xs_5991_);
v___x_5996_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5997_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5995_, v___x_5996_);
v___x_5998_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5999_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_6000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5999_);
lean_ctor_set(v___x_6000_, 1, v___x_5997_);
v___x_6001_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6000_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v___x_6003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_5998_);
lean_ctor_set(v___x_6003_, 1, v___x_6002_);
v___x_6004_ = l_Std_Format_fill(v___x_6003_);
return v___x_6004_;
}
else
{
lean_object* v___x_6005_; 
lean_dec_ref(v_xs_5991_);
v___x_6005_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_6005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_6008_, lean_object* v_decl_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_){
_start:
{
lean_object* v___y_6016_; lean_object* v___y_6017_; lean_object* v___y_6018_; lean_object* v___y_6019_; lean_object* v_options_6049_; uint8_t v_hasTrace_6050_; 
v_options_6049_ = lean_ctor_get(v_a_6012_, 2);
v_hasTrace_6050_ = lean_ctor_get_uint8(v_options_6049_, sizeof(void*)*1);
if (v_hasTrace_6050_ == 0)
{
v___y_6016_ = v_a_6010_;
v___y_6017_ = v_a_6011_;
v___y_6018_ = v_a_6012_;
v___y_6019_ = v_a_6013_;
goto v___jp_6015_;
}
else
{
lean_object* v_inheritedTraceOptions_6051_; lean_object* v_cls_6052_; uint8_t v___y_6054_; lean_object* v___y_6055_; lean_object* v___x_6091_; uint8_t v___x_6092_; 
v_inheritedTraceOptions_6051_ = lean_ctor_get(v_a_6012_, 13);
v_cls_6052_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6091_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6051_, v_options_6049_, v___x_6091_);
if (v___x_6092_ == 0)
{
v___y_6016_ = v_a_6010_;
v___y_6017_ = v_a_6011_;
v___y_6018_ = v_a_6012_;
v___y_6019_ = v_a_6013_;
goto v___jp_6015_;
}
else
{
lean_object* v_size_6093_; lean_object* v_buckets_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; uint8_t v___x_6098_; 
v_size_6093_ = lean_ctor_get(v_assignment_6008_, 0);
v_buckets_6094_ = lean_ctor_get(v_assignment_6008_, 1);
v___x_6095_ = lean_mk_empty_array_with_capacity(v_size_6093_);
v___x_6096_ = lean_unsigned_to_nat(0u);
v___x_6097_ = lean_array_get_size(v_buckets_6094_);
v___x_6098_ = lean_nat_dec_lt(v___x_6096_, v___x_6097_);
if (v___x_6098_ == 0)
{
v___y_6054_ = v___x_6092_;
v___y_6055_ = v___x_6095_;
goto v___jp_6053_;
}
else
{
size_t v___x_6099_; size_t v___x_6100_; lean_object* v___x_6101_; 
v___x_6099_ = ((size_t)0ULL);
v___x_6100_ = lean_usize_of_nat(v___x_6097_);
v___x_6101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6094_, v___x_6099_, v___x_6100_, v___x_6095_);
v___y_6054_ = v___x_6092_;
v___y_6055_ = v___x_6101_;
goto v___jp_6053_;
}
}
v___jp_6053_:
{
size_t v_sz_6056_; size_t v___x_6057_; lean_object* v___x_6058_; 
v_sz_6056_ = lean_array_size(v___y_6055_);
v___x_6057_ = ((size_t)0ULL);
v___x_6058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6054_, v_sz_6056_, v___x_6057_, v___y_6055_, v_a_6010_, v_a_6011_, v_a_6012_, v_a_6013_);
if (lean_obj_tag(v___x_6058_) == 0)
{
lean_object* v_toSignature_6059_; lean_object* v_a_6060_; lean_object* v_name_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v_toSignature_6059_ = lean_ctor_get(v_decl_6009_, 0);
v_a_6060_ = lean_ctor_get(v___x_6058_, 0);
lean_inc(v_a_6060_);
lean_dec_ref_known(v___x_6058_, 1);
v_name_6061_ = lean_ctor_get(v_toSignature_6059_, 0);
v___x_6062_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6061_);
v___x_6063_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6061_, v___y_6054_);
v___x_6064_ = lean_string_append(v___x_6062_, v___x_6063_);
lean_dec_ref(v___x_6063_);
v___x_6065_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6066_ = lean_string_append(v___x_6064_, v___x_6065_);
v___x_6067_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6060_);
v___x_6068_ = l_Std_Format_defWidth;
v___x_6069_ = lean_unsigned_to_nat(0u);
v___x_6070_ = l_Std_Format_pretty(v___x_6067_, v___x_6068_, v___x_6069_, v___x_6069_);
v___x_6071_ = lean_string_append(v___x_6066_, v___x_6070_);
lean_dec_ref(v___x_6070_);
v___x_6072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
v___x_6073_ = l_Lean_MessageData_ofFormat(v___x_6072_);
v___x_6074_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_6052_, v___x_6073_, v_a_6010_, v_a_6011_, v_a_6012_, v_a_6013_);
if (lean_obj_tag(v___x_6074_) == 0)
{
lean_dec_ref_known(v___x_6074_, 1);
v___y_6016_ = v_a_6010_;
v___y_6017_ = v_a_6011_;
v___y_6018_ = v_a_6012_;
v___y_6019_ = v_a_6013_;
goto v___jp_6015_;
}
else
{
lean_object* v_a_6075_; lean_object* v___x_6077_; uint8_t v_isShared_6078_; uint8_t v_isSharedCheck_6082_; 
lean_dec_ref(v_decl_6009_);
lean_dec_ref(v_assignment_6008_);
v_a_6075_ = lean_ctor_get(v___x_6074_, 0);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6074_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6077_ = v___x_6074_;
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_a_6075_);
lean_dec(v___x_6074_);
v___x_6077_ = lean_box(0);
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
v_resetjp_6076_:
{
lean_object* v___x_6080_; 
if (v_isShared_6078_ == 0)
{
v___x_6080_ = v___x_6077_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v_a_6075_);
v___x_6080_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
return v___x_6080_;
}
}
}
}
else
{
lean_object* v_a_6083_; lean_object* v___x_6085_; uint8_t v_isShared_6086_; uint8_t v_isSharedCheck_6090_; 
lean_dec_ref(v_decl_6009_);
lean_dec_ref(v_assignment_6008_);
v_a_6083_ = lean_ctor_get(v___x_6058_, 0);
v_isSharedCheck_6090_ = !lean_is_exclusive(v___x_6058_);
if (v_isSharedCheck_6090_ == 0)
{
v___x_6085_ = v___x_6058_;
v_isShared_6086_ = v_isSharedCheck_6090_;
goto v_resetjp_6084_;
}
else
{
lean_inc(v_a_6083_);
lean_dec(v___x_6058_);
v___x_6085_ = lean_box(0);
v_isShared_6086_ = v_isSharedCheck_6090_;
goto v_resetjp_6084_;
}
v_resetjp_6084_:
{
lean_object* v___x_6088_; 
if (v_isShared_6086_ == 0)
{
v___x_6088_ = v___x_6085_;
goto v_reusejp_6087_;
}
else
{
lean_object* v_reuseFailAlloc_6089_; 
v_reuseFailAlloc_6089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6089_, 0, v_a_6083_);
v___x_6088_ = v_reuseFailAlloc_6089_;
goto v_reusejp_6087_;
}
v_reusejp_6087_:
{
return v___x_6088_;
}
}
}
}
}
v___jp_6015_:
{
lean_object* v_toSignature_6020_; lean_object* v_value_6021_; uint8_t v_recursive_6022_; lean_object* v_inlineAttr_x3f_6023_; lean_object* v___x_6025_; uint8_t v_isShared_6026_; uint8_t v_isSharedCheck_6048_; 
v_toSignature_6020_ = lean_ctor_get(v_decl_6009_, 0);
v_value_6021_ = lean_ctor_get(v_decl_6009_, 1);
v_recursive_6022_ = lean_ctor_get_uint8(v_decl_6009_, sizeof(void*)*3);
v_inlineAttr_x3f_6023_ = lean_ctor_get(v_decl_6009_, 2);
v_isSharedCheck_6048_ = !lean_is_exclusive(v_decl_6009_);
if (v_isSharedCheck_6048_ == 0)
{
v___x_6025_ = v_decl_6009_;
v_isShared_6026_ = v_isSharedCheck_6048_;
goto v_resetjp_6024_;
}
else
{
lean_inc(v_inlineAttr_x3f_6023_);
lean_inc(v_value_6021_);
lean_inc(v_toSignature_6020_);
lean_dec(v_decl_6009_);
v___x_6025_ = lean_box(0);
v_isShared_6026_ = v_isSharedCheck_6048_;
goto v_resetjp_6024_;
}
v_resetjp_6024_:
{
lean_object* v___x_6027_; lean_object* v___x_6028_; 
v___x_6027_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_6027_, 0, v_assignment_6008_);
v___x_6028_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_6027_, v_value_6021_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
if (lean_obj_tag(v___x_6028_) == 0)
{
lean_object* v_a_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6039_; 
v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6039_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6039_ == 0)
{
v___x_6031_ = v___x_6028_;
v_isShared_6032_ = v_isSharedCheck_6039_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_a_6029_);
lean_dec(v___x_6028_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6039_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6034_; 
if (v_isShared_6026_ == 0)
{
lean_ctor_set(v___x_6025_, 1, v_a_6029_);
v___x_6034_ = v___x_6025_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_toSignature_6020_);
lean_ctor_set(v_reuseFailAlloc_6038_, 1, v_a_6029_);
lean_ctor_set(v_reuseFailAlloc_6038_, 2, v_inlineAttr_x3f_6023_);
lean_ctor_set_uint8(v_reuseFailAlloc_6038_, sizeof(void*)*3, v_recursive_6022_);
v___x_6034_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
lean_object* v___x_6036_; 
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 0, v___x_6034_);
v___x_6036_ = v___x_6031_;
goto v_reusejp_6035_;
}
else
{
lean_object* v_reuseFailAlloc_6037_; 
v_reuseFailAlloc_6037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6034_);
v___x_6036_ = v_reuseFailAlloc_6037_;
goto v_reusejp_6035_;
}
v_reusejp_6035_:
{
return v___x_6036_;
}
}
}
}
else
{
lean_object* v_a_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6047_; 
lean_del_object(v___x_6025_);
lean_dec(v_inlineAttr_x3f_6023_);
lean_dec_ref(v_toSignature_6020_);
v_a_6040_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6047_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6047_ == 0)
{
v___x_6042_ = v___x_6028_;
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_a_6040_);
lean_dec(v___x_6028_);
v___x_6042_ = lean_box(0);
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
v_resetjp_6041_:
{
lean_object* v___x_6045_; 
if (v_isShared_6043_ == 0)
{
v___x_6045_ = v___x_6042_;
goto v_reusejp_6044_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_a_6040_);
v___x_6045_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6044_;
}
v_reusejp_6044_:
{
return v___x_6045_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6102_, lean_object* v_decl_6103_, lean_object* v_a_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_, lean_object* v_a_6107_, lean_object* v_a_6108_){
_start:
{
lean_object* v_res_6109_; 
v_res_6109_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6102_, v_decl_6103_, v_a_6104_, v_a_6105_, v_a_6106_, v_a_6107_);
lean_dec(v_a_6107_);
lean_dec_ref(v_a_6106_);
lean_dec(v_a_6105_);
lean_dec_ref(v_a_6104_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6110_, lean_object* v_x_6111_){
_start:
{
lean_object* v___x_6112_; 
v___x_6112_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6110_);
return v___x_6112_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6113_, lean_object* v_x_6114_){
_start:
{
lean_object* v_res_6115_; 
v_res_6115_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6113_, v_x_6114_);
lean_dec(v_x_6114_);
return v_res_6115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6116_, size_t v_i_6117_, lean_object* v_bs_6118_){
_start:
{
uint8_t v___x_6119_; 
v___x_6119_ = lean_usize_dec_lt(v_i_6117_, v_sz_6116_);
if (v___x_6119_ == 0)
{
return v_bs_6118_;
}
else
{
lean_object* v_v_6120_; lean_object* v_toSignature_6121_; lean_object* v_name_6122_; lean_object* v___x_6123_; lean_object* v_bs_x27_6124_; size_t v___x_6125_; size_t v___x_6126_; lean_object* v___x_6127_; 
v_v_6120_ = lean_array_uget_borrowed(v_bs_6118_, v_i_6117_);
v_toSignature_6121_ = lean_ctor_get(v_v_6120_, 0);
v_name_6122_ = lean_ctor_get(v_toSignature_6121_, 0);
lean_inc(v_name_6122_);
v___x_6123_ = lean_unsigned_to_nat(0u);
v_bs_x27_6124_ = lean_array_uset(v_bs_6118_, v_i_6117_, v___x_6123_);
v___x_6125_ = ((size_t)1ULL);
v___x_6126_ = lean_usize_add(v_i_6117_, v___x_6125_);
v___x_6127_ = lean_array_uset(v_bs_x27_6124_, v_i_6117_, v_name_6122_);
v_i_6117_ = v___x_6126_;
v_bs_6118_ = v___x_6127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6129_, lean_object* v_i_6130_, lean_object* v_bs_6131_){
_start:
{
size_t v_sz_boxed_6132_; size_t v_i_boxed_6133_; lean_object* v_res_6134_; 
v_sz_boxed_6132_ = lean_unbox_usize(v_sz_6129_);
lean_dec(v_sz_6129_);
v_i_boxed_6133_ = lean_unbox_usize(v_i_6130_);
lean_dec(v_i_6130_);
v_res_6134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6132_, v_i_boxed_6133_, v_bs_6131_);
return v_res_6134_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6135_, lean_object* v_a_6136_){
_start:
{
if (lean_obj_tag(v_a_6135_) == 0)
{
lean_object* v___x_6137_; 
v___x_6137_ = l_List_reverse___redArg(v_a_6136_);
return v___x_6137_;
}
else
{
lean_object* v_head_6138_; lean_object* v_tail_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6148_; 
v_head_6138_ = lean_ctor_get(v_a_6135_, 0);
v_tail_6139_ = lean_ctor_get(v_a_6135_, 1);
v_isSharedCheck_6148_ = !lean_is_exclusive(v_a_6135_);
if (v_isSharedCheck_6148_ == 0)
{
v___x_6141_ = v_a_6135_;
v_isShared_6142_ = v_isSharedCheck_6148_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_tail_6139_);
lean_inc(v_head_6138_);
lean_dec(v_a_6135_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6148_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6143_; lean_object* v___x_6145_; 
v___x_6143_ = l_Lean_MessageData_ofName(v_head_6138_);
if (v_isShared_6142_ == 0)
{
lean_ctor_set(v___x_6141_, 1, v_a_6136_);
lean_ctor_set(v___x_6141_, 0, v___x_6143_);
v___x_6145_ = v___x_6141_;
goto v_reusejp_6144_;
}
else
{
lean_object* v_reuseFailAlloc_6147_; 
v_reuseFailAlloc_6147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6147_, 0, v___x_6143_);
lean_ctor_set(v_reuseFailAlloc_6147_, 1, v_a_6136_);
v___x_6145_ = v_reuseFailAlloc_6147_;
goto v_reusejp_6144_;
}
v_reusejp_6144_:
{
v_a_6135_ = v_tail_6139_;
v_a_6136_ = v___x_6145_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6150_; lean_object* v___x_6151_; 
v___x_6150_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6151_ = l_Lean_stringToMessageData(v___x_6150_);
return v___x_6151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6152_, lean_object* v_x_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_){
_start:
{
lean_object* v___x_6161_; size_t v_sz_6162_; size_t v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; 
v___x_6161_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6162_ = lean_array_size(v___y_6152_);
v___x_6163_ = ((size_t)0ULL);
v___x_6164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6162_, v___x_6163_, v___y_6152_);
v___x_6165_ = lean_array_to_list(v___x_6164_);
v___x_6166_ = lean_box(0);
v___x_6167_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6165_, v___x_6166_);
v___x_6168_ = l_Lean_MessageData_ofList(v___x_6167_);
v___x_6169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6161_);
lean_ctor_set(v___x_6169_, 1, v___x_6168_);
v___x_6170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
return v___x_6170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6171_, lean_object* v_x_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_){
_start:
{
lean_object* v_res_6180_; 
v_res_6180_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6171_, v_x_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_);
lean_dec(v___y_6178_);
lean_dec_ref(v___y_6177_);
lean_dec(v___y_6176_);
lean_dec_ref(v___y_6175_);
lean_dec(v___y_6174_);
lean_dec_ref(v___y_6173_);
lean_dec_ref(v_x_6172_);
return v_res_6180_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6181_; lean_object* v___x_6182_; 
v___x_6181_ = 0;
v___x_6182_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6181_);
return v___x_6182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6183_, lean_object* v_n_6184_, lean_object* v_j_6185_, lean_object* v_a_6186_){
_start:
{
lean_object* v_zero_6187_; uint8_t v_isZero_6188_; 
v_zero_6187_ = lean_unsigned_to_nat(0u);
v_isZero_6188_ = lean_nat_dec_eq(v_j_6185_, v_zero_6187_);
if (v_isZero_6188_ == 1)
{
lean_dec(v_j_6185_);
return v_a_6186_;
}
else
{
lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v_toSignature_6192_; uint8_t v_safe_6193_; lean_object* v_one_6194_; lean_object* v_n_6195_; 
v___x_6189_ = lean_nat_sub(v_n_6184_, v_j_6185_);
v___x_6190_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6191_ = lean_array_get_borrowed(v___x_6190_, v___y_6183_, v___x_6189_);
lean_dec(v___x_6189_);
v_toSignature_6192_ = lean_ctor_get(v___x_6191_, 0);
v_safe_6193_ = lean_ctor_get_uint8(v_toSignature_6192_, sizeof(void*)*4);
v_one_6194_ = lean_unsigned_to_nat(1u);
v_n_6195_ = lean_nat_sub(v_j_6185_, v_one_6194_);
lean_dec(v_j_6185_);
if (v_safe_6193_ == 0)
{
lean_object* v___x_6196_; lean_object* v___x_6197_; 
v___x_6196_ = lean_box(1);
v___x_6197_ = lean_array_push(v_a_6186_, v___x_6196_);
v_j_6185_ = v_n_6195_;
v_a_6186_ = v___x_6197_;
goto _start;
}
else
{
lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6199_ = lean_box(0);
v___x_6200_ = lean_array_push(v_a_6186_, v___x_6199_);
v_j_6185_ = v_n_6195_;
v_a_6186_ = v___x_6200_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6202_, lean_object* v_n_6203_, lean_object* v_j_6204_, lean_object* v_a_6205_){
_start:
{
lean_object* v_res_6206_; 
v_res_6206_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6202_, v_n_6203_, v_j_6204_, v_a_6205_);
lean_dec(v_n_6203_);
lean_dec_ref(v___y_6202_);
return v_res_6206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6207_, size_t v_sz_6208_, size_t v_i_6209_, lean_object* v_bs_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_){
_start:
{
uint8_t v___x_6216_; 
v___x_6216_ = lean_usize_dec_lt(v_i_6209_, v_sz_6208_);
if (v___x_6216_ == 0)
{
lean_object* v___x_6217_; 
v___x_6217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6217_, 0, v_bs_6210_);
return v___x_6217_;
}
else
{
lean_object* v_v_6218_; lean_object* v_toSignature_6219_; uint8_t v_safe_6220_; lean_object* v___x_6221_; lean_object* v_bs_x27_6222_; lean_object* v_a_6224_; 
v_v_6218_ = lean_array_uget(v_bs_6210_, v_i_6209_);
v_toSignature_6219_ = lean_ctor_get(v_v_6218_, 0);
v_safe_6220_ = lean_ctor_get_uint8(v_toSignature_6219_, sizeof(void*)*4);
v___x_6221_ = lean_unsigned_to_nat(0u);
v_bs_x27_6222_ = lean_array_uset(v_bs_6210_, v_i_6209_, v___x_6221_);
if (v_safe_6220_ == 0)
{
v_a_6224_ = v_v_6218_;
goto v___jp_6223_;
}
else
{
lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; 
v___x_6229_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6230_ = lean_usize_to_nat(v_i_6209_);
v___x_6231_ = lean_array_get_borrowed(v___x_6229_, v___x_6207_, v___x_6230_);
lean_dec(v___x_6230_);
lean_inc(v___x_6231_);
v___x_6232_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6231_, v_v_6218_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_);
if (lean_obj_tag(v___x_6232_) == 0)
{
lean_object* v_a_6233_; 
v_a_6233_ = lean_ctor_get(v___x_6232_, 0);
lean_inc(v_a_6233_);
lean_dec_ref_known(v___x_6232_, 1);
v_a_6224_ = v_a_6233_;
goto v___jp_6223_;
}
else
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6241_; 
lean_dec_ref(v_bs_x27_6222_);
v_a_6234_ = lean_ctor_get(v___x_6232_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v___x_6232_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6236_ = v___x_6232_;
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v___x_6232_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
}
}
}
}
v___jp_6223_:
{
size_t v___x_6225_; size_t v___x_6226_; lean_object* v___x_6227_; 
v___x_6225_ = ((size_t)1ULL);
v___x_6226_ = lean_usize_add(v_i_6209_, v___x_6225_);
v___x_6227_ = lean_array_uset(v_bs_x27_6222_, v_i_6209_, v_a_6224_);
v_i_6209_ = v___x_6226_;
v_bs_6210_ = v___x_6227_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6242_, lean_object* v_sz_6243_, lean_object* v_i_6244_, lean_object* v_bs_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_){
_start:
{
size_t v_sz_boxed_6251_; size_t v_i_boxed_6252_; lean_object* v_res_6253_; 
v_sz_boxed_6251_ = lean_unbox_usize(v_sz_6243_);
lean_dec(v_sz_6243_);
v_i_boxed_6252_ = lean_unbox_usize(v_i_6244_);
lean_dec(v_i_6244_);
v_res_6253_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6242_, v_sz_boxed_6251_, v_i_boxed_6252_, v_bs_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_);
lean_dec(v___y_6249_);
lean_dec_ref(v___y_6248_);
lean_dec(v___y_6247_);
lean_dec_ref(v___y_6246_);
lean_dec_ref(v___x_6242_);
return v_res_6253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6256_, lean_object* v_pivot_6257_, lean_object* v_as_6258_, lean_object* v_i_6259_, lean_object* v_k_6260_){
_start:
{
uint8_t v___x_6261_; 
v___x_6261_ = lean_nat_dec_lt(v_k_6260_, v_hi_6256_);
if (v___x_6261_ == 0)
{
lean_object* v___x_6262_; lean_object* v___x_6263_; 
lean_dec(v_k_6260_);
lean_dec_ref(v_pivot_6257_);
v___x_6262_ = lean_array_fswap(v_as_6258_, v_i_6259_, v_hi_6256_);
v___x_6263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6263_, 0, v_i_6259_);
lean_ctor_set(v___x_6263_, 1, v___x_6262_);
return v___x_6263_;
}
else
{
lean_object* v___x_6264_; lean_object* v_toSignature_6265_; lean_object* v_toSignature_6266_; lean_object* v_name_6267_; lean_object* v_name_6268_; uint8_t v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; uint8_t v___x_6279_; 
v___x_6264_ = lean_array_fget_borrowed(v_as_6258_, v_k_6260_);
v_toSignature_6265_ = lean_ctor_get(v___x_6264_, 0);
v_toSignature_6266_ = lean_ctor_get(v_pivot_6257_, 0);
v_name_6267_ = lean_ctor_get(v_toSignature_6265_, 0);
v_name_6268_ = lean_ctor_get(v_toSignature_6266_, 0);
v___x_6269_ = 0;
v___x_6270_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6269_, v___x_6264_);
v___x_6271_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6272_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6273_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6267_);
v___x_6274_ = l_Lean_Name_toString(v_name_6267_, v___x_6261_);
v___x_6275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6275_, 0, v___x_6270_);
lean_ctor_set(v___x_6275_, 1, v___x_6274_);
v___x_6276_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6269_, v_pivot_6257_);
lean_inc(v_name_6268_);
v___x_6277_ = l_Lean_Name_toString(v_name_6268_, v___x_6261_);
v___x_6278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6278_, 0, v___x_6276_);
lean_ctor_set(v___x_6278_, 1, v___x_6277_);
v___x_6279_ = l_Prod_lexLtDec___redArg(v___x_6271_, v___x_6272_, v___x_6273_, v___x_6275_, v___x_6278_);
if (v___x_6279_ == 0)
{
lean_object* v___x_6280_; lean_object* v___x_6281_; 
v___x_6280_ = lean_unsigned_to_nat(1u);
v___x_6281_ = lean_nat_add(v_k_6260_, v___x_6280_);
lean_dec(v_k_6260_);
v_k_6260_ = v___x_6281_;
goto _start;
}
else
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; 
v___x_6283_ = lean_array_fswap(v_as_6258_, v_i_6259_, v_k_6260_);
v___x_6284_ = lean_unsigned_to_nat(1u);
v___x_6285_ = lean_nat_add(v_i_6259_, v___x_6284_);
lean_dec(v_i_6259_);
v___x_6286_ = lean_nat_add(v_k_6260_, v___x_6284_);
lean_dec(v_k_6260_);
v_as_6258_ = v___x_6283_;
v_i_6259_ = v___x_6285_;
v_k_6260_ = v___x_6286_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6288_, lean_object* v_pivot_6289_, lean_object* v_as_6290_, lean_object* v_i_6291_, lean_object* v_k_6292_){
_start:
{
lean_object* v_res_6293_; 
v_res_6293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6288_, v_pivot_6289_, v_as_6290_, v_i_6291_, v_k_6292_);
lean_dec(v_hi_6288_);
return v_res_6293_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6294_, lean_object* v_l_6295_, lean_object* v_r_6296_){
_start:
{
lean_object* v_toSignature_6297_; lean_object* v_toSignature_6298_; lean_object* v_name_6299_; lean_object* v_name_6300_; uint8_t v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; uint8_t v___x_6311_; 
v_toSignature_6297_ = lean_ctor_get(v_l_6295_, 0);
v_toSignature_6298_ = lean_ctor_get(v_r_6296_, 0);
v_name_6299_ = lean_ctor_get(v_toSignature_6297_, 0);
lean_inc(v_name_6299_);
v_name_6300_ = lean_ctor_get(v_toSignature_6298_, 0);
lean_inc(v_name_6300_);
v___x_6301_ = 0;
v___x_6302_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6301_, v_l_6295_);
lean_dec_ref(v_l_6295_);
v___x_6303_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6304_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6305_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6306_ = l_Lean_Name_toString(v_name_6299_, v___x_6294_);
v___x_6307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6307_, 0, v___x_6302_);
lean_ctor_set(v___x_6307_, 1, v___x_6306_);
v___x_6308_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6301_, v_r_6296_);
lean_dec_ref(v_r_6296_);
v___x_6309_ = l_Lean_Name_toString(v_name_6300_, v___x_6294_);
v___x_6310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6310_, 0, v___x_6308_);
lean_ctor_set(v___x_6310_, 1, v___x_6309_);
v___x_6311_ = l_Prod_lexLtDec___redArg(v___x_6303_, v___x_6304_, v___x_6305_, v___x_6307_, v___x_6310_);
return v___x_6311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6312_, lean_object* v_l_6313_, lean_object* v_r_6314_){
_start:
{
uint8_t v___x_13176__boxed_6315_; uint8_t v_res_6316_; lean_object* v_r_6317_; 
v___x_13176__boxed_6315_ = lean_unbox(v___x_6312_);
v_res_6316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13176__boxed_6315_, v_l_6313_, v_r_6314_);
v_r_6317_ = lean_box(v_res_6316_);
return v_r_6317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6318_, lean_object* v_as_6319_, lean_object* v_lo_6320_, lean_object* v_hi_6321_){
_start:
{
lean_object* v___y_6323_; uint8_t v___x_6333_; 
v___x_6333_ = lean_nat_dec_lt(v_lo_6320_, v_hi_6321_);
if (v___x_6333_ == 0)
{
lean_dec(v_lo_6320_);
return v_as_6319_;
}
else
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v_mid_6336_; lean_object* v___y_6338_; lean_object* v___y_6344_; lean_object* v___x_6349_; lean_object* v___x_6350_; uint8_t v___x_6351_; 
v___x_6334_ = lean_nat_add(v_lo_6320_, v_hi_6321_);
v___x_6335_ = lean_unsigned_to_nat(1u);
v_mid_6336_ = lean_nat_shiftr(v___x_6334_, v___x_6335_);
lean_dec(v___x_6334_);
v___x_6349_ = lean_array_fget_borrowed(v_as_6319_, v_mid_6336_);
v___x_6350_ = lean_array_fget_borrowed(v_as_6319_, v_lo_6320_);
lean_inc(v___x_6350_);
lean_inc(v___x_6349_);
v___x_6351_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6333_, v___x_6349_, v___x_6350_);
if (v___x_6351_ == 0)
{
v___y_6344_ = v_as_6319_;
goto v___jp_6343_;
}
else
{
lean_object* v___x_6352_; 
v___x_6352_ = lean_array_fswap(v_as_6319_, v_lo_6320_, v_mid_6336_);
v___y_6344_ = v___x_6352_;
goto v___jp_6343_;
}
v___jp_6337_:
{
lean_object* v___x_6339_; lean_object* v___x_6340_; uint8_t v___x_6341_; 
v___x_6339_ = lean_array_fget_borrowed(v___y_6338_, v_mid_6336_);
v___x_6340_ = lean_array_fget_borrowed(v___y_6338_, v_hi_6321_);
lean_inc(v___x_6340_);
lean_inc(v___x_6339_);
v___x_6341_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6333_, v___x_6339_, v___x_6340_);
if (v___x_6341_ == 0)
{
lean_dec(v_mid_6336_);
v___y_6323_ = v___y_6338_;
goto v___jp_6322_;
}
else
{
lean_object* v___x_6342_; 
v___x_6342_ = lean_array_fswap(v___y_6338_, v_mid_6336_, v_hi_6321_);
lean_dec(v_mid_6336_);
v___y_6323_ = v___x_6342_;
goto v___jp_6322_;
}
}
v___jp_6343_:
{
lean_object* v___x_6345_; lean_object* v___x_6346_; uint8_t v___x_6347_; 
v___x_6345_ = lean_array_fget_borrowed(v___y_6344_, v_hi_6321_);
v___x_6346_ = lean_array_fget_borrowed(v___y_6344_, v_lo_6320_);
lean_inc(v___x_6346_);
lean_inc(v___x_6345_);
v___x_6347_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6333_, v___x_6345_, v___x_6346_);
if (v___x_6347_ == 0)
{
v___y_6338_ = v___y_6344_;
goto v___jp_6337_;
}
else
{
lean_object* v___x_6348_; 
v___x_6348_ = lean_array_fswap(v___y_6344_, v_lo_6320_, v_hi_6321_);
v___y_6338_ = v___x_6348_;
goto v___jp_6337_;
}
}
}
v___jp_6322_:
{
lean_object* v_pivot_6324_; lean_object* v___x_6325_; lean_object* v_fst_6326_; lean_object* v_snd_6327_; uint8_t v___x_6328_; 
v_pivot_6324_ = lean_array_fget(v___y_6323_, v_hi_6321_);
lean_inc_n(v_lo_6320_, 2);
v___x_6325_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6321_, v_pivot_6324_, v___y_6323_, v_lo_6320_, v_lo_6320_);
v_fst_6326_ = lean_ctor_get(v___x_6325_, 0);
lean_inc(v_fst_6326_);
v_snd_6327_ = lean_ctor_get(v___x_6325_, 1);
lean_inc(v_snd_6327_);
lean_dec_ref(v___x_6325_);
v___x_6328_ = lean_nat_dec_le(v_hi_6321_, v_fst_6326_);
if (v___x_6328_ == 0)
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6318_, v_snd_6327_, v_lo_6320_, v_fst_6326_);
v___x_6330_ = lean_unsigned_to_nat(1u);
v___x_6331_ = lean_nat_add(v_fst_6326_, v___x_6330_);
lean_dec(v_fst_6326_);
v_as_6319_ = v___x_6329_;
v_lo_6320_ = v___x_6331_;
goto _start;
}
else
{
lean_dec(v_fst_6326_);
lean_dec(v_lo_6320_);
return v_snd_6327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6353_, lean_object* v_as_6354_, lean_object* v_lo_6355_, lean_object* v_hi_6356_){
_start:
{
lean_object* v_res_6357_; 
v_res_6357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6353_, v_as_6354_, v_lo_6355_, v_hi_6356_);
lean_dec(v_hi_6356_);
lean_dec(v_n_6353_);
return v_res_6357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6358_, lean_object* v___x_6359_, lean_object* v_n_6360_, lean_object* v_j_6361_, lean_object* v_a_6362_){
_start:
{
lean_object* v_zero_6363_; uint8_t v_isZero_6364_; 
v_zero_6363_ = lean_unsigned_to_nat(0u);
v_isZero_6364_ = lean_nat_dec_eq(v_j_6361_, v_zero_6363_);
if (v_isZero_6364_ == 1)
{
lean_dec(v_j_6361_);
return v_a_6362_;
}
else
{
lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v_toSignature_6367_; lean_object* v_name_6368_; lean_object* v___x_6369_; lean_object* v_one_6370_; lean_object* v_n_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6365_ = lean_nat_sub(v_n_6360_, v_j_6361_);
v___x_6366_ = lean_array_fget_borrowed(v___y_6358_, v___x_6365_);
v_toSignature_6367_ = lean_ctor_get(v___x_6366_, 0);
v_name_6368_ = lean_ctor_get(v_toSignature_6367_, 0);
v___x_6369_ = lean_box(0);
v_one_6370_ = lean_unsigned_to_nat(1u);
v_n_6371_ = lean_nat_sub(v_j_6361_, v_one_6370_);
lean_dec(v_j_6361_);
v___x_6372_ = lean_array_get_borrowed(v___x_6369_, v___x_6359_, v___x_6365_);
lean_dec(v___x_6365_);
lean_inc(v___x_6372_);
lean_inc(v_name_6368_);
v___x_6373_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6362_, v_name_6368_, v___x_6372_);
v_j_6361_ = v_n_6371_;
v_a_6362_ = v___x_6373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6375_, lean_object* v___x_6376_, lean_object* v_n_6377_, lean_object* v_j_6378_, lean_object* v_a_6379_){
_start:
{
lean_object* v_res_6380_; 
v_res_6380_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6375_, v___x_6376_, v_n_6377_, v_j_6378_, v_a_6379_);
lean_dec(v_n_6377_);
lean_dec_ref(v___x_6376_);
lean_dec_ref(v___y_6375_);
return v_res_6380_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6381_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6382_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6383_, 0, v___x_6382_);
return v___x_6383_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; 
v___x_6384_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6385_, 0, v___x_6384_);
lean_ctor_set(v___x_6385_, 1, v___x_6384_);
return v___x_6385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_){
_start:
{
lean_object* v___y_6395_; size_t v___y_6396_; lean_object* v___y_6397_; lean_object* v___y_6398_; size_t v___y_6399_; lean_object* v___y_6400_; uint8_t v___y_6434_; lean_object* v___y_6435_; lean_object* v___y_6436_; lean_object* v___y_6437_; lean_object* v___y_6438_; uint8_t v___y_6439_; lean_object* v___y_6440_; lean_object* v___y_6441_; lean_object* v___y_6442_; size_t v___y_6443_; lean_object* v___y_6444_; size_t v___y_6445_; lean_object* v___y_6446_; lean_object* v___y_6447_; lean_object* v_a_6448_; uint8_t v___y_6458_; lean_object* v___y_6459_; lean_object* v___y_6460_; lean_object* v___y_6461_; lean_object* v___y_6462_; uint8_t v___y_6463_; lean_object* v___y_6464_; lean_object* v___y_6465_; size_t v___y_6466_; lean_object* v___y_6467_; size_t v___y_6468_; lean_object* v___y_6469_; lean_object* v___y_6470_; lean_object* v___y_6471_; lean_object* v_a_6472_; lean_object* v___x_6484_; uint8_t v___y_6486_; lean_object* v___y_6487_; lean_object* v___y_6488_; lean_object* v___y_6489_; lean_object* v___y_6490_; uint8_t v___y_6491_; lean_object* v___y_6492_; lean_object* v___y_6493_; size_t v___y_6494_; size_t v___y_6495_; lean_object* v___y_6496_; lean_object* v___y_6497_; lean_object* v___y_6539_; lean_object* v___x_6561_; lean_object* v___y_6563_; lean_object* v___y_6564_; uint8_t v___x_6566_; 
v___x_6484_ = lean_unsigned_to_nat(0u);
v___x_6561_ = lean_array_get_size(v_decls_6388_);
v___x_6566_ = lean_nat_dec_eq(v___x_6561_, v___x_6484_);
if (v___x_6566_ == 0)
{
lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___y_6570_; uint8_t v___x_6572_; 
v___x_6567_ = lean_unsigned_to_nat(1u);
v___x_6568_ = lean_nat_sub(v___x_6561_, v___x_6567_);
v___x_6572_ = lean_nat_dec_le(v___x_6484_, v___x_6568_);
if (v___x_6572_ == 0)
{
lean_inc(v___x_6568_);
v___y_6570_ = v___x_6568_;
goto v___jp_6569_;
}
else
{
v___y_6570_ = v___x_6484_;
goto v___jp_6569_;
}
v___jp_6569_:
{
uint8_t v___x_6571_; 
v___x_6571_ = lean_nat_dec_le(v___y_6570_, v___x_6568_);
if (v___x_6571_ == 0)
{
lean_dec(v___x_6568_);
lean_inc(v___y_6570_);
v___y_6563_ = v___y_6570_;
v___y_6564_ = v___y_6570_;
goto v___jp_6562_;
}
else
{
v___y_6563_ = v___y_6570_;
v___y_6564_ = v___x_6568_;
goto v___jp_6562_;
}
}
}
else
{
v___y_6539_ = v_decls_6388_;
goto v___jp_6538_;
}
v___jp_6394_:
{
if (lean_obj_tag(v___y_6400_) == 0)
{
lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v_assignments_6403_; lean_object* v_funVals_6404_; lean_object* v_env_6405_; lean_object* v_nextMacroScope_6406_; lean_object* v_ngen_6407_; lean_object* v_auxDeclNGen_6408_; lean_object* v_traceState_6409_; lean_object* v_messages_6410_; lean_object* v_infoState_6411_; lean_object* v_snapshotTasks_6412_; lean_object* v___x_6414_; uint8_t v_isShared_6415_; uint8_t v_isSharedCheck_6423_; 
lean_dec_ref_known(v___y_6400_, 1);
v___x_6401_ = lean_st_ref_get(v___y_6398_);
lean_dec(v___y_6398_);
v___x_6402_ = lean_st_ref_take(v_a_6392_);
v_assignments_6403_ = lean_ctor_get(v___x_6401_, 0);
lean_inc_ref(v_assignments_6403_);
v_funVals_6404_ = lean_ctor_get(v___x_6401_, 1);
lean_inc_ref(v_funVals_6404_);
lean_dec(v___x_6401_);
v_env_6405_ = lean_ctor_get(v___x_6402_, 0);
v_nextMacroScope_6406_ = lean_ctor_get(v___x_6402_, 1);
v_ngen_6407_ = lean_ctor_get(v___x_6402_, 2);
v_auxDeclNGen_6408_ = lean_ctor_get(v___x_6402_, 3);
v_traceState_6409_ = lean_ctor_get(v___x_6402_, 4);
v_messages_6410_ = lean_ctor_get(v___x_6402_, 6);
v_infoState_6411_ = lean_ctor_get(v___x_6402_, 7);
v_snapshotTasks_6412_ = lean_ctor_get(v___x_6402_, 8);
v_isSharedCheck_6423_ = !lean_is_exclusive(v___x_6402_);
if (v_isSharedCheck_6423_ == 0)
{
lean_object* v_unused_6424_; 
v_unused_6424_ = lean_ctor_get(v___x_6402_, 5);
lean_dec(v_unused_6424_);
v___x_6414_ = v___x_6402_;
v_isShared_6415_ = v_isSharedCheck_6423_;
goto v_resetjp_6413_;
}
else
{
lean_inc(v_snapshotTasks_6412_);
lean_inc(v_infoState_6411_);
lean_inc(v_messages_6410_);
lean_inc(v_traceState_6409_);
lean_inc(v_auxDeclNGen_6408_);
lean_inc(v_ngen_6407_);
lean_inc(v_nextMacroScope_6406_);
lean_inc(v_env_6405_);
lean_dec(v___x_6402_);
v___x_6414_ = lean_box(0);
v_isShared_6415_ = v_isSharedCheck_6423_;
goto v_resetjp_6413_;
}
v_resetjp_6413_:
{
lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6419_; 
lean_inc(v___y_6397_);
v___x_6416_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6395_, v_funVals_6404_, v___y_6397_, v___y_6397_, v_env_6405_);
lean_dec(v___y_6397_);
lean_dec_ref(v_funVals_6404_);
v___x_6417_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6415_ == 0)
{
lean_ctor_set(v___x_6414_, 5, v___x_6417_);
lean_ctor_set(v___x_6414_, 0, v___x_6416_);
v___x_6419_ = v___x_6414_;
goto v_reusejp_6418_;
}
else
{
lean_object* v_reuseFailAlloc_6422_; 
v_reuseFailAlloc_6422_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6422_, 0, v___x_6416_);
lean_ctor_set(v_reuseFailAlloc_6422_, 1, v_nextMacroScope_6406_);
lean_ctor_set(v_reuseFailAlloc_6422_, 2, v_ngen_6407_);
lean_ctor_set(v_reuseFailAlloc_6422_, 3, v_auxDeclNGen_6408_);
lean_ctor_set(v_reuseFailAlloc_6422_, 4, v_traceState_6409_);
lean_ctor_set(v_reuseFailAlloc_6422_, 5, v___x_6417_);
lean_ctor_set(v_reuseFailAlloc_6422_, 6, v_messages_6410_);
lean_ctor_set(v_reuseFailAlloc_6422_, 7, v_infoState_6411_);
lean_ctor_set(v_reuseFailAlloc_6422_, 8, v_snapshotTasks_6412_);
v___x_6419_ = v_reuseFailAlloc_6422_;
goto v_reusejp_6418_;
}
v_reusejp_6418_:
{
lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6420_ = lean_st_ref_put(v_a_6392_, v___x_6419_);
v___x_6421_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6403_, v___y_6399_, v___y_6396_, v___y_6395_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
lean_dec_ref(v_assignments_6403_);
return v___x_6421_;
}
}
}
else
{
lean_object* v_a_6425_; lean_object* v___x_6427_; uint8_t v_isShared_6428_; uint8_t v_isSharedCheck_6432_; 
lean_dec(v___y_6398_);
lean_dec(v___y_6397_);
lean_dec_ref(v___y_6395_);
v_a_6425_ = lean_ctor_get(v___y_6400_, 0);
v_isSharedCheck_6432_ = !lean_is_exclusive(v___y_6400_);
if (v_isSharedCheck_6432_ == 0)
{
v___x_6427_ = v___y_6400_;
v_isShared_6428_ = v_isSharedCheck_6432_;
goto v_resetjp_6426_;
}
else
{
lean_inc(v_a_6425_);
lean_dec(v___y_6400_);
v___x_6427_ = lean_box(0);
v_isShared_6428_ = v_isSharedCheck_6432_;
goto v_resetjp_6426_;
}
v_resetjp_6426_:
{
lean_object* v___x_6430_; 
if (v_isShared_6428_ == 0)
{
v___x_6430_ = v___x_6427_;
goto v_reusejp_6429_;
}
else
{
lean_object* v_reuseFailAlloc_6431_; 
v_reuseFailAlloc_6431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6431_, 0, v_a_6425_);
v___x_6430_ = v_reuseFailAlloc_6431_;
goto v_reusejp_6429_;
}
v_reusejp_6429_:
{
return v___x_6430_;
}
}
}
}
v___jp_6433_:
{
lean_object* v___x_6449_; double v___x_6450_; double v___x_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6449_ = lean_io_get_num_heartbeats();
v___x_6450_ = lean_float_of_nat(v___y_6440_);
v___x_6451_ = lean_float_of_nat(v___x_6449_);
v___x_6452_ = lean_box_float(v___x_6450_);
v___x_6453_ = lean_box_float(v___x_6451_);
v___x_6454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6454_, 0, v___x_6452_);
lean_ctor_set(v___x_6454_, 1, v___x_6453_);
v___x_6455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6455_, 0, v_a_6448_);
lean_ctor_set(v___x_6455_, 1, v___x_6454_);
lean_inc_ref(v___y_6441_);
lean_inc(v___y_6436_);
v___x_6456_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6436_, v___y_6439_, v___y_6441_, v___y_6438_, v___y_6434_, v___y_6444_, v___y_6447_, v___x_6455_, v___y_6446_, v___y_6442_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
lean_dec_ref(v___y_6446_);
v___y_6395_ = v___y_6435_;
v___y_6396_ = v___y_6443_;
v___y_6397_ = v___y_6437_;
v___y_6398_ = v___y_6442_;
v___y_6399_ = v___y_6445_;
v___y_6400_ = v___x_6456_;
goto v___jp_6394_;
}
v___jp_6457_:
{
lean_object* v___x_6473_; double v___x_6474_; double v___x_6475_; double v___x_6476_; double v___x_6477_; double v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; 
v___x_6473_ = lean_io_mono_nanos_now();
v___x_6474_ = lean_float_of_nat(v___y_6470_);
v___x_6475_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6476_ = lean_float_div(v___x_6474_, v___x_6475_);
v___x_6477_ = lean_float_of_nat(v___x_6473_);
v___x_6478_ = lean_float_div(v___x_6477_, v___x_6475_);
v___x_6479_ = lean_box_float(v___x_6476_);
v___x_6480_ = lean_box_float(v___x_6478_);
v___x_6481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6481_, 0, v___x_6479_);
lean_ctor_set(v___x_6481_, 1, v___x_6480_);
v___x_6482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6482_, 0, v_a_6472_);
lean_ctor_set(v___x_6482_, 1, v___x_6481_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6460_);
v___x_6483_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6460_, v___y_6463_, v___y_6464_, v___y_6462_, v___y_6458_, v___y_6467_, v___y_6471_, v___x_6482_, v___y_6469_, v___y_6465_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
lean_dec_ref(v___y_6469_);
v___y_6395_ = v___y_6459_;
v___y_6396_ = v___y_6466_;
v___y_6397_ = v___y_6461_;
v___y_6398_ = v___y_6465_;
v___y_6399_ = v___y_6468_;
v___y_6400_ = v___x_6483_;
goto v___jp_6394_;
}
v___jp_6485_:
{
lean_object* v___x_6498_; lean_object* v_a_6499_; lean_object* v___x_6500_; uint8_t v___x_6501_; 
v___x_6498_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6392_);
v_a_6499_ = lean_ctor_get(v___x_6498_, 0);
lean_inc(v_a_6499_);
lean_dec_ref(v___x_6498_);
v___x_6500_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6501_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6490_, v___x_6500_);
if (v___x_6501_ == 0)
{
lean_object* v___x_6502_; lean_object* v___x_6503_; 
v___x_6502_ = lean_io_mono_nanos_now();
v___x_6503_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6484_, v___y_6496_, v___y_6493_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
if (lean_obj_tag(v___x_6503_) == 0)
{
lean_object* v_a_6504_; lean_object* v___x_6506_; uint8_t v_isShared_6507_; uint8_t v_isSharedCheck_6511_; 
v_a_6504_ = lean_ctor_get(v___x_6503_, 0);
v_isSharedCheck_6511_ = !lean_is_exclusive(v___x_6503_);
if (v_isSharedCheck_6511_ == 0)
{
v___x_6506_ = v___x_6503_;
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
else
{
lean_inc(v_a_6504_);
lean_dec(v___x_6503_);
v___x_6506_ = lean_box(0);
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
v_resetjp_6505_:
{
lean_object* v___x_6509_; 
if (v_isShared_6507_ == 0)
{
lean_ctor_set_tag(v___x_6506_, 1);
v___x_6509_ = v___x_6506_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_a_6504_);
v___x_6509_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
v___y_6458_ = v___y_6486_;
v___y_6459_ = v___y_6487_;
v___y_6460_ = v___y_6488_;
v___y_6461_ = v___y_6489_;
v___y_6462_ = v___y_6490_;
v___y_6463_ = v___y_6491_;
v___y_6464_ = v___y_6492_;
v___y_6465_ = v___y_6493_;
v___y_6466_ = v___y_6494_;
v___y_6467_ = v_a_6499_;
v___y_6468_ = v___y_6495_;
v___y_6469_ = v___y_6496_;
v___y_6470_ = v___x_6502_;
v___y_6471_ = v___y_6497_;
v_a_6472_ = v___x_6509_;
goto v___jp_6457_;
}
}
}
else
{
lean_object* v_a_6512_; lean_object* v___x_6514_; uint8_t v_isShared_6515_; uint8_t v_isSharedCheck_6519_; 
v_a_6512_ = lean_ctor_get(v___x_6503_, 0);
v_isSharedCheck_6519_ = !lean_is_exclusive(v___x_6503_);
if (v_isSharedCheck_6519_ == 0)
{
v___x_6514_ = v___x_6503_;
v_isShared_6515_ = v_isSharedCheck_6519_;
goto v_resetjp_6513_;
}
else
{
lean_inc(v_a_6512_);
lean_dec(v___x_6503_);
v___x_6514_ = lean_box(0);
v_isShared_6515_ = v_isSharedCheck_6519_;
goto v_resetjp_6513_;
}
v_resetjp_6513_:
{
lean_object* v___x_6517_; 
if (v_isShared_6515_ == 0)
{
lean_ctor_set_tag(v___x_6514_, 0);
v___x_6517_ = v___x_6514_;
goto v_reusejp_6516_;
}
else
{
lean_object* v_reuseFailAlloc_6518_; 
v_reuseFailAlloc_6518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6518_, 0, v_a_6512_);
v___x_6517_ = v_reuseFailAlloc_6518_;
goto v_reusejp_6516_;
}
v_reusejp_6516_:
{
v___y_6458_ = v___y_6486_;
v___y_6459_ = v___y_6487_;
v___y_6460_ = v___y_6488_;
v___y_6461_ = v___y_6489_;
v___y_6462_ = v___y_6490_;
v___y_6463_ = v___y_6491_;
v___y_6464_ = v___y_6492_;
v___y_6465_ = v___y_6493_;
v___y_6466_ = v___y_6494_;
v___y_6467_ = v_a_6499_;
v___y_6468_ = v___y_6495_;
v___y_6469_ = v___y_6496_;
v___y_6470_ = v___x_6502_;
v___y_6471_ = v___y_6497_;
v_a_6472_ = v___x_6517_;
goto v___jp_6457_;
}
}
}
}
else
{
lean_object* v___x_6520_; lean_object* v___x_6521_; 
v___x_6520_ = lean_io_get_num_heartbeats();
v___x_6521_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6484_, v___y_6496_, v___y_6493_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
if (lean_obj_tag(v___x_6521_) == 0)
{
lean_object* v_a_6522_; lean_object* v___x_6524_; uint8_t v_isShared_6525_; uint8_t v_isSharedCheck_6529_; 
v_a_6522_ = lean_ctor_get(v___x_6521_, 0);
v_isSharedCheck_6529_ = !lean_is_exclusive(v___x_6521_);
if (v_isSharedCheck_6529_ == 0)
{
v___x_6524_ = v___x_6521_;
v_isShared_6525_ = v_isSharedCheck_6529_;
goto v_resetjp_6523_;
}
else
{
lean_inc(v_a_6522_);
lean_dec(v___x_6521_);
v___x_6524_ = lean_box(0);
v_isShared_6525_ = v_isSharedCheck_6529_;
goto v_resetjp_6523_;
}
v_resetjp_6523_:
{
lean_object* v___x_6527_; 
if (v_isShared_6525_ == 0)
{
lean_ctor_set_tag(v___x_6524_, 1);
v___x_6527_ = v___x_6524_;
goto v_reusejp_6526_;
}
else
{
lean_object* v_reuseFailAlloc_6528_; 
v_reuseFailAlloc_6528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_a_6522_);
v___x_6527_ = v_reuseFailAlloc_6528_;
goto v_reusejp_6526_;
}
v_reusejp_6526_:
{
v___y_6434_ = v___y_6486_;
v___y_6435_ = v___y_6487_;
v___y_6436_ = v___y_6488_;
v___y_6437_ = v___y_6489_;
v___y_6438_ = v___y_6490_;
v___y_6439_ = v___y_6491_;
v___y_6440_ = v___x_6520_;
v___y_6441_ = v___y_6492_;
v___y_6442_ = v___y_6493_;
v___y_6443_ = v___y_6494_;
v___y_6444_ = v_a_6499_;
v___y_6445_ = v___y_6495_;
v___y_6446_ = v___y_6496_;
v___y_6447_ = v___y_6497_;
v_a_6448_ = v___x_6527_;
goto v___jp_6433_;
}
}
}
else
{
lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6537_; 
v_a_6530_ = lean_ctor_get(v___x_6521_, 0);
v_isSharedCheck_6537_ = !lean_is_exclusive(v___x_6521_);
if (v_isSharedCheck_6537_ == 0)
{
v___x_6532_ = v___x_6521_;
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_dec(v___x_6521_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v___x_6535_; 
if (v_isShared_6533_ == 0)
{
lean_ctor_set_tag(v___x_6532_, 0);
v___x_6535_ = v___x_6532_;
goto v_reusejp_6534_;
}
else
{
lean_object* v_reuseFailAlloc_6536_; 
v_reuseFailAlloc_6536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_a_6530_);
v___x_6535_ = v_reuseFailAlloc_6536_;
goto v_reusejp_6534_;
}
v_reusejp_6534_:
{
v___y_6434_ = v___y_6486_;
v___y_6435_ = v___y_6487_;
v___y_6436_ = v___y_6488_;
v___y_6437_ = v___y_6489_;
v___y_6438_ = v___y_6490_;
v___y_6439_ = v___y_6491_;
v___y_6440_ = v___x_6520_;
v___y_6441_ = v___y_6492_;
v___y_6442_ = v___y_6493_;
v___y_6443_ = v___y_6494_;
v___y_6444_ = v_a_6499_;
v___y_6445_ = v___y_6495_;
v___y_6446_ = v___y_6496_;
v___y_6447_ = v___y_6497_;
v_a_6448_ = v___x_6535_;
goto v___jp_6433_;
}
}
}
}
}
v___jp_6538_:
{
size_t v_sz_6540_; size_t v___x_6541_; lean_object* v_assignments_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v_funVals_6545_; lean_object* v_state_6546_; lean_object* v___x_6547_; lean_object* v_options_6548_; lean_object* v_inheritedTraceOptions_6549_; uint8_t v_hasTrace_6550_; lean_object* v_ctx_6551_; 
v_sz_6540_ = lean_array_size(v___y_6539_);
v___x_6541_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6539_, 2);
v_assignments_6542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6540_, v___x_6541_, v___y_6539_);
v___x_6543_ = lean_array_get_size(v___y_6539_);
v___x_6544_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6545_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6539_, v___x_6543_, v___x_6543_, v___x_6544_);
v_state_6546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6546_, 0, v_assignments_6542_);
lean_ctor_set(v_state_6546_, 1, v_funVals_6545_);
v___x_6547_ = lean_st_mk_ref(v_state_6546_);
v_options_6548_ = lean_ctor_get(v_a_6391_, 2);
v_inheritedTraceOptions_6549_ = lean_ctor_get(v_a_6391_, 13);
v_hasTrace_6550_ = lean_ctor_get_uint8(v_options_6548_, sizeof(void*)*1);
v_ctx_6551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6551_, 0, v___y_6539_);
lean_ctor_set(v_ctx_6551_, 1, v___x_6484_);
if (v_hasTrace_6550_ == 0)
{
lean_object* v___x_6552_; 
v___x_6552_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6484_, v_ctx_6551_, v___x_6547_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
lean_dec_ref_known(v_ctx_6551_, 2);
v___y_6395_ = v___y_6539_;
v___y_6396_ = v___x_6541_;
v___y_6397_ = v___x_6543_;
v___y_6398_ = v___x_6547_;
v___y_6399_ = v_sz_6540_;
v___y_6400_ = v___x_6552_;
goto v___jp_6394_;
}
else
{
lean_object* v___f_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; uint8_t v___x_6557_; 
lean_inc_ref(v___y_6539_);
v___f_6553_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6553_, 0, v___y_6539_);
v___x_6554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6555_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6556_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6557_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6549_, v_options_6548_, v___x_6556_);
if (v___x_6557_ == 0)
{
lean_object* v___x_6558_; uint8_t v___x_6559_; 
v___x_6558_ = l_Lean_trace_profiler;
v___x_6559_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6548_, v___x_6558_);
if (v___x_6559_ == 0)
{
lean_object* v___x_6560_; 
lean_dec_ref(v___f_6553_);
v___x_6560_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6484_, v_ctx_6551_, v___x_6547_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
lean_dec_ref_known(v_ctx_6551_, 2);
v___y_6395_ = v___y_6539_;
v___y_6396_ = v___x_6541_;
v___y_6397_ = v___x_6543_;
v___y_6398_ = v___x_6547_;
v___y_6399_ = v_sz_6540_;
v___y_6400_ = v___x_6560_;
goto v___jp_6394_;
}
else
{
v___y_6486_ = v___x_6557_;
v___y_6487_ = v___y_6539_;
v___y_6488_ = v___x_6554_;
v___y_6489_ = v___x_6543_;
v___y_6490_ = v_options_6548_;
v___y_6491_ = v_hasTrace_6550_;
v___y_6492_ = v___x_6555_;
v___y_6493_ = v___x_6547_;
v___y_6494_ = v___x_6541_;
v___y_6495_ = v_sz_6540_;
v___y_6496_ = v_ctx_6551_;
v___y_6497_ = v___f_6553_;
goto v___jp_6485_;
}
}
else
{
v___y_6486_ = v___x_6557_;
v___y_6487_ = v___y_6539_;
v___y_6488_ = v___x_6554_;
v___y_6489_ = v___x_6543_;
v___y_6490_ = v_options_6548_;
v___y_6491_ = v_hasTrace_6550_;
v___y_6492_ = v___x_6555_;
v___y_6493_ = v___x_6547_;
v___y_6494_ = v___x_6541_;
v___y_6495_ = v_sz_6540_;
v___y_6496_ = v_ctx_6551_;
v___y_6497_ = v___f_6553_;
goto v___jp_6485_;
}
}
}
v___jp_6562_:
{
lean_object* v___x_6565_; 
v___x_6565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6561_, v_decls_6388_, v___y_6563_, v___y_6564_);
lean_dec(v___y_6564_);
v___y_6539_ = v___x_6565_;
goto v___jp_6538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6573_, lean_object* v_a_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_, lean_object* v_a_6577_, lean_object* v_a_6578_){
_start:
{
lean_object* v_res_6579_; 
v_res_6579_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6573_, v_a_6574_, v_a_6575_, v_a_6576_, v_a_6577_);
lean_dec(v_a_6577_);
lean_dec_ref(v_a_6576_);
lean_dec(v_a_6575_);
lean_dec_ref(v_a_6574_);
return v_res_6579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6580_, lean_object* v_n_6581_, lean_object* v_j_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_){
_start:
{
lean_object* v___x_6585_; 
v___x_6585_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6580_, v_n_6581_, v_j_6582_, v_a_6584_);
return v___x_6585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6586_, lean_object* v_n_6587_, lean_object* v_j_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_){
_start:
{
lean_object* v_res_6591_; 
v_res_6591_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6586_, v_n_6587_, v_j_6588_, v_a_6589_, v_a_6590_);
lean_dec(v_n_6587_);
lean_dec_ref(v___y_6586_);
return v_res_6591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6592_, lean_object* v___x_6593_, lean_object* v_n_6594_, lean_object* v_j_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_){
_start:
{
lean_object* v___x_6598_; 
v___x_6598_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6592_, v___x_6593_, v_n_6594_, v_j_6595_, v_a_6597_);
return v___x_6598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6599_, lean_object* v___x_6600_, lean_object* v_n_6601_, lean_object* v_j_6602_, lean_object* v_a_6603_, lean_object* v_a_6604_){
_start:
{
lean_object* v_res_6605_; 
v_res_6605_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6599_, v___x_6600_, v_n_6601_, v_j_6602_, v_a_6603_, v_a_6604_);
lean_dec(v_n_6601_);
lean_dec_ref(v___x_6600_);
lean_dec_ref(v___y_6599_);
return v_res_6605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6606_, lean_object* v_as_6607_, size_t v_sz_6608_, size_t v_i_6609_, lean_object* v_bs_6610_, lean_object* v___y_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_, lean_object* v___y_6614_){
_start:
{
lean_object* v___x_6616_; 
v___x_6616_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6606_, v_sz_6608_, v_i_6609_, v_bs_6610_, v___y_6611_, v___y_6612_, v___y_6613_, v___y_6614_);
return v___x_6616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6617_, lean_object* v_as_6618_, lean_object* v_sz_6619_, lean_object* v_i_6620_, lean_object* v_bs_6621_, lean_object* v___y_6622_, lean_object* v___y_6623_, lean_object* v___y_6624_, lean_object* v___y_6625_, lean_object* v___y_6626_){
_start:
{
size_t v_sz_boxed_6627_; size_t v_i_boxed_6628_; lean_object* v_res_6629_; 
v_sz_boxed_6627_ = lean_unbox_usize(v_sz_6619_);
lean_dec(v_sz_6619_);
v_i_boxed_6628_ = lean_unbox_usize(v_i_6620_);
lean_dec(v_i_6620_);
v_res_6629_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6617_, v_as_6618_, v_sz_boxed_6627_, v_i_boxed_6628_, v_bs_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_);
lean_dec(v___y_6625_);
lean_dec_ref(v___y_6624_);
lean_dec(v___y_6623_);
lean_dec_ref(v___y_6622_);
lean_dec_ref(v_as_6618_);
lean_dec_ref(v___x_6617_);
return v_res_6629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6630_, lean_object* v_as_6631_, lean_object* v_lo_6632_, lean_object* v_hi_6633_, lean_object* v_w_6634_, lean_object* v_hlo_6635_, lean_object* v_hhi_6636_){
_start:
{
lean_object* v___x_6637_; 
v___x_6637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6630_, v_as_6631_, v_lo_6632_, v_hi_6633_);
return v___x_6637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6638_, lean_object* v_as_6639_, lean_object* v_lo_6640_, lean_object* v_hi_6641_, lean_object* v_w_6642_, lean_object* v_hlo_6643_, lean_object* v_hhi_6644_){
_start:
{
lean_object* v_res_6645_; 
v_res_6645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6638_, v_as_6639_, v_lo_6640_, v_hi_6641_, v_w_6642_, v_hlo_6643_, v_hhi_6644_);
lean_dec(v_hi_6641_);
lean_dec(v_n_6638_);
return v_res_6645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6646_, lean_object* v_lo_6647_, lean_object* v_hi_6648_, lean_object* v_hhi_6649_, lean_object* v_pivot_6650_, lean_object* v_as_6651_, lean_object* v_i_6652_, lean_object* v_k_6653_, lean_object* v_ilo_6654_, lean_object* v_ik_6655_, lean_object* v_w_6656_){
_start:
{
lean_object* v___x_6657_; 
v___x_6657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6648_, v_pivot_6650_, v_as_6651_, v_i_6652_, v_k_6653_);
return v___x_6657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6658_, lean_object* v_lo_6659_, lean_object* v_hi_6660_, lean_object* v_hhi_6661_, lean_object* v_pivot_6662_, lean_object* v_as_6663_, lean_object* v_i_6664_, lean_object* v_k_6665_, lean_object* v_ilo_6666_, lean_object* v_ik_6667_, lean_object* v_w_6668_){
_start:
{
lean_object* v_res_6669_; 
v_res_6669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6658_, v_lo_6659_, v_hi_6660_, v_hhi_6661_, v_pivot_6662_, v_as_6663_, v_i_6664_, v_k_6665_, v_ilo_6666_, v_ik_6667_, v_w_6668_);
lean_dec(v_hi_6660_);
lean_dec(v_lo_6659_);
lean_dec(v_n_6658_);
return v_res_6669_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; 
v___x_6729_ = lean_unsigned_to_nat(3955956072u);
v___x_6730_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6731_ = l_Lean_Name_num___override(v___x_6730_, v___x_6729_);
return v___x_6731_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6733_; lean_object* v___x_6734_; lean_object* v___x_6735_; 
v___x_6733_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6734_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6735_ = l_Lean_Name_str___override(v___x_6734_, v___x_6733_);
return v___x_6735_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
v___x_6737_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6738_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6739_ = l_Lean_Name_str___override(v___x_6738_, v___x_6737_);
return v___x_6739_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; 
v___x_6740_ = lean_unsigned_to_nat(2u);
v___x_6741_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6742_ = l_Lean_Name_num___override(v___x_6741_, v___x_6740_);
return v___x_6742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6744_; uint8_t v___x_6745_; lean_object* v___x_6746_; lean_object* v___x_6747_; 
v___x_6744_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6745_ = 1;
v___x_6746_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6747_ = l_Lean_registerTraceClass(v___x_6744_, v___x_6745_, v___x_6746_);
return v___x_6747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6748_){
_start:
{
lean_object* v_res_6749_; 
v_res_6749_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6749_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
