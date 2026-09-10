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
lean_object* v_toCold_4346_; lean_object* v___x_4347_; lean_object* v_traceState_4348_; lean_object* v_traces_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_toCold_4346_ = lean_ctor_get(v___y_4343_, 0);
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
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4410_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4410_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4410_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v_env_4357_; lean_object* v_lctx_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4408_; 
v_env_4357_ = lean_ctor_get(v___x_4350_, 0);
lean_inc_ref(v_env_4357_);
lean_dec(v___x_4350_);
v_lctx_4358_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v___x_4351_, 1);
lean_dec(v_unused_4409_);
v___x_4360_ = v___x_4351_;
v_isShared_4361_ = v_isSharedCheck_4408_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_lctx_4358_);
lean_dec(v___x_4351_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4408_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_options_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v_traceState_4365_; lean_object* v_env_4366_; lean_object* v_nextMacroScope_4367_; lean_object* v_ngen_4368_; lean_object* v_auxDeclNGen_4369_; lean_object* v_cache_4370_; lean_object* v_messages_4371_; lean_object* v_infoState_4372_; lean_object* v_snapshotTasks_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4407_; 
v_options_4362_ = lean_ctor_get(v_toCold_4346_, 2);
v___x_4363_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4364_ = lean_st_ref_take(v___y_4344_);
v_traceState_4365_ = lean_ctor_get(v___x_4364_, 4);
v_env_4366_ = lean_ctor_get(v___x_4364_, 0);
v_nextMacroScope_4367_ = lean_ctor_get(v___x_4364_, 1);
v_ngen_4368_ = lean_ctor_get(v___x_4364_, 2);
v_auxDeclNGen_4369_ = lean_ctor_get(v___x_4364_, 3);
v_cache_4370_ = lean_ctor_get(v___x_4364_, 5);
v_messages_4371_ = lean_ctor_get(v___x_4364_, 6);
v_infoState_4372_ = lean_ctor_get(v___x_4364_, 7);
v_snapshotTasks_4373_ = lean_ctor_get(v___x_4364_, 8);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4375_ = v___x_4364_;
v_isShared_4376_ = v_isSharedCheck_4407_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_snapshotTasks_4373_);
lean_inc(v_infoState_4372_);
lean_inc(v_messages_4371_);
lean_inc(v_cache_4370_);
lean_inc(v_traceState_4365_);
lean_inc(v_auxDeclNGen_4369_);
lean_inc(v_ngen_4368_);
lean_inc(v_nextMacroScope_4367_);
lean_inc(v_env_4366_);
lean_dec(v___x_4364_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4407_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
uint64_t v_tid_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4405_; 
v_tid_4377_ = lean_ctor_get_uint64(v_traceState_4365_, sizeof(void*)*1);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_traceState_4365_);
if (v_isSharedCheck_4405_ == 0)
{
lean_object* v_unused_4406_; 
v_unused_4406_ = lean_ctor_get(v_traceState_4365_, 0);
lean_dec(v_unused_4406_);
v___x_4379_ = v_traceState_4365_;
v_isShared_4380_ = v_isSharedCheck_4405_;
goto v_resetjp_4378_;
}
else
{
lean_dec(v_traceState_4365_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4405_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; size_t v_sz_4382_; size_t v___x_4383_; lean_object* v___x_4384_; lean_object* v_msg_4385_; uint8_t v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4381_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4349_);
lean_dec_ref(v_traces_4349_);
v_sz_4382_ = lean_array_size(v___x_4381_);
v___x_4383_ = ((size_t)0ULL);
v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4382_, v___x_4383_, v___x_4381_);
v_msg_4385_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4385_, 0, v_data_4338_);
lean_ctor_set(v_msg_4385_, 1, v_msg_4340_);
lean_ctor_set(v_msg_4385_, 2, v___x_4384_);
v___x_4386_ = lean_unbox(v_a_4353_);
lean_dec(v_a_4353_);
v___x_4387_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4358_, v___x_4386_);
lean_dec_ref(v_lctx_4358_);
lean_inc_ref(v_options_4362_);
v___x_4388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4388_, 0, v_env_4357_);
lean_ctor_set(v___x_4388_, 1, v___x_4363_);
lean_ctor_set(v___x_4388_, 2, v___x_4387_);
lean_ctor_set(v___x_4388_, 3, v_options_4362_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set_tag(v___x_4360_, 3);
lean_ctor_set(v___x_4360_, 1, v_msg_4385_);
lean_ctor_set(v___x_4360_, 0, v___x_4388_);
v___x_4390_ = v___x_4360_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_msg_4385_);
v___x_4390_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v_ref_4339_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4337_, v___x_4391_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4392_);
v___x_4394_ = v___x_4379_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4392_);
lean_ctor_set_uint64(v_reuseFailAlloc_4403_, sizeof(void*)*1, v_tid_4377_);
v___x_4394_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4396_; 
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 4, v___x_4394_);
v___x_4396_ = v___x_4375_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_env_4366_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_nextMacroScope_4367_);
lean_ctor_set(v_reuseFailAlloc_4402_, 2, v_ngen_4368_);
lean_ctor_set(v_reuseFailAlloc_4402_, 3, v_auxDeclNGen_4369_);
lean_ctor_set(v_reuseFailAlloc_4402_, 4, v___x_4394_);
lean_ctor_set(v_reuseFailAlloc_4402_, 5, v_cache_4370_);
lean_ctor_set(v_reuseFailAlloc_4402_, 6, v_messages_4371_);
lean_ctor_set(v_reuseFailAlloc_4402_, 7, v_infoState_4372_);
lean_ctor_set(v_reuseFailAlloc_4402_, 8, v_snapshotTasks_4373_);
v___x_4396_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4397_ = lean_st_ref_put(v___y_4344_, v___x_4396_);
v___x_4398_ = lean_box(0);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4398_);
v___x_4400_ = v___x_4355_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
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
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v___x_4351_);
lean_dec(v___x_4350_);
lean_dec_ref(v_traces_4349_);
lean_dec_ref(v_msg_4340_);
lean_dec(v_ref_4339_);
lean_dec_ref(v_data_4338_);
lean_dec_ref(v_oldTraces_4337_);
v_a_4411_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4352_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4352_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4419_, lean_object* v_data_4420_, lean_object* v_ref_4421_, lean_object* v_msg_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4419_, v_data_4420_, v_ref_4421_, v_msg_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
return v_res_4428_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4429_; double v___x_4430_; 
v___x_4429_ = lean_unsigned_to_nat(0u);
v___x_4430_ = lean_float_of_nat(v___x_4429_);
return v___x_4430_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4432_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4433_ = l_Lean_stringToMessageData(v___x_4432_);
return v___x_4433_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4434_; double v___x_4435_; 
v___x_4434_ = lean_unsigned_to_nat(1000u);
v___x_4435_ = lean_float_of_nat(v___x_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4436_, uint8_t v_collapsed_4437_, lean_object* v_tag_4438_, lean_object* v_opts_4439_, uint8_t v_clsEnabled_4440_, lean_object* v_oldTraces_4441_, lean_object* v_msg_4442_, lean_object* v_resStartStop_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_fst_4451_; lean_object* v_snd_4452_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v_data_4456_; lean_object* v_fst_4459_; lean_object* v_snd_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; lean_object* v___y_4464_; lean_object* v_a_4465_; uint8_t v___y_4480_; double v___y_4511_; 
v_fst_4451_ = lean_ctor_get(v_resStartStop_4443_, 0);
lean_inc(v_fst_4451_);
v_snd_4452_ = lean_ctor_get(v_resStartStop_4443_, 1);
lean_inc(v_snd_4452_);
lean_dec_ref(v_resStartStop_4443_);
v_fst_4459_ = lean_ctor_get(v_snd_4452_, 0);
lean_inc(v_fst_4459_);
v_snd_4460_ = lean_ctor_get(v_snd_4452_, 1);
lean_inc(v_snd_4460_);
lean_dec(v_snd_4452_);
v___x_4461_ = l_Lean_trace_profiler;
v___x_4462_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4439_, v___x_4461_);
if (v___x_4462_ == 0)
{
v___y_4480_ = v___x_4462_;
goto v___jp_4479_;
}
else
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4517_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4439_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; double v___x_4520_; double v___x_4521_; double v___x_4522_; 
v___x_4518_ = l_Lean_trace_profiler_threshold;
v___x_4519_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4439_, v___x_4518_);
v___x_4520_ = lean_float_of_nat(v___x_4519_);
v___x_4521_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4522_ = lean_float_div(v___x_4520_, v___x_4521_);
v___y_4511_ = v___x_4522_;
goto v___jp_4510_;
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; double v___x_4525_; 
v___x_4523_ = l_Lean_trace_profiler_threshold;
v___x_4524_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4439_, v___x_4523_);
v___x_4525_ = lean_float_of_nat(v___x_4524_);
v___y_4511_ = v___x_4525_;
goto v___jp_4510_;
}
}
v___jp_4453_:
{
lean_object* v___x_4457_; 
lean_inc(v___y_4455_);
v___x_4457_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4441_, v_data_4456_, v___y_4455_, v___y_4454_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; 
lean_dec_ref_known(v___x_4457_, 1);
v___x_4458_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4451_);
return v___x_4458_;
}
else
{
lean_dec(v_fst_4451_);
return v___x_4457_;
}
}
v___jp_4463_:
{
uint8_t v_result_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; double v___x_4469_; lean_object* v_data_4470_; 
v_result_4466_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4451_);
v___x_4467_ = lean_box(v_result_4466_);
v___x_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
v___x_4469_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4438_);
lean_inc_ref(v___x_4468_);
lean_inc(v_cls_4436_);
v_data_4470_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4470_, 0, v_cls_4436_);
lean_ctor_set(v_data_4470_, 1, v___x_4468_);
lean_ctor_set(v_data_4470_, 2, v_tag_4438_);
lean_ctor_set_float(v_data_4470_, sizeof(void*)*3, v___x_4469_);
lean_ctor_set_float(v_data_4470_, sizeof(void*)*3 + 8, v___x_4469_);
lean_ctor_set_uint8(v_data_4470_, sizeof(void*)*3 + 16, v_collapsed_4437_);
if (v___x_4462_ == 0)
{
lean_dec_ref_known(v___x_4468_, 1);
lean_dec(v_snd_4460_);
lean_dec(v_fst_4459_);
lean_dec_ref(v_tag_4438_);
lean_dec(v_cls_4436_);
v___y_4454_ = v_a_4465_;
v___y_4455_ = v___y_4464_;
v_data_4456_ = v_data_4470_;
goto v___jp_4453_;
}
else
{
lean_object* v_data_4471_; double v___x_4472_; double v___x_4473_; 
lean_dec_ref_known(v_data_4470_, 3);
v_data_4471_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4471_, 0, v_cls_4436_);
lean_ctor_set(v_data_4471_, 1, v___x_4468_);
lean_ctor_set(v_data_4471_, 2, v_tag_4438_);
v___x_4472_ = lean_unbox_float(v_fst_4459_);
lean_dec(v_fst_4459_);
lean_ctor_set_float(v_data_4471_, sizeof(void*)*3, v___x_4472_);
v___x_4473_ = lean_unbox_float(v_snd_4460_);
lean_dec(v_snd_4460_);
lean_ctor_set_float(v_data_4471_, sizeof(void*)*3 + 8, v___x_4473_);
lean_ctor_set_uint8(v_data_4471_, sizeof(void*)*3 + 16, v_collapsed_4437_);
v___y_4454_ = v_a_4465_;
v___y_4455_ = v___y_4464_;
v_data_4456_ = v_data_4471_;
goto v___jp_4453_;
}
}
v___jp_4474_:
{
lean_object* v_ref_4475_; lean_object* v___x_4476_; 
v_ref_4475_ = lean_ctor_get(v___y_4448_, 2);
lean_inc(v___y_4449_);
lean_inc_ref(v___y_4448_);
lean_inc(v___y_4447_);
lean_inc_ref(v___y_4446_);
lean_inc(v___y_4445_);
lean_inc_ref(v___y_4444_);
lean_inc(v_fst_4451_);
v___x_4476_ = lean_apply_8(v_msg_4442_, v_fst_4451_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, lean_box(0));
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
v___y_4464_ = v_ref_4475_;
v_a_4465_ = v_a_4477_;
goto v___jp_4463_;
}
else
{
lean_object* v___x_4478_; 
lean_dec_ref_known(v___x_4476_, 1);
v___x_4478_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4464_ = v_ref_4475_;
v_a_4465_ = v___x_4478_;
goto v___jp_4463_;
}
}
v___jp_4479_:
{
if (v_clsEnabled_4440_ == 0)
{
if (v___y_4480_ == 0)
{
lean_object* v___x_4481_; lean_object* v_traceState_4482_; lean_object* v_env_4483_; lean_object* v_nextMacroScope_4484_; lean_object* v_ngen_4485_; lean_object* v_auxDeclNGen_4486_; lean_object* v_cache_4487_; lean_object* v_messages_4488_; lean_object* v_infoState_4489_; lean_object* v_snapshotTasks_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v_snd_4460_);
lean_dec(v_fst_4459_);
lean_dec_ref(v_msg_4442_);
lean_dec_ref(v_tag_4438_);
lean_dec(v_cls_4436_);
v___x_4481_ = lean_st_ref_take(v___y_4449_);
v_traceState_4482_ = lean_ctor_get(v___x_4481_, 4);
v_env_4483_ = lean_ctor_get(v___x_4481_, 0);
v_nextMacroScope_4484_ = lean_ctor_get(v___x_4481_, 1);
v_ngen_4485_ = lean_ctor_get(v___x_4481_, 2);
v_auxDeclNGen_4486_ = lean_ctor_get(v___x_4481_, 3);
v_cache_4487_ = lean_ctor_get(v___x_4481_, 5);
v_messages_4488_ = lean_ctor_get(v___x_4481_, 6);
v_infoState_4489_ = lean_ctor_get(v___x_4481_, 7);
v_snapshotTasks_4490_ = lean_ctor_get(v___x_4481_, 8);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4492_ = v___x_4481_;
v_isShared_4493_ = v_isSharedCheck_4509_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_snapshotTasks_4490_);
lean_inc(v_infoState_4489_);
lean_inc(v_messages_4488_);
lean_inc(v_cache_4487_);
lean_inc(v_traceState_4482_);
lean_inc(v_auxDeclNGen_4486_);
lean_inc(v_ngen_4485_);
lean_inc(v_nextMacroScope_4484_);
lean_inc(v_env_4483_);
lean_dec(v___x_4481_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4509_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
uint64_t v_tid_4494_; lean_object* v_traces_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4508_; 
v_tid_4494_ = lean_ctor_get_uint64(v_traceState_4482_, sizeof(void*)*1);
v_traces_4495_ = lean_ctor_get(v_traceState_4482_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_traceState_4482_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4497_ = v_traceState_4482_;
v_isShared_4498_ = v_isSharedCheck_4508_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_traces_4495_);
lean_dec(v_traceState_4482_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4508_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4499_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4441_, v_traces_4495_);
lean_dec_ref(v_traces_4495_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4499_);
v___x_4501_ = v___x_4497_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4499_);
lean_ctor_set_uint64(v_reuseFailAlloc_4507_, sizeof(void*)*1, v_tid_4494_);
v___x_4501_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4503_; 
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 4, v___x_4501_);
v___x_4503_ = v___x_4492_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_env_4483_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_nextMacroScope_4484_);
lean_ctor_set(v_reuseFailAlloc_4506_, 2, v_ngen_4485_);
lean_ctor_set(v_reuseFailAlloc_4506_, 3, v_auxDeclNGen_4486_);
lean_ctor_set(v_reuseFailAlloc_4506_, 4, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4506_, 5, v_cache_4487_);
lean_ctor_set(v_reuseFailAlloc_4506_, 6, v_messages_4488_);
lean_ctor_set(v_reuseFailAlloc_4506_, 7, v_infoState_4489_);
lean_ctor_set(v_reuseFailAlloc_4506_, 8, v_snapshotTasks_4490_);
v___x_4503_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_st_ref_put(v___y_4449_, v___x_4503_);
v___x_4505_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4451_);
return v___x_4505_;
}
}
}
}
}
else
{
goto v___jp_4474_;
}
}
else
{
goto v___jp_4474_;
}
}
v___jp_4510_:
{
double v___x_4512_; double v___x_4513_; double v___x_4514_; uint8_t v___x_4515_; 
v___x_4512_ = lean_unbox_float(v_snd_4460_);
v___x_4513_ = lean_unbox_float(v_fst_4459_);
v___x_4514_ = lean_float_sub(v___x_4512_, v___x_4513_);
v___x_4515_ = lean_float_decLt(v___y_4511_, v___x_4514_);
v___y_4480_ = v___x_4515_;
goto v___jp_4479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4526_, lean_object* v_collapsed_4527_, lean_object* v_tag_4528_, lean_object* v_opts_4529_, lean_object* v_clsEnabled_4530_, lean_object* v_oldTraces_4531_, lean_object* v_msg_4532_, lean_object* v_resStartStop_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
uint8_t v_collapsed_boxed_4541_; uint8_t v_clsEnabled_boxed_4542_; lean_object* v_res_4543_; 
v_collapsed_boxed_4541_ = lean_unbox(v_collapsed_4527_);
v_clsEnabled_boxed_4542_ = lean_unbox(v_clsEnabled_4530_);
v_res_4543_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4526_, v_collapsed_boxed_4541_, v_tag_4528_, v_opts_4529_, v_clsEnabled_boxed_4542_, v_oldTraces_4531_, v_msg_4532_, v_resStartStop_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec_ref(v_opts_4529_);
return v_res_4543_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4547_; double v___x_4548_; 
v___x_4547_ = lean_unsigned_to_nat(1000000000u);
v___x_4548_ = lean_float_of_nat(v___x_4547_);
return v___x_4548_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4558_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4559_ = l_Lean_Name_append(v___x_4558_, v___x_4557_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4560_, lean_object* v___x_4561_, lean_object* v_a_4562_, lean_object* v_b_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_a_4572_; uint8_t v___x_4576_; 
v___x_4576_ = lean_nat_dec_lt(v_a_4562_, v_upperBound_4560_);
if (v___x_4576_ == 0)
{
lean_object* v___x_4577_; 
lean_dec(v_a_4562_);
v___x_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4577_, 0, v_b_4563_);
return v___x_4577_;
}
else
{
lean_object* v___x_4578_; lean_object* v_toSignature_4579_; lean_object* v_value_4580_; lean_object* v_name_4581_; lean_object* v_params_4582_; uint8_t v_safe_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
lean_dec_ref(v_b_4563_);
v___x_4578_ = lean_array_fget_borrowed(v___x_4561_, v_a_4562_);
v_toSignature_4579_ = lean_ctor_get(v___x_4578_, 0);
v_value_4580_ = lean_ctor_get(v___x_4578_, 1);
v_name_4581_ = lean_ctor_get(v_toSignature_4579_, 0);
v_params_4582_ = lean_ctor_get(v_toSignature_4579_, 3);
v_safe_4583_ = lean_ctor_get_uint8(v_toSignature_4579_, sizeof(void*)*4);
v___x_4584_ = lean_box(0);
v___x_4585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4583_ == 0)
{
v_a_4572_ = v___x_4585_;
goto v___jp_4571_;
}
else
{
lean_object* v___x_4586_; 
v___x_4586_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4562_, v___y_4565_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___y_4589_; lean_object* v_decls_4619_; lean_object* v___f_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; uint8_t v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v_a_4631_; lean_object* v___y_4644_; lean_object* v___y_4645_; uint8_t v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v_a_4650_; lean_object* v___y_4660_; uint8_t v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4731_; uint8_t v___x_4740_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4586_, 1);
v_decls_4619_ = lean_ctor_get(v___y_4564_, 0);
lean_inc(v_name_4581_);
v___f_4620_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4620_, 0, v_name_4581_);
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = lean_array_get_size(v_params_4582_);
lean_inc(v_a_4562_);
lean_inc_ref(v_decls_4619_);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v_decls_4619_);
lean_ctor_set(v___x_4623_, 1, v_a_4562_);
v___x_4740_ = lean_nat_dec_lt(v___x_4621_, v___x_4622_);
if (v___x_4740_ == 0)
{
goto v___jp_4713_;
}
else
{
uint8_t v___x_4741_; 
v___x_4741_ = lean_nat_dec_le(v___x_4622_, v___x_4622_);
if (v___x_4741_ == 0)
{
if (v___x_4740_ == 0)
{
goto v___jp_4713_;
}
else
{
size_t v___x_4742_; size_t v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = ((size_t)0ULL);
v___x_4743_ = lean_usize_of_nat(v___x_4622_);
v___x_4744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4582_, v___x_4742_, v___x_4743_, v___x_4584_, v___x_4623_, v___y_4565_, v___y_4569_);
v___y_4731_ = v___x_4744_;
goto v___jp_4730_;
}
}
else
{
size_t v___x_4745_; size_t v___x_4746_; lean_object* v___x_4747_; 
v___x_4745_ = ((size_t)0ULL);
v___x_4746_ = lean_usize_of_nat(v___x_4622_);
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4582_, v___x_4745_, v___x_4746_, v___x_4584_, v___x_4623_, v___y_4565_, v___y_4569_);
v___y_4731_ = v___x_4747_;
goto v___jp_4730_;
}
}
v___jp_4588_:
{
if (lean_obj_tag(v___y_4589_) == 0)
{
lean_object* v___x_4590_; 
lean_dec_ref_known(v___y_4589_, 1);
v___x_4590_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4562_, v___y_4565_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4602_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4593_ = v___x_4590_;
v_isShared_4594_ = v_isSharedCheck_4602_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4590_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4602_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
uint8_t v___x_4595_; 
v___x_4595_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4587_, v_a_4591_);
lean_dec(v_a_4591_);
lean_dec(v_a_4587_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4600_; 
lean_dec(v_a_4562_);
v___x_4596_ = lean_box(v___x_4576_);
v___x_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
v___x_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4597_);
lean_ctor_set(v___x_4598_, 1, v___x_4584_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4598_);
v___x_4600_ = v___x_4593_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
else
{
lean_del_object(v___x_4593_);
v_a_4572_ = v___x_4585_;
goto v___jp_4571_;
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_dec(v_a_4587_);
lean_dec(v_a_4562_);
v_a_4603_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4590_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4590_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
lean_dec(v_a_4587_);
lean_dec(v_a_4562_);
v_a_4611_ = lean_ctor_get(v___y_4589_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___y_4589_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___y_4589_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___y_4589_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
v___jp_4624_:
{
lean_object* v___x_4632_; double v___x_4633_; double v___x_4634_; double v___x_4635_; double v___x_4636_; double v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4632_ = lean_io_mono_nanos_now();
v___x_4633_ = lean_float_of_nat(v___y_4625_);
v___x_4634_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4635_ = lean_float_div(v___x_4633_, v___x_4634_);
v___x_4636_ = lean_float_of_nat(v___x_4632_);
v___x_4637_ = lean_float_div(v___x_4636_, v___x_4634_);
v___x_4638_ = lean_box_float(v___x_4635_);
v___x_4639_ = lean_box_float(v___x_4637_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4638_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
v___x_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4641_, 0, v_a_4631_);
lean_ctor_set(v___x_4641_, 1, v___x_4640_);
lean_inc_ref(v___y_4630_);
lean_inc(v___y_4629_);
v___x_4642_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4629_, v___x_4576_, v___y_4630_, v___y_4626_, v___y_4628_, v___y_4627_, v___f_4620_, v___x_4641_, v___x_4623_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec_ref_known(v___x_4623_, 2);
v___y_4589_ = v___x_4642_;
goto v___jp_4588_;
}
v___jp_4643_:
{
lean_object* v___x_4651_; double v___x_4652_; double v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4651_ = lean_io_get_num_heartbeats();
v___x_4652_ = lean_float_of_nat(v___y_4649_);
v___x_4653_ = lean_float_of_nat(v___x_4651_);
v___x_4654_ = lean_box_float(v___x_4652_);
v___x_4655_ = lean_box_float(v___x_4653_);
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4654_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v_a_4650_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
lean_inc_ref(v___y_4648_);
lean_inc(v___y_4647_);
v___x_4658_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4647_, v___x_4576_, v___y_4648_, v___y_4644_, v___y_4646_, v___y_4645_, v___f_4620_, v___x_4657_, v___x_4623_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec_ref_known(v___x_4623_, 2);
v___y_4589_ = v___x_4658_;
goto v___jp_4588_;
}
v___jp_4659_:
{
lean_object* v___x_4665_; 
v___x_4665_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4569_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v___x_4667_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4668_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4660_, v___x_4667_);
if (v___x_4668_ == 0)
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = lean_io_mono_nanos_now();
v___x_4670_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4662_, v___x_4623_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
lean_ctor_set_tag(v___x_4673_, 1);
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
v___y_4625_ = v___x_4669_;
v___y_4626_ = v___y_4660_;
v___y_4627_ = v_a_4666_;
v___y_4628_ = v___y_4661_;
v___y_4629_ = v___y_4663_;
v___y_4630_ = v___y_4664_;
v_a_4631_ = v___x_4676_;
goto v___jp_4624_;
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
v_a_4679_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4670_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4670_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
lean_ctor_set_tag(v___x_4681_, 0);
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
v___y_4625_ = v___x_4669_;
v___y_4626_ = v___y_4660_;
v___y_4627_ = v_a_4666_;
v___y_4628_ = v___y_4661_;
v___y_4629_ = v___y_4663_;
v___y_4630_ = v___y_4664_;
v_a_4631_ = v___x_4684_;
goto v___jp_4624_;
}
}
}
}
else
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = lean_io_get_num_heartbeats();
v___x_4688_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4662_, v___x_4623_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4688_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set_tag(v___x_4691_, 1);
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
v___y_4644_ = v___y_4660_;
v___y_4645_ = v_a_4666_;
v___y_4646_ = v___y_4661_;
v___y_4647_ = v___y_4663_;
v___y_4648_ = v___y_4664_;
v___y_4649_ = v___x_4687_;
v_a_4650_ = v___x_4694_;
goto v___jp_4643_;
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
v_a_4697_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4688_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4688_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set_tag(v___x_4699_, 0);
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
v___y_4644_ = v___y_4660_;
v___y_4645_ = v_a_4666_;
v___y_4646_ = v___y_4661_;
v___y_4647_ = v___y_4663_;
v___y_4648_ = v___y_4664_;
v___y_4649_ = v___x_4687_;
v_a_4650_ = v___x_4702_;
goto v___jp_4643_;
}
}
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref(v___y_4662_);
lean_dec_ref_known(v___x_4623_, 2);
lean_dec_ref(v___f_4620_);
lean_dec(v_a_4587_);
lean_dec(v_a_4562_);
v_a_4705_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4665_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4665_);
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
v___jp_4713_:
{
if (lean_obj_tag(v_value_4580_) == 0)
{
lean_object* v_toCold_4714_; lean_object* v_options_4715_; uint8_t v_hasTrace_4716_; 
v_toCold_4714_ = lean_ctor_get(v___y_4568_, 0);
v_options_4715_ = lean_ctor_get(v_toCold_4714_, 2);
v_hasTrace_4716_ = lean_ctor_get_uint8(v_options_4715_, sizeof(void*)*1);
if (v_hasTrace_4716_ == 0)
{
lean_object* v_code_4717_; lean_object* v___x_4718_; 
lean_dec_ref(v___f_4620_);
v_code_4717_ = lean_ctor_get(v_value_4580_, 0);
lean_inc_ref(v_code_4717_);
v___x_4718_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4717_, v___x_4623_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec_ref_known(v___x_4623_, 2);
v___y_4589_ = v___x_4718_;
goto v___jp_4588_;
}
else
{
lean_object* v_code_4719_; lean_object* v_inheritedTraceOptions_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; 
v_code_4719_ = lean_ctor_get(v_value_4580_, 0);
v_inheritedTraceOptions_4720_ = lean_ctor_get(v_toCold_4714_, 11);
v___x_4721_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4723_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4724_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4720_, v_options_4715_, v___x_4723_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; uint8_t v___x_4726_; 
v___x_4725_ = l_Lean_trace_profiler;
v___x_4726_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4715_, v___x_4725_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; 
lean_dec_ref(v___f_4620_);
lean_inc_ref(v_code_4719_);
v___x_4727_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4719_, v___x_4623_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec_ref_known(v___x_4623_, 2);
v___y_4589_ = v___x_4727_;
goto v___jp_4588_;
}
else
{
lean_inc_ref(v_code_4719_);
v___y_4660_ = v_options_4715_;
v___y_4661_ = v___x_4724_;
v___y_4662_ = v_code_4719_;
v___y_4663_ = v___x_4721_;
v___y_4664_ = v___x_4722_;
goto v___jp_4659_;
}
}
else
{
lean_inc_ref(v_code_4719_);
v___y_4660_ = v_options_4715_;
v___y_4661_ = v___x_4724_;
v___y_4662_ = v_code_4719_;
v___y_4663_ = v___x_4721_;
v___y_4664_ = v___x_4722_;
goto v___jp_4659_;
}
}
}
else
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
lean_dec_ref(v___f_4620_);
v___x_4728_ = lean_box(1);
v___x_4729_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4728_, v___x_4623_, v___y_4565_, v___y_4569_);
lean_dec_ref_known(v___x_4623_, 2);
v___y_4589_ = v___x_4729_;
goto v___jp_4588_;
}
}
v___jp_4730_:
{
if (lean_obj_tag(v___y_4731_) == 0)
{
lean_dec_ref_known(v___y_4731_, 1);
goto v___jp_4713_;
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_dec_ref_known(v___x_4623_, 2);
lean_dec_ref(v___f_4620_);
lean_dec(v_a_4587_);
lean_dec(v_a_4562_);
v_a_4732_ = lean_ctor_get(v___y_4731_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___y_4731_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___y_4731_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___y_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
lean_dec(v_a_4562_);
v_a_4748_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4586_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4586_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
}
v___jp_4571_:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = lean_unsigned_to_nat(1u);
v___x_4574_ = lean_nat_add(v_a_4562_, v___x_4573_);
lean_dec(v_a_4562_);
lean_inc_ref(v_a_4572_);
v_a_4562_ = v___x_4574_;
v_b_4563_ = v_a_4572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4756_, lean_object* v___x_4757_, lean_object* v_a_4758_, lean_object* v_b_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4756_, v___x_4757_, v_a_4758_, v_b_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec_ref(v___x_4757_);
lean_dec(v_upperBound_4756_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_decls_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v_decls_4775_ = lean_ctor_get(v_a_4768_, 0);
v___x_4776_ = lean_array_get_size(v_decls_4775_);
v___x_4777_ = lean_unsigned_to_nat(0u);
v___x_4778_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4776_, v_decls_4775_, v___x_4777_, v___x_4778_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4794_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4782_ = v___x_4779_;
v_isShared_4783_ = v_isSharedCheck_4794_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4794_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v_fst_4784_; 
v_fst_4784_ = lean_ctor_get(v_a_4780_, 0);
lean_inc(v_fst_4784_);
lean_dec(v_a_4780_);
if (lean_obj_tag(v_fst_4784_) == 0)
{
uint8_t v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4785_ = 0;
v___x_4786_ = lean_box(v___x_4785_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4786_);
v___x_4788_ = v___x_4782_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
else
{
lean_object* v_val_4790_; lean_object* v___x_4792_; 
v_val_4790_ = lean_ctor_get(v_fst_4784_, 0);
lean_inc(v_val_4790_);
lean_dec_ref_known(v_fst_4784_, 1);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v_val_4790_);
v___x_4792_ = v___x_4782_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_val_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
v_a_4795_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4779_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4779_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4811_, lean_object* v_x_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4812_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4821_, lean_object* v_x_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4821_, v_x_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4831_, lean_object* v___x_4832_, lean_object* v_inst_4833_, lean_object* v_R_4834_, lean_object* v_a_4835_, lean_object* v_b_4836_, lean_object* v_c_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4831_, v___x_4832_, v_a_4835_, v_b_4836_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4846_, lean_object* v___x_4847_, lean_object* v_inst_4848_, lean_object* v_R_4849_, lean_object* v_a_4850_, lean_object* v_b_4851_, lean_object* v_c_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4846_, v___x_4847_, v_inst_4848_, v_R_4849_, v_a_4850_, v_b_4851_, v_c_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec_ref(v___x_4847_);
lean_dec(v_upperBound_4846_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4861_, lean_object* v_data_4862_, lean_object* v_ref_4863_, lean_object* v_msg_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4861_, v_data_4862_, v_ref_4863_, v_msg_4864_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4873_, lean_object* v_data_4874_, lean_object* v_ref_4875_, lean_object* v_msg_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4873_, v_data_4874_, v_ref_4875_, v_msg_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4887_, lean_object* v_msg_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_){
_start:
{
lean_object* v_toCold_4894_; lean_object* v_ref_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v_toCold_4894_ = lean_ctor_get(v___y_4891_, 0);
v_ref_4895_ = lean_ctor_get(v___y_4891_, 2);
v___x_4896_ = lean_st_ref_get(v___y_4892_);
v___x_4897_ = lean_st_ref_get(v___y_4890_);
v___x_4898_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4889_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4958_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4958_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4958_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v_env_4903_; lean_object* v_lctx_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4956_; 
v_env_4903_ = lean_ctor_get(v___x_4896_, 0);
lean_inc_ref(v_env_4903_);
lean_dec(v___x_4896_);
v_lctx_4904_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4956_ == 0)
{
lean_object* v_unused_4957_; 
v_unused_4957_ = lean_ctor_get(v___x_4897_, 1);
lean_dec(v_unused_4957_);
v___x_4906_ = v___x_4897_;
v_isShared_4907_ = v_isSharedCheck_4956_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_lctx_4904_);
lean_dec(v___x_4897_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4956_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v_options_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v_traceState_4911_; lean_object* v_env_4912_; lean_object* v_nextMacroScope_4913_; lean_object* v_ngen_4914_; lean_object* v_auxDeclNGen_4915_; lean_object* v_cache_4916_; lean_object* v_messages_4917_; lean_object* v_infoState_4918_; lean_object* v_snapshotTasks_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4955_; 
v_options_4908_ = lean_ctor_get(v_toCold_4894_, 2);
v___x_4909_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4910_ = lean_st_ref_take(v___y_4892_);
v_traceState_4911_ = lean_ctor_get(v___x_4910_, 4);
v_env_4912_ = lean_ctor_get(v___x_4910_, 0);
v_nextMacroScope_4913_ = lean_ctor_get(v___x_4910_, 1);
v_ngen_4914_ = lean_ctor_get(v___x_4910_, 2);
v_auxDeclNGen_4915_ = lean_ctor_get(v___x_4910_, 3);
v_cache_4916_ = lean_ctor_get(v___x_4910_, 5);
v_messages_4917_ = lean_ctor_get(v___x_4910_, 6);
v_infoState_4918_ = lean_ctor_get(v___x_4910_, 7);
v_snapshotTasks_4919_ = lean_ctor_get(v___x_4910_, 8);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4921_ = v___x_4910_;
v_isShared_4922_ = v_isSharedCheck_4955_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_snapshotTasks_4919_);
lean_inc(v_infoState_4918_);
lean_inc(v_messages_4917_);
lean_inc(v_cache_4916_);
lean_inc(v_traceState_4911_);
lean_inc(v_auxDeclNGen_4915_);
lean_inc(v_ngen_4914_);
lean_inc(v_nextMacroScope_4913_);
lean_inc(v_env_4912_);
lean_dec(v___x_4910_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4955_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
uint64_t v_tid_4923_; lean_object* v_traces_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4954_; 
v_tid_4923_ = lean_ctor_get_uint64(v_traceState_4911_, sizeof(void*)*1);
v_traces_4924_ = lean_ctor_get(v_traceState_4911_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v_traceState_4911_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4926_ = v_traceState_4911_;
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_traces_4924_);
lean_dec(v_traceState_4911_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
uint8_t v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4932_; 
v___x_4928_ = lean_unbox(v_a_4899_);
lean_dec(v_a_4899_);
v___x_4929_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4904_, v___x_4928_);
lean_dec_ref(v_lctx_4904_);
lean_inc_ref(v_options_4908_);
v___x_4930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4930_, 0, v_env_4903_);
lean_ctor_set(v___x_4930_, 1, v___x_4909_);
lean_ctor_set(v___x_4930_, 2, v___x_4929_);
lean_ctor_set(v___x_4930_, 3, v_options_4908_);
if (v_isShared_4907_ == 0)
{
lean_ctor_set_tag(v___x_4906_, 3);
lean_ctor_set(v___x_4906_, 1, v_msg_4888_);
lean_ctor_set(v___x_4906_, 0, v___x_4930_);
v___x_4932_ = v___x_4906_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v_msg_4888_);
v___x_4932_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
lean_object* v___x_4933_; double v___x_4934_; uint8_t v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4943_; 
v___x_4933_ = lean_box(0);
v___x_4934_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4935_ = 0;
v___x_4936_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4937_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4937_, 0, v_cls_4887_);
lean_ctor_set(v___x_4937_, 1, v___x_4933_);
lean_ctor_set(v___x_4937_, 2, v___x_4936_);
lean_ctor_set_float(v___x_4937_, sizeof(void*)*3, v___x_4934_);
lean_ctor_set_float(v___x_4937_, sizeof(void*)*3 + 8, v___x_4934_);
lean_ctor_set_uint8(v___x_4937_, sizeof(void*)*3 + 16, v___x_4935_);
v___x_4938_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4939_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v___x_4932_);
lean_ctor_set(v___x_4939_, 2, v___x_4938_);
lean_inc(v_ref_4895_);
v___x_4940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4940_, 0, v_ref_4895_);
lean_ctor_set(v___x_4940_, 1, v___x_4939_);
v___x_4941_ = l_Lean_PersistentArray_push___redArg(v_traces_4924_, v___x_4940_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4941_);
v___x_4943_ = v___x_4926_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4941_);
lean_ctor_set_uint64(v_reuseFailAlloc_4952_, sizeof(void*)*1, v_tid_4923_);
v___x_4943_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
lean_object* v___x_4945_; 
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 4, v___x_4943_);
v___x_4945_ = v___x_4921_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_env_4912_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_nextMacroScope_4913_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_ngen_4914_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_auxDeclNGen_4915_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v___x_4943_);
lean_ctor_set(v_reuseFailAlloc_4951_, 5, v_cache_4916_);
lean_ctor_set(v_reuseFailAlloc_4951_, 6, v_messages_4917_);
lean_ctor_set(v_reuseFailAlloc_4951_, 7, v_infoState_4918_);
lean_ctor_set(v_reuseFailAlloc_4951_, 8, v_snapshotTasks_4919_);
v___x_4945_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4946_ = lean_st_ref_put(v___y_4892_, v___x_4945_);
v___x_4947_ = lean_box(0);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4947_);
v___x_4949_ = v___x_4901_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
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
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec(v___x_4897_);
lean_dec(v___x_4896_);
lean_dec_ref(v_msg_4888_);
lean_dec(v_cls_4887_);
v_a_4959_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4898_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4898_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4967_, lean_object* v_msg_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4967_, v_msg_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
lean_dec(v___y_4970_);
lean_dec_ref(v___y_4969_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4975_, lean_object* v_msg_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v___x_4984_; 
v___x_4984_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4975_, v_msg_4976_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4985_, lean_object* v_msg_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4985_, v_msg_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
return v_res_4994_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4995_ = lean_box(0);
v___x_4996_ = lean_unsigned_to_nat(16u);
v___x_4997_ = lean_mk_array(v___x_4996_, v___x_4995_);
return v___x_4997_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4998_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_4999_ = lean_unsigned_to_nat(0u);
v___x_5000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
lean_ctor_set(v___x_5000_, 1, v___x_4998_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_5001_, size_t v_i_5002_, lean_object* v_bs_5003_){
_start:
{
uint8_t v___x_5004_; 
v___x_5004_ = lean_usize_dec_lt(v_i_5002_, v_sz_5001_);
if (v___x_5004_ == 0)
{
return v_bs_5003_;
}
else
{
lean_object* v___x_5005_; lean_object* v_bs_x27_5006_; lean_object* v___x_5007_; size_t v___x_5008_; size_t v___x_5009_; lean_object* v___x_5010_; 
v___x_5005_ = lean_unsigned_to_nat(0u);
v_bs_x27_5006_ = lean_array_uset(v_bs_5003_, v_i_5002_, v___x_5005_);
v___x_5007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5008_ = ((size_t)1ULL);
v___x_5009_ = lean_usize_add(v_i_5002_, v___x_5008_);
v___x_5010_ = lean_array_uset(v_bs_x27_5006_, v_i_5002_, v___x_5007_);
v_i_5002_ = v___x_5009_;
v_bs_5003_ = v___x_5010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_5012_, lean_object* v_i_5013_, lean_object* v_bs_5014_){
_start:
{
size_t v_sz_boxed_5015_; size_t v_i_boxed_5016_; lean_object* v_res_5017_; 
v_sz_boxed_5015_ = lean_unbox_usize(v_sz_5012_);
lean_dec(v_sz_5012_);
v_i_boxed_5016_ = lean_unbox_usize(v_i_5013_);
lean_dec(v_i_5013_);
v_res_5017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_5015_, v_i_boxed_5016_, v_bs_5014_);
return v_res_5017_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5019_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5020_ = l_Lean_stringToMessageData(v___x_5019_);
return v___x_5020_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5022_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5023_ = l_Lean_stringToMessageData(v___x_5022_);
return v___x_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_){
_start:
{
lean_object* v___x_5035_; lean_object* v_decls_5036_; lean_object* v_funVals_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5077_; 
v___x_5035_ = lean_st_ref_take(v_a_5026_);
v_decls_5036_ = lean_ctor_get(v_a_5025_, 0);
v_funVals_5037_ = lean_ctor_get(v___x_5035_, 1);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5077_ == 0)
{
lean_object* v_unused_5078_; 
v_unused_5078_ = lean_ctor_get(v___x_5035_, 0);
lean_dec(v_unused_5078_);
v___x_5039_ = v___x_5035_;
v_isShared_5040_ = v_isSharedCheck_5077_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_funVals_5037_);
lean_dec(v___x_5035_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5077_;
goto v_resetjp_5038_;
}
v___jp_5032_:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = lean_box(0);
v___x_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5033_);
return v___x_5034_;
}
v_resetjp_5038_:
{
size_t v_sz_5041_; size_t v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5045_; 
v_sz_5041_ = lean_array_size(v_decls_5036_);
v___x_5042_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5036_);
v___x_5043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5041_, v___x_5042_, v_decls_5036_);
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5043_);
v___x_5045_ = v___x_5039_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5043_);
lean_ctor_set(v_reuseFailAlloc_5076_, 1, v_funVals_5037_);
v___x_5045_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5046_ = lean_st_ref_put(v_a_5026_, v___x_5045_);
v___x_5047_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; uint8_t v___x_5049_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
v___x_5049_ = lean_unbox(v_a_5048_);
lean_dec(v_a_5048_);
if (v___x_5049_ == 0)
{
lean_object* v_toCold_5050_; lean_object* v_options_5051_; uint8_t v_hasTrace_5052_; 
v_toCold_5050_ = lean_ctor_get(v_a_5029_, 0);
v_options_5051_ = lean_ctor_get(v_toCold_5050_, 2);
v_hasTrace_5052_ = lean_ctor_get_uint8(v_options_5051_, sizeof(void*)*1);
if (v_hasTrace_5052_ == 0)
{
lean_dec(v_n_5024_);
goto v___jp_5032_;
}
else
{
lean_object* v_inheritedTraceOptions_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; uint8_t v___x_5056_; 
v_inheritedTraceOptions_5053_ = lean_ctor_get(v_toCold_5050_, 11);
v___x_5054_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5055_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5056_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5053_, v_options_5051_, v___x_5055_);
if (v___x_5056_ == 0)
{
lean_dec(v_n_5024_);
goto v___jp_5032_;
}
else
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5057_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5058_ = l_Nat_reprFast(v_n_5024_);
v___x_5059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5058_);
v___x_5060_ = l_Lean_MessageData_ofFormat(v___x_5059_);
v___x_5061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5057_);
lean_ctor_set(v___x_5061_, 1, v___x_5060_);
v___x_5062_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5061_);
lean_ctor_set(v___x_5063_, 1, v___x_5062_);
v___x_5064_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5054_, v___x_5063_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_dec_ref_known(v___x_5064_, 1);
goto v___jp_5032_;
}
else
{
return v___x_5064_;
}
}
}
}
else
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = lean_unsigned_to_nat(1u);
v___x_5066_ = lean_nat_add(v_n_5024_, v___x_5065_);
lean_dec(v_n_5024_);
v_n_5024_ = v___x_5066_;
goto _start;
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec(v_n_5024_);
v_a_5068_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5047_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5047_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_);
lean_dec(v_a_5085_);
lean_dec_ref(v_a_5084_);
lean_dec(v_a_5083_);
lean_dec_ref(v_a_5082_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
return v_res_5087_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5088_; lean_object* v___x_5089_; 
v___x_5088_ = 0;
v___x_5089_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5090_){
_start:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5091_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5092_ = lean_panic_fn_borrowed(v___x_5091_, v_msg_5090_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5093_, lean_object* v_msg_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v_toCold_5100_; lean_object* v_ref_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v_toCold_5100_ = lean_ctor_get(v___y_5097_, 0);
v_ref_5101_ = lean_ctor_get(v___y_5097_, 2);
v___x_5102_ = lean_st_ref_get(v___y_5098_);
v___x_5103_ = lean_st_ref_get(v___y_5096_);
v___x_5104_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5095_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5164_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5107_ = v___x_5104_;
v_isShared_5108_ = v_isSharedCheck_5164_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___x_5104_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5164_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v_env_5109_; lean_object* v_lctx_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5162_; 
v_env_5109_ = lean_ctor_get(v___x_5102_, 0);
lean_inc_ref(v_env_5109_);
lean_dec(v___x_5102_);
v_lctx_5110_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5162_ == 0)
{
lean_object* v_unused_5163_; 
v_unused_5163_ = lean_ctor_get(v___x_5103_, 1);
lean_dec(v_unused_5163_);
v___x_5112_ = v___x_5103_;
v_isShared_5113_ = v_isSharedCheck_5162_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_lctx_5110_);
lean_dec(v___x_5103_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5162_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v_options_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v_traceState_5117_; lean_object* v_env_5118_; lean_object* v_nextMacroScope_5119_; lean_object* v_ngen_5120_; lean_object* v_auxDeclNGen_5121_; lean_object* v_cache_5122_; lean_object* v_messages_5123_; lean_object* v_infoState_5124_; lean_object* v_snapshotTasks_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5161_; 
v_options_5114_ = lean_ctor_get(v_toCold_5100_, 2);
v___x_5115_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_5116_ = lean_st_ref_take(v___y_5098_);
v_traceState_5117_ = lean_ctor_get(v___x_5116_, 4);
v_env_5118_ = lean_ctor_get(v___x_5116_, 0);
v_nextMacroScope_5119_ = lean_ctor_get(v___x_5116_, 1);
v_ngen_5120_ = lean_ctor_get(v___x_5116_, 2);
v_auxDeclNGen_5121_ = lean_ctor_get(v___x_5116_, 3);
v_cache_5122_ = lean_ctor_get(v___x_5116_, 5);
v_messages_5123_ = lean_ctor_get(v___x_5116_, 6);
v_infoState_5124_ = lean_ctor_get(v___x_5116_, 7);
v_snapshotTasks_5125_ = lean_ctor_get(v___x_5116_, 8);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5127_ = v___x_5116_;
v_isShared_5128_ = v_isSharedCheck_5161_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_snapshotTasks_5125_);
lean_inc(v_infoState_5124_);
lean_inc(v_messages_5123_);
lean_inc(v_cache_5122_);
lean_inc(v_traceState_5117_);
lean_inc(v_auxDeclNGen_5121_);
lean_inc(v_ngen_5120_);
lean_inc(v_nextMacroScope_5119_);
lean_inc(v_env_5118_);
lean_dec(v___x_5116_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5161_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
uint64_t v_tid_5129_; lean_object* v_traces_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5160_; 
v_tid_5129_ = lean_ctor_get_uint64(v_traceState_5117_, sizeof(void*)*1);
v_traces_5130_ = lean_ctor_get(v_traceState_5117_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v_traceState_5117_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5132_ = v_traceState_5117_;
v_isShared_5133_ = v_isSharedCheck_5160_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_traces_5130_);
lean_dec(v_traceState_5117_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5160_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
uint8_t v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5138_; 
v___x_5134_ = lean_unbox(v_a_5105_);
lean_dec(v_a_5105_);
v___x_5135_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5110_, v___x_5134_);
lean_dec_ref(v_lctx_5110_);
lean_inc_ref(v_options_5114_);
v___x_5136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5136_, 0, v_env_5109_);
lean_ctor_set(v___x_5136_, 1, v___x_5115_);
lean_ctor_set(v___x_5136_, 2, v___x_5135_);
lean_ctor_set(v___x_5136_, 3, v_options_5114_);
if (v_isShared_5113_ == 0)
{
lean_ctor_set_tag(v___x_5112_, 3);
lean_ctor_set(v___x_5112_, 1, v_msg_5094_);
lean_ctor_set(v___x_5112_, 0, v___x_5136_);
v___x_5138_ = v___x_5112_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5159_, 1, v_msg_5094_);
v___x_5138_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
lean_object* v___x_5139_; double v___x_5140_; uint8_t v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5149_; 
v___x_5139_ = lean_box(0);
v___x_5140_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5141_ = 0;
v___x_5142_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5143_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5143_, 0, v_cls_5093_);
lean_ctor_set(v___x_5143_, 1, v___x_5139_);
lean_ctor_set(v___x_5143_, 2, v___x_5142_);
lean_ctor_set_float(v___x_5143_, sizeof(void*)*3, v___x_5140_);
lean_ctor_set_float(v___x_5143_, sizeof(void*)*3 + 8, v___x_5140_);
lean_ctor_set_uint8(v___x_5143_, sizeof(void*)*3 + 16, v___x_5141_);
v___x_5144_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5145_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5143_);
lean_ctor_set(v___x_5145_, 1, v___x_5138_);
lean_ctor_set(v___x_5145_, 2, v___x_5144_);
lean_inc(v_ref_5101_);
v___x_5146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5146_, 0, v_ref_5101_);
lean_ctor_set(v___x_5146_, 1, v___x_5145_);
v___x_5147_ = l_Lean_PersistentArray_push___redArg(v_traces_5130_, v___x_5146_);
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 0, v___x_5147_);
v___x_5149_ = v___x_5132_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5147_);
lean_ctor_set_uint64(v_reuseFailAlloc_5158_, sizeof(void*)*1, v_tid_5129_);
v___x_5149_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
lean_object* v___x_5151_; 
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 4, v___x_5149_);
v___x_5151_ = v___x_5127_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_env_5118_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v_nextMacroScope_5119_);
lean_ctor_set(v_reuseFailAlloc_5157_, 2, v_ngen_5120_);
lean_ctor_set(v_reuseFailAlloc_5157_, 3, v_auxDeclNGen_5121_);
lean_ctor_set(v_reuseFailAlloc_5157_, 4, v___x_5149_);
lean_ctor_set(v_reuseFailAlloc_5157_, 5, v_cache_5122_);
lean_ctor_set(v_reuseFailAlloc_5157_, 6, v_messages_5123_);
lean_ctor_set(v_reuseFailAlloc_5157_, 7, v_infoState_5124_);
lean_ctor_set(v_reuseFailAlloc_5157_, 8, v_snapshotTasks_5125_);
v___x_5151_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5155_; 
v___x_5152_ = lean_st_ref_put(v___y_5098_, v___x_5151_);
v___x_5153_ = lean_box(0);
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v___x_5153_);
v___x_5155_ = v___x_5107_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5153_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
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
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec(v___x_5103_);
lean_dec(v___x_5102_);
lean_dec_ref(v_msg_5094_);
lean_dec(v_cls_5093_);
v_a_5165_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5104_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5104_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5173_, lean_object* v_msg_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5173_, v_msg_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5181_, size_t v_i_5182_, size_t v_stop_5183_, lean_object* v_b_5184_){
_start:
{
uint8_t v___x_5186_; 
v___x_5186_ = lean_usize_dec_eq(v_i_5182_, v_stop_5183_);
if (v___x_5186_ == 0)
{
lean_object* v_fst_5187_; lean_object* v_snd_5188_; lean_object* v___x_5189_; lean_object* v_snd_5190_; lean_object* v_fst_5191_; lean_object* v_fst_5192_; lean_object* v_snd_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5208_; 
v_fst_5187_ = lean_ctor_get(v_b_5184_, 0);
lean_inc(v_fst_5187_);
v_snd_5188_ = lean_ctor_get(v_b_5184_, 1);
lean_inc(v_snd_5188_);
lean_dec_ref(v_b_5184_);
v___x_5189_ = lean_array_uget_borrowed(v_as_5181_, v_i_5182_);
v_snd_5190_ = lean_ctor_get(v___x_5189_, 1);
lean_inc(v_snd_5190_);
v_fst_5191_ = lean_ctor_get(v___x_5189_, 0);
v_fst_5192_ = lean_ctor_get(v_snd_5190_, 0);
v_snd_5193_ = lean_ctor_get(v_snd_5190_, 1);
v_isSharedCheck_5208_ = !lean_is_exclusive(v_snd_5190_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5195_ = v_snd_5190_;
v_isShared_5196_ = v_isSharedCheck_5208_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_snd_5193_);
lean_inc(v_fst_5192_);
lean_dec(v_snd_5190_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5208_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v_fvarId_5197_; uint8_t v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5203_; 
v_fvarId_5197_ = lean_ctor_get(v_fst_5191_, 0);
v___x_5198_ = 0;
v___x_5199_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5198_, v_fst_5192_, v_fst_5187_);
lean_dec(v_fst_5192_);
v___x_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5200_, 0, v_snd_5193_);
lean_inc(v_fvarId_5197_);
v___x_5201_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5188_, v_fvarId_5197_, v___x_5200_);
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 1, v___x_5201_);
lean_ctor_set(v___x_5195_, 0, v___x_5199_);
v___x_5203_ = v___x_5195_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v___x_5199_);
lean_ctor_set(v_reuseFailAlloc_5207_, 1, v___x_5201_);
v___x_5203_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
size_t v___x_5204_; size_t v___x_5205_; 
v___x_5204_ = ((size_t)1ULL);
v___x_5205_ = lean_usize_add(v_i_5182_, v___x_5204_);
v_i_5182_ = v___x_5205_;
v_b_5184_ = v___x_5203_;
goto _start;
}
}
}
else
{
lean_object* v___x_5209_; 
v___x_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5209_, 0, v_b_5184_);
return v___x_5209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5210_, lean_object* v_i_5211_, lean_object* v_stop_5212_, lean_object* v_b_5213_, lean_object* v___y_5214_){
_start:
{
size_t v_i_boxed_5215_; size_t v_stop_boxed_5216_; lean_object* v_res_5217_; 
v_i_boxed_5215_ = lean_unbox_usize(v_i_5211_);
lean_dec(v_i_5211_);
v_stop_boxed_5216_ = lean_unbox_usize(v_stop_5212_);
lean_dec(v_stop_5212_);
v_res_5217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5210_, v_i_boxed_5215_, v_stop_boxed_5216_, v_b_5213_);
lean_dec_ref(v_as_5210_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5218_, lean_object* v_x_5219_){
_start:
{
if (lean_obj_tag(v_x_5219_) == 0)
{
lean_object* v___x_5220_; 
v___x_5220_ = lean_box(0);
return v___x_5220_;
}
else
{
lean_object* v_key_5221_; lean_object* v_value_5222_; lean_object* v_tail_5223_; uint8_t v___x_5224_; 
v_key_5221_ = lean_ctor_get(v_x_5219_, 0);
v_value_5222_ = lean_ctor_get(v_x_5219_, 1);
v_tail_5223_ = lean_ctor_get(v_x_5219_, 2);
v___x_5224_ = l_Lean_instBEqFVarId_beq(v_key_5221_, v_a_5218_);
if (v___x_5224_ == 0)
{
v_x_5219_ = v_tail_5223_;
goto _start;
}
else
{
lean_object* v___x_5226_; 
lean_inc(v_value_5222_);
v___x_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5226_, 0, v_value_5222_);
return v___x_5226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5227_, lean_object* v_x_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5227_, v_x_5228_);
lean_dec(v_x_5228_);
lean_dec(v_a_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5230_, lean_object* v_a_5231_){
_start:
{
lean_object* v_buckets_5232_; lean_object* v___x_5233_; uint64_t v___x_5234_; uint64_t v___x_5235_; uint64_t v___x_5236_; uint64_t v_fold_5237_; uint64_t v___x_5238_; uint64_t v___x_5239_; uint64_t v___x_5240_; size_t v___x_5241_; size_t v___x_5242_; size_t v___x_5243_; size_t v___x_5244_; size_t v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v_buckets_5232_ = lean_ctor_get(v_m_5230_, 1);
v___x_5233_ = lean_array_get_size(v_buckets_5232_);
v___x_5234_ = l_Lean_instHashableFVarId_hash(v_a_5231_);
v___x_5235_ = 32ULL;
v___x_5236_ = lean_uint64_shift_right(v___x_5234_, v___x_5235_);
v_fold_5237_ = lean_uint64_xor(v___x_5234_, v___x_5236_);
v___x_5238_ = 16ULL;
v___x_5239_ = lean_uint64_shift_right(v_fold_5237_, v___x_5238_);
v___x_5240_ = lean_uint64_xor(v_fold_5237_, v___x_5239_);
v___x_5241_ = lean_uint64_to_usize(v___x_5240_);
v___x_5242_ = lean_usize_of_nat(v___x_5233_);
v___x_5243_ = ((size_t)1ULL);
v___x_5244_ = lean_usize_sub(v___x_5242_, v___x_5243_);
v___x_5245_ = lean_usize_land(v___x_5241_, v___x_5244_);
v___x_5246_ = lean_array_uget_borrowed(v_buckets_5232_, v___x_5245_);
v___x_5247_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5231_, v___x_5246_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5248_, v_a_5249_);
lean_dec(v_a_5249_);
lean_dec_ref(v_m_5248_);
return v_res_5250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5251_, lean_object* v_as_5252_, size_t v_i_5253_, size_t v_stop_5254_, lean_object* v_b_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_a_5262_; uint8_t v___x_5266_; 
v___x_5266_ = lean_usize_dec_eq(v_i_5253_, v_stop_5254_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; lean_object* v_fvarId_5268_; lean_object* v___x_5269_; 
v___x_5267_ = lean_array_uget_borrowed(v_as_5252_, v_i_5253_);
v_fvarId_5268_ = lean_ctor_get(v___x_5267_, 0);
v___x_5269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5251_, v_fvarId_5268_);
if (lean_obj_tag(v___x_5269_) == 1)
{
lean_object* v_val_5270_; lean_object* v___x_5271_; 
v_val_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_val_5270_);
lean_dec_ref_known(v___x_5269_, 1);
v___x_5271_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5270_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
lean_inc(v_a_5272_);
lean_dec_ref_known(v___x_5271_, 1);
if (lean_obj_tag(v_a_5272_) == 1)
{
lean_object* v_val_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; 
v_val_5273_ = lean_ctor_get(v_a_5272_, 0);
lean_inc(v_val_5273_);
lean_dec_ref_known(v_a_5272_, 1);
lean_inc(v___x_5267_);
v___x_5274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5267_);
lean_ctor_set(v___x_5274_, 1, v_val_5273_);
v___x_5275_ = lean_array_push(v_b_5255_, v___x_5274_);
v_a_5262_ = v___x_5275_;
goto v___jp_5261_;
}
else
{
lean_dec(v_a_5272_);
v_a_5262_ = v_b_5255_;
goto v___jp_5261_;
}
}
else
{
lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5283_; 
lean_dec_ref(v_b_5255_);
v_a_5276_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5278_ = v___x_5271_;
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_dec(v___x_5271_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5281_; 
if (v_isShared_5279_ == 0)
{
v___x_5281_ = v___x_5278_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
v___x_5281_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
return v___x_5281_;
}
}
}
}
else
{
lean_dec(v___x_5269_);
v_a_5262_ = v_b_5255_;
goto v___jp_5261_;
}
}
else
{
lean_object* v___x_5284_; 
v___x_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5284_, 0, v_b_5255_);
return v___x_5284_;
}
v___jp_5261_:
{
size_t v___x_5263_; size_t v___x_5264_; 
v___x_5263_ = ((size_t)1ULL);
v___x_5264_ = lean_usize_add(v_i_5253_, v___x_5263_);
v_i_5253_ = v___x_5264_;
v_b_5255_ = v_a_5262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5285_, lean_object* v_as_5286_, lean_object* v_i_5287_, lean_object* v_stop_5288_, lean_object* v_b_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
size_t v_i_boxed_5295_; size_t v_stop_boxed_5296_; lean_object* v_res_5297_; 
v_i_boxed_5295_ = lean_unbox_usize(v_i_5287_);
lean_dec(v_i_5287_);
v_stop_boxed_5296_ = lean_unbox_usize(v_stop_5288_);
lean_dec(v_stop_5288_);
v_res_5297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5285_, v_as_5286_, v_i_boxed_5295_, v_stop_boxed_5296_, v_b_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
lean_dec_ref(v_as_5286_);
lean_dec_ref(v_assignment_5285_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5300_, lean_object* v_as_5301_, lean_object* v_start_5302_, lean_object* v_stop_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_){
_start:
{
lean_object* v___x_5309_; uint8_t v___x_5310_; 
v___x_5309_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5310_ = lean_nat_dec_lt(v_start_5302_, v_stop_5303_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5309_);
return v___x_5311_;
}
else
{
lean_object* v___x_5312_; uint8_t v___x_5313_; 
v___x_5312_ = lean_array_get_size(v_as_5301_);
v___x_5313_ = lean_nat_dec_le(v_stop_5303_, v___x_5312_);
if (v___x_5313_ == 0)
{
uint8_t v___x_5314_; 
v___x_5314_ = lean_nat_dec_lt(v_start_5302_, v___x_5312_);
if (v___x_5314_ == 0)
{
lean_object* v___x_5315_; 
v___x_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5315_, 0, v___x_5309_);
return v___x_5315_;
}
else
{
size_t v___x_5316_; size_t v___x_5317_; lean_object* v___x_5318_; 
v___x_5316_ = lean_usize_of_nat(v_start_5302_);
v___x_5317_ = lean_usize_of_nat(v___x_5312_);
v___x_5318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5300_, v_as_5301_, v___x_5316_, v___x_5317_, v___x_5309_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
return v___x_5318_;
}
}
else
{
size_t v___x_5319_; size_t v___x_5320_; lean_object* v___x_5321_; 
v___x_5319_ = lean_usize_of_nat(v_start_5302_);
v___x_5320_ = lean_usize_of_nat(v_stop_5303_);
v___x_5321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5300_, v_as_5301_, v___x_5319_, v___x_5320_, v___x_5309_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
return v___x_5321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5322_, lean_object* v_as_5323_, lean_object* v_start_5324_, lean_object* v_stop_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5322_, v_as_5323_, v_start_5324_, v_stop_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec(v_stop_5325_);
lean_dec(v_start_5324_);
lean_dec_ref(v_as_5323_);
lean_dec_ref(v_assignment_5322_);
return v_res_5331_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5334_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5335_ = lean_unsigned_to_nat(9u);
v___x_5336_ = lean_unsigned_to_nat(641u);
v___x_5337_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5339_ = l_mkPanicMessageWithDecl(v___x_5338_, v___x_5337_, v___x_5336_, v___x_5335_, v___x_5334_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5342_, lean_object* v_discrVal_5343_, lean_object* v_discr_5344_, lean_object* v_assignment_5345_, lean_object* v_i_5346_, lean_object* v_as_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
lean_object* v___x_5353_; uint8_t v___x_5354_; 
v___x_5353_ = lean_array_get_size(v_as_5347_);
v___x_5354_ = lean_nat_dec_lt(v_i_5346_, v___x_5353_);
if (v___x_5354_ == 0)
{
lean_object* v___x_5355_; 
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v___x_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5355_, 0, v_as_5347_);
return v___x_5355_;
}
else
{
lean_object* v_a_5356_; lean_object* v_a_5358_; 
v_a_5356_ = lean_array_fget_borrowed(v_as_5347_, v_i_5346_);
if (lean_obj_tag(v_a_5356_) == 0)
{
lean_object* v_ctorName_5369_; lean_object* v_params_5370_; lean_object* v_code_5371_; uint8_t v___x_5372_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v___y_5388_; uint8_t v___x_5392_; 
v_ctorName_5369_ = lean_ctor_get(v_a_5356_, 0);
v_params_5370_ = lean_ctor_get(v_a_5356_, 1);
v_code_5371_ = lean_ctor_get(v_a_5356_, 2);
v___x_5372_ = 0;
v___x_5392_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5343_, v_ctorName_5369_);
if (v___x_5392_ == 0)
{
lean_object* v_toCold_5393_; lean_object* v_options_5394_; uint8_t v_hasTrace_5395_; 
v_toCold_5393_ = lean_ctor_get(v___y_5350_, 0);
v_options_5394_ = lean_ctor_get(v_toCold_5393_, 2);
v_hasTrace_5395_ = lean_ctor_get_uint8(v_options_5394_, sizeof(void*)*1);
if (v_hasTrace_5395_ == 0)
{
v___y_5388_ = v___y_5349_;
goto v___jp_5387_;
}
else
{
lean_object* v_inheritedTraceOptions_5396_; lean_object* v_cls_5397_; lean_object* v___x_5398_; uint8_t v___x_5399_; 
v_inheritedTraceOptions_5396_ = lean_ctor_get(v_toCold_5393_, 11);
v_cls_5397_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5398_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5396_, v_options_5394_, v___x_5398_);
if (v___x_5399_ == 0)
{
v___y_5388_ = v___y_5349_;
goto v___jp_5387_;
}
else
{
lean_object* v___x_5400_; 
lean_inc(v_discr_5344_);
v___x_5400_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5344_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v_a_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
lean_inc(v_a_5401_);
lean_dec_ref_known(v___x_5400_, 1);
v___x_5402_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5401_, v___x_5399_);
v___x_5404_ = lean_string_append(v___x_5402_, v___x_5403_);
lean_dec_ref(v___x_5403_);
v___x_5405_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5406_ = lean_string_append(v___x_5404_, v___x_5405_);
lean_inc(v_ctorName_5369_);
v___x_5407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5369_, v___x_5399_);
v___x_5408_ = lean_string_append(v___x_5406_, v___x_5407_);
lean_dec_ref(v___x_5407_);
v___x_5409_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5408_);
v___x_5410_ = l_Lean_MessageData_ofFormat(v___x_5409_);
v___x_5411_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5397_, v___x_5410_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5411_) == 0)
{
lean_dec_ref_known(v___x_5411_, 1);
v___y_5388_ = v___y_5349_;
goto v___jp_5387_;
}
else
{
lean_object* v_a_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5419_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5412_ = lean_ctor_get(v___x_5411_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5414_ = v___x_5411_;
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_a_5412_);
lean_dec(v___x_5411_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v___x_5417_; 
if (v_isShared_5415_ == 0)
{
v___x_5417_ = v___x_5414_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_a_5412_);
v___x_5417_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
return v___x_5417_;
}
}
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5427_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5420_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5422_ = v___x_5400_;
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5400_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5425_; 
if (v_isShared_5423_ == 0)
{
v___x_5425_ = v___x_5422_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5420_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
}
}
else
{
lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5428_ = lean_unsigned_to_nat(0u);
v___x_5429_ = lean_array_get_size(v_params_5370_);
v___x_5430_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5345_, v_params_5370_, v___x_5428_, v___x_5429_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5444_; uint8_t v___x_5445_; lean_object* v_fst_5447_; lean_object* v_snd_5448_; lean_object* v___y_5461_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
lean_inc(v_a_5431_);
lean_dec_ref_known(v___x_5430_, 1);
v___x_5444_ = lean_array_get_size(v_a_5431_);
v___x_5445_ = lean_nat_dec_eq(v___x_5444_, v___x_5428_);
if (v___x_5445_ == 0)
{
if (v___x_5392_ == 0)
{
lean_dec(v_a_5431_);
goto v___jp_5432_;
}
else
{
lean_object* v___x_5473_; 
lean_inc_ref(v_code_5371_);
v___x_5473_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5345_, v_code_5371_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; lean_object* v___x_5475_; uint8_t v___x_5476_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
lean_inc(v_a_5474_);
lean_dec_ref_known(v___x_5473_, 1);
v___x_5475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5476_ = lean_nat_dec_lt(v___x_5428_, v___x_5444_);
if (v___x_5476_ == 0)
{
lean_dec(v_a_5431_);
v_fst_5447_ = v_a_5474_;
v_snd_5448_ = v___x_5475_;
goto v___jp_5446_;
}
else
{
lean_object* v___x_5477_; uint8_t v___x_5478_; 
lean_inc(v_a_5474_);
v___x_5477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5477_, 0, v_a_5474_);
lean_ctor_set(v___x_5477_, 1, v___x_5475_);
v___x_5478_ = lean_nat_dec_le(v___x_5444_, v___x_5444_);
if (v___x_5478_ == 0)
{
if (v___x_5476_ == 0)
{
lean_dec_ref_known(v___x_5477_, 2);
lean_dec(v_a_5431_);
v_fst_5447_ = v_a_5474_;
v_snd_5448_ = v___x_5475_;
goto v___jp_5446_;
}
else
{
size_t v___x_5479_; size_t v___x_5480_; lean_object* v___x_5481_; 
lean_dec(v_a_5474_);
v___x_5479_ = ((size_t)0ULL);
v___x_5480_ = lean_usize_of_nat(v___x_5444_);
v___x_5481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5431_, v___x_5479_, v___x_5480_, v___x_5477_);
lean_dec(v_a_5431_);
v___y_5461_ = v___x_5481_;
goto v___jp_5460_;
}
}
else
{
size_t v___x_5482_; size_t v___x_5483_; lean_object* v___x_5484_; 
lean_dec(v_a_5474_);
v___x_5482_ = ((size_t)0ULL);
v___x_5483_ = lean_usize_of_nat(v___x_5444_);
v___x_5484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5431_, v___x_5482_, v___x_5483_, v___x_5477_);
lean_dec(v_a_5431_);
v___y_5461_ = v___x_5484_;
goto v___jp_5460_;
}
}
}
else
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5492_; 
lean_dec(v_a_5431_);
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5485_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5487_ = v___x_5473_;
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v___x_5473_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5488_ == 0)
{
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
}
else
{
lean_dec(v_a_5431_);
goto v___jp_5432_;
}
v___jp_5432_:
{
lean_object* v___x_5433_; 
lean_inc_ref(v_code_5371_);
v___x_5433_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5345_, v_code_5371_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; lean_object* v___x_5435_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_a_5434_);
lean_dec_ref_known(v___x_5433_, 1);
lean_inc_ref(v_a_5356_);
v___x_5435_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5356_, v_a_5434_);
v_a_5358_ = v___x_5435_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5443_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5436_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5443_ == 0)
{
v___x_5438_ = v___x_5433_;
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_dec(v___x_5433_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5439_ == 0)
{
v___x_5441_ = v___x_5438_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5436_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
}
}
v___jp_5446_:
{
lean_object* v___x_5449_; 
v___x_5449_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5372_, v_fst_5447_, v_snd_5448_, v___x_5445_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
lean_dec_ref(v_snd_5448_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5451_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_a_5450_);
lean_dec_ref_known(v___x_5449_, 1);
lean_inc_ref(v_a_5356_);
v___x_5451_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5356_, v_a_5450_);
v_a_5358_ = v___x_5451_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5459_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5452_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5459_ == 0)
{
v___x_5454_ = v___x_5449_;
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v___x_5449_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5457_; 
if (v_isShared_5455_ == 0)
{
v___x_5457_ = v___x_5454_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5452_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
}
v___jp_5460_:
{
if (lean_obj_tag(v___y_5461_) == 0)
{
lean_object* v_a_5462_; lean_object* v_fst_5463_; lean_object* v_snd_5464_; 
v_a_5462_ = lean_ctor_get(v___y_5461_, 0);
lean_inc(v_a_5462_);
lean_dec_ref_known(v___y_5461_, 1);
v_fst_5463_ = lean_ctor_get(v_a_5462_, 0);
lean_inc(v_fst_5463_);
v_snd_5464_ = lean_ctor_get(v_a_5462_, 1);
lean_inc(v_snd_5464_);
lean_dec(v_a_5462_);
v_fst_5447_ = v_fst_5463_;
v_snd_5448_ = v_snd_5464_;
goto v___jp_5446_;
}
else
{
lean_object* v_a_5465_; lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5472_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5465_ = lean_ctor_get(v___y_5461_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___y_5461_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5467_ = v___y_5461_;
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
else
{
lean_inc(v_a_5465_);
lean_dec(v___y_5461_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v___x_5470_; 
if (v_isShared_5468_ == 0)
{
v___x_5470_ = v___x_5467_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_a_5465_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5500_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5493_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5500_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5495_ = v___x_5430_;
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5430_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5498_; 
if (v_isShared_5496_ == 0)
{
v___x_5498_ = v___x_5495_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
v___jp_5373_:
{
lean_object* v___x_5376_; 
v___x_5376_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5372_, v___y_5375_, v___y_5374_);
lean_dec_ref(v___y_5375_);
if (lean_obj_tag(v___x_5376_) == 0)
{
lean_object* v___x_5377_; lean_object* v___x_5378_; 
lean_dec_ref_known(v___x_5376_, 1);
lean_inc_ref(v_resultType_5342_);
v___x_5377_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5377_, 0, v_resultType_5342_);
lean_inc_ref(v_a_5356_);
v___x_5378_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5356_, v___x_5377_);
v_a_5358_ = v___x_5378_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5386_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5379_ = lean_ctor_get(v___x_5376_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5376_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5381_ = v___x_5376_;
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_a_5379_);
lean_dec(v___x_5376_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5384_; 
if (v_isShared_5382_ == 0)
{
v___x_5384_ = v___x_5381_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5379_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
}
}
}
}
v___jp_5387_:
{
switch(lean_obj_tag(v_a_5356_))
{
case 0:
{
lean_object* v_code_5389_; 
v_code_5389_ = lean_ctor_get(v_a_5356_, 2);
lean_inc_ref(v_code_5389_);
v___y_5374_ = v___y_5388_;
v___y_5375_ = v_code_5389_;
goto v___jp_5373_;
}
case 1:
{
lean_object* v_code_5390_; 
v_code_5390_ = lean_ctor_get(v_a_5356_, 1);
lean_inc_ref(v_code_5390_);
v___y_5374_ = v___y_5388_;
v___y_5375_ = v_code_5390_;
goto v___jp_5373_;
}
default: 
{
lean_object* v_code_5391_; 
v_code_5391_ = lean_ctor_get(v_a_5356_, 0);
lean_inc_ref(v_code_5391_);
v___y_5374_ = v___y_5388_;
v___y_5375_ = v_code_5391_;
goto v___jp_5373_;
}
}
}
}
else
{
lean_object* v_code_5501_; lean_object* v___x_5502_; 
v_code_5501_ = lean_ctor_get(v_a_5356_, 0);
lean_inc_ref(v_code_5501_);
v___x_5502_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5345_, v_code_5501_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v___x_5504_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
lean_dec_ref_known(v___x_5502_, 1);
lean_inc_ref(v_a_5356_);
v___x_5504_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5356_, v_a_5503_);
v_a_5358_ = v___x_5504_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5512_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5505_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5507_ = v___x_5502_;
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5502_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
v___jp_5357_:
{
size_t v___x_5359_; size_t v___x_5360_; uint8_t v___x_5361_; 
v___x_5359_ = lean_ptr_addr(v_a_5356_);
v___x_5360_ = lean_ptr_addr(v_a_5358_);
v___x_5361_ = lean_usize_dec_eq(v___x_5359_, v___x_5360_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
v___x_5362_ = lean_unsigned_to_nat(1u);
v___x_5363_ = lean_nat_add(v_i_5346_, v___x_5362_);
v___x_5364_ = lean_array_fset(v_as_5347_, v_i_5346_, v_a_5358_);
lean_dec(v_i_5346_);
v_i_5346_ = v___x_5363_;
v_as_5347_ = v___x_5364_;
goto _start;
}
else
{
lean_object* v___x_5366_; lean_object* v___x_5367_; 
lean_dec_ref(v_a_5358_);
v___x_5366_ = lean_unsigned_to_nat(1u);
v___x_5367_ = lean_nat_add(v_i_5346_, v___x_5366_);
lean_dec(v_i_5346_);
v_i_5346_ = v___x_5367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5513_, lean_object* v_code_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_){
_start:
{
lean_object* v_decl_5521_; lean_object* v_k_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; 
switch(lean_obj_tag(v_code_5514_))
{
case 0:
{
lean_object* v_decl_5634_; lean_object* v_k_5635_; lean_object* v___x_5636_; 
v_decl_5634_ = lean_ctor_get(v_code_5514_, 0);
v_k_5635_ = lean_ctor_get(v_code_5514_, 1);
lean_inc_ref(v_k_5635_);
v___x_5636_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5513_, v_k_5635_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_);
if (lean_obj_tag(v___x_5636_) == 0)
{
lean_object* v_a_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5673_; 
v_a_5637_ = lean_ctor_get(v___x_5636_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5636_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5639_ = v___x_5636_;
v_isShared_5640_ = v_isSharedCheck_5673_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_a_5637_);
lean_dec(v___x_5636_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5673_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
size_t v___x_5641_; size_t v___x_5642_; uint8_t v___x_5643_; 
v___x_5641_ = lean_ptr_addr(v_k_5635_);
v___x_5642_ = lean_ptr_addr(v_a_5637_);
v___x_5643_ = lean_usize_dec_eq(v___x_5641_, v___x_5642_);
if (v___x_5643_ == 0)
{
lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5653_; 
lean_inc_ref(v_decl_5634_);
v_isSharedCheck_5653_ = !lean_is_exclusive(v_code_5514_);
if (v_isSharedCheck_5653_ == 0)
{
lean_object* v_unused_5654_; lean_object* v_unused_5655_; 
v_unused_5654_ = lean_ctor_get(v_code_5514_, 1);
lean_dec(v_unused_5654_);
v_unused_5655_ = lean_ctor_get(v_code_5514_, 0);
lean_dec(v_unused_5655_);
v___x_5645_ = v_code_5514_;
v_isShared_5646_ = v_isSharedCheck_5653_;
goto v_resetjp_5644_;
}
else
{
lean_dec(v_code_5514_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5653_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 1, v_a_5637_);
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_decl_5634_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_a_5637_);
v___x_5648_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
lean_object* v___x_5650_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 0, v___x_5648_);
v___x_5650_ = v___x_5639_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
}
else
{
size_t v___x_5656_; uint8_t v___x_5657_; 
v___x_5656_ = lean_ptr_addr(v_decl_5634_);
v___x_5657_ = lean_usize_dec_eq(v___x_5656_, v___x_5656_);
if (v___x_5657_ == 0)
{
lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5667_; 
lean_inc_ref(v_decl_5634_);
v_isSharedCheck_5667_ = !lean_is_exclusive(v_code_5514_);
if (v_isSharedCheck_5667_ == 0)
{
lean_object* v_unused_5668_; lean_object* v_unused_5669_; 
v_unused_5668_ = lean_ctor_get(v_code_5514_, 1);
lean_dec(v_unused_5668_);
v_unused_5669_ = lean_ctor_get(v_code_5514_, 0);
lean_dec(v_unused_5669_);
v___x_5659_ = v_code_5514_;
v_isShared_5660_ = v_isSharedCheck_5667_;
goto v_resetjp_5658_;
}
else
{
lean_dec(v_code_5514_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5667_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5662_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 1, v_a_5637_);
v___x_5662_ = v___x_5659_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_decl_5634_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_a_5637_);
v___x_5662_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5664_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 0, v___x_5662_);
v___x_5664_ = v___x_5639_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v___x_5662_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
else
{
lean_object* v___x_5671_; 
lean_dec(v_a_5637_);
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 0, v_code_5514_);
v___x_5671_ = v___x_5639_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_code_5514_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_5514_, 2);
return v___x_5636_;
}
}
case 1:
{
lean_object* v_decl_5674_; lean_object* v_k_5675_; 
v_decl_5674_ = lean_ctor_get(v_code_5514_, 0);
v_k_5675_ = lean_ctor_get(v_code_5514_, 1);
lean_inc_ref(v_k_5675_);
lean_inc_ref(v_decl_5674_);
v_decl_5521_ = v_decl_5674_;
v_k_5522_ = v_k_5675_;
v___y_5523_ = v_a_5515_;
v___y_5524_ = v_a_5516_;
v___y_5525_ = v_a_5517_;
v___y_5526_ = v_a_5518_;
goto v___jp_5520_;
}
case 2:
{
lean_object* v_decl_5676_; lean_object* v_k_5677_; 
v_decl_5676_ = lean_ctor_get(v_code_5514_, 0);
v_k_5677_ = lean_ctor_get(v_code_5514_, 1);
lean_inc_ref(v_k_5677_);
lean_inc_ref(v_decl_5676_);
v_decl_5521_ = v_decl_5676_;
v_k_5522_ = v_k_5677_;
v___y_5523_ = v_a_5515_;
v___y_5524_ = v_a_5516_;
v___y_5525_ = v_a_5517_;
v___y_5526_ = v_a_5518_;
goto v___jp_5520_;
}
case 4:
{
lean_object* v_cases_5678_; lean_object* v_typeName_5679_; lean_object* v_resultType_5680_; lean_object* v_discr_5681_; lean_object* v_alts_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5723_; 
v_cases_5678_ = lean_ctor_get(v_code_5514_, 0);
lean_inc_ref(v_cases_5678_);
v_typeName_5679_ = lean_ctor_get(v_cases_5678_, 0);
v_resultType_5680_ = lean_ctor_get(v_cases_5678_, 1);
v_discr_5681_ = lean_ctor_get(v_cases_5678_, 2);
v_alts_5682_ = lean_ctor_get(v_cases_5678_, 3);
v_isSharedCheck_5723_ = !lean_is_exclusive(v_cases_5678_);
if (v_isSharedCheck_5723_ == 0)
{
v___x_5684_ = v_cases_5678_;
v_isShared_5685_ = v_isSharedCheck_5723_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_alts_5682_);
lean_inc(v_discr_5681_);
lean_inc(v_resultType_5680_);
lean_inc(v_typeName_5679_);
lean_dec(v_cases_5678_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5723_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v___x_5686_; lean_object* v_discrVal_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5686_ = lean_box(0);
v_discrVal_5687_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5513_, v_discr_5681_, v___x_5686_);
v___x_5688_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5682_);
lean_inc(v_discr_5681_);
lean_inc_ref(v_resultType_5680_);
v___x_5689_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5680_, v_discrVal_5687_, v_discr_5681_, v_assignment_5513_, v___x_5688_, v_alts_5682_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_);
lean_dec(v_discrVal_5687_);
if (lean_obj_tag(v___x_5689_) == 0)
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5714_; 
v_a_5690_ = lean_ctor_get(v___x_5689_, 0);
v_isSharedCheck_5714_ = !lean_is_exclusive(v___x_5689_);
if (v_isSharedCheck_5714_ == 0)
{
v___x_5692_ = v___x_5689_;
v_isShared_5693_ = v_isSharedCheck_5714_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5689_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5714_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
size_t v___x_5694_; size_t v___x_5695_; uint8_t v___x_5696_; 
v___x_5694_ = lean_ptr_addr(v_alts_5682_);
lean_dec_ref(v_alts_5682_);
v___x_5695_ = lean_ptr_addr(v_a_5690_);
v___x_5696_ = lean_usize_dec_eq(v___x_5694_, v___x_5695_);
if (v___x_5696_ == 0)
{
lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5709_; 
v_isSharedCheck_5709_ = !lean_is_exclusive(v_code_5514_);
if (v_isSharedCheck_5709_ == 0)
{
lean_object* v_unused_5710_; 
v_unused_5710_ = lean_ctor_get(v_code_5514_, 0);
lean_dec(v_unused_5710_);
v___x_5698_ = v_code_5514_;
v_isShared_5699_ = v_isSharedCheck_5709_;
goto v_resetjp_5697_;
}
else
{
lean_dec(v_code_5514_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5709_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 3, v_a_5690_);
v___x_5701_ = v___x_5684_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_typeName_5679_);
lean_ctor_set(v_reuseFailAlloc_5708_, 1, v_resultType_5680_);
lean_ctor_set(v_reuseFailAlloc_5708_, 2, v_discr_5681_);
lean_ctor_set(v_reuseFailAlloc_5708_, 3, v_a_5690_);
v___x_5701_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
lean_object* v___x_5703_; 
if (v_isShared_5699_ == 0)
{
lean_ctor_set(v___x_5698_, 0, v___x_5701_);
v___x_5703_ = v___x_5698_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v___x_5701_);
v___x_5703_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
lean_object* v___x_5705_; 
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 0, v___x_5703_);
v___x_5705_ = v___x_5692_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5706_; 
v_reuseFailAlloc_5706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5706_, 0, v___x_5703_);
v___x_5705_ = v_reuseFailAlloc_5706_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
return v___x_5705_;
}
}
}
}
}
else
{
lean_object* v___x_5712_; 
lean_dec(v_a_5690_);
lean_del_object(v___x_5684_);
lean_dec(v_discr_5681_);
lean_dec_ref(v_resultType_5680_);
lean_dec(v_typeName_5679_);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 0, v_code_5514_);
v___x_5712_ = v___x_5692_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_code_5514_);
v___x_5712_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
return v___x_5712_;
}
}
}
}
else
{
lean_object* v_a_5715_; lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5722_; 
lean_del_object(v___x_5684_);
lean_dec_ref(v_alts_5682_);
lean_dec(v_discr_5681_);
lean_dec_ref(v_resultType_5680_);
lean_dec(v_typeName_5679_);
lean_dec_ref_known(v_code_5514_, 1);
v_a_5715_ = lean_ctor_get(v___x_5689_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5689_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5717_ = v___x_5689_;
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
else
{
lean_inc(v_a_5715_);
lean_dec(v___x_5689_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v___x_5720_; 
if (v_isShared_5718_ == 0)
{
v___x_5720_ = v___x_5717_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_a_5715_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
}
}
default: 
{
lean_object* v___x_5724_; 
v___x_5724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5724_, 0, v_code_5514_);
return v___x_5724_;
}
}
v___jp_5520_:
{
lean_object* v_params_5527_; lean_object* v_type_5528_; lean_object* v_value_5529_; lean_object* v___x_5530_; 
v_params_5527_ = lean_ctor_get(v_decl_5521_, 2);
lean_inc_ref(v_params_5527_);
v_type_5528_ = lean_ctor_get(v_decl_5521_, 3);
lean_inc_ref(v_type_5528_);
v_value_5529_ = lean_ctor_get(v_decl_5521_, 4);
lean_inc_ref(v_value_5529_);
v___x_5530_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5513_, v_value_5529_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_object* v_a_5531_; uint8_t v___x_5532_; lean_object* v___x_5533_; 
v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
lean_inc(v_a_5531_);
lean_dec_ref_known(v___x_5530_, 1);
v___x_5532_ = 0;
v___x_5533_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5532_, v_decl_5521_, v_type_5528_, v_params_5527_, v_a_5531_, v___y_5524_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v_a_5534_; lean_object* v___x_5535_; 
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v___x_5533_, 1);
v___x_5535_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5513_, v_k_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5535_) == 0)
{
switch(lean_obj_tag(v_code_5514_))
{
case 1:
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5575_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5538_ = v___x_5535_;
v_isShared_5539_ = v_isSharedCheck_5575_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5575_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v_decl_5540_; lean_object* v_k_5541_; size_t v___x_5542_; size_t v___x_5543_; uint8_t v___x_5544_; 
v_decl_5540_ = lean_ctor_get(v_code_5514_, 0);
v_k_5541_ = lean_ctor_get(v_code_5514_, 1);
v___x_5542_ = lean_ptr_addr(v_k_5541_);
v___x_5543_ = lean_ptr_addr(v_a_5536_);
v___x_5544_ = lean_usize_dec_eq(v___x_5542_, v___x_5543_);
if (v___x_5544_ == 0)
{
lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5554_; 
v_isSharedCheck_5554_ = !lean_is_exclusive(v_code_5514_);
if (v_isSharedCheck_5554_ == 0)
{
lean_object* v_unused_5555_; lean_object* v_unused_5556_; 
v_unused_5555_ = lean_ctor_get(v_code_5514_, 1);
lean_dec(v_unused_5555_);
v_unused_5556_ = lean_ctor_get(v_code_5514_, 0);
lean_dec(v_unused_5556_);
v___x_5546_ = v_code_5514_;
v_isShared_5547_ = v_isSharedCheck_5554_;
goto v_resetjp_5545_;
}
else
{
lean_dec(v_code_5514_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5554_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 1, v_a_5536_);
lean_ctor_set(v___x_5546_, 0, v_a_5534_);
v___x_5549_ = v___x_5546_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5534_);
lean_ctor_set(v_reuseFailAlloc_5553_, 1, v_a_5536_);
v___x_5549_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
lean_object* v___x_5551_; 
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v___x_5549_);
v___x_5551_ = v___x_5538_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v___x_5549_);
v___x_5551_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
return v___x_5551_;
}
}
}
}
else
{
size_t v___x_5557_; size_t v___x_5558_; uint8_t v___x_5559_; 
v___x_5557_ = lean_ptr_addr(v_decl_5540_);
v___x_5558_ = lean_ptr_addr(v_a_5534_);
v___x_5559_ = lean_usize_dec_eq(v___x_5557_, v___x_5558_);
if (v___x_5559_ == 0)
{
lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5569_; 
v_isSharedCheck_5569_ = !lean_is_exclusive(v_code_5514_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; lean_object* v_unused_5571_; 
v_unused_5570_ = lean_ctor_get(v_code_5514_, 1);
lean_dec(v_unused_5570_);
v_unused_5571_ = lean_ctor_get(v_code_5514_, 0);
lean_dec(v_unused_5571_);
v___x_5561_ = v_code_5514_;
v_isShared_5562_ = v_isSharedCheck_5569_;
goto v_resetjp_5560_;
}
else
{
lean_dec(v_code_5514_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5569_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5564_; 
if (v_isShared_5562_ == 0)
{
lean_ctor_set(v___x_5561_, 1, v_a_5536_);
lean_ctor_set(v___x_5561_, 0, v_a_5534_);
v___x_5564_ = v___x_5561_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5534_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_a_5536_);
v___x_5564_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
lean_object* v___x_5566_; 
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v___x_5564_);
v___x_5566_ = v___x_5538_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5564_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
}
else
{
lean_object* v___x_5573_; 
lean_dec(v_a_5536_);
lean_dec(v_a_5534_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v_code_5514_);
v___x_5573_ = v___x_5538_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_code_5514_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
return v___x_5573_;
}
}
}
}
}
case 2:
{
lean_object* v_a_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5615_; 
v_a_5576_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5578_ = v___x_5535_;
v_isShared_5579_ = v_isSharedCheck_5615_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_a_5576_);
lean_dec(v___x_5535_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5615_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v_decl_5580_; lean_object* v_k_5581_; size_t v___x_5582_; size_t v___x_5583_; uint8_t v___x_5584_; 
v_decl_5580_ = lean_ctor_get(v_code_5514_, 0);
v_k_5581_ = lean_ctor_get(v_code_5514_, 1);
v___x_5582_ = lean_ptr_addr(v_k_5581_);
v___x_5583_ = lean_ptr_addr(v_a_5576_);
v___x_5584_ = lean_usize_dec_eq(v___x_5582_, v___x_5583_);
if (v___x_5584_ == 0)
{
lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5594_; 
v_isSharedCheck_5594_ = !lean_is_exclusive(v_code_5514_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; lean_object* v_unused_5596_; 
v_unused_5595_ = lean_ctor_get(v_code_5514_, 1);
lean_dec(v_unused_5595_);
v_unused_5596_ = lean_ctor_get(v_code_5514_, 0);
lean_dec(v_unused_5596_);
v___x_5586_ = v_code_5514_;
v_isShared_5587_ = v_isSharedCheck_5594_;
goto v_resetjp_5585_;
}
else
{
lean_dec(v_code_5514_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5594_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 1, v_a_5576_);
lean_ctor_set(v___x_5586_, 0, v_a_5534_);
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5534_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_a_5576_);
v___x_5589_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
lean_object* v___x_5591_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 0, v___x_5589_);
v___x_5591_ = v___x_5578_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5589_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
}
else
{
size_t v___x_5597_; size_t v___x_5598_; uint8_t v___x_5599_; 
v___x_5597_ = lean_ptr_addr(v_decl_5580_);
v___x_5598_ = lean_ptr_addr(v_a_5534_);
v___x_5599_ = lean_usize_dec_eq(v___x_5597_, v___x_5598_);
if (v___x_5599_ == 0)
{
lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5609_; 
v_isSharedCheck_5609_ = !lean_is_exclusive(v_code_5514_);
if (v_isSharedCheck_5609_ == 0)
{
lean_object* v_unused_5610_; lean_object* v_unused_5611_; 
v_unused_5610_ = lean_ctor_get(v_code_5514_, 1);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_code_5514_, 0);
lean_dec(v_unused_5611_);
v___x_5601_ = v_code_5514_;
v_isShared_5602_ = v_isSharedCheck_5609_;
goto v_resetjp_5600_;
}
else
{
lean_dec(v_code_5514_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5609_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
lean_ctor_set(v___x_5601_, 1, v_a_5576_);
lean_ctor_set(v___x_5601_, 0, v_a_5534_);
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5534_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v_a_5576_);
v___x_5604_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
lean_object* v___x_5606_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 0, v___x_5604_);
v___x_5606_ = v___x_5578_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5604_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
return v___x_5606_;
}
}
}
}
else
{
lean_object* v___x_5613_; 
lean_dec(v_a_5576_);
lean_dec(v_a_5534_);
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 0, v_code_5514_);
v___x_5613_ = v___x_5578_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_code_5514_);
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
}
default: 
{
lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5624_; 
lean_dec(v_a_5534_);
lean_dec_ref(v_code_5514_);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5624_ == 0)
{
lean_object* v_unused_5625_; 
v_unused_5625_ = lean_ctor_get(v___x_5535_, 0);
lean_dec(v_unused_5625_);
v___x_5617_ = v___x_5535_;
v_isShared_5618_ = v_isSharedCheck_5624_;
goto v_resetjp_5616_;
}
else
{
lean_dec(v___x_5535_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5624_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5622_; 
v___x_5619_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5620_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5619_);
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 0, v___x_5620_);
v___x_5622_ = v___x_5617_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5620_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
}
else
{
lean_dec(v_a_5534_);
lean_dec_ref(v_code_5514_);
return v___x_5535_;
}
}
else
{
lean_object* v_a_5626_; lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5633_; 
lean_dec_ref(v_k_5522_);
lean_dec_ref(v_code_5514_);
v_a_5626_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5633_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5633_ == 0)
{
v___x_5628_ = v___x_5533_;
v_isShared_5629_ = v_isSharedCheck_5633_;
goto v_resetjp_5627_;
}
else
{
lean_inc(v_a_5626_);
lean_dec(v___x_5533_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5633_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
lean_object* v___x_5631_; 
if (v_isShared_5629_ == 0)
{
v___x_5631_ = v___x_5628_;
goto v_reusejp_5630_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_a_5626_);
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
lean_dec_ref(v_type_5528_);
lean_dec_ref(v_params_5527_);
lean_dec_ref(v_k_5522_);
lean_dec_ref(v_decl_5521_);
lean_dec_ref(v_code_5514_);
return v___x_5530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5725_, lean_object* v_code_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_){
_start:
{
lean_object* v_res_5732_; 
v_res_5732_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5725_, v_code_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_);
lean_dec(v_a_5730_);
lean_dec_ref(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_a_5727_);
lean_dec_ref(v_assignment_5725_);
return v_res_5732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5733_, lean_object* v_discrVal_5734_, lean_object* v_discr_5735_, lean_object* v_assignment_5736_, lean_object* v_i_5737_, lean_object* v_as_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5733_, v_discrVal_5734_, v_discr_5735_, v_assignment_5736_, v_i_5737_, v_as_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
lean_dec_ref(v_assignment_5736_);
lean_dec(v_discrVal_5734_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5745_, lean_object* v_m_5746_, lean_object* v_a_5747_){
_start:
{
lean_object* v___x_5748_; 
v___x_5748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5746_, v_a_5747_);
return v___x_5748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5749_, lean_object* v_m_5750_, lean_object* v_a_5751_){
_start:
{
lean_object* v_res_5752_; 
v_res_5752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5749_, v_m_5750_, v_a_5751_);
lean_dec(v_a_5751_);
lean_dec_ref(v_m_5750_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5753_, size_t v_i_5754_, size_t v_stop_5755_, lean_object* v_b_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v___x_5762_; 
v___x_5762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5753_, v_i_5754_, v_stop_5755_, v_b_5756_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5763_, lean_object* v_i_5764_, lean_object* v_stop_5765_, lean_object* v_b_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_){
_start:
{
size_t v_i_boxed_5772_; size_t v_stop_boxed_5773_; lean_object* v_res_5774_; 
v_i_boxed_5772_ = lean_unbox_usize(v_i_5764_);
lean_dec(v_i_5764_);
v_stop_boxed_5773_ = lean_unbox_usize(v_stop_5765_);
lean_dec(v_stop_5765_);
v_res_5774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5763_, v_i_boxed_5772_, v_stop_boxed_5773_, v_b_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec_ref(v_as_5763_);
return v_res_5774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5775_, lean_object* v_a_5776_, lean_object* v_x_5777_){
_start:
{
lean_object* v___x_5778_; 
v___x_5778_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5776_, v_x_5777_);
return v___x_5778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5779_, lean_object* v_a_5780_, lean_object* v_x_5781_){
_start:
{
lean_object* v_res_5782_; 
v_res_5782_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5779_, v_a_5780_, v_x_5781_);
lean_dec(v_x_5781_);
lean_dec(v_a_5780_);
return v_res_5782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5783_, lean_object* v_v_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_){
_start:
{
if (lean_obj_tag(v_v_5784_) == 0)
{
lean_object* v_code_5790_; lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5814_; 
v_code_5790_ = lean_ctor_get(v_v_5784_, 0);
v_isSharedCheck_5814_ = !lean_is_exclusive(v_v_5784_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5792_ = v_v_5784_;
v_isShared_5793_ = v_isSharedCheck_5814_;
goto v_resetjp_5791_;
}
else
{
lean_inc(v_code_5790_);
lean_dec(v_v_5784_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5814_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
lean_object* v___x_5794_; 
lean_inc(v___y_5788_);
lean_inc_ref(v___y_5787_);
lean_inc(v___y_5786_);
lean_inc_ref(v___y_5785_);
v___x_5794_ = lean_apply_6(v_f_5783_, v_code_5790_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, lean_box(0));
if (lean_obj_tag(v___x_5794_) == 0)
{
lean_object* v_a_5795_; lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5805_; 
v_a_5795_ = lean_ctor_get(v___x_5794_, 0);
v_isSharedCheck_5805_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5805_ == 0)
{
v___x_5797_ = v___x_5794_;
v_isShared_5798_ = v_isSharedCheck_5805_;
goto v_resetjp_5796_;
}
else
{
lean_inc(v_a_5795_);
lean_dec(v___x_5794_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5805_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
lean_object* v___x_5800_; 
if (v_isShared_5793_ == 0)
{
lean_ctor_set(v___x_5792_, 0, v_a_5795_);
v___x_5800_ = v___x_5792_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v_a_5795_);
v___x_5800_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
lean_object* v___x_5802_; 
if (v_isShared_5798_ == 0)
{
lean_ctor_set(v___x_5797_, 0, v___x_5800_);
v___x_5802_ = v___x_5797_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
}
else
{
lean_object* v_a_5806_; lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5813_; 
lean_del_object(v___x_5792_);
v_a_5806_ = lean_ctor_get(v___x_5794_, 0);
v_isSharedCheck_5813_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5813_ == 0)
{
v___x_5808_ = v___x_5794_;
v_isShared_5809_ = v_isSharedCheck_5813_;
goto v_resetjp_5807_;
}
else
{
lean_inc(v_a_5806_);
lean_dec(v___x_5794_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5813_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
lean_object* v___x_5811_; 
if (v_isShared_5809_ == 0)
{
v___x_5811_ = v___x_5808_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v_a_5806_);
v___x_5811_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
return v___x_5811_;
}
}
}
}
}
else
{
lean_object* v___x_5815_; 
lean_dec_ref(v_f_5783_);
v___x_5815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5815_, 0, v_v_5784_);
return v___x_5815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5816_, lean_object* v_v_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_){
_start:
{
lean_object* v_res_5823_; 
v_res_5823_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5816_, v_v_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
return v_res_5823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5824_, lean_object* v_f_5825_, lean_object* v_v_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_){
_start:
{
lean_object* v___x_5832_; 
v___x_5832_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5825_, v_v_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
return v___x_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5833_, lean_object* v_f_5834_, lean_object* v_v_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_){
_start:
{
uint8_t v_pu_boxed_5841_; lean_object* v_res_5842_; 
v_pu_boxed_5841_ = lean_unbox(v_pu_5833_);
v_res_5842_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5841_, v_f_5834_, v_v_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
lean_dec(v___y_5839_);
lean_dec_ref(v___y_5838_);
lean_dec(v___y_5837_);
lean_dec_ref(v___y_5836_);
return v_res_5842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5843_, lean_object* v_x_5844_){
_start:
{
if (lean_obj_tag(v_x_5844_) == 0)
{
return v_x_5843_;
}
else
{
lean_object* v_key_5845_; lean_object* v_value_5846_; lean_object* v_tail_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
v_key_5845_ = lean_ctor_get(v_x_5844_, 0);
v_value_5846_ = lean_ctor_get(v_x_5844_, 1);
v_tail_5847_ = lean_ctor_get(v_x_5844_, 2);
lean_inc(v_value_5846_);
lean_inc(v_key_5845_);
v___x_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5848_, 0, v_key_5845_);
lean_ctor_set(v___x_5848_, 1, v_value_5846_);
v___x_5849_ = lean_array_push(v_x_5843_, v___x_5848_);
v_x_5843_ = v___x_5849_;
v_x_5844_ = v_tail_5847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5851_, lean_object* v_x_5852_){
_start:
{
lean_object* v_res_5853_; 
v_res_5853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5851_, v_x_5852_);
lean_dec(v_x_5852_);
return v_res_5853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5854_, size_t v_i_5855_, size_t v_stop_5856_, lean_object* v_b_5857_){
_start:
{
uint8_t v___x_5858_; 
v___x_5858_ = lean_usize_dec_eq(v_i_5855_, v_stop_5856_);
if (v___x_5858_ == 0)
{
lean_object* v___x_5859_; lean_object* v___x_5860_; size_t v___x_5861_; size_t v___x_5862_; 
v___x_5859_ = lean_array_uget_borrowed(v_as_5854_, v_i_5855_);
v___x_5860_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5857_, v___x_5859_);
v___x_5861_ = ((size_t)1ULL);
v___x_5862_ = lean_usize_add(v_i_5855_, v___x_5861_);
v_i_5855_ = v___x_5862_;
v_b_5857_ = v___x_5860_;
goto _start;
}
else
{
return v_b_5857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5864_, lean_object* v_i_5865_, lean_object* v_stop_5866_, lean_object* v_b_5867_){
_start:
{
size_t v_i_boxed_5868_; size_t v_stop_boxed_5869_; lean_object* v_res_5870_; 
v_i_boxed_5868_ = lean_unbox_usize(v_i_5865_);
lean_dec(v_i_5865_);
v_stop_boxed_5869_ = lean_unbox_usize(v_stop_5866_);
lean_dec(v_stop_5866_);
v_res_5870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5864_, v_i_boxed_5868_, v_stop_boxed_5869_, v_b_5867_);
lean_dec_ref(v_as_5864_);
return v_res_5870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5871_, size_t v_sz_5872_, size_t v_i_5873_, lean_object* v_bs_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_){
_start:
{
uint8_t v___x_5880_; 
v___x_5880_ = lean_usize_dec_lt(v_i_5873_, v_sz_5872_);
if (v___x_5880_ == 0)
{
lean_object* v___x_5881_; 
v___x_5881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5881_, 0, v_bs_5874_);
return v___x_5881_;
}
else
{
lean_object* v_v_5882_; lean_object* v_fst_5883_; lean_object* v_snd_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5908_; 
v_v_5882_ = lean_array_uget(v_bs_5874_, v_i_5873_);
v_fst_5883_ = lean_ctor_get(v_v_5882_, 0);
v_snd_5884_ = lean_ctor_get(v_v_5882_, 1);
v_isSharedCheck_5908_ = !lean_is_exclusive(v_v_5882_);
if (v_isSharedCheck_5908_ == 0)
{
v___x_5886_ = v_v_5882_;
v_isShared_5887_ = v_isSharedCheck_5908_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_snd_5884_);
lean_inc(v_fst_5883_);
lean_dec(v_v_5882_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5908_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5888_; 
v___x_5888_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5883_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_object* v_a_5889_; lean_object* v___x_5890_; lean_object* v_bs_x27_5891_; lean_object* v___x_5892_; lean_object* v___x_5894_; 
v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
lean_inc(v_a_5889_);
lean_dec_ref_known(v___x_5888_, 1);
v___x_5890_ = lean_unsigned_to_nat(0u);
v_bs_x27_5891_ = lean_array_uset(v_bs_5874_, v_i_5873_, v___x_5890_);
v___x_5892_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5889_, v_a_5871_);
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 0, v___x_5892_);
v___x_5894_ = v___x_5886_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v___x_5892_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v_snd_5884_);
v___x_5894_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
size_t v___x_5895_; size_t v___x_5896_; lean_object* v___x_5897_; 
v___x_5895_ = ((size_t)1ULL);
v___x_5896_ = lean_usize_add(v_i_5873_, v___x_5895_);
v___x_5897_ = lean_array_uset(v_bs_x27_5891_, v_i_5873_, v___x_5894_);
v_i_5873_ = v___x_5896_;
v_bs_5874_ = v___x_5897_;
goto _start;
}
}
else
{
lean_object* v_a_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5907_; 
lean_del_object(v___x_5886_);
lean_dec(v_snd_5884_);
lean_dec_ref(v_bs_5874_);
v_a_5900_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5902_ = v___x_5888_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_a_5900_);
lean_dec(v___x_5888_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
v___x_5905_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
return v___x_5905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5909_, lean_object* v_sz_5910_, lean_object* v_i_5911_, lean_object* v_bs_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_){
_start:
{
uint8_t v_a_2400__boxed_5918_; size_t v_sz_boxed_5919_; size_t v_i_boxed_5920_; lean_object* v_res_5921_; 
v_a_2400__boxed_5918_ = lean_unbox(v_a_5909_);
v_sz_boxed_5919_ = lean_unbox_usize(v_sz_5910_);
lean_dec(v_sz_5910_);
v_i_boxed_5920_ = lean_unbox_usize(v_i_5911_);
lean_dec(v_i_5911_);
v_res_5921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2400__boxed_5918_, v_sz_boxed_5919_, v_i_boxed_5920_, v_bs_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
lean_dec(v___y_5914_);
lean_dec_ref(v___y_5913_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5922_){
_start:
{
lean_object* v_fst_5923_; lean_object* v_snd_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5947_; 
v_fst_5923_ = lean_ctor_get(v_x_5922_, 0);
v_snd_5924_ = lean_ctor_get(v_x_5922_, 1);
v_isSharedCheck_5947_ = !lean_is_exclusive(v_x_5922_);
if (v_isSharedCheck_5947_ == 0)
{
v___x_5926_ = v_x_5922_;
v_isShared_5927_ = v_isSharedCheck_5947_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_snd_5924_);
lean_inc(v_fst_5923_);
lean_dec(v_x_5922_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5947_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5932_; 
v___x_5928_ = l_String_quote(v_fst_5923_);
v___x_5929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5928_);
v___x_5930_ = lean_box(0);
if (v_isShared_5927_ == 0)
{
lean_ctor_set_tag(v___x_5926_, 1);
lean_ctor_set(v___x_5926_, 1, v___x_5930_);
lean_ctor_set(v___x_5926_, 0, v___x_5929_);
v___x_5932_ = v___x_5926_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v___x_5929_);
lean_ctor_set(v_reuseFailAlloc_5946_, 1, v___x_5930_);
v___x_5932_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; uint8_t v___x_5944_; lean_object* v___x_5945_; 
v___x_5933_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5924_);
v___x_5934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
lean_ctor_set(v___x_5934_, 1, v___x_5932_);
v___x_5935_ = l_List_reverse___redArg(v___x_5934_);
v___x_5936_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5937_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5935_, v___x_5936_);
v___x_5938_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5939_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5939_);
lean_ctor_set(v___x_5940_, 1, v___x_5937_);
v___x_5941_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
v___x_5943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5938_);
lean_ctor_set(v___x_5943_, 1, v___x_5942_);
v___x_5944_ = 0;
v___x_5945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5945_, 0, v___x_5943_);
lean_ctor_set_uint8(v___x_5945_, sizeof(void*)*1, v___x_5944_);
return v___x_5945_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5948_, lean_object* v_x_5949_, lean_object* v_x_5950_){
_start:
{
if (lean_obj_tag(v_x_5950_) == 0)
{
lean_dec(v_x_5948_);
return v_x_5949_;
}
else
{
lean_object* v_head_5951_; lean_object* v_tail_5952_; lean_object* v___x_5954_; uint8_t v_isShared_5955_; uint8_t v_isSharedCheck_5962_; 
v_head_5951_ = lean_ctor_get(v_x_5950_, 0);
v_tail_5952_ = lean_ctor_get(v_x_5950_, 1);
v_isSharedCheck_5962_ = !lean_is_exclusive(v_x_5950_);
if (v_isSharedCheck_5962_ == 0)
{
v___x_5954_ = v_x_5950_;
v_isShared_5955_ = v_isSharedCheck_5962_;
goto v_resetjp_5953_;
}
else
{
lean_inc(v_tail_5952_);
lean_inc(v_head_5951_);
lean_dec(v_x_5950_);
v___x_5954_ = lean_box(0);
v_isShared_5955_ = v_isSharedCheck_5962_;
goto v_resetjp_5953_;
}
v_resetjp_5953_:
{
lean_object* v___x_5957_; 
lean_inc(v_x_5948_);
if (v_isShared_5955_ == 0)
{
lean_ctor_set_tag(v___x_5954_, 5);
lean_ctor_set(v___x_5954_, 1, v_x_5948_);
lean_ctor_set(v___x_5954_, 0, v_x_5949_);
v___x_5957_ = v___x_5954_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_x_5949_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v_x_5948_);
v___x_5957_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
lean_object* v___x_5958_; lean_object* v___x_5959_; 
v___x_5958_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5951_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5957_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v_x_5949_ = v___x_5959_;
v_x_5950_ = v_tail_5952_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5963_, lean_object* v_x_5964_, lean_object* v_x_5965_){
_start:
{
if (lean_obj_tag(v_x_5965_) == 0)
{
lean_dec(v_x_5963_);
return v_x_5964_;
}
else
{
lean_object* v_head_5966_; lean_object* v_tail_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5977_; 
v_head_5966_ = lean_ctor_get(v_x_5965_, 0);
v_tail_5967_ = lean_ctor_get(v_x_5965_, 1);
v_isSharedCheck_5977_ = !lean_is_exclusive(v_x_5965_);
if (v_isSharedCheck_5977_ == 0)
{
v___x_5969_ = v_x_5965_;
v_isShared_5970_ = v_isSharedCheck_5977_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_tail_5967_);
lean_inc(v_head_5966_);
lean_dec(v_x_5965_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5977_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5972_; 
lean_inc(v_x_5963_);
if (v_isShared_5970_ == 0)
{
lean_ctor_set_tag(v___x_5969_, 5);
lean_ctor_set(v___x_5969_, 1, v_x_5963_);
lean_ctor_set(v___x_5969_, 0, v_x_5964_);
v___x_5972_ = v___x_5969_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_x_5964_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v_x_5963_);
v___x_5972_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5973_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5966_);
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5972_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5963_, v___x_5974_, v_tail_5967_);
return v___x_5975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5978_, lean_object* v_x_5979_){
_start:
{
if (lean_obj_tag(v_x_5978_) == 0)
{
lean_object* v___x_5980_; 
lean_dec(v_x_5979_);
v___x_5980_ = lean_box(0);
return v___x_5980_;
}
else
{
lean_object* v_tail_5981_; 
v_tail_5981_ = lean_ctor_get(v_x_5978_, 1);
if (lean_obj_tag(v_tail_5981_) == 0)
{
lean_object* v_head_5982_; lean_object* v___x_5983_; 
lean_dec(v_x_5979_);
v_head_5982_ = lean_ctor_get(v_x_5978_, 0);
lean_inc(v_head_5982_);
lean_dec_ref_known(v_x_5978_, 2);
v___x_5983_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5982_);
return v___x_5983_;
}
else
{
lean_object* v_head_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; 
lean_inc(v_tail_5981_);
v_head_5984_ = lean_ctor_get(v_x_5978_, 0);
lean_inc(v_head_5984_);
lean_dec_ref_known(v_x_5978_, 2);
v___x_5985_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5984_);
v___x_5986_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5979_, v___x_5985_, v_tail_5981_);
return v___x_5986_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5988_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5989_ = lean_string_length(v___x_5988_);
return v___x_5989_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5990_; lean_object* v___x_5991_; 
v___x_5990_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5991_ = lean_nat_to_int(v___x_5990_);
return v___x_5991_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5997_){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; uint8_t v___x_6000_; 
v___x_5998_ = lean_array_get_size(v_xs_5997_);
v___x_5999_ = lean_unsigned_to_nat(0u);
v___x_6000_ = lean_nat_dec_eq(v___x_5998_, v___x_5999_);
if (v___x_6000_ == 0)
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; 
v___x_6001_ = lean_array_to_list(v_xs_5997_);
v___x_6002_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_6003_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_6001_, v___x_6002_);
v___x_6004_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_6005_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
lean_ctor_set(v___x_6006_, 1, v___x_6003_);
v___x_6007_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6006_);
lean_ctor_set(v___x_6008_, 1, v___x_6007_);
v___x_6009_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6004_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
v___x_6010_ = l_Std_Format_fill(v___x_6009_);
return v___x_6010_;
}
else
{
lean_object* v___x_6011_; 
lean_dec_ref(v_xs_5997_);
v___x_6011_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_6011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_6014_, lean_object* v_decl_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_){
_start:
{
lean_object* v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6024_; lean_object* v___y_6025_; lean_object* v_toCold_6055_; lean_object* v_options_6056_; uint8_t v_hasTrace_6057_; 
v_toCold_6055_ = lean_ctor_get(v_a_6018_, 0);
v_options_6056_ = lean_ctor_get(v_toCold_6055_, 2);
v_hasTrace_6057_ = lean_ctor_get_uint8(v_options_6056_, sizeof(void*)*1);
if (v_hasTrace_6057_ == 0)
{
v___y_6022_ = v_a_6016_;
v___y_6023_ = v_a_6017_;
v___y_6024_ = v_a_6018_;
v___y_6025_ = v_a_6019_;
goto v___jp_6021_;
}
else
{
lean_object* v_inheritedTraceOptions_6058_; lean_object* v_cls_6059_; uint8_t v___y_6061_; lean_object* v___y_6062_; lean_object* v___x_6098_; uint8_t v___x_6099_; 
v_inheritedTraceOptions_6058_ = lean_ctor_get(v_toCold_6055_, 11);
v_cls_6059_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6098_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6099_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6058_, v_options_6056_, v___x_6098_);
if (v___x_6099_ == 0)
{
v___y_6022_ = v_a_6016_;
v___y_6023_ = v_a_6017_;
v___y_6024_ = v_a_6018_;
v___y_6025_ = v_a_6019_;
goto v___jp_6021_;
}
else
{
lean_object* v_size_6100_; lean_object* v_buckets_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; uint8_t v___x_6105_; 
v_size_6100_ = lean_ctor_get(v_assignment_6014_, 0);
v_buckets_6101_ = lean_ctor_get(v_assignment_6014_, 1);
v___x_6102_ = lean_mk_empty_array_with_capacity(v_size_6100_);
v___x_6103_ = lean_unsigned_to_nat(0u);
v___x_6104_ = lean_array_get_size(v_buckets_6101_);
v___x_6105_ = lean_nat_dec_lt(v___x_6103_, v___x_6104_);
if (v___x_6105_ == 0)
{
v___y_6061_ = v___x_6099_;
v___y_6062_ = v___x_6102_;
goto v___jp_6060_;
}
else
{
size_t v___x_6106_; size_t v___x_6107_; lean_object* v___x_6108_; 
v___x_6106_ = ((size_t)0ULL);
v___x_6107_ = lean_usize_of_nat(v___x_6104_);
v___x_6108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6101_, v___x_6106_, v___x_6107_, v___x_6102_);
v___y_6061_ = v___x_6099_;
v___y_6062_ = v___x_6108_;
goto v___jp_6060_;
}
}
v___jp_6060_:
{
size_t v_sz_6063_; size_t v___x_6064_; lean_object* v___x_6065_; 
v_sz_6063_ = lean_array_size(v___y_6062_);
v___x_6064_ = ((size_t)0ULL);
v___x_6065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6061_, v_sz_6063_, v___x_6064_, v___y_6062_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_);
if (lean_obj_tag(v___x_6065_) == 0)
{
lean_object* v_toSignature_6066_; lean_object* v_a_6067_; lean_object* v_name_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; 
v_toSignature_6066_ = lean_ctor_get(v_decl_6015_, 0);
v_a_6067_ = lean_ctor_get(v___x_6065_, 0);
lean_inc(v_a_6067_);
lean_dec_ref_known(v___x_6065_, 1);
v_name_6068_ = lean_ctor_get(v_toSignature_6066_, 0);
v___x_6069_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6068_);
v___x_6070_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6068_, v___y_6061_);
v___x_6071_ = lean_string_append(v___x_6069_, v___x_6070_);
lean_dec_ref(v___x_6070_);
v___x_6072_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6073_ = lean_string_append(v___x_6071_, v___x_6072_);
v___x_6074_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6067_);
v___x_6075_ = l_Std_Format_defWidth;
v___x_6076_ = lean_unsigned_to_nat(0u);
v___x_6077_ = l_Std_Format_pretty(v___x_6074_, v___x_6075_, v___x_6076_, v___x_6076_);
v___x_6078_ = lean_string_append(v___x_6073_, v___x_6077_);
lean_dec_ref(v___x_6077_);
v___x_6079_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
v___x_6080_ = l_Lean_MessageData_ofFormat(v___x_6079_);
v___x_6081_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_6059_, v___x_6080_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_);
if (lean_obj_tag(v___x_6081_) == 0)
{
lean_dec_ref_known(v___x_6081_, 1);
v___y_6022_ = v_a_6016_;
v___y_6023_ = v_a_6017_;
v___y_6024_ = v_a_6018_;
v___y_6025_ = v_a_6019_;
goto v___jp_6021_;
}
else
{
lean_object* v_a_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6089_; 
lean_dec_ref(v_decl_6015_);
lean_dec_ref(v_assignment_6014_);
v_a_6082_ = lean_ctor_get(v___x_6081_, 0);
v_isSharedCheck_6089_ = !lean_is_exclusive(v___x_6081_);
if (v_isSharedCheck_6089_ == 0)
{
v___x_6084_ = v___x_6081_;
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_a_6082_);
lean_dec(v___x_6081_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6087_; 
if (v_isShared_6085_ == 0)
{
v___x_6087_ = v___x_6084_;
goto v_reusejp_6086_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_a_6082_);
v___x_6087_ = v_reuseFailAlloc_6088_;
goto v_reusejp_6086_;
}
v_reusejp_6086_:
{
return v___x_6087_;
}
}
}
}
else
{
lean_object* v_a_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6097_; 
lean_dec_ref(v_decl_6015_);
lean_dec_ref(v_assignment_6014_);
v_a_6090_ = lean_ctor_get(v___x_6065_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v___x_6065_);
if (v_isSharedCheck_6097_ == 0)
{
v___x_6092_ = v___x_6065_;
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_a_6090_);
lean_dec(v___x_6065_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v___x_6095_; 
if (v_isShared_6093_ == 0)
{
v___x_6095_ = v___x_6092_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_a_6090_);
v___x_6095_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
return v___x_6095_;
}
}
}
}
}
v___jp_6021_:
{
lean_object* v_toSignature_6026_; lean_object* v_value_6027_; uint8_t v_recursive_6028_; lean_object* v_inlineAttr_x3f_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6054_; 
v_toSignature_6026_ = lean_ctor_get(v_decl_6015_, 0);
v_value_6027_ = lean_ctor_get(v_decl_6015_, 1);
v_recursive_6028_ = lean_ctor_get_uint8(v_decl_6015_, sizeof(void*)*3);
v_inlineAttr_x3f_6029_ = lean_ctor_get(v_decl_6015_, 2);
v_isSharedCheck_6054_ = !lean_is_exclusive(v_decl_6015_);
if (v_isSharedCheck_6054_ == 0)
{
v___x_6031_ = v_decl_6015_;
v_isShared_6032_ = v_isSharedCheck_6054_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_inlineAttr_x3f_6029_);
lean_inc(v_value_6027_);
lean_inc(v_toSignature_6026_);
lean_dec(v_decl_6015_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6054_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6033_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_6033_, 0, v_assignment_6014_);
v___x_6034_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_6033_, v_value_6027_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_);
if (lean_obj_tag(v___x_6034_) == 0)
{
lean_object* v_a_6035_; lean_object* v___x_6037_; uint8_t v_isShared_6038_; uint8_t v_isSharedCheck_6045_; 
v_a_6035_ = lean_ctor_get(v___x_6034_, 0);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_6034_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6037_ = v___x_6034_;
v_isShared_6038_ = v_isSharedCheck_6045_;
goto v_resetjp_6036_;
}
else
{
lean_inc(v_a_6035_);
lean_dec(v___x_6034_);
v___x_6037_ = lean_box(0);
v_isShared_6038_ = v_isSharedCheck_6045_;
goto v_resetjp_6036_;
}
v_resetjp_6036_:
{
lean_object* v___x_6040_; 
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 1, v_a_6035_);
v___x_6040_ = v___x_6031_;
goto v_reusejp_6039_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_toSignature_6026_);
lean_ctor_set(v_reuseFailAlloc_6044_, 1, v_a_6035_);
lean_ctor_set(v_reuseFailAlloc_6044_, 2, v_inlineAttr_x3f_6029_);
lean_ctor_set_uint8(v_reuseFailAlloc_6044_, sizeof(void*)*3, v_recursive_6028_);
v___x_6040_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6039_;
}
v_reusejp_6039_:
{
lean_object* v___x_6042_; 
if (v_isShared_6038_ == 0)
{
lean_ctor_set(v___x_6037_, 0, v___x_6040_);
v___x_6042_ = v___x_6037_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6043_; 
v_reuseFailAlloc_6043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6043_, 0, v___x_6040_);
v___x_6042_ = v_reuseFailAlloc_6043_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
return v___x_6042_;
}
}
}
}
else
{
lean_object* v_a_6046_; lean_object* v___x_6048_; uint8_t v_isShared_6049_; uint8_t v_isSharedCheck_6053_; 
lean_del_object(v___x_6031_);
lean_dec(v_inlineAttr_x3f_6029_);
lean_dec_ref(v_toSignature_6026_);
v_a_6046_ = lean_ctor_get(v___x_6034_, 0);
v_isSharedCheck_6053_ = !lean_is_exclusive(v___x_6034_);
if (v_isSharedCheck_6053_ == 0)
{
v___x_6048_ = v___x_6034_;
v_isShared_6049_ = v_isSharedCheck_6053_;
goto v_resetjp_6047_;
}
else
{
lean_inc(v_a_6046_);
lean_dec(v___x_6034_);
v___x_6048_ = lean_box(0);
v_isShared_6049_ = v_isSharedCheck_6053_;
goto v_resetjp_6047_;
}
v_resetjp_6047_:
{
lean_object* v___x_6051_; 
if (v_isShared_6049_ == 0)
{
v___x_6051_ = v___x_6048_;
goto v_reusejp_6050_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_a_6046_);
v___x_6051_ = v_reuseFailAlloc_6052_;
goto v_reusejp_6050_;
}
v_reusejp_6050_:
{
return v___x_6051_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6109_, lean_object* v_decl_6110_, lean_object* v_a_6111_, lean_object* v_a_6112_, lean_object* v_a_6113_, lean_object* v_a_6114_, lean_object* v_a_6115_){
_start:
{
lean_object* v_res_6116_; 
v_res_6116_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6109_, v_decl_6110_, v_a_6111_, v_a_6112_, v_a_6113_, v_a_6114_);
lean_dec(v_a_6114_);
lean_dec_ref(v_a_6113_);
lean_dec(v_a_6112_);
lean_dec_ref(v_a_6111_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6117_, lean_object* v_x_6118_){
_start:
{
lean_object* v___x_6119_; 
v___x_6119_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6117_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6120_, lean_object* v_x_6121_){
_start:
{
lean_object* v_res_6122_; 
v_res_6122_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6120_, v_x_6121_);
lean_dec(v_x_6121_);
return v_res_6122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6123_, size_t v_i_6124_, lean_object* v_bs_6125_){
_start:
{
uint8_t v___x_6126_; 
v___x_6126_ = lean_usize_dec_lt(v_i_6124_, v_sz_6123_);
if (v___x_6126_ == 0)
{
return v_bs_6125_;
}
else
{
lean_object* v_v_6127_; lean_object* v_toSignature_6128_; lean_object* v_name_6129_; lean_object* v___x_6130_; lean_object* v_bs_x27_6131_; size_t v___x_6132_; size_t v___x_6133_; lean_object* v___x_6134_; 
v_v_6127_ = lean_array_uget_borrowed(v_bs_6125_, v_i_6124_);
v_toSignature_6128_ = lean_ctor_get(v_v_6127_, 0);
v_name_6129_ = lean_ctor_get(v_toSignature_6128_, 0);
lean_inc(v_name_6129_);
v___x_6130_ = lean_unsigned_to_nat(0u);
v_bs_x27_6131_ = lean_array_uset(v_bs_6125_, v_i_6124_, v___x_6130_);
v___x_6132_ = ((size_t)1ULL);
v___x_6133_ = lean_usize_add(v_i_6124_, v___x_6132_);
v___x_6134_ = lean_array_uset(v_bs_x27_6131_, v_i_6124_, v_name_6129_);
v_i_6124_ = v___x_6133_;
v_bs_6125_ = v___x_6134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6136_, lean_object* v_i_6137_, lean_object* v_bs_6138_){
_start:
{
size_t v_sz_boxed_6139_; size_t v_i_boxed_6140_; lean_object* v_res_6141_; 
v_sz_boxed_6139_ = lean_unbox_usize(v_sz_6136_);
lean_dec(v_sz_6136_);
v_i_boxed_6140_ = lean_unbox_usize(v_i_6137_);
lean_dec(v_i_6137_);
v_res_6141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6139_, v_i_boxed_6140_, v_bs_6138_);
return v_res_6141_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6142_, lean_object* v_a_6143_){
_start:
{
if (lean_obj_tag(v_a_6142_) == 0)
{
lean_object* v___x_6144_; 
v___x_6144_ = l_List_reverse___redArg(v_a_6143_);
return v___x_6144_;
}
else
{
lean_object* v_head_6145_; lean_object* v_tail_6146_; lean_object* v___x_6148_; uint8_t v_isShared_6149_; uint8_t v_isSharedCheck_6155_; 
v_head_6145_ = lean_ctor_get(v_a_6142_, 0);
v_tail_6146_ = lean_ctor_get(v_a_6142_, 1);
v_isSharedCheck_6155_ = !lean_is_exclusive(v_a_6142_);
if (v_isSharedCheck_6155_ == 0)
{
v___x_6148_ = v_a_6142_;
v_isShared_6149_ = v_isSharedCheck_6155_;
goto v_resetjp_6147_;
}
else
{
lean_inc(v_tail_6146_);
lean_inc(v_head_6145_);
lean_dec(v_a_6142_);
v___x_6148_ = lean_box(0);
v_isShared_6149_ = v_isSharedCheck_6155_;
goto v_resetjp_6147_;
}
v_resetjp_6147_:
{
lean_object* v___x_6150_; lean_object* v___x_6152_; 
v___x_6150_ = l_Lean_MessageData_ofName(v_head_6145_);
if (v_isShared_6149_ == 0)
{
lean_ctor_set(v___x_6148_, 1, v_a_6143_);
lean_ctor_set(v___x_6148_, 0, v___x_6150_);
v___x_6152_ = v___x_6148_;
goto v_reusejp_6151_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v___x_6150_);
lean_ctor_set(v_reuseFailAlloc_6154_, 1, v_a_6143_);
v___x_6152_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6151_;
}
v_reusejp_6151_:
{
v_a_6142_ = v_tail_6146_;
v_a_6143_ = v___x_6152_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6157_; lean_object* v___x_6158_; 
v___x_6157_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6158_ = l_Lean_stringToMessageData(v___x_6157_);
return v___x_6158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6159_, lean_object* v_x_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_){
_start:
{
lean_object* v___x_6168_; size_t v_sz_6169_; size_t v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; 
v___x_6168_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6169_ = lean_array_size(v___y_6159_);
v___x_6170_ = ((size_t)0ULL);
v___x_6171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6169_, v___x_6170_, v___y_6159_);
v___x_6172_ = lean_array_to_list(v___x_6171_);
v___x_6173_ = lean_box(0);
v___x_6174_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6172_, v___x_6173_);
v___x_6175_ = l_Lean_MessageData_ofList(v___x_6174_);
v___x_6176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6168_);
lean_ctor_set(v___x_6176_, 1, v___x_6175_);
v___x_6177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6178_, lean_object* v_x_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6178_, v_x_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_);
lean_dec(v___y_6185_);
lean_dec_ref(v___y_6184_);
lean_dec(v___y_6183_);
lean_dec_ref(v___y_6182_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
lean_dec_ref(v_x_6179_);
return v_res_6187_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6188_; lean_object* v___x_6189_; 
v___x_6188_ = 0;
v___x_6189_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6188_);
return v___x_6189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6190_, lean_object* v_n_6191_, lean_object* v_j_6192_, lean_object* v_a_6193_){
_start:
{
lean_object* v_zero_6194_; uint8_t v_isZero_6195_; 
v_zero_6194_ = lean_unsigned_to_nat(0u);
v_isZero_6195_ = lean_nat_dec_eq(v_j_6192_, v_zero_6194_);
if (v_isZero_6195_ == 1)
{
lean_dec(v_j_6192_);
return v_a_6193_;
}
else
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v_toSignature_6199_; uint8_t v_safe_6200_; lean_object* v_one_6201_; lean_object* v_n_6202_; 
v___x_6196_ = lean_nat_sub(v_n_6191_, v_j_6192_);
v___x_6197_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6198_ = lean_array_get_borrowed(v___x_6197_, v___y_6190_, v___x_6196_);
lean_dec(v___x_6196_);
v_toSignature_6199_ = lean_ctor_get(v___x_6198_, 0);
v_safe_6200_ = lean_ctor_get_uint8(v_toSignature_6199_, sizeof(void*)*4);
v_one_6201_ = lean_unsigned_to_nat(1u);
v_n_6202_ = lean_nat_sub(v_j_6192_, v_one_6201_);
lean_dec(v_j_6192_);
if (v_safe_6200_ == 0)
{
lean_object* v___x_6203_; lean_object* v___x_6204_; 
v___x_6203_ = lean_box(1);
v___x_6204_ = lean_array_push(v_a_6193_, v___x_6203_);
v_j_6192_ = v_n_6202_;
v_a_6193_ = v___x_6204_;
goto _start;
}
else
{
lean_object* v___x_6206_; lean_object* v___x_6207_; 
v___x_6206_ = lean_box(0);
v___x_6207_ = lean_array_push(v_a_6193_, v___x_6206_);
v_j_6192_ = v_n_6202_;
v_a_6193_ = v___x_6207_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6209_, lean_object* v_n_6210_, lean_object* v_j_6211_, lean_object* v_a_6212_){
_start:
{
lean_object* v_res_6213_; 
v_res_6213_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6209_, v_n_6210_, v_j_6211_, v_a_6212_);
lean_dec(v_n_6210_);
lean_dec_ref(v___y_6209_);
return v_res_6213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6214_, size_t v_sz_6215_, size_t v_i_6216_, lean_object* v_bs_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_){
_start:
{
uint8_t v___x_6223_; 
v___x_6223_ = lean_usize_dec_lt(v_i_6216_, v_sz_6215_);
if (v___x_6223_ == 0)
{
lean_object* v___x_6224_; 
v___x_6224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6224_, 0, v_bs_6217_);
return v___x_6224_;
}
else
{
lean_object* v_v_6225_; lean_object* v_toSignature_6226_; uint8_t v_safe_6227_; lean_object* v___x_6228_; lean_object* v_bs_x27_6229_; lean_object* v_a_6231_; 
v_v_6225_ = lean_array_uget(v_bs_6217_, v_i_6216_);
v_toSignature_6226_ = lean_ctor_get(v_v_6225_, 0);
v_safe_6227_ = lean_ctor_get_uint8(v_toSignature_6226_, sizeof(void*)*4);
v___x_6228_ = lean_unsigned_to_nat(0u);
v_bs_x27_6229_ = lean_array_uset(v_bs_6217_, v_i_6216_, v___x_6228_);
if (v_safe_6227_ == 0)
{
v_a_6231_ = v_v_6225_;
goto v___jp_6230_;
}
else
{
lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; 
v___x_6236_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6237_ = lean_usize_to_nat(v_i_6216_);
v___x_6238_ = lean_array_get_borrowed(v___x_6236_, v___x_6214_, v___x_6237_);
lean_dec(v___x_6237_);
lean_inc(v___x_6238_);
v___x_6239_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6238_, v_v_6225_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_);
if (lean_obj_tag(v___x_6239_) == 0)
{
lean_object* v_a_6240_; 
v_a_6240_ = lean_ctor_get(v___x_6239_, 0);
lean_inc(v_a_6240_);
lean_dec_ref_known(v___x_6239_, 1);
v_a_6231_ = v_a_6240_;
goto v___jp_6230_;
}
else
{
lean_object* v_a_6241_; lean_object* v___x_6243_; uint8_t v_isShared_6244_; uint8_t v_isSharedCheck_6248_; 
lean_dec_ref(v_bs_x27_6229_);
v_a_6241_ = lean_ctor_get(v___x_6239_, 0);
v_isSharedCheck_6248_ = !lean_is_exclusive(v___x_6239_);
if (v_isSharedCheck_6248_ == 0)
{
v___x_6243_ = v___x_6239_;
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
else
{
lean_inc(v_a_6241_);
lean_dec(v___x_6239_);
v___x_6243_ = lean_box(0);
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
v_resetjp_6242_:
{
lean_object* v___x_6246_; 
if (v_isShared_6244_ == 0)
{
v___x_6246_ = v___x_6243_;
goto v_reusejp_6245_;
}
else
{
lean_object* v_reuseFailAlloc_6247_; 
v_reuseFailAlloc_6247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6247_, 0, v_a_6241_);
v___x_6246_ = v_reuseFailAlloc_6247_;
goto v_reusejp_6245_;
}
v_reusejp_6245_:
{
return v___x_6246_;
}
}
}
}
v___jp_6230_:
{
size_t v___x_6232_; size_t v___x_6233_; lean_object* v___x_6234_; 
v___x_6232_ = ((size_t)1ULL);
v___x_6233_ = lean_usize_add(v_i_6216_, v___x_6232_);
v___x_6234_ = lean_array_uset(v_bs_x27_6229_, v_i_6216_, v_a_6231_);
v_i_6216_ = v___x_6233_;
v_bs_6217_ = v___x_6234_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6249_, lean_object* v_sz_6250_, lean_object* v_i_6251_, lean_object* v_bs_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_){
_start:
{
size_t v_sz_boxed_6258_; size_t v_i_boxed_6259_; lean_object* v_res_6260_; 
v_sz_boxed_6258_ = lean_unbox_usize(v_sz_6250_);
lean_dec(v_sz_6250_);
v_i_boxed_6259_ = lean_unbox_usize(v_i_6251_);
lean_dec(v_i_6251_);
v_res_6260_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6249_, v_sz_boxed_6258_, v_i_boxed_6259_, v_bs_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
lean_dec(v___y_6256_);
lean_dec_ref(v___y_6255_);
lean_dec(v___y_6254_);
lean_dec_ref(v___y_6253_);
lean_dec_ref(v___x_6249_);
return v_res_6260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6263_, lean_object* v_pivot_6264_, lean_object* v_as_6265_, lean_object* v_i_6266_, lean_object* v_k_6267_){
_start:
{
uint8_t v___x_6268_; 
v___x_6268_ = lean_nat_dec_lt(v_k_6267_, v_hi_6263_);
if (v___x_6268_ == 0)
{
lean_object* v___x_6269_; lean_object* v___x_6270_; 
lean_dec(v_k_6267_);
lean_dec_ref(v_pivot_6264_);
v___x_6269_ = lean_array_fswap(v_as_6265_, v_i_6266_, v_hi_6263_);
v___x_6270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6270_, 0, v_i_6266_);
lean_ctor_set(v___x_6270_, 1, v___x_6269_);
return v___x_6270_;
}
else
{
lean_object* v___x_6271_; lean_object* v_toSignature_6272_; lean_object* v_toSignature_6273_; lean_object* v_name_6274_; lean_object* v_name_6275_; uint8_t v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; uint8_t v___x_6286_; 
v___x_6271_ = lean_array_fget_borrowed(v_as_6265_, v_k_6267_);
v_toSignature_6272_ = lean_ctor_get(v___x_6271_, 0);
v_toSignature_6273_ = lean_ctor_get(v_pivot_6264_, 0);
v_name_6274_ = lean_ctor_get(v_toSignature_6272_, 0);
v_name_6275_ = lean_ctor_get(v_toSignature_6273_, 0);
v___x_6276_ = 0;
v___x_6277_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6276_, v___x_6271_);
v___x_6278_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6279_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6280_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6274_);
v___x_6281_ = l_Lean_Name_toString(v_name_6274_, v___x_6268_);
v___x_6282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6282_, 0, v___x_6277_);
lean_ctor_set(v___x_6282_, 1, v___x_6281_);
v___x_6283_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6276_, v_pivot_6264_);
lean_inc(v_name_6275_);
v___x_6284_ = l_Lean_Name_toString(v_name_6275_, v___x_6268_);
v___x_6285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6285_, 0, v___x_6283_);
lean_ctor_set(v___x_6285_, 1, v___x_6284_);
v___x_6286_ = l_Prod_lexLtDec___redArg(v___x_6278_, v___x_6279_, v___x_6280_, v___x_6282_, v___x_6285_);
if (v___x_6286_ == 0)
{
lean_object* v___x_6287_; lean_object* v___x_6288_; 
v___x_6287_ = lean_unsigned_to_nat(1u);
v___x_6288_ = lean_nat_add(v_k_6267_, v___x_6287_);
lean_dec(v_k_6267_);
v_k_6267_ = v___x_6288_;
goto _start;
}
else
{
lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; 
v___x_6290_ = lean_array_fswap(v_as_6265_, v_i_6266_, v_k_6267_);
v___x_6291_ = lean_unsigned_to_nat(1u);
v___x_6292_ = lean_nat_add(v_i_6266_, v___x_6291_);
lean_dec(v_i_6266_);
v___x_6293_ = lean_nat_add(v_k_6267_, v___x_6291_);
lean_dec(v_k_6267_);
v_as_6265_ = v___x_6290_;
v_i_6266_ = v___x_6292_;
v_k_6267_ = v___x_6293_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6295_, lean_object* v_pivot_6296_, lean_object* v_as_6297_, lean_object* v_i_6298_, lean_object* v_k_6299_){
_start:
{
lean_object* v_res_6300_; 
v_res_6300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6295_, v_pivot_6296_, v_as_6297_, v_i_6298_, v_k_6299_);
lean_dec(v_hi_6295_);
return v_res_6300_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6301_, lean_object* v_l_6302_, lean_object* v_r_6303_){
_start:
{
lean_object* v_toSignature_6304_; lean_object* v_toSignature_6305_; lean_object* v_name_6306_; lean_object* v_name_6307_; uint8_t v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; uint8_t v___x_6318_; 
v_toSignature_6304_ = lean_ctor_get(v_l_6302_, 0);
v_toSignature_6305_ = lean_ctor_get(v_r_6303_, 0);
v_name_6306_ = lean_ctor_get(v_toSignature_6304_, 0);
lean_inc(v_name_6306_);
v_name_6307_ = lean_ctor_get(v_toSignature_6305_, 0);
lean_inc(v_name_6307_);
v___x_6308_ = 0;
v___x_6309_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6308_, v_l_6302_);
lean_dec_ref(v_l_6302_);
v___x_6310_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6311_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6312_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6313_ = l_Lean_Name_toString(v_name_6306_, v___x_6301_);
v___x_6314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6314_, 0, v___x_6309_);
lean_ctor_set(v___x_6314_, 1, v___x_6313_);
v___x_6315_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6308_, v_r_6303_);
lean_dec_ref(v_r_6303_);
v___x_6316_ = l_Lean_Name_toString(v_name_6307_, v___x_6301_);
v___x_6317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6317_, 0, v___x_6315_);
lean_ctor_set(v___x_6317_, 1, v___x_6316_);
v___x_6318_ = l_Prod_lexLtDec___redArg(v___x_6310_, v___x_6311_, v___x_6312_, v___x_6314_, v___x_6317_);
return v___x_6318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6319_, lean_object* v_l_6320_, lean_object* v_r_6321_){
_start:
{
uint8_t v___x_13189__boxed_6322_; uint8_t v_res_6323_; lean_object* v_r_6324_; 
v___x_13189__boxed_6322_ = lean_unbox(v___x_6319_);
v_res_6323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13189__boxed_6322_, v_l_6320_, v_r_6321_);
v_r_6324_ = lean_box(v_res_6323_);
return v_r_6324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6325_, lean_object* v_as_6326_, lean_object* v_lo_6327_, lean_object* v_hi_6328_){
_start:
{
lean_object* v___y_6330_; uint8_t v___x_6340_; 
v___x_6340_ = lean_nat_dec_lt(v_lo_6327_, v_hi_6328_);
if (v___x_6340_ == 0)
{
lean_dec(v_lo_6327_);
return v_as_6326_;
}
else
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v_mid_6343_; lean_object* v___y_6345_; lean_object* v___y_6351_; lean_object* v___x_6356_; lean_object* v___x_6357_; uint8_t v___x_6358_; 
v___x_6341_ = lean_nat_add(v_lo_6327_, v_hi_6328_);
v___x_6342_ = lean_unsigned_to_nat(1u);
v_mid_6343_ = lean_nat_shiftr(v___x_6341_, v___x_6342_);
lean_dec(v___x_6341_);
v___x_6356_ = lean_array_fget_borrowed(v_as_6326_, v_mid_6343_);
v___x_6357_ = lean_array_fget_borrowed(v_as_6326_, v_lo_6327_);
lean_inc(v___x_6357_);
lean_inc(v___x_6356_);
v___x_6358_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6340_, v___x_6356_, v___x_6357_);
if (v___x_6358_ == 0)
{
v___y_6351_ = v_as_6326_;
goto v___jp_6350_;
}
else
{
lean_object* v___x_6359_; 
v___x_6359_ = lean_array_fswap(v_as_6326_, v_lo_6327_, v_mid_6343_);
v___y_6351_ = v___x_6359_;
goto v___jp_6350_;
}
v___jp_6344_:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; uint8_t v___x_6348_; 
v___x_6346_ = lean_array_fget_borrowed(v___y_6345_, v_mid_6343_);
v___x_6347_ = lean_array_fget_borrowed(v___y_6345_, v_hi_6328_);
lean_inc(v___x_6347_);
lean_inc(v___x_6346_);
v___x_6348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6340_, v___x_6346_, v___x_6347_);
if (v___x_6348_ == 0)
{
lean_dec(v_mid_6343_);
v___y_6330_ = v___y_6345_;
goto v___jp_6329_;
}
else
{
lean_object* v___x_6349_; 
v___x_6349_ = lean_array_fswap(v___y_6345_, v_mid_6343_, v_hi_6328_);
lean_dec(v_mid_6343_);
v___y_6330_ = v___x_6349_;
goto v___jp_6329_;
}
}
v___jp_6350_:
{
lean_object* v___x_6352_; lean_object* v___x_6353_; uint8_t v___x_6354_; 
v___x_6352_ = lean_array_fget_borrowed(v___y_6351_, v_hi_6328_);
v___x_6353_ = lean_array_fget_borrowed(v___y_6351_, v_lo_6327_);
lean_inc(v___x_6353_);
lean_inc(v___x_6352_);
v___x_6354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6340_, v___x_6352_, v___x_6353_);
if (v___x_6354_ == 0)
{
v___y_6345_ = v___y_6351_;
goto v___jp_6344_;
}
else
{
lean_object* v___x_6355_; 
v___x_6355_ = lean_array_fswap(v___y_6351_, v_lo_6327_, v_hi_6328_);
v___y_6345_ = v___x_6355_;
goto v___jp_6344_;
}
}
}
v___jp_6329_:
{
lean_object* v_pivot_6331_; lean_object* v___x_6332_; lean_object* v_fst_6333_; lean_object* v_snd_6334_; uint8_t v___x_6335_; 
v_pivot_6331_ = lean_array_fget(v___y_6330_, v_hi_6328_);
lean_inc_n(v_lo_6327_, 2);
v___x_6332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6328_, v_pivot_6331_, v___y_6330_, v_lo_6327_, v_lo_6327_);
v_fst_6333_ = lean_ctor_get(v___x_6332_, 0);
lean_inc(v_fst_6333_);
v_snd_6334_ = lean_ctor_get(v___x_6332_, 1);
lean_inc(v_snd_6334_);
lean_dec_ref(v___x_6332_);
v___x_6335_ = lean_nat_dec_le(v_hi_6328_, v_fst_6333_);
if (v___x_6335_ == 0)
{
lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; 
v___x_6336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6325_, v_snd_6334_, v_lo_6327_, v_fst_6333_);
v___x_6337_ = lean_unsigned_to_nat(1u);
v___x_6338_ = lean_nat_add(v_fst_6333_, v___x_6337_);
lean_dec(v_fst_6333_);
v_as_6326_ = v___x_6336_;
v_lo_6327_ = v___x_6338_;
goto _start;
}
else
{
lean_dec(v_fst_6333_);
lean_dec(v_lo_6327_);
return v_snd_6334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6360_, lean_object* v_as_6361_, lean_object* v_lo_6362_, lean_object* v_hi_6363_){
_start:
{
lean_object* v_res_6364_; 
v_res_6364_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6360_, v_as_6361_, v_lo_6362_, v_hi_6363_);
lean_dec(v_hi_6363_);
lean_dec(v_n_6360_);
return v_res_6364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6365_, lean_object* v___x_6366_, lean_object* v_n_6367_, lean_object* v_j_6368_, lean_object* v_a_6369_){
_start:
{
lean_object* v_zero_6370_; uint8_t v_isZero_6371_; 
v_zero_6370_ = lean_unsigned_to_nat(0u);
v_isZero_6371_ = lean_nat_dec_eq(v_j_6368_, v_zero_6370_);
if (v_isZero_6371_ == 1)
{
lean_dec(v_j_6368_);
return v_a_6369_;
}
else
{
lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v_toSignature_6374_; lean_object* v_name_6375_; lean_object* v___x_6376_; lean_object* v_one_6377_; lean_object* v_n_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6372_ = lean_nat_sub(v_n_6367_, v_j_6368_);
v___x_6373_ = lean_array_fget_borrowed(v___y_6365_, v___x_6372_);
v_toSignature_6374_ = lean_ctor_get(v___x_6373_, 0);
v_name_6375_ = lean_ctor_get(v_toSignature_6374_, 0);
v___x_6376_ = lean_box(0);
v_one_6377_ = lean_unsigned_to_nat(1u);
v_n_6378_ = lean_nat_sub(v_j_6368_, v_one_6377_);
lean_dec(v_j_6368_);
v___x_6379_ = lean_array_get_borrowed(v___x_6376_, v___x_6366_, v___x_6372_);
lean_dec(v___x_6372_);
lean_inc(v___x_6379_);
lean_inc(v_name_6375_);
v___x_6380_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6369_, v_name_6375_, v___x_6379_);
v_j_6368_ = v_n_6378_;
v_a_6369_ = v___x_6380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6382_, lean_object* v___x_6383_, lean_object* v_n_6384_, lean_object* v_j_6385_, lean_object* v_a_6386_){
_start:
{
lean_object* v_res_6387_; 
v_res_6387_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6382_, v___x_6383_, v_n_6384_, v_j_6385_, v_a_6386_);
lean_dec(v_n_6384_);
lean_dec_ref(v___x_6383_);
lean_dec_ref(v___y_6382_);
return v_res_6387_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6388_; 
v___x_6388_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6388_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6389_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6390_, 0, v___x_6389_);
return v___x_6390_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6391_; lean_object* v___x_6392_; 
v___x_6391_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6392_, 0, v___x_6391_);
lean_ctor_set(v___x_6392_, 1, v___x_6391_);
return v___x_6392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6395_, lean_object* v_a_6396_, lean_object* v_a_6397_, lean_object* v_a_6398_, lean_object* v_a_6399_){
_start:
{
lean_object* v___y_6402_; size_t v___y_6403_; lean_object* v___y_6404_; size_t v___y_6405_; lean_object* v___y_6406_; lean_object* v___y_6407_; lean_object* v___y_6441_; lean_object* v___y_6442_; lean_object* v___y_6443_; lean_object* v___y_6444_; uint8_t v___y_6445_; lean_object* v___y_6446_; lean_object* v___y_6447_; uint8_t v___y_6448_; lean_object* v___y_6449_; size_t v___y_6450_; lean_object* v___y_6451_; size_t v___y_6452_; lean_object* v___y_6453_; lean_object* v___y_6454_; lean_object* v_a_6455_; lean_object* v___y_6465_; lean_object* v___y_6466_; lean_object* v___y_6467_; lean_object* v___y_6468_; uint8_t v___y_6469_; lean_object* v___y_6470_; uint8_t v___y_6471_; lean_object* v___y_6472_; size_t v___y_6473_; lean_object* v___y_6474_; size_t v___y_6475_; lean_object* v___y_6476_; lean_object* v___y_6477_; lean_object* v___y_6478_; lean_object* v_a_6479_; lean_object* v___x_6491_; lean_object* v___y_6493_; lean_object* v___y_6494_; lean_object* v___y_6495_; uint8_t v___y_6496_; lean_object* v___y_6497_; uint8_t v___y_6498_; lean_object* v___y_6499_; size_t v___y_6500_; lean_object* v___y_6501_; size_t v___y_6502_; lean_object* v___y_6503_; lean_object* v___y_6504_; lean_object* v___y_6546_; lean_object* v___x_6569_; lean_object* v___y_6571_; lean_object* v___y_6572_; uint8_t v___x_6574_; 
v___x_6491_ = lean_unsigned_to_nat(0u);
v___x_6569_ = lean_array_get_size(v_decls_6395_);
v___x_6574_ = lean_nat_dec_eq(v___x_6569_, v___x_6491_);
if (v___x_6574_ == 0)
{
lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___y_6578_; uint8_t v___x_6580_; 
v___x_6575_ = lean_unsigned_to_nat(1u);
v___x_6576_ = lean_nat_sub(v___x_6569_, v___x_6575_);
v___x_6580_ = lean_nat_dec_le(v___x_6491_, v___x_6576_);
if (v___x_6580_ == 0)
{
lean_inc(v___x_6576_);
v___y_6578_ = v___x_6576_;
goto v___jp_6577_;
}
else
{
v___y_6578_ = v___x_6491_;
goto v___jp_6577_;
}
v___jp_6577_:
{
uint8_t v___x_6579_; 
v___x_6579_ = lean_nat_dec_le(v___y_6578_, v___x_6576_);
if (v___x_6579_ == 0)
{
lean_dec(v___x_6576_);
lean_inc(v___y_6578_);
v___y_6571_ = v___y_6578_;
v___y_6572_ = v___y_6578_;
goto v___jp_6570_;
}
else
{
v___y_6571_ = v___y_6578_;
v___y_6572_ = v___x_6576_;
goto v___jp_6570_;
}
}
}
else
{
v___y_6546_ = v_decls_6395_;
goto v___jp_6545_;
}
v___jp_6401_:
{
if (lean_obj_tag(v___y_6407_) == 0)
{
lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v_assignments_6410_; lean_object* v_funVals_6411_; lean_object* v_env_6412_; lean_object* v_nextMacroScope_6413_; lean_object* v_ngen_6414_; lean_object* v_auxDeclNGen_6415_; lean_object* v_traceState_6416_; lean_object* v_messages_6417_; lean_object* v_infoState_6418_; lean_object* v_snapshotTasks_6419_; lean_object* v___x_6421_; uint8_t v_isShared_6422_; uint8_t v_isSharedCheck_6430_; 
lean_dec_ref_known(v___y_6407_, 1);
v___x_6408_ = lean_st_ref_get(v___y_6406_);
lean_dec(v___y_6406_);
v___x_6409_ = lean_st_ref_take(v_a_6399_);
v_assignments_6410_ = lean_ctor_get(v___x_6408_, 0);
lean_inc_ref(v_assignments_6410_);
v_funVals_6411_ = lean_ctor_get(v___x_6408_, 1);
lean_inc_ref(v_funVals_6411_);
lean_dec(v___x_6408_);
v_env_6412_ = lean_ctor_get(v___x_6409_, 0);
v_nextMacroScope_6413_ = lean_ctor_get(v___x_6409_, 1);
v_ngen_6414_ = lean_ctor_get(v___x_6409_, 2);
v_auxDeclNGen_6415_ = lean_ctor_get(v___x_6409_, 3);
v_traceState_6416_ = lean_ctor_get(v___x_6409_, 4);
v_messages_6417_ = lean_ctor_get(v___x_6409_, 6);
v_infoState_6418_ = lean_ctor_get(v___x_6409_, 7);
v_snapshotTasks_6419_ = lean_ctor_get(v___x_6409_, 8);
v_isSharedCheck_6430_ = !lean_is_exclusive(v___x_6409_);
if (v_isSharedCheck_6430_ == 0)
{
lean_object* v_unused_6431_; 
v_unused_6431_ = lean_ctor_get(v___x_6409_, 5);
lean_dec(v_unused_6431_);
v___x_6421_ = v___x_6409_;
v_isShared_6422_ = v_isSharedCheck_6430_;
goto v_resetjp_6420_;
}
else
{
lean_inc(v_snapshotTasks_6419_);
lean_inc(v_infoState_6418_);
lean_inc(v_messages_6417_);
lean_inc(v_traceState_6416_);
lean_inc(v_auxDeclNGen_6415_);
lean_inc(v_ngen_6414_);
lean_inc(v_nextMacroScope_6413_);
lean_inc(v_env_6412_);
lean_dec(v___x_6409_);
v___x_6421_ = lean_box(0);
v_isShared_6422_ = v_isSharedCheck_6430_;
goto v_resetjp_6420_;
}
v_resetjp_6420_:
{
lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6426_; 
lean_inc(v___y_6404_);
v___x_6423_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6402_, v_funVals_6411_, v___y_6404_, v___y_6404_, v_env_6412_);
lean_dec(v___y_6404_);
lean_dec_ref(v_funVals_6411_);
v___x_6424_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6422_ == 0)
{
lean_ctor_set(v___x_6421_, 5, v___x_6424_);
lean_ctor_set(v___x_6421_, 0, v___x_6423_);
v___x_6426_ = v___x_6421_;
goto v_reusejp_6425_;
}
else
{
lean_object* v_reuseFailAlloc_6429_; 
v_reuseFailAlloc_6429_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6429_, 0, v___x_6423_);
lean_ctor_set(v_reuseFailAlloc_6429_, 1, v_nextMacroScope_6413_);
lean_ctor_set(v_reuseFailAlloc_6429_, 2, v_ngen_6414_);
lean_ctor_set(v_reuseFailAlloc_6429_, 3, v_auxDeclNGen_6415_);
lean_ctor_set(v_reuseFailAlloc_6429_, 4, v_traceState_6416_);
lean_ctor_set(v_reuseFailAlloc_6429_, 5, v___x_6424_);
lean_ctor_set(v_reuseFailAlloc_6429_, 6, v_messages_6417_);
lean_ctor_set(v_reuseFailAlloc_6429_, 7, v_infoState_6418_);
lean_ctor_set(v_reuseFailAlloc_6429_, 8, v_snapshotTasks_6419_);
v___x_6426_ = v_reuseFailAlloc_6429_;
goto v_reusejp_6425_;
}
v_reusejp_6425_:
{
lean_object* v___x_6427_; lean_object* v___x_6428_; 
v___x_6427_ = lean_st_ref_put(v_a_6399_, v___x_6426_);
v___x_6428_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6410_, v___y_6405_, v___y_6403_, v___y_6402_, v_a_6396_, v_a_6397_, v_a_6398_, v_a_6399_);
lean_dec_ref(v_assignments_6410_);
return v___x_6428_;
}
}
}
else
{
lean_object* v_a_6432_; lean_object* v___x_6434_; uint8_t v_isShared_6435_; uint8_t v_isSharedCheck_6439_; 
lean_dec(v___y_6406_);
lean_dec(v___y_6404_);
lean_dec_ref(v___y_6402_);
v_a_6432_ = lean_ctor_get(v___y_6407_, 0);
v_isSharedCheck_6439_ = !lean_is_exclusive(v___y_6407_);
if (v_isSharedCheck_6439_ == 0)
{
v___x_6434_ = v___y_6407_;
v_isShared_6435_ = v_isSharedCheck_6439_;
goto v_resetjp_6433_;
}
else
{
lean_inc(v_a_6432_);
lean_dec(v___y_6407_);
v___x_6434_ = lean_box(0);
v_isShared_6435_ = v_isSharedCheck_6439_;
goto v_resetjp_6433_;
}
v_resetjp_6433_:
{
lean_object* v___x_6437_; 
if (v_isShared_6435_ == 0)
{
v___x_6437_ = v___x_6434_;
goto v_reusejp_6436_;
}
else
{
lean_object* v_reuseFailAlloc_6438_; 
v_reuseFailAlloc_6438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6438_, 0, v_a_6432_);
v___x_6437_ = v_reuseFailAlloc_6438_;
goto v_reusejp_6436_;
}
v_reusejp_6436_:
{
return v___x_6437_;
}
}
}
}
v___jp_6440_:
{
lean_object* v___x_6456_; double v___x_6457_; double v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; 
v___x_6456_ = lean_io_get_num_heartbeats();
v___x_6457_ = lean_float_of_nat(v___y_6446_);
v___x_6458_ = lean_float_of_nat(v___x_6456_);
v___x_6459_ = lean_box_float(v___x_6457_);
v___x_6460_ = lean_box_float(v___x_6458_);
v___x_6461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6461_, 0, v___x_6459_);
lean_ctor_set(v___x_6461_, 1, v___x_6460_);
v___x_6462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6462_, 0, v_a_6455_);
lean_ctor_set(v___x_6462_, 1, v___x_6461_);
lean_inc_ref(v___y_6449_);
lean_inc(v___y_6443_);
v___x_6463_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6443_, v___y_6445_, v___y_6449_, v___y_6451_, v___y_6448_, v___y_6441_, v___y_6454_, v___x_6462_, v___y_6453_, v___y_6447_, v_a_6396_, v_a_6397_, v_a_6398_, v_a_6399_);
lean_dec_ref(v___y_6453_);
v___y_6402_ = v___y_6442_;
v___y_6403_ = v___y_6450_;
v___y_6404_ = v___y_6444_;
v___y_6405_ = v___y_6452_;
v___y_6406_ = v___y_6447_;
v___y_6407_ = v___x_6463_;
goto v___jp_6401_;
}
v___jp_6464_:
{
lean_object* v___x_6480_; double v___x_6481_; double v___x_6482_; double v___x_6483_; double v___x_6484_; double v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6480_ = lean_io_mono_nanos_now();
v___x_6481_ = lean_float_of_nat(v___y_6478_);
v___x_6482_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6483_ = lean_float_div(v___x_6481_, v___x_6482_);
v___x_6484_ = lean_float_of_nat(v___x_6480_);
v___x_6485_ = lean_float_div(v___x_6484_, v___x_6482_);
v___x_6486_ = lean_box_float(v___x_6483_);
v___x_6487_ = lean_box_float(v___x_6485_);
v___x_6488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6488_, 0, v___x_6486_);
lean_ctor_set(v___x_6488_, 1, v___x_6487_);
v___x_6489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6489_, 0, v_a_6479_);
lean_ctor_set(v___x_6489_, 1, v___x_6488_);
lean_inc_ref(v___y_6472_);
lean_inc(v___y_6467_);
v___x_6490_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6467_, v___y_6469_, v___y_6472_, v___y_6474_, v___y_6471_, v___y_6465_, v___y_6477_, v___x_6489_, v___y_6476_, v___y_6470_, v_a_6396_, v_a_6397_, v_a_6398_, v_a_6399_);
lean_dec_ref(v___y_6476_);
v___y_6402_ = v___y_6466_;
v___y_6403_ = v___y_6473_;
v___y_6404_ = v___y_6468_;
v___y_6405_ = v___y_6475_;
v___y_6406_ = v___y_6470_;
v___y_6407_ = v___x_6490_;
goto v___jp_6401_;
}
v___jp_6492_:
{
lean_object* v___x_6505_; lean_object* v_a_6506_; lean_object* v___x_6507_; uint8_t v___x_6508_; 
v___x_6505_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6399_);
v_a_6506_ = lean_ctor_get(v___x_6505_, 0);
lean_inc(v_a_6506_);
lean_dec_ref(v___x_6505_);
v___x_6507_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6508_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6501_, v___x_6507_);
if (v___x_6508_ == 0)
{
lean_object* v___x_6509_; lean_object* v___x_6510_; 
v___x_6509_ = lean_io_mono_nanos_now();
v___x_6510_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6491_, v___y_6503_, v___y_6497_, v_a_6396_, v_a_6397_, v_a_6398_, v_a_6399_);
if (lean_obj_tag(v___x_6510_) == 0)
{
lean_object* v_a_6511_; lean_object* v___x_6513_; uint8_t v_isShared_6514_; uint8_t v_isSharedCheck_6518_; 
v_a_6511_ = lean_ctor_get(v___x_6510_, 0);
v_isSharedCheck_6518_ = !lean_is_exclusive(v___x_6510_);
if (v_isSharedCheck_6518_ == 0)
{
v___x_6513_ = v___x_6510_;
v_isShared_6514_ = v_isSharedCheck_6518_;
goto v_resetjp_6512_;
}
else
{
lean_inc(v_a_6511_);
lean_dec(v___x_6510_);
v___x_6513_ = lean_box(0);
v_isShared_6514_ = v_isSharedCheck_6518_;
goto v_resetjp_6512_;
}
v_resetjp_6512_:
{
lean_object* v___x_6516_; 
if (v_isShared_6514_ == 0)
{
lean_ctor_set_tag(v___x_6513_, 1);
v___x_6516_ = v___x_6513_;
goto v_reusejp_6515_;
}
else
{
lean_object* v_reuseFailAlloc_6517_; 
v_reuseFailAlloc_6517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6517_, 0, v_a_6511_);
v___x_6516_ = v_reuseFailAlloc_6517_;
goto v_reusejp_6515_;
}
v_reusejp_6515_:
{
v___y_6465_ = v_a_6506_;
v___y_6466_ = v___y_6493_;
v___y_6467_ = v___y_6494_;
v___y_6468_ = v___y_6495_;
v___y_6469_ = v___y_6496_;
v___y_6470_ = v___y_6497_;
v___y_6471_ = v___y_6498_;
v___y_6472_ = v___y_6499_;
v___y_6473_ = v___y_6500_;
v___y_6474_ = v___y_6501_;
v___y_6475_ = v___y_6502_;
v___y_6476_ = v___y_6503_;
v___y_6477_ = v___y_6504_;
v___y_6478_ = v___x_6509_;
v_a_6479_ = v___x_6516_;
goto v___jp_6464_;
}
}
}
else
{
lean_object* v_a_6519_; lean_object* v___x_6521_; uint8_t v_isShared_6522_; uint8_t v_isSharedCheck_6526_; 
v_a_6519_ = lean_ctor_get(v___x_6510_, 0);
v_isSharedCheck_6526_ = !lean_is_exclusive(v___x_6510_);
if (v_isSharedCheck_6526_ == 0)
{
v___x_6521_ = v___x_6510_;
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
else
{
lean_inc(v_a_6519_);
lean_dec(v___x_6510_);
v___x_6521_ = lean_box(0);
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
v_resetjp_6520_:
{
lean_object* v___x_6524_; 
if (v_isShared_6522_ == 0)
{
lean_ctor_set_tag(v___x_6521_, 0);
v___x_6524_ = v___x_6521_;
goto v_reusejp_6523_;
}
else
{
lean_object* v_reuseFailAlloc_6525_; 
v_reuseFailAlloc_6525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6525_, 0, v_a_6519_);
v___x_6524_ = v_reuseFailAlloc_6525_;
goto v_reusejp_6523_;
}
v_reusejp_6523_:
{
v___y_6465_ = v_a_6506_;
v___y_6466_ = v___y_6493_;
v___y_6467_ = v___y_6494_;
v___y_6468_ = v___y_6495_;
v___y_6469_ = v___y_6496_;
v___y_6470_ = v___y_6497_;
v___y_6471_ = v___y_6498_;
v___y_6472_ = v___y_6499_;
v___y_6473_ = v___y_6500_;
v___y_6474_ = v___y_6501_;
v___y_6475_ = v___y_6502_;
v___y_6476_ = v___y_6503_;
v___y_6477_ = v___y_6504_;
v___y_6478_ = v___x_6509_;
v_a_6479_ = v___x_6524_;
goto v___jp_6464_;
}
}
}
}
else
{
lean_object* v___x_6527_; lean_object* v___x_6528_; 
v___x_6527_ = lean_io_get_num_heartbeats();
v___x_6528_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6491_, v___y_6503_, v___y_6497_, v_a_6396_, v_a_6397_, v_a_6398_, v_a_6399_);
if (lean_obj_tag(v___x_6528_) == 0)
{
lean_object* v_a_6529_; lean_object* v___x_6531_; uint8_t v_isShared_6532_; uint8_t v_isSharedCheck_6536_; 
v_a_6529_ = lean_ctor_get(v___x_6528_, 0);
v_isSharedCheck_6536_ = !lean_is_exclusive(v___x_6528_);
if (v_isSharedCheck_6536_ == 0)
{
v___x_6531_ = v___x_6528_;
v_isShared_6532_ = v_isSharedCheck_6536_;
goto v_resetjp_6530_;
}
else
{
lean_inc(v_a_6529_);
lean_dec(v___x_6528_);
v___x_6531_ = lean_box(0);
v_isShared_6532_ = v_isSharedCheck_6536_;
goto v_resetjp_6530_;
}
v_resetjp_6530_:
{
lean_object* v___x_6534_; 
if (v_isShared_6532_ == 0)
{
lean_ctor_set_tag(v___x_6531_, 1);
v___x_6534_ = v___x_6531_;
goto v_reusejp_6533_;
}
else
{
lean_object* v_reuseFailAlloc_6535_; 
v_reuseFailAlloc_6535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6535_, 0, v_a_6529_);
v___x_6534_ = v_reuseFailAlloc_6535_;
goto v_reusejp_6533_;
}
v_reusejp_6533_:
{
v___y_6441_ = v_a_6506_;
v___y_6442_ = v___y_6493_;
v___y_6443_ = v___y_6494_;
v___y_6444_ = v___y_6495_;
v___y_6445_ = v___y_6496_;
v___y_6446_ = v___x_6527_;
v___y_6447_ = v___y_6497_;
v___y_6448_ = v___y_6498_;
v___y_6449_ = v___y_6499_;
v___y_6450_ = v___y_6500_;
v___y_6451_ = v___y_6501_;
v___y_6452_ = v___y_6502_;
v___y_6453_ = v___y_6503_;
v___y_6454_ = v___y_6504_;
v_a_6455_ = v___x_6534_;
goto v___jp_6440_;
}
}
}
else
{
lean_object* v_a_6537_; lean_object* v___x_6539_; uint8_t v_isShared_6540_; uint8_t v_isSharedCheck_6544_; 
v_a_6537_ = lean_ctor_get(v___x_6528_, 0);
v_isSharedCheck_6544_ = !lean_is_exclusive(v___x_6528_);
if (v_isSharedCheck_6544_ == 0)
{
v___x_6539_ = v___x_6528_;
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
else
{
lean_inc(v_a_6537_);
lean_dec(v___x_6528_);
v___x_6539_ = lean_box(0);
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
v_resetjp_6538_:
{
lean_object* v___x_6542_; 
if (v_isShared_6540_ == 0)
{
lean_ctor_set_tag(v___x_6539_, 0);
v___x_6542_ = v___x_6539_;
goto v_reusejp_6541_;
}
else
{
lean_object* v_reuseFailAlloc_6543_; 
v_reuseFailAlloc_6543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6537_);
v___x_6542_ = v_reuseFailAlloc_6543_;
goto v_reusejp_6541_;
}
v_reusejp_6541_:
{
v___y_6441_ = v_a_6506_;
v___y_6442_ = v___y_6493_;
v___y_6443_ = v___y_6494_;
v___y_6444_ = v___y_6495_;
v___y_6445_ = v___y_6496_;
v___y_6446_ = v___x_6527_;
v___y_6447_ = v___y_6497_;
v___y_6448_ = v___y_6498_;
v___y_6449_ = v___y_6499_;
v___y_6450_ = v___y_6500_;
v___y_6451_ = v___y_6501_;
v___y_6452_ = v___y_6502_;
v___y_6453_ = v___y_6503_;
v___y_6454_ = v___y_6504_;
v_a_6455_ = v___x_6542_;
goto v___jp_6440_;
}
}
}
}
}
v___jp_6545_:
{
size_t v_sz_6547_; size_t v___x_6548_; lean_object* v_assignments_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v_funVals_6552_; lean_object* v_state_6553_; lean_object* v___x_6554_; lean_object* v_toCold_6555_; lean_object* v_options_6556_; lean_object* v_inheritedTraceOptions_6557_; uint8_t v_hasTrace_6558_; lean_object* v_ctx_6559_; 
v_sz_6547_ = lean_array_size(v___y_6546_);
v___x_6548_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6546_, 2);
v_assignments_6549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6547_, v___x_6548_, v___y_6546_);
v___x_6550_ = lean_array_get_size(v___y_6546_);
v___x_6551_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6552_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6546_, v___x_6550_, v___x_6550_, v___x_6551_);
v_state_6553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6553_, 0, v_assignments_6549_);
lean_ctor_set(v_state_6553_, 1, v_funVals_6552_);
v___x_6554_ = lean_st_mk_ref(v_state_6553_);
v_toCold_6555_ = lean_ctor_get(v_a_6398_, 0);
v_options_6556_ = lean_ctor_get(v_toCold_6555_, 2);
v_inheritedTraceOptions_6557_ = lean_ctor_get(v_toCold_6555_, 11);
v_hasTrace_6558_ = lean_ctor_get_uint8(v_options_6556_, sizeof(void*)*1);
v_ctx_6559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6559_, 0, v___y_6546_);
lean_ctor_set(v_ctx_6559_, 1, v___x_6491_);
if (v_hasTrace_6558_ == 0)
{
lean_object* v___x_6560_; 
v___x_6560_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6491_, v_ctx_6559_, v___x_6554_, v_a_6396_, v_a_6397_, v_a_6398_, v_a_6399_);
lean_dec_ref_known(v_ctx_6559_, 2);
v___y_6402_ = v___y_6546_;
v___y_6403_ = v___x_6548_;
v___y_6404_ = v___x_6550_;
v___y_6405_ = v_sz_6547_;
v___y_6406_ = v___x_6554_;
v___y_6407_ = v___x_6560_;
goto v___jp_6401_;
}
else
{
lean_object* v___f_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; uint8_t v___x_6565_; 
lean_inc_ref(v___y_6546_);
v___f_6561_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6561_, 0, v___y_6546_);
v___x_6562_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6563_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6564_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6565_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6557_, v_options_6556_, v___x_6564_);
if (v___x_6565_ == 0)
{
lean_object* v___x_6566_; uint8_t v___x_6567_; 
v___x_6566_ = l_Lean_trace_profiler;
v___x_6567_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6556_, v___x_6566_);
if (v___x_6567_ == 0)
{
lean_object* v___x_6568_; 
lean_dec_ref(v___f_6561_);
v___x_6568_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6491_, v_ctx_6559_, v___x_6554_, v_a_6396_, v_a_6397_, v_a_6398_, v_a_6399_);
lean_dec_ref_known(v_ctx_6559_, 2);
v___y_6402_ = v___y_6546_;
v___y_6403_ = v___x_6548_;
v___y_6404_ = v___x_6550_;
v___y_6405_ = v_sz_6547_;
v___y_6406_ = v___x_6554_;
v___y_6407_ = v___x_6568_;
goto v___jp_6401_;
}
else
{
v___y_6493_ = v___y_6546_;
v___y_6494_ = v___x_6562_;
v___y_6495_ = v___x_6550_;
v___y_6496_ = v_hasTrace_6558_;
v___y_6497_ = v___x_6554_;
v___y_6498_ = v___x_6565_;
v___y_6499_ = v___x_6563_;
v___y_6500_ = v___x_6548_;
v___y_6501_ = v_options_6556_;
v___y_6502_ = v_sz_6547_;
v___y_6503_ = v_ctx_6559_;
v___y_6504_ = v___f_6561_;
goto v___jp_6492_;
}
}
else
{
v___y_6493_ = v___y_6546_;
v___y_6494_ = v___x_6562_;
v___y_6495_ = v___x_6550_;
v___y_6496_ = v_hasTrace_6558_;
v___y_6497_ = v___x_6554_;
v___y_6498_ = v___x_6565_;
v___y_6499_ = v___x_6563_;
v___y_6500_ = v___x_6548_;
v___y_6501_ = v_options_6556_;
v___y_6502_ = v_sz_6547_;
v___y_6503_ = v_ctx_6559_;
v___y_6504_ = v___f_6561_;
goto v___jp_6492_;
}
}
}
v___jp_6570_:
{
lean_object* v___x_6573_; 
v___x_6573_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6569_, v_decls_6395_, v___y_6571_, v___y_6572_);
lean_dec(v___y_6572_);
v___y_6546_ = v___x_6573_;
goto v___jp_6545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_){
_start:
{
lean_object* v_res_6587_; 
v_res_6587_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6581_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_);
lean_dec(v_a_6585_);
lean_dec_ref(v_a_6584_);
lean_dec(v_a_6583_);
lean_dec_ref(v_a_6582_);
return v_res_6587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6588_, lean_object* v_n_6589_, lean_object* v_j_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_){
_start:
{
lean_object* v___x_6593_; 
v___x_6593_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6588_, v_n_6589_, v_j_6590_, v_a_6592_);
return v___x_6593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6594_, lean_object* v_n_6595_, lean_object* v_j_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_){
_start:
{
lean_object* v_res_6599_; 
v_res_6599_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6594_, v_n_6595_, v_j_6596_, v_a_6597_, v_a_6598_);
lean_dec(v_n_6595_);
lean_dec_ref(v___y_6594_);
return v_res_6599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6600_, lean_object* v___x_6601_, lean_object* v_n_6602_, lean_object* v_j_6603_, lean_object* v_a_6604_, lean_object* v_a_6605_){
_start:
{
lean_object* v___x_6606_; 
v___x_6606_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6600_, v___x_6601_, v_n_6602_, v_j_6603_, v_a_6605_);
return v___x_6606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6607_, lean_object* v___x_6608_, lean_object* v_n_6609_, lean_object* v_j_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_){
_start:
{
lean_object* v_res_6613_; 
v_res_6613_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6607_, v___x_6608_, v_n_6609_, v_j_6610_, v_a_6611_, v_a_6612_);
lean_dec(v_n_6609_);
lean_dec_ref(v___x_6608_);
lean_dec_ref(v___y_6607_);
return v_res_6613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6614_, lean_object* v_as_6615_, size_t v_sz_6616_, size_t v_i_6617_, lean_object* v_bs_6618_, lean_object* v___y_6619_, lean_object* v___y_6620_, lean_object* v___y_6621_, lean_object* v___y_6622_){
_start:
{
lean_object* v___x_6624_; 
v___x_6624_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6614_, v_sz_6616_, v_i_6617_, v_bs_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_);
return v___x_6624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6625_, lean_object* v_as_6626_, lean_object* v_sz_6627_, lean_object* v_i_6628_, lean_object* v_bs_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_){
_start:
{
size_t v_sz_boxed_6635_; size_t v_i_boxed_6636_; lean_object* v_res_6637_; 
v_sz_boxed_6635_ = lean_unbox_usize(v_sz_6627_);
lean_dec(v_sz_6627_);
v_i_boxed_6636_ = lean_unbox_usize(v_i_6628_);
lean_dec(v_i_6628_);
v_res_6637_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6625_, v_as_6626_, v_sz_boxed_6635_, v_i_boxed_6636_, v_bs_6629_, v___y_6630_, v___y_6631_, v___y_6632_, v___y_6633_);
lean_dec(v___y_6633_);
lean_dec_ref(v___y_6632_);
lean_dec(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_as_6626_);
lean_dec_ref(v___x_6625_);
return v_res_6637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6638_, lean_object* v_as_6639_, lean_object* v_lo_6640_, lean_object* v_hi_6641_, lean_object* v_w_6642_, lean_object* v_hlo_6643_, lean_object* v_hhi_6644_){
_start:
{
lean_object* v___x_6645_; 
v___x_6645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6638_, v_as_6639_, v_lo_6640_, v_hi_6641_);
return v___x_6645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6646_, lean_object* v_as_6647_, lean_object* v_lo_6648_, lean_object* v_hi_6649_, lean_object* v_w_6650_, lean_object* v_hlo_6651_, lean_object* v_hhi_6652_){
_start:
{
lean_object* v_res_6653_; 
v_res_6653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6646_, v_as_6647_, v_lo_6648_, v_hi_6649_, v_w_6650_, v_hlo_6651_, v_hhi_6652_);
lean_dec(v_hi_6649_);
lean_dec(v_n_6646_);
return v_res_6653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6654_, lean_object* v_lo_6655_, lean_object* v_hi_6656_, lean_object* v_hhi_6657_, lean_object* v_pivot_6658_, lean_object* v_as_6659_, lean_object* v_i_6660_, lean_object* v_k_6661_, lean_object* v_ilo_6662_, lean_object* v_ik_6663_, lean_object* v_w_6664_){
_start:
{
lean_object* v___x_6665_; 
v___x_6665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6656_, v_pivot_6658_, v_as_6659_, v_i_6660_, v_k_6661_);
return v___x_6665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6666_, lean_object* v_lo_6667_, lean_object* v_hi_6668_, lean_object* v_hhi_6669_, lean_object* v_pivot_6670_, lean_object* v_as_6671_, lean_object* v_i_6672_, lean_object* v_k_6673_, lean_object* v_ilo_6674_, lean_object* v_ik_6675_, lean_object* v_w_6676_){
_start:
{
lean_object* v_res_6677_; 
v_res_6677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6666_, v_lo_6667_, v_hi_6668_, v_hhi_6669_, v_pivot_6670_, v_as_6671_, v_i_6672_, v_k_6673_, v_ilo_6674_, v_ik_6675_, v_w_6676_);
lean_dec(v_hi_6668_);
lean_dec(v_lo_6667_);
lean_dec(v_n_6666_);
return v_res_6677_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
v___x_6737_ = lean_unsigned_to_nat(3955956072u);
v___x_6738_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6739_ = l_Lean_Name_num___override(v___x_6738_, v___x_6737_);
return v___x_6739_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6741_; lean_object* v___x_6742_; lean_object* v___x_6743_; 
v___x_6741_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6742_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6743_ = l_Lean_Name_str___override(v___x_6742_, v___x_6741_);
return v___x_6743_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6745_; lean_object* v___x_6746_; lean_object* v___x_6747_; 
v___x_6745_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6746_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6747_ = l_Lean_Name_str___override(v___x_6746_, v___x_6745_);
return v___x_6747_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; 
v___x_6748_ = lean_unsigned_to_nat(2u);
v___x_6749_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6750_ = l_Lean_Name_num___override(v___x_6749_, v___x_6748_);
return v___x_6750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6752_; uint8_t v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; 
v___x_6752_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6753_ = 1;
v___x_6754_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6755_ = l_Lean_registerTraceClass(v___x_6752_, v___x_6753_, v___x_6754_);
return v___x_6755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6756_){
_start:
{
lean_object* v_res_6757_; 
v_res_6757_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6757_;
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
