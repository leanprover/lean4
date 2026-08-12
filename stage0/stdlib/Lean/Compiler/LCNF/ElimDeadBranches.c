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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_158__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v___x_158__boxed_338_ = lean_unbox(v___x_336_);
v_res_339_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(v___x_158__boxed_338_, v_v_337_);
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
uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = 1;
v___x_394_ = lean_array_uget_borrowed(v_as_389_, v_i_390_);
v___x_395_ = lean_box(1);
v___x_396_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
return v___x_393_;
}
else
{
if (v___x_392_ == 0)
{
size_t v___x_397_; size_t v___x_398_; 
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_390_, v___x_397_);
v_i_390_ = v___x_398_;
goto _start;
}
else
{
return v___x_393_;
}
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
v___x_517_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v___y_515_, v_env_510_, v___x_516_);
if (v___x_517_ == 0)
{
return v___y_514_;
}
else
{
lean_object* v___x_518_; 
lean_dec(v___y_514_);
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
v___y_514_ = v___y_520_;
v___y_515_ = v_i_521_;
goto v___jp_513_;
}
else
{
if (v___x_525_ == 0)
{
lean_dec_ref(v_vs_522_);
v___y_514_ = v___y_520_;
v___y_515_ = v_i_521_;
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
v___y_514_ = v___y_520_;
v___y_515_ = v_i_521_;
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
uint8_t v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = 1;
v___x_928_ = lean_array_uget_borrowed(v_as_923_, v_i_924_);
v___x_929_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v___x_928_);
if (v___x_929_ == 0)
{
return v___x_927_;
}
else
{
if (v___x_926_ == 0)
{
size_t v___x_930_; size_t v___x_931_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_924_, v___x_930_);
v_i_924_ = v___x_931_;
goto _start;
}
else
{
return v___x_927_;
}
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
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; lean_object* v___x_1979__overap_1024_; lean_object* v___x_1025_; 
v___x_1018_ = l_StateRefT_x27_instMonad___redArg(v___x_1017_);
v___x_1019_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_instInhabitedOfMonad___redArg(v___x_1018_, v___x_1021_);
v___f_1023_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1023_, 0, v___x_1022_);
v___x_1979__overap_1024_ = lean_panic_fn_borrowed(v___f_1023_, v_msg_987_);
lean_dec_ref(v___f_1023_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
v___x_1025_ = lean_apply_5(v___x_1979__overap_1024_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
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
v___y_1098_ = v___y_1154_;
v___y_1099_ = v___y_1156_;
v___y_1100_ = v___y_1155_;
v___y_1101_ = v_ctorName_1152_;
v___y_1102_ = v___y_1153_;
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
v___y_1098_ = v___y_1154_;
v___y_1099_ = v___y_1156_;
v___y_1100_ = v___y_1155_;
v___y_1101_ = v_ctorName_1152_;
v___y_1102_ = v___y_1153_;
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
v___y_1131_ = v___y_1154_;
v___y_1132_ = v___y_1156_;
v___y_1133_ = v___y_1155_;
v___y_1134_ = v_ctorName_1152_;
v___y_1135_ = v___y_1153_;
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
v___y_1131_ = v___y_1154_;
v___y_1132_ = v___y_1156_;
v___y_1133_ = v___y_1155_;
v___y_1134_ = v_ctorName_1152_;
v___y_1135_ = v___y_1153_;
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
lean_ctor_set(v___x_1107_, 0, v___y_1101_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
lean_ctor_set(v___x_1107_, 2, v_snd_1104_);
v___x_1108_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1109_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1105_, v___x_1107_, v___x_1108_, v___y_1102_, v___y_1098_, v___y_1100_, v___y_1099_);
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
return v___x_1397_;
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
size_t v_x_1160__boxed_1428_; uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_x_1160__boxed_1428_ = lean_unbox_usize(v_x_1426_);
lean_dec(v_x_1426_);
v_res_1429_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1425_, v_x_1160__boxed_1428_, v_x_1427_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
lean_object* v_es_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_es_1475_ = lean_ctor_get(v_x_1473_, 0);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_get_size(v_es_1475_);
v___x_1478_ = lean_nat_dec_lt(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_dec(v_f_1472_);
return v_x_1474_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_nat_dec_le(v___x_1477_, v___x_1477_);
if (v___x_1479_ == 0)
{
if (v___x_1478_ == 0)
{
lean_dec(v_f_1472_);
return v_x_1474_;
}
else
{
size_t v___x_1480_; size_t v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = ((size_t)0ULL);
v___x_1481_ = lean_usize_of_nat(v___x_1477_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1472_, v_es_1475_, v___x_1480_, v___x_1481_, v_x_1474_);
return v___x_1482_;
}
}
else
{
size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((size_t)0ULL);
v___x_1484_ = lean_usize_of_nat(v___x_1477_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1472_, v_es_1475_, v___x_1483_, v___x_1484_, v_x_1474_);
return v___x_1485_;
}
}
}
else
{
lean_object* v_ks_1486_; lean_object* v_vs_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_ks_1486_ = lean_ctor_get(v_x_1473_, 0);
v_vs_1487_ = lean_ctor_get(v_x_1473_, 1);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1472_, v_ks_1486_, v_vs_1487_, v___x_1488_, v_x_1474_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1490_, lean_object* v_as_1491_, size_t v_i_1492_, size_t v_stop_1493_, lean_object* v_b_1494_){
_start:
{
lean_object* v___y_1496_; uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_eq(v_i_1492_, v_stop_1493_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_array_uget_borrowed(v_as_1491_, v_i_1492_);
switch(lean_obj_tag(v___x_1501_))
{
case 0:
{
lean_object* v_key_1502_; lean_object* v_val_1503_; lean_object* v___x_1504_; 
v_key_1502_ = lean_ctor_get(v___x_1501_, 0);
v_val_1503_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_f_1490_);
lean_inc(v_val_1503_);
lean_inc(v_key_1502_);
v___x_1504_ = lean_apply_3(v_f_1490_, v_b_1494_, v_key_1502_, v_val_1503_);
v___y_1496_ = v___x_1504_;
goto v___jp_1495_;
}
case 1:
{
lean_object* v_node_1505_; lean_object* v___x_1506_; 
v_node_1505_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_f_1490_);
v___x_1506_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1490_, v_node_1505_, v_b_1494_);
v___y_1496_ = v___x_1506_;
goto v___jp_1495_;
}
default: 
{
v___y_1496_ = v_b_1494_;
goto v___jp_1495_;
}
}
}
else
{
lean_dec(v_f_1490_);
return v_b_1494_;
}
v___jp_1495_:
{
size_t v___x_1497_; size_t v___x_1498_; 
v___x_1497_ = ((size_t)1ULL);
v___x_1498_ = lean_usize_add(v_i_1492_, v___x_1497_);
v_i_1492_ = v___x_1498_;
v_b_1494_ = v___y_1496_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1515_, v_x_1516_, v_x_1517_);
lean_dec_ref(v_x_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1519_, lean_object* v_x1_1520_, lean_object* v_x2_1521_, lean_object* v_x3_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_apply_3(v_f_1519_, v_x1_1520_, v_x2_1521_, v_x3_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1524_, lean_object* v_f_1525_, lean_object* v_init_1526_){
_start:
{
lean_object* v___f_1527_; lean_object* v___x_1528_; 
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1527_, 0, v_f_1525_);
v___x_1528_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1527_, v_map_1524_, v_init_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1529_, lean_object* v_f_1530_, lean_object* v_init_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1529_, v_f_1530_, v_init_1531_);
lean_dec_ref(v_map_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1533_, lean_object* v_k_1534_, lean_object* v_v_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_k_1534_);
lean_ctor_set(v___x_1536_, 1, v_v_1535_);
v___x_1537_ = lean_array_push(v_ps_1533_, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1541_){
_start:
{
lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___f_1542_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1543_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1544_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1541_, v___f_1542_, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1545_);
lean_dec_ref(v_m_1545_);
return v_res_1546_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_fst_1549_; lean_object* v_fst_1550_; uint8_t v___x_1551_; 
v_fst_1549_ = lean_ctor_get(v___y_1547_, 0);
v_fst_1550_ = lean_ctor_get(v___y_1548_, 0);
v___x_1551_ = l_Lean_Name_quickLt(v_fst_1549_, v_fst_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1552_, v___y_1553_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___y_1552_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_hi_1556_, lean_object* v_pivot_1557_, lean_object* v_as_1558_, lean_object* v_i_1559_, lean_object* v_k_1560_){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_nat_dec_lt(v_k_1560_, v_hi_1556_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_k_1560_);
v___x_1562_ = lean_array_fswap(v_as_1558_, v_i_1559_, v_hi_1556_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_i_1559_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; lean_object* v_fst_1565_; lean_object* v_fst_1566_; uint8_t v___x_1567_; 
v___x_1564_ = lean_array_fget_borrowed(v_as_1558_, v_k_1560_);
v_fst_1565_ = lean_ctor_get(v___x_1564_, 0);
v_fst_1566_ = lean_ctor_get(v_pivot_1557_, 0);
v___x_1567_ = l_Lean_Name_quickLt(v_fst_1565_, v_fst_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_add(v_k_1560_, v___x_1568_);
lean_dec(v_k_1560_);
v_k_1560_ = v___x_1569_;
goto _start;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1571_ = lean_array_fswap(v_as_1558_, v_i_1559_, v_k_1560_);
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_add(v_i_1559_, v___x_1572_);
lean_dec(v_i_1559_);
v___x_1574_ = lean_nat_add(v_k_1560_, v___x_1572_);
lean_dec(v_k_1560_);
v_as_1558_ = v___x_1571_;
v_i_1559_ = v___x_1573_;
v_k_1560_ = v___x_1574_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_hi_1576_, lean_object* v_pivot_1577_, lean_object* v_as_1578_, lean_object* v_i_1579_, lean_object* v_k_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1576_, v_pivot_1577_, v_as_1578_, v_i_1579_, v_k_1580_);
lean_dec_ref(v_pivot_1577_);
lean_dec(v_hi_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_1582_, lean_object* v_as_1583_, lean_object* v_lo_1584_, lean_object* v_hi_1585_){
_start:
{
lean_object* v___y_1587_; uint8_t v___x_1597_; 
v___x_1597_ = lean_nat_dec_lt(v_lo_1584_, v_hi_1585_);
if (v___x_1597_ == 0)
{
lean_dec(v_lo_1584_);
return v_as_1583_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v_mid_1600_; lean_object* v___y_1602_; lean_object* v___y_1608_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1598_ = lean_nat_add(v_lo_1584_, v_hi_1585_);
v___x_1599_ = lean_unsigned_to_nat(1u);
v_mid_1600_ = lean_nat_shiftr(v___x_1598_, v___x_1599_);
lean_dec(v___x_1598_);
v___x_1613_ = lean_array_fget_borrowed(v_as_1583_, v_mid_1600_);
v___x_1614_ = lean_array_fget_borrowed(v_as_1583_, v_lo_1584_);
v___x_1615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
v___y_1608_ = v_as_1583_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_array_fswap(v_as_1583_, v_lo_1584_, v_mid_1600_);
v___y_1608_ = v___x_1616_;
goto v___jp_1607_;
}
v___jp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1603_ = lean_array_fget_borrowed(v___y_1602_, v_mid_1600_);
v___x_1604_ = lean_array_fget_borrowed(v___y_1602_, v_hi_1585_);
v___x_1605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_dec(v_mid_1600_);
v___y_1587_ = v___y_1602_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_array_fswap(v___y_1602_, v_mid_1600_, v_hi_1585_);
lean_dec(v_mid_1600_);
v___y_1587_ = v___x_1606_;
goto v___jp_1586_;
}
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = lean_array_fget_borrowed(v___y_1608_, v_hi_1585_);
v___x_1610_ = lean_array_fget_borrowed(v___y_1608_, v_lo_1584_);
v___x_1611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
v___y_1602_ = v___y_1608_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_array_fswap(v___y_1608_, v_lo_1584_, v_hi_1585_);
v___y_1602_ = v___x_1612_;
goto v___jp_1601_;
}
}
}
v___jp_1586_:
{
lean_object* v_pivot_1588_; lean_object* v___x_1589_; lean_object* v_fst_1590_; lean_object* v_snd_1591_; uint8_t v___x_1592_; 
v_pivot_1588_ = lean_array_fget(v___y_1587_, v_hi_1585_);
lean_inc_n(v_lo_1584_, 2);
v___x_1589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1585_, v_pivot_1588_, v___y_1587_, v_lo_1584_, v_lo_1584_);
lean_dec(v_pivot_1588_);
v_fst_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_fst_1590_);
v_snd_1591_ = lean_ctor_get(v___x_1589_, 1);
lean_inc(v_snd_1591_);
lean_dec_ref(v___x_1589_);
v___x_1592_ = lean_nat_dec_le(v_hi_1585_, v_fst_1590_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1582_, v_snd_1591_, v_lo_1584_, v_fst_1590_);
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = lean_nat_add(v_fst_1590_, v___x_1594_);
lean_dec(v_fst_1590_);
v_as_1583_ = v___x_1593_;
v_lo_1584_ = v___x_1595_;
goto _start;
}
else
{
lean_dec(v_fst_1590_);
lean_dec(v_lo_1584_);
return v_snd_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_1617_, lean_object* v_as_1618_, lean_object* v_lo_1619_, lean_object* v_hi_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1617_, v_as_1618_, v_lo_1619_, v_hi_1620_);
lean_dec(v_hi_1620_);
lean_dec(v_n_1617_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1624_, lean_object* v_s_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___y_1632_; lean_object* v___y_1633_; uint8_t v___x_1636_; 
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1629_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1625_);
v___x_1630_ = lean_array_get_size(v___x_1629_);
v___x_1636_ = lean_nat_dec_eq(v___x_1630_, v___x_1627_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___y_1640_; uint8_t v___x_1642_; 
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_sub(v___x_1630_, v___x_1637_);
v___x_1642_ = lean_nat_dec_le(v___x_1627_, v___x_1638_);
if (v___x_1642_ == 0)
{
lean_inc(v___x_1638_);
v___y_1640_ = v___x_1638_;
goto v___jp_1639_;
}
else
{
v___y_1640_ = v___x_1627_;
goto v___jp_1639_;
}
v___jp_1639_:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_le(v___y_1640_, v___x_1638_);
if (v___x_1641_ == 0)
{
lean_dec(v___x_1638_);
lean_inc(v___y_1640_);
v___y_1632_ = v___y_1640_;
v___y_1633_ = v___y_1640_;
goto v___jp_1631_;
}
else
{
v___y_1632_ = v___y_1640_;
v___y_1633_ = v___x_1638_;
goto v___jp_1631_;
}
}
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1628_);
lean_ctor_set(v___x_1643_, 1, v___x_1628_);
lean_ctor_set(v___x_1643_, 2, v___x_1629_);
return v___x_1643_;
}
v___jp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1630_, v___x_1629_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
v___x_1635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1628_);
lean_ctor_set(v___x_1635_, 1, v___x_1628_);
lean_ctor_set(v___x_1635_, 2, v___x_1634_);
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1644_, lean_object* v_s_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1644_, v_s_1645_, v_x_1646_);
lean_dec(v_x_1646_);
lean_dec_ref(v_s_1645_);
lean_dec_ref(v_x_1644_);
return v_res_1647_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1653_);
lean_dec_ref(v_x_1653_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_ks_1659_; lean_object* v_vs_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1684_; 
v_ks_1659_ = lean_ctor_get(v_x_1655_, 0);
v_vs_1660_ = lean_ctor_get(v_x_1655_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1655_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1662_ = v_x_1655_;
v_isShared_1663_ = v_isSharedCheck_1684_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_vs_1660_);
lean_inc(v_ks_1659_);
lean_dec(v_x_1655_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1684_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_array_get_size(v_ks_1659_);
v___x_1665_ = lean_nat_dec_lt(v_x_1656_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec(v_x_1656_);
v___x_1666_ = lean_array_push(v_ks_1659_, v_x_1657_);
v___x_1667_ = lean_array_push(v_vs_1660_, v_x_1658_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1667_);
lean_ctor_set(v___x_1662_, 0, v___x_1666_);
v___x_1669_ = v___x_1662_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
else
{
lean_object* v_k_x27_1671_; uint8_t v___x_1672_; 
v_k_x27_1671_ = lean_array_fget_borrowed(v_ks_1659_, v_x_1656_);
v___x_1672_ = lean_name_eq(v_x_1657_, v_k_x27_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1674_; 
if (v_isShared_1663_ == 0)
{
v___x_1674_ = v___x_1662_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_ks_1659_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_vs_1660_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_nat_add(v_x_1656_, v___x_1675_);
lean_dec(v_x_1656_);
v_x_1655_ = v___x_1674_;
v_x_1656_ = v___x_1676_;
goto _start;
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1679_ = lean_array_fset(v_ks_1659_, v_x_1656_, v_x_1657_);
v___x_1680_ = lean_array_fset(v_vs_1660_, v_x_1656_, v_x_1658_);
lean_dec(v_x_1656_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1680_);
lean_ctor_set(v___x_1662_, 0, v___x_1679_);
v___x_1682_ = v___x_1662_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_n_1685_, lean_object* v_k_1686_, lean_object* v_v_1687_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_n_1685_, v___x_1688_, v_k_1686_, v_v_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_x_1691_, size_t v_x_1692_, size_t v_x_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
lean_object* v_es_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v_j_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_es_1696_ = lean_ctor_get(v_x_1691_, 0);
v___x_1697_ = ((size_t)31ULL);
v___x_1698_ = lean_usize_land(v_x_1692_, v___x_1697_);
v_j_1699_ = lean_usize_to_nat(v___x_1698_);
v___x_1700_ = lean_array_get_size(v_es_1696_);
v___x_1701_ = lean_nat_dec_lt(v_j_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_dec(v_j_1699_);
lean_dec(v_x_1695_);
lean_dec(v_x_1694_);
return v_x_1691_;
}
else
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1740_; 
lean_inc_ref(v_es_1696_);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1740_ == 0)
{
lean_object* v_unused_1741_; 
v_unused_1741_ = lean_ctor_get(v_x_1691_, 0);
lean_dec(v_unused_1741_);
v___x_1703_ = v_x_1691_;
v_isShared_1704_ = v_isSharedCheck_1740_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_x_1691_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1740_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_v_1705_; lean_object* v___x_1706_; lean_object* v_xs_x27_1707_; lean_object* v___y_1709_; 
v_v_1705_ = lean_array_fget(v_es_1696_, v_j_1699_);
v___x_1706_ = lean_box(0);
v_xs_x27_1707_ = lean_array_fset(v_es_1696_, v_j_1699_, v___x_1706_);
switch(lean_obj_tag(v_v_1705_))
{
case 0:
{
lean_object* v_key_1714_; lean_object* v_val_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
v_key_1714_ = lean_ctor_get(v_v_1705_, 0);
v_val_1715_ = lean_ctor_get(v_v_1705_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_v_1705_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1717_ = v_v_1705_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_val_1715_);
lean_inc(v_key_1714_);
lean_dec(v_v_1705_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_name_eq(v_x_1694_, v_key_1714_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_del_object(v___x_1717_);
v___x_1720_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1714_, v_val_1715_, v_x_1694_, v_x_1695_);
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
v___y_1709_ = v___x_1721_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1723_; 
lean_dec(v_val_1715_);
lean_dec(v_key_1714_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v_x_1695_);
lean_ctor_set(v___x_1717_, 0, v_x_1694_);
v___x_1723_ = v___x_1717_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_x_1694_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_x_1695_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
v___y_1709_ = v___x_1723_;
goto v___jp_1708_;
}
}
}
}
case 1:
{
lean_object* v_node_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1738_; 
v_node_1726_ = lean_ctor_get(v_v_1705_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_v_1705_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1728_ = v_v_1705_;
v_isShared_1729_ = v_isSharedCheck_1738_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_node_1726_);
lean_dec(v_v_1705_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1738_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
size_t v___x_1730_; size_t v___x_1731_; size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1730_ = ((size_t)5ULL);
v___x_1731_ = lean_usize_shift_right(v_x_1692_, v___x_1730_);
v___x_1732_ = ((size_t)1ULL);
v___x_1733_ = lean_usize_add(v_x_1693_, v___x_1732_);
v___x_1734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_node_1726_, v___x_1731_, v___x_1733_, v_x_1694_, v_x_1695_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1734_);
v___x_1736_ = v___x_1728_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
v___y_1709_ = v___x_1736_;
goto v___jp_1708_;
}
}
}
default: 
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_x_1694_);
lean_ctor_set(v___x_1739_, 1, v_x_1695_);
v___y_1709_ = v___x_1739_;
goto v___jp_1708_;
}
}
v___jp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_array_fset(v_xs_x27_1707_, v_j_1699_, v___y_1709_);
lean_dec(v_j_1699_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1710_);
v___x_1712_ = v___x_1703_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
else
{
lean_object* v_ks_1742_; lean_object* v_vs_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1763_; 
v_ks_1742_ = lean_ctor_get(v_x_1691_, 0);
v_vs_1743_ = lean_ctor_get(v_x_1691_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1745_ = v_x_1691_;
v_isShared_1746_ = v_isSharedCheck_1763_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_vs_1743_);
lean_inc(v_ks_1742_);
lean_dec(v_x_1691_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1763_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_ks_1742_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_vs_1743_);
v___x_1748_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v_newNode_1749_; uint8_t v___y_1751_; size_t v___x_1757_; uint8_t v___x_1758_; 
v_newNode_1749_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v___x_1748_, v_x_1694_, v_x_1695_);
v___x_1757_ = ((size_t)7ULL);
v___x_1758_ = lean_usize_dec_le(v___x_1757_, v_x_1693_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1749_);
v___x_1760_ = lean_unsigned_to_nat(4u);
v___x_1761_ = lean_nat_dec_lt(v___x_1759_, v___x_1760_);
lean_dec(v___x_1759_);
v___y_1751_ = v___x_1761_;
goto v___jp_1750_;
}
else
{
v___y_1751_ = v___x_1758_;
goto v___jp_1750_;
}
v___jp_1750_:
{
if (v___y_1751_ == 0)
{
lean_object* v_ks_1752_; lean_object* v_vs_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_ks_1752_ = lean_ctor_get(v_newNode_1749_, 0);
lean_inc_ref(v_ks_1752_);
v_vs_1753_ = lean_ctor_get(v_newNode_1749_, 1);
lean_inc_ref(v_vs_1753_);
lean_dec_ref(v_newNode_1749_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0);
v___x_1756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_x_1693_, v_ks_1752_, v_vs_1753_, v___x_1754_, v___x_1755_);
lean_dec_ref(v_vs_1753_);
lean_dec_ref(v_ks_1752_);
return v___x_1756_;
}
else
{
return v_newNode_1749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t v_depth_1764_, lean_object* v_keys_1765_, lean_object* v_vals_1766_, lean_object* v_i_1767_, lean_object* v_entries_1768_){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_array_get_size(v_keys_1765_);
v___x_1770_ = lean_nat_dec_lt(v_i_1767_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec(v_i_1767_);
return v_entries_1768_;
}
else
{
lean_object* v_k_1771_; lean_object* v_v_1772_; uint64_t v___y_1774_; 
v_k_1771_ = lean_array_fget_borrowed(v_keys_1765_, v_i_1767_);
v_v_1772_ = lean_array_fget_borrowed(v_vals_1766_, v_i_1767_);
if (lean_obj_tag(v_k_1771_) == 0)
{
uint64_t v___x_1785_; 
v___x_1785_ = 1723ULL;
v___y_1774_ = v___x_1785_;
goto v___jp_1773_;
}
else
{
uint64_t v_hash_1786_; 
v_hash_1786_ = lean_ctor_get_uint64(v_k_1771_, sizeof(void*)*2);
v___y_1774_ = v_hash_1786_;
goto v___jp_1773_;
}
v___jp_1773_:
{
size_t v_h_1775_; size_t v___x_1776_; lean_object* v___x_1777_; size_t v___x_1778_; size_t v___x_1779_; size_t v___x_1780_; size_t v_h_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_h_1775_ = lean_uint64_to_usize(v___y_1774_);
v___x_1776_ = ((size_t)5ULL);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_sub(v_depth_1764_, v___x_1778_);
v___x_1780_ = lean_usize_mul(v___x_1776_, v___x_1779_);
v_h_1781_ = lean_usize_shift_right(v_h_1775_, v___x_1780_);
v___x_1782_ = lean_nat_add(v_i_1767_, v___x_1777_);
lean_dec(v_i_1767_);
lean_inc(v_v_1772_);
lean_inc(v_k_1771_);
v___x_1783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_entries_1768_, v_h_1781_, v_depth_1764_, v_k_1771_, v_v_1772_);
v_i_1767_ = v___x_1782_;
v_entries_1768_ = v___x_1783_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_1787_, lean_object* v_keys_1788_, lean_object* v_vals_1789_, lean_object* v_i_1790_, lean_object* v_entries_1791_){
_start:
{
size_t v_depth_boxed_1792_; lean_object* v_res_1793_; 
v_depth_boxed_1792_ = lean_unbox_usize(v_depth_1787_);
lean_dec(v_depth_1787_);
v_res_1793_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_boxed_1792_, v_keys_1788_, v_vals_1789_, v_i_1790_, v_entries_1791_);
lean_dec_ref(v_vals_1789_);
lean_dec_ref(v_keys_1788_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_x_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
size_t v_x_1562__boxed_1799_; size_t v_x_1563__boxed_1800_; lean_object* v_res_1801_; 
v_x_1562__boxed_1799_ = lean_unbox_usize(v_x_1795_);
lean_dec(v_x_1795_);
v_x_1563__boxed_1800_ = lean_unbox_usize(v_x_1796_);
lean_dec(v_x_1796_);
v_res_1801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1794_, v_x_1562__boxed_1799_, v_x_1563__boxed_1800_, v_x_1797_, v_x_1798_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
uint64_t v___y_1806_; 
if (lean_obj_tag(v_x_1803_) == 0)
{
uint64_t v___x_1810_; 
v___x_1810_ = 1723ULL;
v___y_1806_ = v___x_1810_;
goto v___jp_1805_;
}
else
{
uint64_t v_hash_1811_; 
v_hash_1811_ = lean_ctor_get_uint64(v_x_1803_, sizeof(void*)*2);
v___y_1806_ = v_hash_1811_;
goto v___jp_1805_;
}
v___jp_1805_:
{
size_t v___x_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_uint64_to_usize(v___y_1806_);
v___x_1808_ = ((size_t)1ULL);
v___x_1809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1802_, v___x_1807_, v___x_1808_, v_x_1803_, v_x_1804_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v_fst_1814_; lean_object* v_snd_1815_; lean_object* v___x_1816_; 
v_fst_1814_ = lean_ctor_get(v_x_1813_, 0);
lean_inc(v_fst_1814_);
v_snd_1815_ = lean_ctor_get(v_x_1813_, 1);
lean_inc(v_snd_1815_);
lean_dec_ref(v_x_1813_);
v___x_1816_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1812_, v_fst_1814_, v_snd_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1850_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1852_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_){
_start:
{
uint8_t v_res_1860_; lean_object* v_r_1861_; 
v_res_1860_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1857_, v_x_1858_, v_x_1859_);
lean_dec(v_x_1859_);
lean_dec_ref(v_x_1858_);
v_r_1861_ = lean_box(v_res_1860_);
return v_r_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1862_, lean_object* v_m_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1865_, lean_object* v_m_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1865_, v_m_1866_);
lean_dec_ref(v_m_1866_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1868_, lean_object* v_as_1869_, lean_object* v_lo_1870_, lean_object* v_hi_1871_, lean_object* v_w_1872_, lean_object* v_hlo_1873_, lean_object* v_hhi_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1868_, v_as_1869_, v_lo_1870_, v_hi_1871_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1876_, lean_object* v_as_1877_, lean_object* v_lo_1878_, lean_object* v_hi_1879_, lean_object* v_w_1880_, lean_object* v_hlo_1881_, lean_object* v_hhi_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1876_, v_as_1877_, v_lo_1878_, v_hi_1879_, v_w_1880_, v_hlo_1881_, v_hhi_1882_);
lean_dec(v_hi_1879_);
lean_dec(v_n_1876_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1885_, v_x_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1889_, lean_object* v_x_1890_, size_t v_x_1891_, lean_object* v_x_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1890_, v_x_1891_, v_x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
size_t v_x_1866__boxed_1898_; uint8_t v_res_1899_; lean_object* v_r_1900_; 
v_x_1866__boxed_1898_ = lean_unbox_usize(v_x_1896_);
lean_dec(v_x_1896_);
v_res_1899_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1894_, v_x_1895_, v_x_1866__boxed_1898_, v_x_1897_);
lean_dec(v_x_1897_);
lean_dec_ref(v_x_1895_);
v_r_1900_ = lean_box(v_res_1899_);
return v_r_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_map_1903_, lean_object* v_f_1904_, lean_object* v_init_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1903_, v_f_1904_, v_init_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_map_1909_, lean_object* v_f_1910_, lean_object* v_init_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1907_, v_00_u03b2_1908_, v_map_1909_, v_f_1910_, v_init_1911_);
lean_dec_ref(v_map_1909_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_n_1913_, lean_object* v_lo_1914_, lean_object* v_hi_1915_, lean_object* v_hhi_1916_, lean_object* v_pivot_1917_, lean_object* v_as_1918_, lean_object* v_i_1919_, lean_object* v_k_1920_, lean_object* v_ilo_1921_, lean_object* v_ik_1922_, lean_object* v_w_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1915_, v_pivot_1917_, v_as_1918_, v_i_1919_, v_k_1920_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_n_1925_, lean_object* v_lo_1926_, lean_object* v_hi_1927_, lean_object* v_hhi_1928_, lean_object* v_pivot_1929_, lean_object* v_as_1930_, lean_object* v_i_1931_, lean_object* v_k_1932_, lean_object* v_ilo_1933_, lean_object* v_ik_1934_, lean_object* v_w_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(v_n_1925_, v_lo_1926_, v_hi_1927_, v_hhi_1928_, v_pivot_1929_, v_as_1930_, v_i_1931_, v_k_1932_, v_ilo_1933_, v_ik_1934_, v_w_1935_);
lean_dec_ref(v_pivot_1929_);
lean_dec(v_hi_1927_);
lean_dec(v_lo_1926_);
lean_dec(v_n_1925_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1937_, lean_object* v_x_1938_, size_t v_x_1939_, size_t v_x_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1938_, v_x_1939_, v_x_1940_, v_x_1941_, v_x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_){
_start:
{
size_t v_x_1881__boxed_1950_; size_t v_x_1882__boxed_1951_; lean_object* v_res_1952_; 
v_x_1881__boxed_1950_ = lean_unbox_usize(v_x_1946_);
lean_dec(v_x_1946_);
v_x_1882__boxed_1951_ = lean_unbox_usize(v_x_1947_);
lean_dec(v_x_1947_);
v_res_1952_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1944_, v_x_1945_, v_x_1881__boxed_1950_, v_x_1882__boxed_1951_, v_x_1948_, v_x_1949_);
return v_res_1952_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1953_, lean_object* v_keys_1954_, lean_object* v_vals_1955_, lean_object* v_heq_1956_, lean_object* v_i_1957_, lean_object* v_k_1958_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1954_, v_i_1957_, v_k_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1960_, lean_object* v_keys_1961_, lean_object* v_vals_1962_, lean_object* v_heq_1963_, lean_object* v_i_1964_, lean_object* v_k_1965_){
_start:
{
uint8_t v_res_1966_; lean_object* v_r_1967_; 
v_res_1966_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1960_, v_keys_1961_, v_vals_1962_, v_heq_1963_, v_i_1964_, v_k_1965_);
lean_dec(v_k_1965_);
lean_dec_ref(v_vals_1962_);
lean_dec_ref(v_keys_1961_);
v_r_1967_ = lean_box(v_res_1966_);
return v_r_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1968_, lean_object* v_f_1969_, lean_object* v_init_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1969_, v_map_1968_, v_init_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1972_, lean_object* v_f_1973_, lean_object* v_init_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1972_, v_f_1973_, v_init_1974_);
lean_dec_ref(v_map_1972_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1976_, lean_object* v_00_u03b2_1977_, lean_object* v_map_1978_, lean_object* v_f_1979_, lean_object* v_init_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1979_, v_map_1978_, v_init_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1982_, lean_object* v_00_u03b2_1983_, lean_object* v_map_1984_, lean_object* v_f_1985_, lean_object* v_init_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1982_, v_00_u03b2_1983_, v_map_1984_, v_f_1985_, v_init_1986_);
lean_dec_ref(v_map_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1988_, lean_object* v_n_1989_, lean_object* v_k_1990_, lean_object* v_v_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_n_1989_, v_k_1990_, v_v_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1993_, size_t v_depth_1994_, lean_object* v_keys_1995_, lean_object* v_vals_1996_, lean_object* v_heq_1997_, lean_object* v_i_1998_, lean_object* v_entries_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_1994_, v_keys_1995_, v_vals_1996_, v_i_1998_, v_entries_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2001_, lean_object* v_depth_2002_, lean_object* v_keys_2003_, lean_object* v_vals_2004_, lean_object* v_heq_2005_, lean_object* v_i_2006_, lean_object* v_entries_2007_){
_start:
{
size_t v_depth_boxed_2008_; lean_object* v_res_2009_; 
v_depth_boxed_2008_ = lean_unbox_usize(v_depth_2002_);
lean_dec(v_depth_2002_);
v_res_2009_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(v_00_u03b2_2001_, v_depth_boxed_2008_, v_keys_2003_, v_vals_2004_, v_heq_2005_, v_i_2006_, v_entries_2007_);
lean_dec_ref(v_vals_2004_);
lean_dec_ref(v_keys_2003_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2010_, lean_object* v_00_u03b1_2011_, lean_object* v_00_u03b2_2012_, lean_object* v_f_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2013_, v_x_2014_, v_x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2017_, lean_object* v_00_u03b1_2018_, lean_object* v_00_u03b2_2019_, lean_object* v_f_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_2017_, v_00_u03b1_2018_, v_00_u03b2_2019_, v_f_2020_, v_x_2021_, v_x_2022_);
lean_dec_ref(v_x_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_x_2025_, v_x_2026_, v_x_2027_, v_x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_00_u03c3_2032_, lean_object* v_f_2033_, lean_object* v_as_2034_, size_t v_i_2035_, size_t v_stop_2036_, lean_object* v_b_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_2033_, v_as_2034_, v_i_2035_, v_stop_2036_, v_b_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_00_u03c3_2041_, lean_object* v_f_2042_, lean_object* v_as_2043_, lean_object* v_i_2044_, lean_object* v_stop_2045_, lean_object* v_b_2046_){
_start:
{
size_t v_i_boxed_2047_; size_t v_stop_boxed_2048_; lean_object* v_res_2049_; 
v_i_boxed_2047_ = lean_unbox_usize(v_i_2044_);
lean_dec(v_i_2044_);
v_stop_boxed_2048_ = lean_unbox_usize(v_stop_2045_);
lean_dec(v_stop_2045_);
v_res_2049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_2039_, v_00_u03b2_2040_, v_00_u03c3_2041_, v_f_2042_, v_as_2043_, v_i_boxed_2047_, v_stop_boxed_2048_, v_b_2046_);
lean_dec_ref(v_as_2043_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03c3_2050_, lean_object* v_00_u03b1_2051_, lean_object* v_00_u03b2_2052_, lean_object* v_f_2053_, lean_object* v_keys_2054_, lean_object* v_vals_2055_, lean_object* v_heq_2056_, lean_object* v_i_2057_, lean_object* v_acc_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_2053_, v_keys_2054_, v_vals_2055_, v_i_2057_, v_acc_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03c3_2060_, lean_object* v_00_u03b1_2061_, lean_object* v_00_u03b2_2062_, lean_object* v_f_2063_, lean_object* v_keys_2064_, lean_object* v_vals_2065_, lean_object* v_heq_2066_, lean_object* v_i_2067_, lean_object* v_acc_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(v_00_u03c3_2060_, v_00_u03b1_2061_, v_00_u03b2_2062_, v_f_2063_, v_keys_2064_, v_vals_2065_, v_heq_2066_, v_i_2067_, v_acc_2068_);
lean_dec_ref(v_vals_2065_);
lean_dec_ref(v_keys_2064_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2070_, lean_object* v_fid_2071_, lean_object* v_v_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v_toEnvExtension_2074_; lean_object* v_asyncMode_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2073_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2074_ = lean_ctor_get(v___x_2073_, 0);
v_asyncMode_2075_ = lean_ctor_get(v_toEnvExtension_2074_, 2);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_fid_2071_);
lean_ctor_set(v___x_2076_, 1, v_v_2072_);
v___x_2077_ = lean_box(0);
v___x_2078_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2073_, v_env_2070_, v___x_2076_, v_asyncMode_2075_, v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2079_, lean_object* v_vals_2080_, lean_object* v_i_2081_, lean_object* v_k_2082_){
_start:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = lean_array_get_size(v_keys_2079_);
v___x_2084_ = lean_nat_dec_lt(v_i_2081_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v_i_2081_);
v___x_2085_ = lean_box(0);
return v___x_2085_;
}
else
{
lean_object* v_k_x27_2086_; uint8_t v___x_2087_; 
v_k_x27_2086_ = lean_array_fget_borrowed(v_keys_2079_, v_i_2081_);
v___x_2087_ = lean_name_eq(v_k_2082_, v_k_x27_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_add(v_i_2081_, v___x_2088_);
lean_dec(v_i_2081_);
v_i_2081_ = v___x_2089_;
goto _start;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_array_fget_borrowed(v_vals_2080_, v_i_2081_);
lean_dec(v_i_2081_);
lean_inc(v___x_2091_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2093_, lean_object* v_vals_2094_, lean_object* v_i_2095_, lean_object* v_k_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2093_, v_vals_2094_, v_i_2095_, v_k_2096_);
lean_dec(v_k_2096_);
lean_dec_ref(v_vals_2094_);
lean_dec_ref(v_keys_2093_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2098_, size_t v_x_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2098_) == 0)
{
lean_object* v_es_2101_; lean_object* v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; lean_object* v_j_2105_; lean_object* v___x_2106_; 
v_es_2101_ = lean_ctor_get(v_x_2098_, 0);
v___x_2102_ = lean_box(2);
v___x_2103_ = ((size_t)31ULL);
v___x_2104_ = lean_usize_land(v_x_2099_, v___x_2103_);
v_j_2105_ = lean_usize_to_nat(v___x_2104_);
v___x_2106_ = lean_array_get_borrowed(v___x_2102_, v_es_2101_, v_j_2105_);
lean_dec(v_j_2105_);
switch(lean_obj_tag(v___x_2106_))
{
case 0:
{
lean_object* v_key_2107_; lean_object* v_val_2108_; uint8_t v___x_2109_; 
v_key_2107_ = lean_ctor_get(v___x_2106_, 0);
v_val_2108_ = lean_ctor_get(v___x_2106_, 1);
v___x_2109_ = lean_name_eq(v_x_2100_, v_key_2107_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_box(0);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; 
lean_inc(v_val_2108_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_val_2108_);
return v___x_2111_;
}
}
case 1:
{
lean_object* v_node_2112_; size_t v___x_2113_; size_t v___x_2114_; 
v_node_2112_ = lean_ctor_get(v___x_2106_, 0);
v___x_2113_ = ((size_t)5ULL);
v___x_2114_ = lean_usize_shift_right(v_x_2099_, v___x_2113_);
v_x_2098_ = v_node_2112_;
v_x_2099_ = v___x_2114_;
goto _start;
}
default: 
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_box(0);
return v___x_2116_;
}
}
}
else
{
lean_object* v_ks_2117_; lean_object* v_vs_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_ks_2117_ = lean_ctor_get(v_x_2098_, 0);
v_vs_2118_ = lean_ctor_get(v_x_2098_, 1);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2117_, v_vs_2118_, v___x_2119_, v_x_2100_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
size_t v_x_385__boxed_2124_; lean_object* v_res_2125_; 
v_x_385__boxed_2124_ = lean_unbox_usize(v_x_2122_);
lean_dec(v_x_2122_);
v_res_2125_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2121_, v_x_385__boxed_2124_, v_x_2123_);
lean_dec(v_x_2123_);
lean_dec_ref(v_x_2121_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2126_, lean_object* v_x_2127_){
_start:
{
uint64_t v___y_2129_; 
if (lean_obj_tag(v_x_2127_) == 0)
{
uint64_t v___x_2132_; 
v___x_2132_ = 1723ULL;
v___y_2129_ = v___x_2132_;
goto v___jp_2128_;
}
else
{
uint64_t v_hash_2133_; 
v_hash_2133_ = lean_ctor_get_uint64(v_x_2127_, sizeof(void*)*2);
v___y_2129_ = v_hash_2133_;
goto v___jp_2128_;
}
v___jp_2128_:
{
size_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_uint64_to_usize(v___y_2129_);
v___x_2131_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2126_, v___x_2130_, v_x_2127_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2134_, v_x_2135_);
lean_dec(v_x_2135_);
lean_dec_ref(v_x_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2137_, lean_object* v_k_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_m_2143_; lean_object* v_a_2144_; uint8_t v___x_2145_; 
v___x_2141_ = lean_nat_add(v_x_2139_, v_x_2140_);
v___x_2142_ = lean_unsigned_to_nat(1u);
v_m_2143_ = lean_nat_shiftr(v___x_2141_, v___x_2142_);
lean_dec(v___x_2141_);
v_a_2144_ = lean_array_fget_borrowed(v_as_2137_, v_m_2143_);
v___x_2145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2144_, v_k_2138_);
if (v___x_2145_ == 0)
{
uint8_t v___x_2146_; 
lean_dec(v_x_2140_);
v___x_2146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2138_, v_a_2144_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec(v_m_2143_);
lean_dec(v_x_2139_);
lean_inc(v_a_2144_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_a_2144_);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_nat_dec_eq(v_m_2143_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_nat_sub(v_m_2143_, v___x_2142_);
lean_dec(v_m_2143_);
v___x_2151_ = lean_nat_dec_lt(v___x_2150_, v_x_2139_);
if (v___x_2151_ == 0)
{
v_x_2140_ = v___x_2150_;
goto _start;
}
else
{
lean_object* v___x_2153_; 
lean_dec(v___x_2150_);
lean_dec(v_x_2139_);
v___x_2153_ = lean_box(0);
return v___x_2153_;
}
}
else
{
lean_object* v___x_2154_; 
lean_dec(v_m_2143_);
lean_dec(v_x_2139_);
v___x_2154_ = lean_box(0);
return v___x_2154_;
}
}
}
else
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
lean_dec(v_x_2139_);
v___x_2155_ = lean_nat_add(v_m_2143_, v___x_2142_);
lean_dec(v_m_2143_);
v___x_2156_ = lean_nat_dec_le(v___x_2155_, v_x_2140_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_dec(v___x_2155_);
lean_dec(v_x_2140_);
v___x_2157_ = lean_box(0);
return v___x_2157_;
}
else
{
v_x_2139_ = v___x_2155_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2159_, lean_object* v_k_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2159_, v_k_2160_, v_x_2161_, v_x_2162_);
lean_dec_ref(v_k_2160_);
lean_dec_ref(v_as_2159_);
return v_res_2163_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2167_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2168_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2170_ = lean_box(0);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2172_, lean_object* v_fid_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2183_; 
v___x_2174_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2175_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2183_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2172_, v_fid_2173_);
if (lean_obj_tag(v___x_2183_) == 0)
{
goto v___jp_2176_;
}
else
{
lean_object* v_val_2184_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v_val_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2206_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_2174_, v___x_2175_, v_env_2172_, v_val_2184_);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = lean_array_get_size(v___x_2206_);
v___x_2209_ = lean_nat_dec_lt(v___x_2207_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_dec_ref(v___x_2206_);
goto v___jp_2185_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_sub(v___x_2208_, v___x_2210_);
v___x_2212_ = lean_nat_dec_le(v___x_2207_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_dec(v___x_2211_);
lean_dec_ref(v___x_2206_);
goto v___jp_2185_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_box(0);
lean_inc(v_fid_2173_);
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v_fid_2173_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2206_, v___x_2214_, v___x_2207_, v___x_2211_);
lean_dec_ref_known(v___x_2214_, 2);
lean_dec_ref(v___x_2206_);
if (lean_obj_tag(v___x_2215_) == 0)
{
goto v___jp_2185_;
}
else
{
lean_object* v_val_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_val_2184_);
lean_dec(v_fid_2173_);
lean_dec_ref(v_env_2172_);
v_val_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_val_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_snd_2220_; lean_object* v___x_2222_; 
v_snd_2220_ = lean_ctor_get(v_val_2216_, 1);
lean_inc(v_snd_2220_);
lean_dec(v_val_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v_snd_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_snd_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
v___jp_2185_:
{
uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2186_ = 0;
v___x_2187_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2174_, v___x_2175_, v_env_2172_, v_val_2184_, v___x_2186_);
lean_dec(v_val_2184_);
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_array_get_size(v___x_2187_);
v___x_2190_ = lean_nat_dec_lt(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_dec_ref(v___x_2187_);
goto v___jp_2176_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2191_ = lean_unsigned_to_nat(1u);
v___x_2192_ = lean_nat_sub(v___x_2189_, v___x_2191_);
v___x_2193_ = lean_nat_dec_le(v___x_2188_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_dec(v___x_2192_);
lean_dec_ref(v___x_2187_);
goto v___jp_2176_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_box(0);
lean_inc(v_fid_2173_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_fid_2173_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2187_, v___x_2195_, v___x_2188_, v___x_2192_);
lean_dec_ref_known(v___x_2195_, 2);
lean_dec_ref(v___x_2187_);
if (lean_obj_tag(v___x_2196_) == 0)
{
goto v___jp_2176_;
}
else
{
lean_object* v_val_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_fid_2173_);
lean_dec_ref(v_env_2172_);
v_val_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_val_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v_snd_2201_; lean_object* v___x_2203_; 
v_snd_2201_ = lean_ctor_get(v_val_2197_, 1);
lean_inc(v_snd_2201_);
lean_dec(v_val_2197_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_snd_2201_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_snd_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
}
v___jp_2176_:
{
lean_object* v_toEnvExtension_2177_; lean_object* v_asyncMode_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_snd_2181_; lean_object* v___x_2182_; 
v_toEnvExtension_2177_ = lean_ctor_get(v___x_2175_, 0);
v_asyncMode_2178_ = lean_ctor_get(v_toEnvExtension_2177_, 2);
v___x_2179_ = lean_box(0);
v___x_2180_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2174_, v___x_2175_, v_env_2172_, v_asyncMode_2178_, v___x_2179_);
v_snd_2181_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_snd_2181_);
lean_dec(v___x_2180_);
v___x_2182_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2181_, v_fid_2173_);
lean_dec(v_fid_2173_);
lean_dec(v_snd_2181_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2229_, v_x_2230_, v_x_2231_);
lean_dec(v_x_2231_);
lean_dec_ref(v_x_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2233_, lean_object* v_k_2234_, lean_object* v_x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2233_, v_k_2234_, v_x_2235_, v_x_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2239_, lean_object* v_k_2240_, lean_object* v_x_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2239_, v_k_2240_, v_x_2241_, v_x_2242_, v_x_2243_);
lean_dec_ref(v_k_2240_);
lean_dec_ref(v_as_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2245_, lean_object* v_x_2246_, size_t v_x_2247_, lean_object* v_x_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2246_, v_x_2247_, v_x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
size_t v_x_621__boxed_2254_; lean_object* v_res_2255_; 
v_x_621__boxed_2254_ = lean_unbox_usize(v_x_2252_);
lean_dec(v_x_2252_);
v_res_2255_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2250_, v_x_2251_, v_x_621__boxed_2254_, v_x_2253_);
lean_dec(v_x_2253_);
lean_dec_ref(v_x_2251_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2256_, lean_object* v_keys_2257_, lean_object* v_vals_2258_, lean_object* v_heq_2259_, lean_object* v_i_2260_, lean_object* v_k_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2257_, v_vals_2258_, v_i_2260_, v_k_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2263_, lean_object* v_keys_2264_, lean_object* v_vals_2265_, lean_object* v_heq_2266_, lean_object* v_i_2267_, lean_object* v_k_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2263_, v_keys_2264_, v_vals_2265_, v_heq_2266_, v_i_2267_, v_k_2268_);
lean_dec(v_k_2268_);
lean_dec_ref(v_vals_2265_);
lean_dec_ref(v_keys_2264_);
return v_res_2269_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2273_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2274_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___x_2278_; lean_object* v_assignments_2279_; lean_object* v_currFnIdx_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2278_ = lean_st_ref_get(v_a_2276_);
v_assignments_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_ref(v_assignments_2279_);
lean_dec(v___x_2278_);
v_currFnIdx_2280_ = lean_ctor_get(v_a_2275_, 1);
v___x_2281_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2282_ = lean_array_get(v___x_2281_, v_assignments_2279_, v_currFnIdx_2280_);
lean_dec_ref(v_assignments_2279_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2288_, v_a_2289_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v_funVals_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2307_ = lean_st_ref_get(v_a_2305_);
v_funVals_2308_ = lean_ctor_get(v___x_2307_, 1);
lean_inc_ref(v_funVals_2308_);
lean_dec(v___x_2307_);
v___x_2309_ = lean_box(0);
v___x_2310_ = lean_array_get(v___x_2309_, v_funVals_2308_, v_funIdx_2304_);
lean_dec_ref(v_funVals_2308_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2312_, v_a_2313_);
lean_dec(v_a_2313_);
lean_dec(v_funIdx_2312_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2316_, v_a_2318_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_funIdx_2325_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2334_, lean_object* v_as_2335_, lean_object* v_j_2336_){
_start:
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = lean_array_get_size(v_as_2335_);
v___x_2338_ = lean_nat_dec_lt(v_j_2336_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; 
lean_dec(v_j_2336_);
v___x_2339_ = lean_box(0);
return v___x_2339_;
}
else
{
lean_object* v___x_2340_; lean_object* v_toSignature_2341_; lean_object* v_name_2342_; uint8_t v___x_2343_; 
v___x_2340_ = lean_array_fget_borrowed(v_as_2335_, v_j_2336_);
v_toSignature_2341_ = lean_ctor_get(v___x_2340_, 0);
v_name_2342_ = lean_ctor_get(v_toSignature_2341_, 0);
v___x_2343_ = lean_name_eq(v_name_2342_, v_declName_2334_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = lean_nat_add(v_j_2336_, v___x_2344_);
lean_dec(v_j_2336_);
v_j_2336_ = v___x_2345_;
goto _start;
}
else
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v_j_2336_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2348_, lean_object* v_as_2349_, lean_object* v_j_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2348_, v_as_2349_, v_j_2350_);
lean_dec_ref(v_as_2349_);
lean_dec(v_declName_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_decls_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v_decls_2356_ = lean_ctor_get(v_a_2353_, 0);
v___x_2357_ = lean_unsigned_to_nat(0u);
v___x_2358_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2352_, v_decls_2356_, v___x_2357_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
else
{
lean_object* v_val_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2377_; 
v_val_2361_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2363_ = v___x_2358_;
v_isShared_2364_ = v_isSharedCheck_2377_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_val_2361_);
lean_dec(v___x_2358_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2377_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2376_; 
v___x_2365_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2361_, v_a_2354_);
lean_dec(v_val_2361_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v_a_2366_);
v___x_2371_ = v___x_2363_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2371_);
v___x_2373_ = v___x_2368_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_declName_2378_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2383_, v_a_2384_, v_a_2385_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_declName_2392_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v_currFnIdx_2406_; lean_object* v_assignments_2407_; lean_object* v_funVals_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2426_; 
v___x_2405_ = lean_st_ref_take(v_a_2403_);
v_currFnIdx_2406_ = lean_ctor_get(v_a_2402_, 1);
v_assignments_2407_ = lean_ctor_get(v___x_2405_, 0);
v_funVals_2408_ = lean_ctor_get(v___x_2405_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2410_ = v___x_2405_;
v_isShared_2411_ = v_isSharedCheck_2426_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_funVals_2408_);
lean_inc(v_assignments_2407_);
lean_dec(v___x_2405_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2426_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___y_2414_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2412_ = lean_box(0);
v___x_2420_ = lean_array_get_size(v_assignments_2407_);
v___x_2421_ = lean_nat_dec_lt(v_currFnIdx_2406_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_dec_ref(v_f_2401_);
v___y_2414_ = v_assignments_2407_;
goto v___jp_2413_;
}
else
{
lean_object* v_v_2422_; lean_object* v_xs_x27_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_v_2422_ = lean_array_fget(v_assignments_2407_, v_currFnIdx_2406_);
v_xs_x27_2423_ = lean_array_fset(v_assignments_2407_, v_currFnIdx_2406_, v___x_2412_);
v___x_2424_ = lean_apply_1(v_f_2401_, v_v_2422_);
v___x_2425_ = lean_array_fset(v_xs_x27_2423_, v_currFnIdx_2406_, v___x_2424_);
v___y_2414_ = v___x_2425_;
goto v___jp_2413_;
}
v___jp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___y_2414_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___y_2414_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_funVals_2408_);
v___x_2416_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_st_ref_set(v_a_2403_, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2412_);
return v___x_2418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2432_, v_a_2433_, v_a_2434_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2450_, lean_object* v_fallback_2451_, lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
lean_inc(v_fallback_2451_);
return v_fallback_2451_;
}
else
{
lean_object* v_key_2453_; lean_object* v_value_2454_; lean_object* v_tail_2455_; uint8_t v___x_2456_; 
v_key_2453_ = lean_ctor_get(v_x_2452_, 0);
v_value_2454_ = lean_ctor_get(v_x_2452_, 1);
v_tail_2455_ = lean_ctor_get(v_x_2452_, 2);
v___x_2456_ = l_Lean_instBEqFVarId_beq(v_key_2453_, v_a_2450_);
if (v___x_2456_ == 0)
{
v_x_2452_ = v_tail_2455_;
goto _start;
}
else
{
lean_inc(v_value_2454_);
return v_value_2454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2458_, lean_object* v_fallback_2459_, lean_object* v_x_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2458_, v_fallback_2459_, v_x_2460_);
lean_dec(v_x_2460_);
lean_dec(v_fallback_2459_);
lean_dec(v_a_2458_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2462_, lean_object* v_a_2463_, lean_object* v_fallback_2464_){
_start:
{
lean_object* v_buckets_2465_; lean_object* v___x_2466_; uint64_t v___x_2467_; uint64_t v___x_2468_; uint64_t v___x_2469_; uint64_t v_fold_2470_; uint64_t v___x_2471_; uint64_t v___x_2472_; uint64_t v___x_2473_; size_t v___x_2474_; size_t v___x_2475_; size_t v___x_2476_; size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_buckets_2465_ = lean_ctor_get(v_m_2462_, 1);
v___x_2466_ = lean_array_get_size(v_buckets_2465_);
v___x_2467_ = l_Lean_instHashableFVarId_hash(v_a_2463_);
v___x_2468_ = 32ULL;
v___x_2469_ = lean_uint64_shift_right(v___x_2467_, v___x_2468_);
v_fold_2470_ = lean_uint64_xor(v___x_2467_, v___x_2469_);
v___x_2471_ = 16ULL;
v___x_2472_ = lean_uint64_shift_right(v_fold_2470_, v___x_2471_);
v___x_2473_ = lean_uint64_xor(v_fold_2470_, v___x_2472_);
v___x_2474_ = lean_uint64_to_usize(v___x_2473_);
v___x_2475_ = lean_usize_of_nat(v___x_2466_);
v___x_2476_ = ((size_t)1ULL);
v___x_2477_ = lean_usize_sub(v___x_2475_, v___x_2476_);
v___x_2478_ = lean_usize_land(v___x_2474_, v___x_2477_);
v___x_2479_ = lean_array_uget_borrowed(v_buckets_2465_, v___x_2478_);
v___x_2480_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2463_, v_fallback_2464_, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2481_, lean_object* v_a_2482_, lean_object* v_fallback_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2481_, v_a_2482_, v_fallback_2483_);
lean_dec(v_fallback_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_m_2481_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2499_; 
v___x_2489_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2486_, v_a_2487_);
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2499_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2499_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2494_ = lean_box(0);
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2490_, v_var_2485_, v___x_2494_);
lean_dec(v_a_2490_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2495_);
v___x_2497_ = v___x_2492_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2500_, v_a_2501_, v_a_2502_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_var_2500_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2505_, v_a_2506_, v_a_2507_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_var_2514_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2523_, lean_object* v_m_2524_, lean_object* v_a_2525_, lean_object* v_fallback_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2524_, v_a_2525_, v_fallback_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2528_, lean_object* v_m_2529_, lean_object* v_a_2530_, lean_object* v_fallback_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2528_, v_m_2529_, v_a_2530_, v_fallback_2531_);
lean_dec(v_fallback_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_m_2529_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2533_, lean_object* v_a_2534_, lean_object* v_fallback_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2534_, v_fallback_2535_, v_x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2538_, lean_object* v_a_2539_, lean_object* v_fallback_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2538_, v_a_2539_, v_fallback_2540_, v_x_2541_);
lean_dec(v_x_2541_);
lean_dec(v_fallback_2540_);
lean_dec(v_a_2539_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
if (lean_obj_tag(v_arg_2543_) == 1)
{
lean_object* v_fvarId_2547_; lean_object* v___x_2548_; 
v_fvarId_2547_ = lean_ctor_get(v_arg_2543_, 0);
v___x_2548_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2547_, v_a_2544_, v_a_2545_);
return v___x_2548_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_box(1);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_arg_2551_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2556_, v_a_2557_, v_a_2558_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_arg_2565_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2574_, lean_object* v_b_2575_, lean_object* v_x_2576_){
_start:
{
if (lean_obj_tag(v_x_2576_) == 0)
{
lean_dec(v_b_2575_);
lean_dec(v_a_2574_);
return v_x_2576_;
}
else
{
lean_object* v_key_2577_; lean_object* v_value_2578_; lean_object* v_tail_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2591_; 
v_key_2577_ = lean_ctor_get(v_x_2576_, 0);
v_value_2578_ = lean_ctor_get(v_x_2576_, 1);
v_tail_2579_ = lean_ctor_get(v_x_2576_, 2);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_x_2576_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2581_ = v_x_2576_;
v_isShared_2582_ = v_isSharedCheck_2591_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_tail_2579_);
lean_inc(v_value_2578_);
lean_inc(v_key_2577_);
lean_dec(v_x_2576_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2591_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
uint8_t v___x_2583_; 
v___x_2583_ = l_Lean_instBEqFVarId_beq(v_key_2577_, v_a_2574_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2574_, v_b_2575_, v_tail_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 2, v___x_2584_);
v___x_2586_ = v___x_2581_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_key_2577_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_value_2578_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
else
{
lean_object* v___x_2589_; 
lean_dec(v_value_2578_);
lean_dec(v_key_2577_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 1, v_b_2575_);
lean_ctor_set(v___x_2581_, 0, v_a_2574_);
v___x_2589_ = v___x_2581_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2574_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_b_2575_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_tail_2579_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2592_, lean_object* v_x_2593_){
_start:
{
if (lean_obj_tag(v_x_2593_) == 0)
{
return v_x_2592_;
}
else
{
lean_object* v_key_2594_; lean_object* v_value_2595_; lean_object* v_tail_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2619_; 
v_key_2594_ = lean_ctor_get(v_x_2593_, 0);
v_value_2595_ = lean_ctor_get(v_x_2593_, 1);
v_tail_2596_ = lean_ctor_get(v_x_2593_, 2);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_x_2593_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2598_ = v_x_2593_;
v_isShared_2599_ = v_isSharedCheck_2619_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_tail_2596_);
lean_inc(v_value_2595_);
lean_inc(v_key_2594_);
lean_dec(v_x_2593_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2619_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; uint64_t v___x_2601_; uint64_t v___x_2602_; uint64_t v___x_2603_; uint64_t v_fold_2604_; uint64_t v___x_2605_; uint64_t v___x_2606_; uint64_t v___x_2607_; size_t v___x_2608_; size_t v___x_2609_; size_t v___x_2610_; size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2600_ = lean_array_get_size(v_x_2592_);
v___x_2601_ = l_Lean_instHashableFVarId_hash(v_key_2594_);
v___x_2602_ = 32ULL;
v___x_2603_ = lean_uint64_shift_right(v___x_2601_, v___x_2602_);
v_fold_2604_ = lean_uint64_xor(v___x_2601_, v___x_2603_);
v___x_2605_ = 16ULL;
v___x_2606_ = lean_uint64_shift_right(v_fold_2604_, v___x_2605_);
v___x_2607_ = lean_uint64_xor(v_fold_2604_, v___x_2606_);
v___x_2608_ = lean_uint64_to_usize(v___x_2607_);
v___x_2609_ = lean_usize_of_nat(v___x_2600_);
v___x_2610_ = ((size_t)1ULL);
v___x_2611_ = lean_usize_sub(v___x_2609_, v___x_2610_);
v___x_2612_ = lean_usize_land(v___x_2608_, v___x_2611_);
v___x_2613_ = lean_array_uget_borrowed(v_x_2592_, v___x_2612_);
lean_inc(v___x_2613_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 2, v___x_2613_);
v___x_2615_ = v___x_2598_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_key_2594_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_value_2595_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_array_uset(v_x_2592_, v___x_2612_, v___x_2615_);
v_x_2592_ = v___x_2616_;
v_x_2593_ = v_tail_2596_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2620_, lean_object* v_source_2621_, lean_object* v_target_2622_){
_start:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = lean_array_get_size(v_source_2621_);
v___x_2624_ = lean_nat_dec_lt(v_i_2620_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_dec_ref(v_source_2621_);
lean_dec(v_i_2620_);
return v_target_2622_;
}
else
{
lean_object* v_es_2625_; lean_object* v___x_2626_; lean_object* v_source_2627_; lean_object* v_target_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_es_2625_ = lean_array_fget(v_source_2621_, v_i_2620_);
v___x_2626_ = lean_box(0);
v_source_2627_ = lean_array_fset(v_source_2621_, v_i_2620_, v___x_2626_);
v_target_2628_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2622_, v_es_2625_);
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_add(v_i_2620_, v___x_2629_);
lean_dec(v_i_2620_);
v_i_2620_ = v___x_2630_;
v_source_2621_ = v_source_2627_;
v_target_2622_ = v_target_2628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2632_){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v_nbuckets_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2633_ = lean_array_get_size(v_data_2632_);
v___x_2634_ = lean_unsigned_to_nat(2u);
v_nbuckets_2635_ = lean_nat_mul(v___x_2633_, v___x_2634_);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_box(0);
v___x_2638_ = lean_mk_array(v_nbuckets_2635_, v___x_2637_);
v___x_2639_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2636_, v_data_2632_, v___x_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2640_, lean_object* v_x_2641_){
_start:
{
if (lean_obj_tag(v_x_2641_) == 0)
{
uint8_t v___x_2642_; 
v___x_2642_ = 0;
return v___x_2642_;
}
else
{
lean_object* v_key_2643_; lean_object* v_tail_2644_; uint8_t v___x_2645_; 
v_key_2643_ = lean_ctor_get(v_x_2641_, 0);
v_tail_2644_ = lean_ctor_get(v_x_2641_, 2);
v___x_2645_ = l_Lean_instBEqFVarId_beq(v_key_2643_, v_a_2640_);
if (v___x_2645_ == 0)
{
v_x_2641_ = v_tail_2644_;
goto _start;
}
else
{
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2647_, lean_object* v_x_2648_){
_start:
{
uint8_t v_res_2649_; lean_object* v_r_2650_; 
v_res_2649_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2647_, v_x_2648_);
lean_dec(v_x_2648_);
lean_dec(v_a_2647_);
v_r_2650_ = lean_box(v_res_2649_);
return v_r_2650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2651_, lean_object* v_a_2652_, lean_object* v_b_2653_){
_start:
{
lean_object* v_size_2654_; lean_object* v_buckets_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2698_; 
v_size_2654_ = lean_ctor_get(v_m_2651_, 0);
v_buckets_2655_ = lean_ctor_get(v_m_2651_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_m_2651_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2657_ = v_m_2651_;
v_isShared_2658_ = v_isSharedCheck_2698_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_buckets_2655_);
lean_inc(v_size_2654_);
lean_dec(v_m_2651_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2698_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; uint64_t v___x_2660_; uint64_t v___x_2661_; uint64_t v___x_2662_; uint64_t v_fold_2663_; uint64_t v___x_2664_; uint64_t v___x_2665_; uint64_t v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; size_t v___x_2669_; size_t v___x_2670_; size_t v___x_2671_; lean_object* v_bkt_2672_; uint8_t v___x_2673_; 
v___x_2659_ = lean_array_get_size(v_buckets_2655_);
v___x_2660_ = l_Lean_instHashableFVarId_hash(v_a_2652_);
v___x_2661_ = 32ULL;
v___x_2662_ = lean_uint64_shift_right(v___x_2660_, v___x_2661_);
v_fold_2663_ = lean_uint64_xor(v___x_2660_, v___x_2662_);
v___x_2664_ = 16ULL;
v___x_2665_ = lean_uint64_shift_right(v_fold_2663_, v___x_2664_);
v___x_2666_ = lean_uint64_xor(v_fold_2663_, v___x_2665_);
v___x_2667_ = lean_uint64_to_usize(v___x_2666_);
v___x_2668_ = lean_usize_of_nat(v___x_2659_);
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_sub(v___x_2668_, v___x_2669_);
v___x_2671_ = lean_usize_land(v___x_2667_, v___x_2670_);
v_bkt_2672_ = lean_array_uget_borrowed(v_buckets_2655_, v___x_2671_);
v___x_2673_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2652_, v_bkt_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v_size_x27_2675_; lean_object* v___x_2676_; lean_object* v_buckets_x27_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2674_ = lean_unsigned_to_nat(1u);
v_size_x27_2675_ = lean_nat_add(v_size_2654_, v___x_2674_);
lean_dec(v_size_2654_);
lean_inc(v_bkt_2672_);
v___x_2676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2676_, 0, v_a_2652_);
lean_ctor_set(v___x_2676_, 1, v_b_2653_);
lean_ctor_set(v___x_2676_, 2, v_bkt_2672_);
v_buckets_x27_2677_ = lean_array_uset(v_buckets_2655_, v___x_2671_, v___x_2676_);
v___x_2678_ = lean_unsigned_to_nat(4u);
v___x_2679_ = lean_nat_mul(v_size_x27_2675_, v___x_2678_);
v___x_2680_ = lean_unsigned_to_nat(3u);
v___x_2681_ = lean_nat_div(v___x_2679_, v___x_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_array_get_size(v_buckets_x27_2677_);
v___x_2683_ = lean_nat_dec_le(v___x_2681_, v___x_2682_);
lean_dec(v___x_2681_);
if (v___x_2683_ == 0)
{
lean_object* v_val_2684_; lean_object* v___x_2686_; 
v_val_2684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2677_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v_val_2684_);
lean_ctor_set(v___x_2657_, 0, v_size_x27_2675_);
v___x_2686_ = v___x_2657_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_size_x27_2675_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_val_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
else
{
lean_object* v___x_2689_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v_buckets_x27_2677_);
lean_ctor_set(v___x_2657_, 0, v_size_x27_2675_);
v___x_2689_ = v___x_2657_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_size_x27_2675_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_buckets_x27_2677_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_object* v___x_2691_; lean_object* v_buckets_x27_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
lean_inc(v_bkt_2672_);
v___x_2691_ = lean_box(0);
v_buckets_x27_2692_ = lean_array_uset(v_buckets_2655_, v___x_2671_, v___x_2691_);
v___x_2693_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2652_, v_b_2653_, v_bkt_2672_);
v___x_2694_ = lean_array_uset(v_buckets_x27_2692_, v___x_2671_, v___x_2693_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___x_2694_);
v___x_2696_ = v___x_2657_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_size_2654_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2699_, lean_object* v___x_2700_, lean_object* v_x_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2701_, v_var_2699_, v___x_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2703_, lean_object* v_newVal_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_st_ref_get(v_a_2707_);
v___x_2710_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2703_, v_a_2705_, v_a_2706_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v_env_2712_; lean_object* v___x_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v_env_2712_ = lean_ctor_get(v___x_2709_, 0);
lean_inc_ref(v_env_2712_);
lean_dec(v___x_2709_);
v___x_2713_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2712_, v_a_2711_, v_newVal_2704_);
v___f_2714_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2714_, 0, v_var_2703_);
lean_closure_set(v___f_2714_, 1, v___x_2713_);
v___x_2715_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2714_, v_a_2705_, v_a_2706_);
return v___x_2715_;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v___x_2709_);
lean_dec(v_newVal_2704_);
lean_dec(v_var_2703_);
v_a_2716_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2710_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2710_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2724_, lean_object* v_newVal_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2724_, v_newVal_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2731_, lean_object* v_newVal_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2731_, v_newVal_2732_, v_a_2733_, v_a_2734_, v_a_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2741_, lean_object* v_newVal_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2741_, v_newVal_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2751_, lean_object* v_m_2752_, lean_object* v_a_2753_, lean_object* v_b_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2752_, v_a_2753_, v_b_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2756_, lean_object* v_a_2757_, lean_object* v_x_2758_){
_start:
{
uint8_t v___x_2759_; 
v___x_2759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2757_, v_x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2760_, lean_object* v_a_2761_, lean_object* v_x_2762_){
_start:
{
uint8_t v_res_2763_; lean_object* v_r_2764_; 
v_res_2763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2760_, v_a_2761_, v_x_2762_);
lean_dec(v_x_2762_);
lean_dec(v_a_2761_);
v_r_2764_ = lean_box(v_res_2763_);
return v_r_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2765_, lean_object* v_data_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2768_, lean_object* v_a_2769_, lean_object* v_b_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2769_, v_b_2770_, v_x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2773_, lean_object* v_i_2774_, lean_object* v_source_2775_, lean_object* v_target_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2774_, v_source_2775_, v_target_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2779_, v_x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2782_, lean_object* v_x_2783_){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_box(0);
v___x_2785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2783_, v_var_2782_, v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___f_2790_; lean_object* v___x_2791_; 
v___f_2790_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2790_, 0, v_var_2786_);
v___x_2791_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2790_, v_a_2787_, v_a_2788_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2797_, v_a_2798_, v_a_2799_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v_fst_2823_; lean_object* v_snd_2824_; lean_object* v_currFnIdx_2827_; lean_object* v_assignments_2828_; lean_object* v_funVals_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2820_ = lean_st_ref_get(v_a_2818_);
v___x_2821_ = lean_st_ref_take(v_a_2817_);
v_currFnIdx_2827_ = lean_ctor_get(v_a_2816_, 1);
v_assignments_2828_ = lean_ctor_get(v___x_2821_, 0);
lean_inc_ref(v_assignments_2828_);
v_funVals_2829_ = lean_ctor_get(v___x_2821_, 1);
lean_inc_ref(v_funVals_2829_);
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_array_get_size(v_funVals_2829_);
v___x_2832_ = lean_nat_dec_lt(v_currFnIdx_2827_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_dec_ref(v_funVals_2829_);
lean_dec_ref(v_assignments_2828_);
lean_dec(v___x_2820_);
lean_dec(v_v_2815_);
v_fst_2823_ = v___x_2830_;
v_snd_2824_ = v___x_2821_;
goto v___jp_2822_;
}
else
{
lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2844_; 
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; lean_object* v_unused_2846_; 
v_unused_2845_ = lean_ctor_get(v___x_2821_, 1);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v___x_2821_, 0);
lean_dec(v_unused_2846_);
v___x_2834_ = v___x_2821_;
v_isShared_2835_ = v_isSharedCheck_2844_;
goto v_resetjp_2833_;
}
else
{
lean_dec(v___x_2821_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2844_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_env_2836_; lean_object* v_v_2837_; lean_object* v_xs_x27_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v_env_2836_ = lean_ctor_get(v___x_2820_, 0);
lean_inc_ref(v_env_2836_);
lean_dec(v___x_2820_);
v_v_2837_ = lean_array_fget(v_funVals_2829_, v_currFnIdx_2827_);
v_xs_x27_2838_ = lean_array_fset(v_funVals_2829_, v_currFnIdx_2827_, v___x_2830_);
v___x_2839_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2836_, v_v_2815_, v_v_2837_);
v___x_2840_ = lean_array_fset(v_xs_x27_2838_, v_currFnIdx_2827_, v___x_2839_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 1, v___x_2840_);
v___x_2842_ = v___x_2834_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_assignments_2828_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
v_fst_2823_ = v___x_2830_;
v_snd_2824_ = v___x_2842_;
goto v___jp_2822_;
}
}
}
v___jp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_st_ref_set(v_a_2817_, v_snd_2824_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_fst_2823_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2853_, v_a_2854_, v_a_2855_, v_a_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2871_, uint8_t v_b_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_array_2877_; lean_object* v_start_2878_; lean_object* v_stop_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2916_; 
v_array_2877_ = lean_ctor_get(v_a_2871_, 0);
v_start_2878_ = lean_ctor_get(v_a_2871_, 1);
v_stop_2879_ = lean_ctor_get(v_a_2871_, 2);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_a_2871_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2881_ = v_a_2871_;
v_isShared_2882_ = v_isSharedCheck_2916_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_stop_2879_);
lean_inc(v_start_2878_);
lean_inc(v_array_2877_);
lean_dec(v_a_2871_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2916_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_nat_dec_lt(v_start_2878_, v_stop_2879_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_del_object(v___x_2881_);
lean_dec(v_stop_2879_);
lean_dec(v_start_2878_);
lean_dec_ref(v_array_2877_);
v___x_2884_ = lean_box(v_b_2872_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
else
{
lean_object* v___x_2886_; lean_object* v_fvarId_2887_; lean_object* v___x_2888_; 
v___x_2886_ = lean_array_fget_borrowed(v_array_2877_, v_start_2878_);
v_fvarId_2887_ = lean_ctor_get(v___x_2886_, 0);
v___x_2888_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2887_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2890_ = lean_box(1);
lean_inc(v_fvarId_2887_);
v___x_2891_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2887_, v___x_2890_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_dec_ref_known(v___x_2891_, 1);
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_nat_add(v_start_2878_, v___x_2892_);
lean_dec(v_start_2878_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2893_);
v___x_2895_ = v___x_2881_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_array_2877_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_stop_2879_);
v___x_2895_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2889_, v___x_2896_);
lean_dec(v_a_2889_);
v_a_2871_ = v___x_2895_;
v_b_2872_ = v___x_2897_;
goto _start;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_a_2889_);
lean_del_object(v___x_2881_);
lean_dec(v_stop_2879_);
lean_dec(v_start_2878_);
lean_dec_ref(v_array_2877_);
v_a_2900_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2891_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2891_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_del_object(v___x_2881_);
lean_dec(v_stop_2879_);
lean_dec(v_start_2878_);
lean_dec_ref(v_array_2877_);
v_a_2908_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2888_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2888_);
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
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2917_, lean_object* v_b_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
uint8_t v_b_boxed_2923_; lean_object* v_res_2924_; 
v_b_boxed_2923_ = lean_unbox(v_b_2918_);
v_res_2924_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2917_, v_b_boxed_2923_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2925_, lean_object* v___x_2926_, lean_object* v_x_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2927_, v_fvarId_2925_, v___x_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2929_, lean_object* v_as_2930_, size_t v_sz_2931_, size_t v_i_2932_, lean_object* v_b_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_a_2938_; uint8_t v___x_2942_; 
v___x_2942_ = lean_usize_dec_lt(v_i_2932_, v_sz_2931_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref(v___x_2929_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_b_2933_);
return v___x_2943_;
}
else
{
lean_object* v_snd_2944_; lean_object* v_fst_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3011_; 
v_snd_2944_ = lean_ctor_get(v_b_2933_, 1);
v_fst_2945_ = lean_ctor_get(v_b_2933_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_b_2933_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2947_ = v_b_2933_;
v_isShared_2948_ = v_isSharedCheck_3011_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_snd_2944_);
lean_inc(v_fst_2945_);
lean_dec(v_b_2933_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3011_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_array_2949_; lean_object* v_start_2950_; lean_object* v_stop_2951_; uint8_t v___x_2952_; 
v_array_2949_ = lean_ctor_get(v_snd_2944_, 0);
v_start_2950_ = lean_ctor_get(v_snd_2944_, 1);
v_stop_2951_ = lean_ctor_get(v_snd_2944_, 2);
v___x_2952_ = lean_nat_dec_lt(v_start_2950_, v_stop_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2954_; 
lean_dec_ref(v___x_2929_);
if (v_isShared_2948_ == 0)
{
v___x_2954_ = v___x_2947_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_snd_2944_);
v___x_2954_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
else
{
lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3007_; 
lean_inc(v_stop_2951_);
lean_inc(v_start_2950_);
lean_inc_ref(v_array_2949_);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_snd_2944_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; lean_object* v_unused_3009_; lean_object* v_unused_3010_; 
v_unused_3008_ = lean_ctor_get(v_snd_2944_, 2);
lean_dec(v_unused_3008_);
v_unused_3009_ = lean_ctor_get(v_snd_2944_, 1);
lean_dec(v_unused_3009_);
v_unused_3010_ = lean_ctor_get(v_snd_2944_, 0);
lean_dec(v_unused_3010_);
v___x_2958_ = v_snd_2944_;
v_isShared_2959_ = v_isSharedCheck_3007_;
goto v_resetjp_2957_;
}
else
{
lean_dec(v_snd_2944_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3007_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_a_2960_; lean_object* v_fvarId_2961_; lean_object* v___x_2962_; 
v_a_2960_ = lean_array_uget_borrowed(v_as_2930_, v_i_2932_);
v_fvarId_2961_ = lean_ctor_get(v_a_2960_, 0);
v___x_2962_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2961_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = lean_array_fget_borrowed(v_array_2949_, v_start_2950_);
v___x_2965_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2964_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v___x_2967_ = lean_unsigned_to_nat(1u);
v___x_2968_ = lean_nat_add(v_start_2950_, v___x_2967_);
lean_dec(v_start_2950_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v___x_2968_);
v___x_2970_ = v___x_2958_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_array_2949_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_stop_2951_);
v___x_2970_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
lean_inc(v_a_2963_);
lean_inc_ref(v___x_2929_);
v___x_2971_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2929_, v_a_2963_, v_a_2966_);
v___x_2972_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2971_, v_a_2963_);
lean_dec(v_a_2963_);
if (v___x_2972_ == 0)
{
lean_object* v___f_2973_; lean_object* v___x_2974_; 
lean_dec(v_fst_2945_);
lean_inc(v_fvarId_2961_);
v___f_2973_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2973_, 0, v_fvarId_2961_);
lean_closure_set(v___f_2973_, 1, v___x_2971_);
v___x_2974_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2973_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2977_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = lean_box(v___x_2952_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_2970_);
lean_ctor_set(v___x_2947_, 0, v___x_2975_);
v___x_2977_ = v___x_2947_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2970_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
v_a_2938_ = v___x_2977_;
goto v___jp_2937_;
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec_ref(v___x_2970_);
lean_del_object(v___x_2947_);
lean_dec_ref(v___x_2929_);
v_a_2979_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2974_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2974_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v___x_2988_; 
lean_dec(v___x_2971_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_2970_);
v___x_2988_ = v___x_2947_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v___x_2970_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
v_a_2938_ = v___x_2988_;
goto v___jp_2937_;
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_a_2963_);
lean_del_object(v___x_2958_);
lean_dec(v_stop_2951_);
lean_dec(v_start_2950_);
lean_dec_ref(v_array_2949_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2945_);
lean_dec_ref(v___x_2929_);
v_a_2991_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2965_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2965_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_del_object(v___x_2958_);
lean_dec(v_stop_2951_);
lean_dec(v_start_2950_);
lean_dec_ref(v_array_2949_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2945_);
lean_dec_ref(v___x_2929_);
v_a_2999_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2962_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2962_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
}
v___jp_2937_:
{
size_t v___x_2939_; size_t v___x_2940_; 
v___x_2939_ = ((size_t)1ULL);
v___x_2940_ = lean_usize_add(v_i_2932_, v___x_2939_);
v_i_2932_ = v___x_2940_;
v_b_2933_ = v_a_2938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3012_, lean_object* v_as_3013_, lean_object* v_sz_3014_, lean_object* v_i_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
size_t v_sz_boxed_3020_; size_t v_i_boxed_3021_; lean_object* v_res_3022_; 
v_sz_boxed_3020_ = lean_unbox_usize(v_sz_3014_);
lean_dec(v_sz_3014_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3015_);
lean_dec(v_i_3015_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3012_, v_as_3013_, v_sz_boxed_3020_, v_i_boxed_3021_, v_b_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec_ref(v_as_3013_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3023_, lean_object* v_args_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v___x_3032_; lean_object* v_env_3033_; uint8_t v_ret_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; size_t v_sz_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3032_ = lean_st_ref_get(v_a_3030_);
v_env_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc_ref(v_env_3033_);
lean_dec(v___x_3032_);
v_ret_3034_ = 0;
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = lean_array_get_size(v_args_3024_);
v___x_3037_ = l_Array_toSubarray___redArg(v_args_3024_, v___x_3035_, v___x_3036_);
v___x_3038_ = lean_box(v_ret_3034_);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3037_);
v_sz_3040_ = lean_array_size(v_params_3023_);
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3033_, v_params_3023_, v_sz_3040_, v___x_3041_, v___x_3039_, v_a_3025_, v_a_3026_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3060_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3060_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3060_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_fst_3047_; lean_object* v_lower_3049_; lean_object* v_upper_3050_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v_fst_3047_ = lean_ctor_get(v_a_3043_, 0);
lean_inc(v_fst_3047_);
lean_dec(v_a_3043_);
v___x_3054_ = lean_array_get_size(v_params_3023_);
v___x_3055_ = lean_nat_dec_eq(v___x_3054_, v___x_3036_);
if (v___x_3055_ == 0)
{
uint8_t v___x_3056_; 
lean_del_object(v___x_3045_);
v___x_3056_ = lean_nat_dec_le(v___x_3036_, v___x_3035_);
if (v___x_3056_ == 0)
{
v_lower_3049_ = v___x_3036_;
v_upper_3050_ = v___x_3054_;
goto v___jp_3048_;
}
else
{
v_lower_3049_ = v___x_3035_;
v_upper_3050_ = v___x_3054_;
goto v___jp_3048_;
}
}
else
{
lean_object* v___x_3058_; 
lean_dec_ref(v_params_3023_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v_fst_3047_);
v___x_3058_ = v___x_3045_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_fst_3047_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
v___jp_3048_:
{
lean_object* v___x_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = l_Array_toSubarray___redArg(v_params_3023_, v_lower_3049_, v_upper_3050_);
v___x_3052_ = lean_unbox(v_fst_3047_);
lean_dec(v_fst_3047_);
v___x_3053_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3051_, v___x_3052_, v_a_3025_, v_a_3026_, v_a_3030_);
return v___x_3053_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v_params_3023_);
v_a_3061_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3042_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3042_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3069_, lean_object* v_args_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3069_, v_args_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3079_, lean_object* v_as_3080_, size_t v_sz_3081_, size_t v_i_3082_, lean_object* v_b_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3079_, v_as_3080_, v_sz_3081_, v_i_3082_, v_b_3083_, v___y_3084_, v___y_3085_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3092_, lean_object* v_as_3093_, lean_object* v_sz_3094_, lean_object* v_i_3095_, lean_object* v_b_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
size_t v_sz_boxed_3104_; size_t v_i_boxed_3105_; lean_object* v_res_3106_; 
v_sz_boxed_3104_ = lean_unbox_usize(v_sz_3094_);
lean_dec(v_sz_3094_);
v_i_boxed_3105_ = lean_unbox_usize(v_i_3095_);
lean_dec(v_i_3095_);
v_res_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3092_, v_as_3093_, v_sz_boxed_3104_, v_i_boxed_3105_, v_b_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec_ref(v_as_3093_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3107_, lean_object* v_R_3108_, lean_object* v_a_3109_, uint8_t v_b_3110_, lean_object* v_c_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3109_, v_b_3110_, v___y_3112_, v___y_3113_, v___y_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3120_, lean_object* v_R_3121_, lean_object* v_a_3122_, lean_object* v_b_3123_, lean_object* v_c_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
uint8_t v_b_boxed_3132_; lean_object* v_res_3133_; 
v_b_boxed_3132_ = lean_unbox(v_b_3123_);
v_res_3133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3120_, v_R_3121_, v_a_3122_, v_b_boxed_3132_, v_c_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3134_, size_t v_sz_3135_, size_t v_i_3136_, uint8_t v_b_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
uint8_t v_a_3142_; uint8_t v___x_3146_; 
v___x_3146_ = lean_usize_dec_lt(v_i_3136_, v_sz_3135_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_box(v_b_3137_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
else
{
lean_object* v_a_3149_; lean_object* v_fvarId_3150_; lean_object* v___x_3151_; 
v_a_3149_ = lean_array_uget_borrowed(v_as_3134_, v_i_3136_);
v_fvarId_3150_ = lean_ctor_get(v_a_3149_, 0);
v___x_3151_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3150_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = lean_box(1);
v___x_3154_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3153_, v_a_3152_);
lean_dec(v_a_3152_);
if (v___x_3154_ == 0)
{
lean_object* v___f_3155_; lean_object* v___x_3156_; 
lean_inc(v_fvarId_3150_);
v___f_3155_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3155_, 0, v_fvarId_3150_);
lean_closure_set(v___f_3155_, 1, v___x_3153_);
v___x_3156_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3155_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_dec_ref_known(v___x_3156_, 1);
v_a_3142_ = v___x_3146_;
goto v___jp_3141_;
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
v_a_3142_ = v_b_3137_;
goto v___jp_3141_;
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3151_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3151_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
v___jp_3141_:
{
size_t v___x_3143_; size_t v___x_3144_; 
v___x_3143_ = ((size_t)1ULL);
v___x_3144_ = lean_usize_add(v_i_3136_, v___x_3143_);
v_i_3136_ = v___x_3144_;
v_b_3137_ = v_a_3142_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3173_, lean_object* v_sz_3174_, lean_object* v_i_3175_, lean_object* v_b_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
size_t v_sz_boxed_3180_; size_t v_i_boxed_3181_; uint8_t v_b_boxed_3182_; lean_object* v_res_3183_; 
v_sz_boxed_3180_ = lean_unbox_usize(v_sz_3174_);
lean_dec(v_sz_3174_);
v_i_boxed_3181_ = lean_unbox_usize(v_i_3175_);
lean_dec(v_i_3175_);
v_b_boxed_3182_ = lean_unbox(v_b_3176_);
v_res_3183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3173_, v_sz_boxed_3180_, v_i_boxed_3181_, v_b_boxed_3182_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v_as_3173_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
uint8_t v_ret_3192_; size_t v_sz_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v_ret_3192_ = 0;
v_sz_3193_ = lean_array_size(v_params_3184_);
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3184_, v_sz_3193_, v___x_3194_, v_ret_3192_, v_a_3185_, v_a_3186_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec_ref(v_params_3196_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3205_, size_t v_sz_3206_, size_t v_i_3207_, uint8_t v_b_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3205_, v_sz_3206_, v_i_3207_, v_b_3208_, v___y_3209_, v___y_3210_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3217_, lean_object* v_sz_3218_, lean_object* v_i_3219_, lean_object* v_b_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
size_t v_sz_boxed_3228_; size_t v_i_boxed_3229_; uint8_t v_b_boxed_3230_; lean_object* v_res_3231_; 
v_sz_boxed_3228_ = lean_unbox_usize(v_sz_3218_);
lean_dec(v_sz_3218_);
v_i_boxed_3229_ = lean_unbox_usize(v_i_3219_);
lean_dec(v_i_3219_);
v_b_boxed_3230_ = lean_unbox(v_b_3220_);
v_res_3231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3217_, v_sz_boxed_3228_, v_i_boxed_3229_, v_b_boxed_3230_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v_as_3217_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3232_, size_t v_i_3233_, size_t v_stop_3234_, lean_object* v_b_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v___x_3239_; 
v___x_3239_ = lean_usize_dec_eq(v_i_3233_, v_stop_3234_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v_fvarId_3241_; lean_object* v___x_3242_; 
v___x_3240_ = lean_array_uget_borrowed(v_as_3232_, v_i_3233_);
v_fvarId_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_fvarId_3241_);
v___x_3242_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3241_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; size_t v___x_3244_; size_t v___x_3245_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
v___x_3244_ = ((size_t)1ULL);
v___x_3245_ = lean_usize_add(v_i_3233_, v___x_3244_);
v_i_3233_ = v___x_3245_;
v_b_3235_ = v_a_3243_;
goto _start;
}
else
{
return v___x_3242_;
}
}
else
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_b_3235_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3248_, lean_object* v_i_3249_, lean_object* v_stop_3250_, lean_object* v_b_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
size_t v_i_boxed_3255_; size_t v_stop_boxed_3256_; lean_object* v_res_3257_; 
v_i_boxed_3255_ = lean_unbox_usize(v_i_3249_);
lean_dec(v_i_3249_);
v_stop_boxed_3256_ = lean_unbox_usize(v_stop_3250_);
lean_dec(v_stop_3250_);
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3248_, v_i_boxed_3255_, v_stop_boxed_3256_, v_b_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v_as_3248_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v_decl_3277_; lean_object* v_k_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; 
switch(lean_obj_tag(v_x_3258_))
{
case 0:
{
lean_object* v_k_3299_; 
v_k_3299_ = lean_ctor_get(v_x_3258_, 1);
lean_inc_ref(v_k_3299_);
lean_dec_ref_known(v_x_3258_, 2);
v_x_3258_ = v_k_3299_;
goto _start;
}
case 3:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec_ref_known(v_x_3258_, 2);
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
return v___x_3302_;
}
case 4:
{
lean_object* v_cases_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3325_; 
v_cases_3303_ = lean_ctor_get(v_x_3258_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_x_3258_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3305_ = v_x_3258_;
v_isShared_3306_ = v_isSharedCheck_3325_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_cases_3303_);
lean_dec(v_x_3258_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3325_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_alts_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v_alts_3307_ = lean_ctor_get(v_cases_3303_, 3);
lean_inc_ref(v_alts_3307_);
lean_dec_ref(v_cases_3303_);
v___x_3308_ = lean_unsigned_to_nat(0u);
v___x_3309_ = lean_array_get_size(v_alts_3307_);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_nat_dec_lt(v___x_3308_, v___x_3309_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3313_; 
lean_dec_ref(v_alts_3307_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3310_);
v___x_3313_ = v___x_3305_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3310_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
else
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_nat_dec_le(v___x_3309_, v___x_3309_);
if (v___x_3315_ == 0)
{
if (v___x_3311_ == 0)
{
lean_object* v___x_3317_; 
lean_dec_ref(v_alts_3307_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3310_);
v___x_3317_ = v___x_3305_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3310_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
else
{
size_t v___x_3319_; size_t v___x_3320_; lean_object* v___x_3321_; 
lean_del_object(v___x_3305_);
v___x_3319_ = ((size_t)0ULL);
v___x_3320_ = lean_usize_of_nat(v___x_3309_);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3307_, v___x_3319_, v___x_3320_, v___x_3310_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
lean_dec_ref(v_alts_3307_);
return v___x_3321_;
}
}
else
{
size_t v___x_3322_; size_t v___x_3323_; lean_object* v___x_3324_; 
lean_del_object(v___x_3305_);
v___x_3322_ = ((size_t)0ULL);
v___x_3323_ = lean_usize_of_nat(v___x_3309_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3307_, v___x_3322_, v___x_3323_, v___x_3310_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
lean_dec_ref(v_alts_3307_);
return v___x_3324_;
}
}
}
}
case 5:
{
lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3333_; 
v_isSharedCheck_3333_ = !lean_is_exclusive(v_x_3258_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v_x_3258_, 0);
lean_dec(v_unused_3334_);
v___x_3327_ = v_x_3258_;
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
else
{
lean_dec(v_x_3258_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3329_ = lean_box(0);
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3329_);
v___x_3331_ = v___x_3327_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
case 6:
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3342_; 
v_isSharedCheck_3342_ = !lean_is_exclusive(v_x_3258_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v_x_3258_, 0);
lean_dec(v_unused_3343_);
v___x_3336_ = v_x_3258_;
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v_x_3258_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3338_ = lean_box(0);
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
default: 
{
lean_object* v_decl_3344_; lean_object* v_k_3345_; 
v_decl_3344_ = lean_ctor_get(v_x_3258_, 0);
lean_inc_ref(v_decl_3344_);
v_k_3345_ = lean_ctor_get(v_x_3258_, 1);
lean_inc_ref(v_k_3345_);
lean_dec_ref(v_x_3258_);
v_decl_3277_ = v_decl_3344_;
v_k_3278_ = v_k_3345_;
v___y_3279_ = v_a_3259_;
v___y_3280_ = v_a_3260_;
v___y_3281_ = v_a_3261_;
v___y_3282_ = v_a_3262_;
v___y_3283_ = v_a_3263_;
v___y_3284_ = v_a_3264_;
goto v___jp_3276_;
}
}
v___jp_3266_:
{
if (lean_obj_tag(v___y_3274_) == 0)
{
lean_dec_ref_known(v___y_3274_, 1);
v_x_3258_ = v___y_3271_;
v_a_3259_ = v___y_3273_;
v_a_3260_ = v___y_3268_;
v_a_3261_ = v___y_3270_;
v_a_3262_ = v___y_3272_;
v_a_3263_ = v___y_3267_;
v_a_3264_ = v___y_3269_;
goto _start;
}
else
{
lean_dec_ref(v___y_3271_);
return v___y_3274_;
}
}
v___jp_3276_:
{
lean_object* v_params_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v_params_3285_ = lean_ctor_get(v_decl_3277_, 2);
lean_inc_ref(v_params_3285_);
lean_dec_ref(v_decl_3277_);
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = lean_array_get_size(v_params_3285_);
v___x_3288_ = lean_nat_dec_lt(v___x_3286_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_dec_ref(v_params_3285_);
v_x_3258_ = v_k_3278_;
v_a_3259_ = v___y_3279_;
v_a_3260_ = v___y_3280_;
v_a_3261_ = v___y_3281_;
v_a_3262_ = v___y_3282_;
v_a_3263_ = v___y_3283_;
v_a_3264_ = v___y_3284_;
goto _start;
}
else
{
lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_nat_dec_le(v___x_3287_, v___x_3287_);
if (v___x_3291_ == 0)
{
if (v___x_3288_ == 0)
{
lean_dec_ref(v_params_3285_);
v_x_3258_ = v_k_3278_;
v_a_3259_ = v___y_3279_;
v_a_3260_ = v___y_3280_;
v_a_3261_ = v___y_3281_;
v_a_3262_ = v___y_3282_;
v_a_3263_ = v___y_3283_;
v_a_3264_ = v___y_3284_;
goto _start;
}
else
{
size_t v___x_3293_; size_t v___x_3294_; lean_object* v___x_3295_; 
v___x_3293_ = ((size_t)0ULL);
v___x_3294_ = lean_usize_of_nat(v___x_3287_);
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3285_, v___x_3293_, v___x_3294_, v___x_3290_, v___y_3279_, v___y_3280_);
lean_dec_ref(v_params_3285_);
v___y_3267_ = v___y_3283_;
v___y_3268_ = v___y_3280_;
v___y_3269_ = v___y_3284_;
v___y_3270_ = v___y_3281_;
v___y_3271_ = v_k_3278_;
v___y_3272_ = v___y_3282_;
v___y_3273_ = v___y_3279_;
v___y_3274_ = v___x_3295_;
goto v___jp_3266_;
}
}
else
{
size_t v___x_3296_; size_t v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = lean_usize_of_nat(v___x_3287_);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3285_, v___x_3296_, v___x_3297_, v___x_3290_, v___y_3279_, v___y_3280_);
lean_dec_ref(v_params_3285_);
v___y_3267_ = v___y_3283_;
v___y_3268_ = v___y_3280_;
v___y_3269_ = v___y_3284_;
v___y_3270_ = v___y_3281_;
v___y_3271_ = v_k_3278_;
v___y_3272_ = v___y_3282_;
v___y_3273_ = v___y_3279_;
v___y_3274_ = v___x_3298_;
goto v___jp_3266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3346_, size_t v_i_3347_, size_t v_stop_3348_, lean_object* v_b_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___y_3358_; uint8_t v___x_3364_; 
v___x_3364_ = lean_usize_dec_eq(v_i_3347_, v_stop_3348_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_array_uget_borrowed(v_as_3346_, v_i_3347_);
switch(lean_obj_tag(v___x_3365_))
{
case 0:
{
lean_object* v_code_3366_; 
v_code_3366_ = lean_ctor_get(v___x_3365_, 2);
lean_inc_ref(v_code_3366_);
v___y_3358_ = v_code_3366_;
goto v___jp_3357_;
}
case 1:
{
lean_object* v_code_3367_; 
v_code_3367_ = lean_ctor_get(v___x_3365_, 1);
lean_inc_ref(v_code_3367_);
v___y_3358_ = v_code_3367_;
goto v___jp_3357_;
}
default: 
{
lean_object* v_code_3368_; 
v_code_3368_ = lean_ctor_get(v___x_3365_, 0);
lean_inc_ref(v_code_3368_);
v___y_3358_ = v_code_3368_;
goto v___jp_3357_;
}
}
}
else
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_b_3349_);
return v___x_3369_;
}
v___jp_3357_:
{
lean_object* v___x_3359_; 
v___x_3359_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3358_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; size_t v___x_3361_; size_t v___x_3362_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = ((size_t)1ULL);
v___x_3362_ = lean_usize_add(v_i_3347_, v___x_3361_);
v_i_3347_ = v___x_3362_;
v_b_3349_ = v_a_3360_;
goto _start;
}
else
{
return v___x_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3370_, lean_object* v_i_3371_, lean_object* v_stop_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
size_t v_i_boxed_3381_; size_t v_stop_boxed_3382_; lean_object* v_res_3383_; 
v_i_boxed_3381_ = lean_unbox_usize(v_i_3371_);
lean_dec(v_i_3371_);
v_stop_boxed_3382_ = lean_unbox_usize(v_stop_3372_);
lean_dec(v_stop_3372_);
v_res_3383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3370_, v_i_boxed_3381_, v_stop_boxed_3382_, v_b_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec_ref(v_as_3370_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3393_, size_t v_i_3394_, size_t v_stop_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3393_, v_i_3394_, v_stop_3395_, v_b_3396_, v___y_3397_, v___y_3398_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3405_, lean_object* v_i_3406_, lean_object* v_stop_3407_, lean_object* v_b_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
size_t v_i_boxed_3416_; size_t v_stop_boxed_3417_; lean_object* v_res_3418_; 
v_i_boxed_3416_ = lean_unbox_usize(v_i_3406_);
lean_dec(v_i_3406_);
v_stop_boxed_3417_ = lean_unbox_usize(v_stop_3407_);
lean_dec(v_stop_3407_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3405_, v_i_boxed_3416_, v_stop_boxed_3417_, v_b_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec_ref(v_as_3405_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3419_, lean_object* v_b_3420_){
_start:
{
lean_object* v_array_3421_; lean_object* v_start_3422_; lean_object* v_stop_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3436_; 
v_array_3421_ = lean_ctor_get(v_a_3419_, 0);
v_start_3422_ = lean_ctor_get(v_a_3419_, 1);
v_stop_3423_ = lean_ctor_get(v_a_3419_, 2);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3425_ = v_a_3419_;
v_isShared_3426_ = v_isSharedCheck_3436_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_stop_3423_);
lean_inc(v_start_3422_);
lean_inc(v_array_3421_);
lean_dec(v_a_3419_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3436_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_nat_dec_lt(v_start_3422_, v_stop_3423_);
if (v___x_3427_ == 0)
{
lean_del_object(v___x_3425_);
lean_dec(v_stop_3423_);
lean_dec(v_start_3422_);
lean_dec_ref(v_array_3421_);
return v_b_3420_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3428_ = lean_unsigned_to_nat(1u);
v___x_3429_ = lean_nat_add(v_start_3422_, v___x_3428_);
lean_inc_ref(v_array_3421_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v___x_3429_);
v___x_3431_ = v___x_3425_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_array_3421_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3435_, 2, v_stop_3423_);
v___x_3431_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = lean_array_fget(v_array_3421_, v_start_3422_);
lean_dec(v_start_3422_);
lean_dec_ref(v_array_3421_);
v___x_3433_ = lean_array_push(v_b_3420_, v___x_3432_);
v_a_3419_ = v___x_3431_;
v_b_3420_ = v___x_3433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3437_, size_t v_i_3438_, lean_object* v_bs_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_usize_dec_lt(v_i_3438_, v_sz_3437_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_bs_3439_);
return v___x_3444_;
}
else
{
lean_object* v_v_3445_; lean_object* v___x_3446_; 
v_v_3445_ = lean_array_uget_borrowed(v_bs_3439_, v_i_3438_);
v___x_3446_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3445_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; lean_object* v_bs_x27_3449_; size_t v___x_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___x_3448_ = lean_unsigned_to_nat(0u);
v_bs_x27_3449_ = lean_array_uset(v_bs_3439_, v_i_3438_, v___x_3448_);
v___x_3450_ = ((size_t)1ULL);
v___x_3451_ = lean_usize_add(v_i_3438_, v___x_3450_);
v___x_3452_ = lean_array_uset(v_bs_x27_3449_, v_i_3438_, v_a_3447_);
v_i_3438_ = v___x_3451_;
v_bs_3439_ = v___x_3452_;
goto _start;
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec_ref(v_bs_3439_);
v_a_3454_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3446_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3446_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3462_, lean_object* v_i_3463_, lean_object* v_bs_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
size_t v_sz_boxed_3468_; size_t v_i_boxed_3469_; lean_object* v_res_3470_; 
v_sz_boxed_3468_ = lean_unbox_usize(v_sz_3462_);
lean_dec(v_sz_3462_);
v_i_boxed_3469_ = lean_unbox_usize(v_i_3463_);
lean_dec(v_i_3463_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3468_, v_i_boxed_3469_, v_bs_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3471_, size_t v_i_3472_, size_t v_stop_3473_, lean_object* v_b_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_eq(v_i_3472_, v_stop_3473_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; lean_object* v_fvarId_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3480_ = lean_array_uget_borrowed(v_as_3471_, v_i_3472_);
v_fvarId_3481_ = lean_ctor_get(v___x_3480_, 0);
v___x_3482_ = lean_box(1);
lean_inc(v_fvarId_3481_);
v___x_3483_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3481_, v___x_3482_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; size_t v___x_3485_; size_t v___x_3486_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___x_3485_ = ((size_t)1ULL);
v___x_3486_ = lean_usize_add(v_i_3472_, v___x_3485_);
v_i_3472_ = v___x_3486_;
v_b_3474_ = v_a_3484_;
goto _start;
}
else
{
return v___x_3483_;
}
}
else
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_b_3474_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3489_, lean_object* v_i_3490_, lean_object* v_stop_3491_, lean_object* v_b_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
size_t v_i_boxed_3497_; size_t v_stop_boxed_3498_; lean_object* v_res_3499_; 
v_i_boxed_3497_ = lean_unbox_usize(v_i_3490_);
lean_dec(v_i_3490_);
v_stop_boxed_3498_ = lean_unbox_usize(v_stop_3491_);
lean_dec(v_stop_3491_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3489_, v_i_boxed_3497_, v_stop_boxed_3498_, v_b_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v_as_3489_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3500_, size_t v_i_3501_, size_t v_stop_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
uint8_t v___x_3508_; 
v___x_3508_ = lean_usize_dec_eq(v_i_3501_, v_stop_3502_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v_fst_3510_; lean_object* v_snd_3511_; lean_object* v_fvarId_3512_; lean_object* v___x_3513_; 
v___x_3509_ = lean_array_uget_borrowed(v_as_3500_, v_i_3501_);
v_fst_3510_ = lean_ctor_get(v___x_3509_, 0);
v_snd_3511_ = lean_ctor_get(v___x_3509_, 1);
v_fvarId_3512_ = lean_ctor_get(v_fst_3510_, 0);
lean_inc(v_snd_3511_);
lean_inc(v_fvarId_3512_);
v___x_3513_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3512_, v_snd_3511_, v___y_3504_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; size_t v___x_3515_; size_t v___x_3516_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = ((size_t)1ULL);
v___x_3516_ = lean_usize_add(v_i_3501_, v___x_3515_);
v_i_3501_ = v___x_3516_;
v_b_3503_ = v_a_3514_;
goto _start;
}
else
{
return v___x_3513_;
}
}
else
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v_b_3503_);
return v___x_3518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3519_, lean_object* v_i_3520_, lean_object* v_stop_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
size_t v_i_boxed_3527_; size_t v_stop_boxed_3528_; lean_object* v_res_3529_; 
v_i_boxed_3527_ = lean_unbox_usize(v_i_3520_);
lean_dec(v_i_3520_);
v_stop_boxed_3528_ = lean_unbox_usize(v_stop_3521_);
lean_dec(v_stop_3521_);
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3519_, v_i_boxed_3527_, v_stop_boxed_3528_, v_b_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v_as_3519_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3532_, size_t v_i_3533_, size_t v_stop_3534_, lean_object* v_b_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
uint8_t v___x_3543_; 
v___x_3543_ = lean_usize_dec_eq(v_i_3533_, v_stop_3534_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = lean_array_uget_borrowed(v_as_3532_, v_i_3533_);
v___x_3545_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3544_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; size_t v___x_3547_; size_t v___x_3548_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = ((size_t)1ULL);
v___x_3548_ = lean_usize_add(v_i_3533_, v___x_3547_);
v_i_3533_ = v___x_3548_;
v_b_3535_ = v_a_3546_;
goto _start;
}
else
{
return v___x_3545_;
}
}
else
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_b_3535_);
return v___x_3550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v___y_3566_; 
switch(lean_obj_tag(v_letVal_3551_))
{
case 0:
{
lean_object* v_value_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3583_; 
v_value_3575_ = lean_ctor_get(v_letVal_3551_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_letVal_3551_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3577_ = v_letVal_3551_;
v_isShared_3578_ = v_isSharedCheck_3583_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_value_3575_);
lean_dec(v_letVal_3551_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3583_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3579_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3575_);
lean_dec_ref(v_value_3575_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3579_);
v___x_3581_ = v___x_3577_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
case 1:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = lean_box(1);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
return v___x_3585_;
}
case 2:
{
lean_object* v_idx_3586_; lean_object* v_struct_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v_idx_3586_ = lean_ctor_get(v_letVal_3551_, 1);
lean_inc(v_idx_3586_);
v_struct_3587_ = lean_ctor_get(v_letVal_3551_, 2);
lean_inc(v_struct_3587_);
lean_dec_ref_known(v_letVal_3551_, 3);
v___x_3588_ = lean_st_ref_get(v_a_3557_);
v___x_3589_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3587_, v_a_3552_, v_a_3553_);
lean_dec(v_struct_3587_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3599_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v_env_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
v_env_3594_ = lean_ctor_get(v___x_3588_, 0);
lean_inc_ref(v_env_3594_);
lean_dec(v___x_3588_);
v___x_3595_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3594_, v_a_3590_, v_idx_3586_);
lean_dec(v_idx_3586_);
lean_dec(v_a_3590_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3595_);
v___x_3597_ = v___x_3592_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
else
{
lean_dec(v___x_3588_);
lean_dec(v_idx_3586_);
return v___x_3589_;
}
}
case 3:
{
lean_object* v_declName_3600_; lean_object* v_args_3601_; lean_object* v___x_3602_; lean_object* v_env_3603_; lean_object* v___x_3604_; lean_object* v_numFields_3606_; lean_object* v_lower_3607_; lean_object* v_upper_3608_; lean_object* v___x_3636_; lean_object* v___y_3705_; uint8_t v___x_3714_; 
v_declName_3600_ = lean_ctor_get(v_letVal_3551_, 0);
lean_inc(v_declName_3600_);
v_args_3601_ = lean_ctor_get(v_letVal_3551_, 2);
lean_inc_ref(v_args_3601_);
lean_dec_ref_known(v_letVal_3551_, 3);
v___x_3602_ = lean_st_ref_get(v_a_3557_);
v_env_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3602_);
v___x_3604_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_array_get_size(v_args_3601_);
v___x_3714_ = lean_nat_dec_lt(v___x_3604_, v___x_3636_);
if (v___x_3714_ == 0)
{
goto v___jp_3637_;
}
else
{
lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3715_ = lean_box(0);
v___x_3716_ = lean_nat_dec_le(v___x_3636_, v___x_3636_);
if (v___x_3716_ == 0)
{
if (v___x_3714_ == 0)
{
goto v___jp_3637_;
}
else
{
size_t v___x_3717_; size_t v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = ((size_t)0ULL);
v___x_3718_ = lean_usize_of_nat(v___x_3636_);
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3601_, v___x_3717_, v___x_3718_, v___x_3715_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3705_ = v___x_3719_;
goto v___jp_3704_;
}
}
else
{
size_t v___x_3720_; size_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = lean_usize_of_nat(v___x_3636_);
v___x_3722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3601_, v___x_3720_, v___x_3721_, v___x_3715_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3705_ = v___x_3722_;
goto v___jp_3704_;
}
}
v___jp_3605_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3609_ = l_Array_toSubarray___redArg(v_args_3601_, v_lower_3607_, v_upper_3608_);
v___x_3610_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3611_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_array_get_size(v___x_3611_);
v___x_3613_ = lean_nat_dec_eq(v_numFields_3606_, v___x_3612_);
lean_dec(v_numFields_3606_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v___x_3611_);
lean_dec(v_declName_3600_);
v___x_3614_ = lean_box(1);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
else
{
size_t v_sz_3616_; size_t v___x_3617_; lean_object* v___x_3618_; 
v_sz_3616_ = lean_array_size(v___x_3611_);
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3616_, v___x_3617_, v___x_3611_, v_a_3552_, v_a_3553_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3627_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3627_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3627_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3623_, 0, v_declName_3600_);
lean_ctor_set(v___x_3623_, 1, v_a_3619_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v___x_3623_);
v___x_3625_ = v___x_3621_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v_declName_3600_);
v_a_3628_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3618_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3618_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
v___jp_3637_:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3554_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3638_, 1);
v___x_3640_ = lean_unbox(v_a_3639_);
lean_dec(v_a_3639_);
lean_inc(v_declName_3600_);
v___x_3641_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3600_, v___x_3640_, v_a_3556_, v_a_3557_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3687_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3687_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3687_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
if (lean_obj_tag(v_a_3642_) == 1)
{
lean_object* v_val_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
lean_dec_ref(v_args_3601_);
v_val_3646_ = lean_ctor_get(v_a_3642_, 0);
lean_inc(v_val_3646_);
lean_dec_ref_known(v_a_3642_, 1);
v___x_3647_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3646_);
lean_dec(v_val_3646_);
v___x_3648_ = lean_nat_dec_eq(v___x_3647_, v___x_3636_);
lean_dec(v___x_3647_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
lean_dec_ref(v_env_3603_);
lean_dec(v_declName_3600_);
v___x_3649_ = lean_box(1);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3649_);
v___x_3651_ = v___x_3644_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
else
{
lean_object* v___x_3653_; 
lean_inc(v_declName_3600_);
v___x_3653_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3603_, v_declName_3600_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v___x_3654_; 
lean_del_object(v___x_3644_);
v___x_3654_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3600_, v_a_3552_, v_a_3553_);
lean_dec(v_declName_3600_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3667_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3667_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3667_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
if (lean_obj_tag(v_a_3655_) == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = lean_box(1);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
else
{
lean_object* v_val_3663_; lean_object* v___x_3665_; 
v_val_3663_ = lean_ctor_get(v_a_3655_, 0);
lean_inc(v_val_3663_);
lean_dec_ref_known(v_a_3655_, 1);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v_val_3663_);
v___x_3665_ = v___x_3657_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_val_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
v_a_3668_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3654_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3654_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
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
lean_object* v_val_3676_; lean_object* v___x_3678_; 
lean_dec(v_declName_3600_);
v_val_3676_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_val_3676_);
lean_dec_ref_known(v___x_3653_, 1);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_val_3676_);
v___x_3678_ = v___x_3644_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_val_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
uint8_t v___x_3680_; lean_object* v___x_3681_; 
lean_del_object(v___x_3644_);
lean_dec(v_a_3642_);
v___x_3680_ = 0;
lean_inc(v_declName_3600_);
v___x_3681_ = l_Lean_Environment_find_x3f(v_env_3603_, v_declName_3600_, v___x_3680_);
if (lean_obj_tag(v___x_3681_) == 1)
{
lean_object* v_val_3682_; 
v_val_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_val_3682_);
lean_dec_ref_known(v___x_3681_, 1);
if (lean_obj_tag(v_val_3682_) == 6)
{
lean_object* v_val_3683_; lean_object* v_numParams_3684_; lean_object* v_numFields_3685_; uint8_t v___x_3686_; 
v_val_3683_ = lean_ctor_get(v_val_3682_, 0);
lean_inc_ref(v_val_3683_);
lean_dec_ref_known(v_val_3682_, 1);
v_numParams_3684_ = lean_ctor_get(v_val_3683_, 3);
lean_inc(v_numParams_3684_);
v_numFields_3685_ = lean_ctor_get(v_val_3683_, 4);
lean_inc(v_numFields_3685_);
lean_dec_ref(v_val_3683_);
v___x_3686_ = lean_nat_dec_le(v_numParams_3684_, v___x_3604_);
if (v___x_3686_ == 0)
{
v_numFields_3606_ = v_numFields_3685_;
v_lower_3607_ = v_numParams_3684_;
v_upper_3608_ = v___x_3636_;
goto v___jp_3605_;
}
else
{
lean_dec(v_numParams_3684_);
v_numFields_3606_ = v_numFields_3685_;
v_lower_3607_ = v___x_3604_;
v_upper_3608_ = v___x_3636_;
goto v___jp_3605_;
}
}
else
{
lean_dec(v_val_3682_);
lean_dec_ref(v_args_3601_);
lean_dec(v_declName_3600_);
goto v___jp_3559_;
}
}
else
{
lean_dec(v___x_3681_);
lean_dec_ref(v_args_3601_);
lean_dec(v_declName_3600_);
goto v___jp_3559_;
}
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v_env_3603_);
lean_dec_ref(v_args_3601_);
lean_dec(v_declName_3600_);
v_a_3688_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3641_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3641_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v_env_3603_);
lean_dec_ref(v_args_3601_);
lean_dec(v_declName_3600_);
v_a_3696_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3638_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3638_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
v___jp_3704_:
{
if (lean_obj_tag(v___y_3705_) == 0)
{
lean_dec_ref_known(v___y_3705_, 1);
goto v___jp_3637_;
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_env_3603_);
lean_dec_ref(v_args_3601_);
lean_dec(v_declName_3600_);
v_a_3706_ = lean_ctor_get(v___y_3705_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___y_3705_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___y_3705_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___y_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
default: 
{
lean_object* v_args_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; 
v_args_3723_ = lean_ctor_get(v_letVal_3551_, 1);
lean_inc_ref(v_args_3723_);
lean_dec_ref_known(v_letVal_3551_, 2);
v___x_3724_ = lean_unsigned_to_nat(0u);
v___x_3725_ = lean_array_get_size(v_args_3723_);
v___x_3726_ = lean_nat_dec_lt(v___x_3724_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_dec_ref(v_args_3723_);
goto v___jp_3562_;
}
else
{
lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = lean_box(0);
v___x_3728_ = lean_nat_dec_le(v___x_3725_, v___x_3725_);
if (v___x_3728_ == 0)
{
if (v___x_3726_ == 0)
{
lean_dec_ref(v_args_3723_);
goto v___jp_3562_;
}
else
{
size_t v___x_3729_; size_t v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = lean_usize_of_nat(v___x_3725_);
v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3723_, v___x_3729_, v___x_3730_, v___x_3727_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
lean_dec_ref(v_args_3723_);
v___y_3566_ = v___x_3731_;
goto v___jp_3565_;
}
}
else
{
size_t v___x_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = ((size_t)0ULL);
v___x_3733_ = lean_usize_of_nat(v___x_3725_);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3723_, v___x_3732_, v___x_3733_, v___x_3727_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
lean_dec_ref(v_args_3723_);
v___y_3566_ = v___x_3734_;
goto v___jp_3565_;
}
}
}
}
v___jp_3559_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_box(1);
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
return v___x_3561_;
}
v___jp_3562_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = lean_box(1);
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
return v___x_3564_;
}
v___jp_3565_:
{
if (lean_obj_tag(v___y_3566_) == 0)
{
lean_dec_ref_known(v___y_3566_, 1);
goto v___jp_3562_;
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
v_a_3567_ = lean_ctor_get(v___y_3566_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___y_3566_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___y_3566_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___y_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3735_, lean_object* v_args_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_params_3744_; lean_object* v_value_3745_; lean_object* v___x_3746_; 
v_params_3744_ = lean_ctor_get(v_funDecl_3735_, 2);
lean_inc_ref(v_params_3744_);
v_value_3745_ = lean_ctor_get(v_funDecl_3735_, 4);
lean_inc_ref(v_value_3745_);
lean_dec_ref(v_funDecl_3735_);
v___x_3746_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3744_, v_args_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3758_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3758_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3758_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_unbox(v_a_3747_);
lean_dec(v_a_3747_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3754_; 
lean_dec_ref(v_value_3745_);
v___x_3752_ = lean_box(0);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3752_);
v___x_3754_ = v___x_3749_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
else
{
lean_object* v___x_3756_; 
lean_del_object(v___x_3749_);
lean_inc_ref(v_value_3745_);
v___x_3756_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3745_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v___x_3757_; 
lean_dec_ref_known(v___x_3756_, 1);
v___x_3757_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3745_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
return v___x_3757_;
}
else
{
lean_dec_ref(v_value_3745_);
return v___x_3756_;
}
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v_value_3745_);
v_a_3759_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3746_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3746_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3767_, lean_object* v_as_3768_, size_t v_sz_3769_, size_t v_i_3770_, lean_object* v_b_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_a_3780_; uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3770_, v_sz_3769_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_b_3771_);
return v___x_3785_;
}
else
{
lean_object* v___x_3786_; lean_object* v_a_3787_; 
v___x_3786_ = lean_box(0);
v_a_3787_ = lean_array_uget_borrowed(v_as_3768_, v_i_3770_);
if (lean_obj_tag(v_a_3787_) == 0)
{
lean_object* v_ctorName_3788_; lean_object* v_params_3789_; lean_object* v_code_3790_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3800_; lean_object* v___y_3802_; lean_object* v___x_3803_; 
v_ctorName_3788_ = lean_ctor_get(v_a_3787_, 0);
v_params_3789_ = lean_ctor_get(v_a_3787_, 1);
v_code_3790_ = lean_ctor_get(v_a_3787_, 2);
v___x_3803_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3767_, v_ctorName_3788_);
if (lean_obj_tag(v___x_3803_) == 1)
{
lean_object* v_val_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v_val_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_val_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v___x_3805_ = l_Array_zip___redArg(v_params_3789_, v_val_3804_);
lean_dec(v_val_3804_);
v___x_3806_ = lean_unsigned_to_nat(0u);
v___x_3807_ = lean_array_get_size(v___x_3805_);
v___x_3808_ = lean_nat_dec_lt(v___x_3806_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_dec_ref(v___x_3805_);
v___y_3792_ = v___y_3772_;
v___y_3793_ = v___y_3773_;
v___y_3794_ = v___y_3774_;
v___y_3795_ = v___y_3775_;
v___y_3796_ = v___y_3776_;
v___y_3797_ = v___y_3777_;
goto v___jp_3791_;
}
else
{
uint8_t v___x_3809_; 
v___x_3809_ = lean_nat_dec_le(v___x_3807_, v___x_3807_);
if (v___x_3809_ == 0)
{
if (v___x_3808_ == 0)
{
lean_dec_ref(v___x_3805_);
v___y_3792_ = v___y_3772_;
v___y_3793_ = v___y_3773_;
v___y_3794_ = v___y_3774_;
v___y_3795_ = v___y_3775_;
v___y_3796_ = v___y_3776_;
v___y_3797_ = v___y_3777_;
goto v___jp_3791_;
}
else
{
size_t v___x_3810_; size_t v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = ((size_t)0ULL);
v___x_3811_ = lean_usize_of_nat(v___x_3807_);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3805_, v___x_3810_, v___x_3811_, v___x_3786_, v___y_3772_, v___y_3773_, v___y_3777_);
lean_dec_ref(v___x_3805_);
v___y_3800_ = v___x_3812_;
goto v___jp_3799_;
}
}
else
{
size_t v___x_3813_; size_t v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = ((size_t)0ULL);
v___x_3814_ = lean_usize_of_nat(v___x_3807_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3805_, v___x_3813_, v___x_3814_, v___x_3786_, v___y_3772_, v___y_3773_, v___y_3777_);
lean_dec_ref(v___x_3805_);
v___y_3800_ = v___x_3815_;
goto v___jp_3799_;
}
}
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
lean_dec(v___x_3803_);
v___x_3816_ = lean_unsigned_to_nat(0u);
v___x_3817_ = lean_array_get_size(v_params_3789_);
v___x_3818_ = lean_nat_dec_lt(v___x_3816_, v___x_3817_);
if (v___x_3818_ == 0)
{
v___y_3792_ = v___y_3772_;
v___y_3793_ = v___y_3773_;
v___y_3794_ = v___y_3774_;
v___y_3795_ = v___y_3775_;
v___y_3796_ = v___y_3776_;
v___y_3797_ = v___y_3777_;
goto v___jp_3791_;
}
else
{
uint8_t v___x_3819_; 
v___x_3819_ = lean_nat_dec_le(v___x_3817_, v___x_3817_);
if (v___x_3819_ == 0)
{
if (v___x_3818_ == 0)
{
v___y_3792_ = v___y_3772_;
v___y_3793_ = v___y_3773_;
v___y_3794_ = v___y_3774_;
v___y_3795_ = v___y_3775_;
v___y_3796_ = v___y_3776_;
v___y_3797_ = v___y_3777_;
goto v___jp_3791_;
}
else
{
size_t v___x_3820_; size_t v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = lean_usize_of_nat(v___x_3817_);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3789_, v___x_3820_, v___x_3821_, v___x_3786_, v___y_3772_, v___y_3773_, v___y_3777_);
v___y_3802_ = v___x_3822_;
goto v___jp_3801_;
}
}
else
{
size_t v___x_3823_; size_t v___x_3824_; lean_object* v___x_3825_; 
v___x_3823_ = ((size_t)0ULL);
v___x_3824_ = lean_usize_of_nat(v___x_3817_);
v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3789_, v___x_3823_, v___x_3824_, v___x_3786_, v___y_3772_, v___y_3773_, v___y_3777_);
v___y_3802_ = v___x_3825_;
goto v___jp_3801_;
}
}
}
v___jp_3791_:
{
lean_object* v___x_3798_; 
lean_inc_ref(v_code_3790_);
v___x_3798_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3790_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_dec_ref_known(v___x_3798_, 1);
v_a_3780_ = v___x_3786_;
goto v___jp_3779_;
}
else
{
return v___x_3798_;
}
}
v___jp_3799_:
{
if (lean_obj_tag(v___y_3800_) == 0)
{
lean_dec_ref_known(v___y_3800_, 1);
v___y_3792_ = v___y_3772_;
v___y_3793_ = v___y_3773_;
v___y_3794_ = v___y_3774_;
v___y_3795_ = v___y_3775_;
v___y_3796_ = v___y_3776_;
v___y_3797_ = v___y_3777_;
goto v___jp_3791_;
}
else
{
return v___y_3800_;
}
}
v___jp_3801_:
{
if (lean_obj_tag(v___y_3802_) == 0)
{
lean_dec_ref_known(v___y_3802_, 1);
v___y_3792_ = v___y_3772_;
v___y_3793_ = v___y_3773_;
v___y_3794_ = v___y_3774_;
v___y_3795_ = v___y_3775_;
v___y_3796_ = v___y_3776_;
v___y_3797_ = v___y_3777_;
goto v___jp_3791_;
}
else
{
return v___y_3802_;
}
}
}
else
{
lean_object* v_code_3826_; lean_object* v___x_3827_; 
v_code_3826_ = lean_ctor_get(v_a_3787_, 0);
lean_inc_ref(v_code_3826_);
v___x_3827_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3826_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_dec_ref_known(v___x_3827_, 1);
v_a_3780_ = v___x_3786_;
goto v___jp_3779_;
}
else
{
return v___x_3827_;
}
}
}
v___jp_3779_:
{
size_t v___x_3781_; size_t v___x_3782_; 
v___x_3781_ = ((size_t)1ULL);
v___x_3782_ = lean_usize_add(v_i_3770_, v___x_3781_);
v_i_3770_ = v___x_3782_;
v_b_3771_ = v_a_3780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v_decl_3837_; lean_object* v_k_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; 
switch(lean_obj_tag(v_x_3828_))
{
case 0:
{
lean_object* v_decl_3848_; lean_object* v_k_3849_; lean_object* v_fvarId_3850_; lean_object* v_value_3851_; lean_object* v___x_3852_; 
v_decl_3848_ = lean_ctor_get(v_x_3828_, 0);
lean_inc_ref(v_decl_3848_);
v_k_3849_ = lean_ctor_get(v_x_3828_, 1);
lean_inc_ref(v_k_3849_);
lean_dec_ref_known(v_x_3828_, 2);
v_fvarId_3850_ = lean_ctor_get(v_decl_3848_, 0);
lean_inc(v_fvarId_3850_);
v_value_3851_ = lean_ctor_get(v_decl_3848_, 3);
lean_inc_n(v_value_3851_, 2);
lean_dec_ref(v_decl_3848_);
v___x_3852_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3851_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3850_, v_a_3853_, v_a_3829_, v_a_3830_, v_a_3834_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_dec_ref_known(v___x_3854_, 1);
if (lean_obj_tag(v_value_3851_) == 4)
{
lean_object* v_fvarId_3855_; lean_object* v_args_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; 
v_fvarId_3855_ = lean_ctor_get(v_value_3851_, 0);
lean_inc(v_fvarId_3855_);
v_args_3856_ = lean_ctor_get(v_value_3851_, 1);
lean_inc_ref(v_args_3856_);
lean_dec_ref_known(v_value_3851_, 2);
v___x_3857_ = 0;
v___x_3858_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3857_, v_fvarId_3855_, v_a_3832_);
lean_dec(v_fvarId_3855_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
if (lean_obj_tag(v_a_3859_) == 1)
{
lean_object* v_val_3860_; lean_object* v___x_3861_; 
v_val_3860_ = lean_ctor_get(v_a_3859_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v_a_3859_, 1);
v___x_3861_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3860_, v_args_3856_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_dec_ref_known(v___x_3861_, 1);
v_x_3828_ = v_k_3849_;
goto _start;
}
else
{
lean_dec_ref(v_k_3849_);
return v___x_3861_;
}
}
else
{
lean_dec(v_a_3859_);
lean_dec_ref(v_args_3856_);
v_x_3828_ = v_k_3849_;
goto _start;
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec_ref(v_args_3856_);
lean_dec_ref(v_k_3849_);
v_a_3864_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3858_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3858_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
else
{
lean_dec(v_value_3851_);
v_x_3828_ = v_k_3849_;
goto _start;
}
}
else
{
lean_dec(v_value_3851_);
lean_dec_ref(v_k_3849_);
return v___x_3854_;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v_value_3851_);
lean_dec(v_fvarId_3850_);
lean_dec_ref(v_k_3849_);
v_a_3873_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3852_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3852_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3881_; lean_object* v_args_3882_; uint8_t v___x_3883_; lean_object* v___x_3884_; 
v_fvarId_3881_ = lean_ctor_get(v_x_3828_, 0);
lean_inc(v_fvarId_3881_);
v_args_3882_ = lean_ctor_get(v_x_3828_, 1);
lean_inc_ref(v_args_3882_);
lean_dec_ref_known(v_x_3828_, 2);
v___x_3883_ = 0;
v___x_3884_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3883_, v_fvarId_3881_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___y_3887_; lean_object* v___x_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3889_ = lean_unsigned_to_nat(0u);
v___x_3890_ = lean_array_get_size(v_args_3882_);
v___x_3891_ = lean_nat_dec_lt(v___x_3889_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; 
v___x_3892_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3885_, v_args_3882_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
return v___x_3892_;
}
else
{
lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = lean_box(0);
v___x_3894_ = lean_nat_dec_le(v___x_3890_, v___x_3890_);
if (v___x_3894_ == 0)
{
if (v___x_3891_ == 0)
{
lean_object* v___x_3895_; 
v___x_3895_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3885_, v_args_3882_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
return v___x_3895_;
}
else
{
size_t v___x_3896_; size_t v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = ((size_t)0ULL);
v___x_3897_ = lean_usize_of_nat(v___x_3890_);
v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3882_, v___x_3896_, v___x_3897_, v___x_3893_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
v___y_3887_ = v___x_3898_;
goto v___jp_3886_;
}
}
else
{
size_t v___x_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = ((size_t)0ULL);
v___x_3900_ = lean_usize_of_nat(v___x_3890_);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3882_, v___x_3899_, v___x_3900_, v___x_3893_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
v___y_3887_ = v___x_3901_;
goto v___jp_3886_;
}
}
v___jp_3886_:
{
if (lean_obj_tag(v___y_3887_) == 0)
{
lean_object* v___x_3888_; 
lean_dec_ref_known(v___y_3887_, 1);
v___x_3888_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3885_, v_args_3882_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
return v___x_3888_;
}
else
{
lean_dec(v_a_3885_);
lean_dec_ref(v_args_3882_);
return v___y_3887_;
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec_ref(v_args_3882_);
v_a_3902_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3884_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3884_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
case 4:
{
lean_object* v_cases_3910_; lean_object* v_discr_3911_; lean_object* v_alts_3912_; lean_object* v___x_3913_; 
v_cases_3910_ = lean_ctor_get(v_x_3828_, 0);
lean_inc_ref(v_cases_3910_);
lean_dec_ref_known(v_x_3828_, 1);
v_discr_3911_ = lean_ctor_get(v_cases_3910_, 2);
lean_inc(v_discr_3911_);
v_alts_3912_ = lean_ctor_get(v_cases_3910_, 3);
lean_inc_ref(v_alts_3912_);
lean_dec_ref(v_cases_3910_);
v___x_3913_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3911_, v_a_3829_, v_a_3830_);
lean_dec(v_discr_3911_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; size_t v_sz_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = lean_box(0);
v_sz_3916_ = lean_array_size(v_alts_3912_);
v___x_3917_ = ((size_t)0ULL);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3914_, v_alts_3912_, v_sz_3916_, v___x_3917_, v___x_3915_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
lean_dec_ref(v_alts_3912_);
lean_dec(v_a_3914_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; 
v_unused_3926_ = lean_ctor_get(v___x_3918_, 0);
lean_dec(v_unused_3926_);
v___x_3920_ = v___x_3918_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_dec(v___x_3918_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3915_);
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3915_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
else
{
return v___x_3918_;
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v_alts_3912_);
v_a_3927_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3913_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3913_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3935_; lean_object* v___x_3936_; 
v_fvarId_3935_ = lean_ctor_get(v_x_3828_, 0);
lean_inc(v_fvarId_3935_);
lean_dec_ref_known(v_x_3828_, 1);
v___x_3936_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3935_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3937_; 
lean_dec_ref_known(v___x_3936_, 1);
v___x_3937_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3935_, v_a_3829_, v_a_3830_);
lean_dec(v_fvarId_3935_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3938_, v_a_3829_, v_a_3830_, v_a_3834_);
return v___x_3939_;
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_a_3940_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3937_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3937_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_dec(v_fvarId_3935_);
return v___x_3936_;
}
}
case 6:
{
lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3955_; 
v_isSharedCheck_3955_ = !lean_is_exclusive(v_x_3828_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; 
v_unused_3956_ = lean_ctor_get(v_x_3828_, 0);
lean_dec(v_unused_3956_);
v___x_3949_ = v_x_3828_;
v_isShared_3950_ = v_isSharedCheck_3955_;
goto v_resetjp_3948_;
}
else
{
lean_dec(v_x_3828_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3955_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; lean_object* v___x_3953_; 
v___x_3951_ = lean_box(0);
if (v_isShared_3950_ == 0)
{
lean_ctor_set_tag(v___x_3949_, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3951_);
v___x_3953_ = v___x_3949_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
default: 
{
lean_object* v_decl_3957_; lean_object* v_k_3958_; 
v_decl_3957_ = lean_ctor_get(v_x_3828_, 0);
lean_inc_ref(v_decl_3957_);
v_k_3958_ = lean_ctor_get(v_x_3828_, 1);
lean_inc_ref(v_k_3958_);
lean_dec_ref(v_x_3828_);
v_decl_3837_ = v_decl_3957_;
v_k_3838_ = v_k_3958_;
v___y_3839_ = v_a_3829_;
v___y_3840_ = v_a_3830_;
v___y_3841_ = v_a_3831_;
v___y_3842_ = v_a_3832_;
v___y_3843_ = v_a_3833_;
v___y_3844_ = v_a_3834_;
goto v___jp_3836_;
}
}
v___jp_3836_:
{
lean_object* v_value_3845_; lean_object* v___x_3846_; 
v_value_3845_ = lean_ctor_get(v_decl_3837_, 4);
lean_inc_ref(v_value_3845_);
lean_dec_ref(v_decl_3837_);
v___x_3846_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3845_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_dec_ref_known(v___x_3846_, 1);
v_x_3828_ = v_k_3838_;
v_a_3829_ = v___y_3839_;
v_a_3830_ = v___y_3840_;
v_a_3831_ = v___y_3841_;
v_a_3832_ = v___y_3842_;
v_a_3833_ = v___y_3843_;
v_a_3834_ = v___y_3844_;
goto _start;
}
else
{
lean_dec_ref(v_k_3838_);
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
uint8_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = 0;
v___x_3968_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3967_, v_var_3959_, v_a_3963_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_4001_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_4001_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_4001_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
if (lean_obj_tag(v_a_3969_) == 1)
{
lean_object* v_val_3973_; lean_object* v_params_3974_; lean_object* v_value_3975_; lean_object* v___x_3976_; 
lean_del_object(v___x_3971_);
v_val_3973_ = lean_ctor_get(v_a_3969_, 0);
lean_inc(v_val_3973_);
lean_dec_ref_known(v_a_3969_, 1);
v_params_3974_ = lean_ctor_get(v_val_3973_, 2);
lean_inc_ref(v_params_3974_);
v_value_3975_ = lean_ctor_get(v_val_3973_, 4);
lean_inc_ref(v_value_3975_);
lean_dec(v_val_3973_);
v___x_3976_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3974_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
lean_dec_ref(v_params_3974_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3988_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_3988_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3988_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
uint8_t v___x_3981_; 
v___x_3981_ = lean_unbox(v_a_3977_);
lean_dec(v_a_3977_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3984_; 
lean_dec_ref(v_value_3975_);
v___x_3982_ = lean_box(0);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_3982_);
v___x_3984_ = v___x_3979_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
else
{
lean_object* v___x_3986_; 
lean_del_object(v___x_3979_);
lean_inc_ref(v_value_3975_);
v___x_3986_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3975_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref_known(v___x_3986_, 1);
v___x_3987_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3975_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
return v___x_3987_;
}
else
{
lean_dec_ref(v_value_3975_);
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_dec_ref(v_value_3975_);
v_a_3989_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3976_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3976_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
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
lean_object* v___x_3997_; lean_object* v___x_3999_; 
lean_dec(v_a_3969_);
v___x_3997_ = lean_box(0);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3997_);
v___x_3999_ = v___x_3971_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
v_a_4002_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3968_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3968_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
if (lean_obj_tag(v_arg_4010_) == 1)
{
lean_object* v_fvarId_4018_; lean_object* v___x_4019_; 
v_fvarId_4018_ = lean_ctor_get(v_arg_4010_, 0);
v___x_4019_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4018_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
return v___x_4019_;
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_box(0);
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
return v___x_4021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_a_4026_);
lean_dec_ref(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
lean_dec(v_arg_4022_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_4031_, lean_object* v_i_4032_, lean_object* v_stop_4033_, lean_object* v_b_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
size_t v_i_boxed_4042_; size_t v_stop_boxed_4043_; lean_object* v_res_4044_; 
v_i_boxed_4042_ = lean_unbox_usize(v_i_4032_);
lean_dec(v_i_4032_);
v_stop_boxed_4043_ = lean_unbox_usize(v_stop_4033_);
lean_dec(v_stop_4033_);
v_res_4044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_4031_, v_i_boxed_4042_, v_stop_boxed_4043_, v_b_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec_ref(v_as_4031_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_4045_, lean_object* v_args_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_4045_, v_args_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_var_4055_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4064_, lean_object* v_as_4065_, lean_object* v_sz_4066_, lean_object* v_i_4067_, lean_object* v_b_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
size_t v_sz_boxed_4076_; size_t v_i_boxed_4077_; lean_object* v_res_4078_; 
v_sz_boxed_4076_ = lean_unbox_usize(v_sz_4066_);
lean_dec(v_sz_4066_);
v_i_boxed_4077_ = lean_unbox_usize(v_i_4067_);
lean_dec(v_i_4067_);
v_res_4078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4064_, v_as_4065_, v_sz_boxed_4076_, v_i_boxed_4077_, v_b_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec_ref(v_as_4065_);
lean_dec(v_a_4064_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
lean_dec(v_a_4081_);
lean_dec_ref(v_a_4080_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4097_, lean_object* v_R_4098_, lean_object* v_a_4099_, lean_object* v_b_4100_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4099_, v_b_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4102_, size_t v_i_4103_, lean_object* v_bs_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4102_, v_i_4103_, v_bs_4104_, v___y_4105_, v___y_4106_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4113_, lean_object* v_i_4114_, lean_object* v_bs_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
size_t v_sz_boxed_4123_; size_t v_i_boxed_4124_; lean_object* v_res_4125_; 
v_sz_boxed_4123_ = lean_unbox_usize(v_sz_4113_);
lean_dec(v_sz_4113_);
v_i_boxed_4124_ = lean_unbox_usize(v_i_4114_);
lean_dec(v_i_4114_);
v_res_4125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4123_, v_i_boxed_4124_, v_bs_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4126_, size_t v_i_4127_, size_t v_stop_4128_, lean_object* v_b_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4126_, v_i_4127_, v_stop_4128_, v_b_4129_, v___y_4130_, v___y_4131_, v___y_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4138_, lean_object* v_i_4139_, lean_object* v_stop_4140_, lean_object* v_b_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
size_t v_i_boxed_4149_; size_t v_stop_boxed_4150_; lean_object* v_res_4151_; 
v_i_boxed_4149_ = lean_unbox_usize(v_i_4139_);
lean_dec(v_i_4139_);
v_stop_boxed_4150_ = lean_unbox_usize(v_stop_4140_);
lean_dec(v_stop_4140_);
v_res_4151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4138_, v_i_boxed_4149_, v_stop_boxed_4150_, v_b_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec_ref(v_as_4138_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4152_, size_t v_i_4153_, size_t v_stop_4154_, lean_object* v_b_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4152_, v_i_4153_, v_stop_4154_, v_b_4155_, v___y_4156_, v___y_4157_, v___y_4161_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4164_, lean_object* v_i_4165_, lean_object* v_stop_4166_, lean_object* v_b_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
size_t v_i_boxed_4175_; size_t v_stop_boxed_4176_; lean_object* v_res_4177_; 
v_i_boxed_4175_ = lean_unbox_usize(v_i_4165_);
lean_dec(v_i_4165_);
v_stop_boxed_4176_ = lean_unbox_usize(v_stop_4166_);
lean_dec(v_stop_4166_);
v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4164_, v_i_boxed_4175_, v_stop_boxed_4176_, v_b_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec_ref(v_as_4164_);
return v_res_4177_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = lean_unsigned_to_nat(32u);
v___x_4179_ = lean_mk_empty_array_with_capacity(v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4181_ = ((size_t)5ULL);
v___x_4182_ = lean_unsigned_to_nat(0u);
v___x_4183_ = lean_unsigned_to_nat(32u);
v___x_4184_ = lean_mk_empty_array_with_capacity(v___x_4183_);
v___x_4185_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4186_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v___x_4184_);
lean_ctor_set(v___x_4186_, 2, v___x_4182_);
lean_ctor_set(v___x_4186_, 3, v___x_4182_);
lean_ctor_set_usize(v___x_4186_, 4, v___x_4181_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v_traceState_4190_; lean_object* v_traces_4191_; lean_object* v___x_4192_; lean_object* v_traceState_4193_; lean_object* v_env_4194_; lean_object* v_nextMacroScope_4195_; lean_object* v_ngen_4196_; lean_object* v_auxDeclNGen_4197_; lean_object* v_cache_4198_; lean_object* v_messages_4199_; lean_object* v_infoState_4200_; lean_object* v_snapshotTasks_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4220_; 
v___x_4189_ = lean_st_ref_get(v___y_4187_);
v_traceState_4190_ = lean_ctor_get(v___x_4189_, 4);
lean_inc_ref(v_traceState_4190_);
lean_dec(v___x_4189_);
v_traces_4191_ = lean_ctor_get(v_traceState_4190_, 0);
lean_inc_ref(v_traces_4191_);
lean_dec_ref(v_traceState_4190_);
v___x_4192_ = lean_st_ref_take(v___y_4187_);
v_traceState_4193_ = lean_ctor_get(v___x_4192_, 4);
v_env_4194_ = lean_ctor_get(v___x_4192_, 0);
v_nextMacroScope_4195_ = lean_ctor_get(v___x_4192_, 1);
v_ngen_4196_ = lean_ctor_get(v___x_4192_, 2);
v_auxDeclNGen_4197_ = lean_ctor_get(v___x_4192_, 3);
v_cache_4198_ = lean_ctor_get(v___x_4192_, 5);
v_messages_4199_ = lean_ctor_get(v___x_4192_, 6);
v_infoState_4200_ = lean_ctor_get(v___x_4192_, 7);
v_snapshotTasks_4201_ = lean_ctor_get(v___x_4192_, 8);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4203_ = v___x_4192_;
v_isShared_4204_ = v_isSharedCheck_4220_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_snapshotTasks_4201_);
lean_inc(v_infoState_4200_);
lean_inc(v_messages_4199_);
lean_inc(v_cache_4198_);
lean_inc(v_traceState_4193_);
lean_inc(v_auxDeclNGen_4197_);
lean_inc(v_ngen_4196_);
lean_inc(v_nextMacroScope_4195_);
lean_inc(v_env_4194_);
lean_dec(v___x_4192_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4220_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
uint64_t v_tid_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4218_; 
v_tid_4205_ = lean_ctor_get_uint64(v_traceState_4193_, sizeof(void*)*1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_traceState_4193_);
if (v_isSharedCheck_4218_ == 0)
{
lean_object* v_unused_4219_; 
v_unused_4219_ = lean_ctor_get(v_traceState_4193_, 0);
lean_dec(v_unused_4219_);
v___x_4207_ = v_traceState_4193_;
v_isShared_4208_ = v_isSharedCheck_4218_;
goto v_resetjp_4206_;
}
else
{
lean_dec(v_traceState_4193_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4218_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
v___x_4209_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4209_);
v___x_4211_ = v___x_4207_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4209_);
lean_ctor_set_uint64(v_reuseFailAlloc_4217_, sizeof(void*)*1, v_tid_4205_);
v___x_4211_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
lean_object* v___x_4213_; 
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 4, v___x_4211_);
v___x_4213_ = v___x_4203_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_env_4194_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_nextMacroScope_4195_);
lean_ctor_set(v_reuseFailAlloc_4216_, 2, v_ngen_4196_);
lean_ctor_set(v_reuseFailAlloc_4216_, 3, v_auxDeclNGen_4197_);
lean_ctor_set(v_reuseFailAlloc_4216_, 4, v___x_4211_);
lean_ctor_set(v_reuseFailAlloc_4216_, 5, v_cache_4198_);
lean_ctor_set(v_reuseFailAlloc_4216_, 6, v_messages_4199_);
lean_ctor_set(v_reuseFailAlloc_4216_, 7, v_infoState_4200_);
lean_ctor_set(v_reuseFailAlloc_4216_, 8, v_snapshotTasks_4201_);
v___x_4213_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_st_ref_set(v___y_4187_, v___x_4213_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_traces_4191_);
return v___x_4215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4221_);
lean_dec(v___y_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4229_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
return v_res_4239_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4240_, lean_object* v_opt_4241_){
_start:
{
lean_object* v_name_4242_; lean_object* v_defValue_4243_; lean_object* v_map_4244_; lean_object* v___x_4245_; 
v_name_4242_ = lean_ctor_get(v_opt_4241_, 0);
v_defValue_4243_ = lean_ctor_get(v_opt_4241_, 1);
v_map_4244_ = lean_ctor_get(v_opts_4240_, 0);
v___x_4245_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4244_, v_name_4242_);
if (lean_obj_tag(v___x_4245_) == 0)
{
uint8_t v___x_4246_; 
v___x_4246_ = lean_unbox(v_defValue_4243_);
return v___x_4246_;
}
else
{
lean_object* v_val_4247_; 
v_val_4247_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_val_4247_);
lean_dec_ref_known(v___x_4245_, 1);
if (lean_obj_tag(v_val_4247_) == 1)
{
uint8_t v_v_4248_; 
v_v_4248_ = lean_ctor_get_uint8(v_val_4247_, 0);
lean_dec_ref_known(v_val_4247_, 0);
return v_v_4248_;
}
else
{
uint8_t v___x_4249_; 
lean_dec(v_val_4247_);
v___x_4249_ = lean_unbox(v_defValue_4243_);
return v___x_4249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4250_, lean_object* v_opt_4251_){
_start:
{
uint8_t v_res_4252_; lean_object* v_r_4253_; 
v_res_4252_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4250_, v_opt_4251_);
lean_dec_ref(v_opt_4251_);
lean_dec_ref(v_opts_4250_);
v_r_4253_ = lean_box(v_res_4252_);
return v_r_4253_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4256_ = l_Lean_stringToMessageData(v___x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4257_, lean_object* v_x_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4266_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4267_ = l_Lean_MessageData_ofName(v_name_4257_);
v___x_4268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4266_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4270_, lean_object* v_x_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4270_, v_x_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec_ref(v_x_4271_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4280_, lean_object* v_opt_4281_){
_start:
{
lean_object* v_name_4282_; lean_object* v_defValue_4283_; lean_object* v_map_4284_; lean_object* v___x_4285_; 
v_name_4282_ = lean_ctor_get(v_opt_4281_, 0);
v_defValue_4283_ = lean_ctor_get(v_opt_4281_, 1);
v_map_4284_ = lean_ctor_get(v_opts_4280_, 0);
v___x_4285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4284_, v_name_4282_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_inc(v_defValue_4283_);
return v_defValue_4283_;
}
else
{
lean_object* v_val_4286_; 
v_val_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_val_4286_);
lean_dec_ref_known(v___x_4285_, 1);
if (lean_obj_tag(v_val_4286_) == 3)
{
lean_object* v_v_4287_; 
v_v_4287_ = lean_ctor_get(v_val_4286_, 0);
lean_inc(v_v_4287_);
lean_dec_ref_known(v_val_4286_, 1);
return v_v_4287_;
}
else
{
lean_dec(v_val_4286_);
lean_inc(v_defValue_4283_);
return v_defValue_4283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4288_, lean_object* v_opt_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4288_, v_opt_4289_);
lean_dec_ref(v_opt_4289_);
lean_dec_ref(v_opts_4288_);
return v_res_4290_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4291_){
_start:
{
if (lean_obj_tag(v_e_4291_) == 0)
{
uint8_t v___x_4292_; 
v___x_4292_ = 2;
return v___x_4292_;
}
else
{
uint8_t v___x_4293_; 
v___x_4293_ = 0;
return v___x_4293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4294_){
_start:
{
uint8_t v_res_4295_; lean_object* v_r_4296_; 
v_res_4295_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4294_);
lean_dec_ref(v_e_4294_);
v_r_4296_ = lean_box(v_res_4295_);
return v_r_4296_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4297_){
_start:
{
if (lean_obj_tag(v_x_4297_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
v_a_4299_ = lean_ctor_get(v_x_4297_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_x_4297_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v_x_4297_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v_x_4297_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set_tag(v___x_4301_, 1);
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
v_a_4307_ = lean_ctor_get(v_x_4297_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v_x_4297_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v_x_4297_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v_x_4297_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set_tag(v___x_4309_, 0);
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4315_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4318_, size_t v_i_4319_, lean_object* v_bs_4320_){
_start:
{
uint8_t v___x_4321_; 
v___x_4321_ = lean_usize_dec_lt(v_i_4319_, v_sz_4318_);
if (v___x_4321_ == 0)
{
return v_bs_4320_;
}
else
{
lean_object* v_v_4322_; lean_object* v_msg_4323_; lean_object* v___x_4324_; lean_object* v_bs_x27_4325_; size_t v___x_4326_; size_t v___x_4327_; lean_object* v___x_4328_; 
v_v_4322_ = lean_array_uget_borrowed(v_bs_4320_, v_i_4319_);
v_msg_4323_ = lean_ctor_get(v_v_4322_, 1);
lean_inc_ref(v_msg_4323_);
v___x_4324_ = lean_unsigned_to_nat(0u);
v_bs_x27_4325_ = lean_array_uset(v_bs_4320_, v_i_4319_, v___x_4324_);
v___x_4326_ = ((size_t)1ULL);
v___x_4327_ = lean_usize_add(v_i_4319_, v___x_4326_);
v___x_4328_ = lean_array_uset(v_bs_x27_4325_, v_i_4319_, v_msg_4323_);
v_i_4319_ = v___x_4327_;
v_bs_4320_ = v___x_4328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4330_, lean_object* v_i_4331_, lean_object* v_bs_4332_){
_start:
{
size_t v_sz_boxed_4333_; size_t v_i_boxed_4334_; lean_object* v_res_4335_; 
v_sz_boxed_4333_ = lean_unbox_usize(v_sz_4330_);
lean_dec(v_sz_4330_);
v_i_boxed_4334_ = lean_unbox_usize(v_i_4331_);
lean_dec(v_i_4331_);
v_res_4335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4333_, v_i_boxed_4334_, v_bs_4332_);
return v_res_4335_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4336_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
return v___x_4338_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4339_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
lean_ctor_set(v___x_4341_, 2, v___x_4340_);
lean_ctor_set(v___x_4341_, 3, v___x_4340_);
lean_ctor_set(v___x_4341_, 4, v___x_4339_);
lean_ctor_set(v___x_4341_, 5, v___x_4339_);
lean_ctor_set(v___x_4341_, 6, v___x_4339_);
lean_ctor_set(v___x_4341_, 7, v___x_4339_);
lean_ctor_set(v___x_4341_, 8, v___x_4339_);
lean_ctor_set(v___x_4341_, 9, v___x_4339_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4342_, lean_object* v_data_4343_, lean_object* v_ref_4344_, lean_object* v_msg_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_options_4351_; lean_object* v___x_4352_; lean_object* v_traceState_4353_; lean_object* v_traces_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v_options_4351_ = lean_ctor_get(v___y_4348_, 2);
v___x_4352_ = lean_st_ref_get(v___y_4349_);
v_traceState_4353_ = lean_ctor_get(v___x_4352_, 4);
lean_inc_ref(v_traceState_4353_);
lean_dec(v___x_4352_);
v_traces_4354_ = lean_ctor_get(v_traceState_4353_, 0);
lean_inc_ref(v_traces_4354_);
lean_dec_ref(v_traceState_4353_);
v___x_4355_ = lean_st_ref_get(v___y_4349_);
v___x_4356_ = lean_st_ref_get(v___y_4347_);
v___x_4357_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4346_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4414_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4360_ = v___x_4357_;
v_isShared_4361_ = v_isSharedCheck_4414_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4357_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4414_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_env_4362_; lean_object* v_lctx_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4412_; 
v_env_4362_ = lean_ctor_get(v___x_4355_, 0);
lean_inc_ref(v_env_4362_);
lean_dec(v___x_4355_);
v_lctx_4363_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; 
v_unused_4413_ = lean_ctor_get(v___x_4356_, 1);
lean_dec(v_unused_4413_);
v___x_4365_ = v___x_4356_;
v_isShared_4366_ = v_isSharedCheck_4412_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_lctx_4363_);
lean_dec(v___x_4356_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4412_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v_traceState_4369_; lean_object* v_env_4370_; lean_object* v_nextMacroScope_4371_; lean_object* v_ngen_4372_; lean_object* v_auxDeclNGen_4373_; lean_object* v_cache_4374_; lean_object* v_messages_4375_; lean_object* v_infoState_4376_; lean_object* v_snapshotTasks_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4411_; 
v___x_4367_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4368_ = lean_st_ref_take(v___y_4349_);
v_traceState_4369_ = lean_ctor_get(v___x_4368_, 4);
v_env_4370_ = lean_ctor_get(v___x_4368_, 0);
v_nextMacroScope_4371_ = lean_ctor_get(v___x_4368_, 1);
v_ngen_4372_ = lean_ctor_get(v___x_4368_, 2);
v_auxDeclNGen_4373_ = lean_ctor_get(v___x_4368_, 3);
v_cache_4374_ = lean_ctor_get(v___x_4368_, 5);
v_messages_4375_ = lean_ctor_get(v___x_4368_, 6);
v_infoState_4376_ = lean_ctor_get(v___x_4368_, 7);
v_snapshotTasks_4377_ = lean_ctor_get(v___x_4368_, 8);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4379_ = v___x_4368_;
v_isShared_4380_ = v_isSharedCheck_4411_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_snapshotTasks_4377_);
lean_inc(v_infoState_4376_);
lean_inc(v_messages_4375_);
lean_inc(v_cache_4374_);
lean_inc(v_traceState_4369_);
lean_inc(v_auxDeclNGen_4373_);
lean_inc(v_ngen_4372_);
lean_inc(v_nextMacroScope_4371_);
lean_inc(v_env_4370_);
lean_dec(v___x_4368_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4411_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
uint64_t v_tid_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4409_; 
v_tid_4381_ = lean_ctor_get_uint64(v_traceState_4369_, sizeof(void*)*1);
v_isSharedCheck_4409_ = !lean_is_exclusive(v_traceState_4369_);
if (v_isSharedCheck_4409_ == 0)
{
lean_object* v_unused_4410_; 
v_unused_4410_ = lean_ctor_get(v_traceState_4369_, 0);
lean_dec(v_unused_4410_);
v___x_4383_ = v_traceState_4369_;
v_isShared_4384_ = v_isSharedCheck_4409_;
goto v_resetjp_4382_;
}
else
{
lean_dec(v_traceState_4369_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4409_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; size_t v_sz_4386_; size_t v___x_4387_; lean_object* v___x_4388_; lean_object* v_msg_4389_; uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4385_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4354_);
lean_dec_ref(v_traces_4354_);
v_sz_4386_ = lean_array_size(v___x_4385_);
v___x_4387_ = ((size_t)0ULL);
v___x_4388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4386_, v___x_4387_, v___x_4385_);
v_msg_4389_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4389_, 0, v_data_4343_);
lean_ctor_set(v_msg_4389_, 1, v_msg_4345_);
lean_ctor_set(v_msg_4389_, 2, v___x_4388_);
v___x_4390_ = lean_unbox(v_a_4358_);
lean_dec(v_a_4358_);
v___x_4391_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4363_, v___x_4390_);
lean_dec_ref(v_lctx_4363_);
lean_inc_ref(v_options_4351_);
v___x_4392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4392_, 0, v_env_4362_);
lean_ctor_set(v___x_4392_, 1, v___x_4367_);
lean_ctor_set(v___x_4392_, 2, v___x_4391_);
lean_ctor_set(v___x_4392_, 3, v_options_4351_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set_tag(v___x_4365_, 3);
lean_ctor_set(v___x_4365_, 1, v_msg_4389_);
lean_ctor_set(v___x_4365_, 0, v___x_4392_);
v___x_4394_ = v___x_4365_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_msg_4389_);
v___x_4394_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4398_; 
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v_ref_4344_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4342_, v___x_4395_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4396_);
v___x_4398_ = v___x_4383_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4396_);
lean_ctor_set_uint64(v_reuseFailAlloc_4407_, sizeof(void*)*1, v_tid_4381_);
v___x_4398_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4400_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 4, v___x_4398_);
v___x_4400_ = v___x_4379_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_env_4370_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_nextMacroScope_4371_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_ngen_4372_);
lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_auxDeclNGen_4373_);
lean_ctor_set(v_reuseFailAlloc_4406_, 4, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4406_, 5, v_cache_4374_);
lean_ctor_set(v_reuseFailAlloc_4406_, 6, v_messages_4375_);
lean_ctor_set(v_reuseFailAlloc_4406_, 7, v_infoState_4376_);
lean_ctor_set(v_reuseFailAlloc_4406_, 8, v_snapshotTasks_4377_);
v___x_4400_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4401_ = lean_st_ref_set(v___y_4349_, v___x_4400_);
v___x_4402_ = lean_box(0);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4402_);
v___x_4404_ = v___x_4360_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
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
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec(v___x_4356_);
lean_dec(v___x_4355_);
lean_dec_ref(v_traces_4354_);
lean_dec_ref(v_msg_4345_);
lean_dec(v_ref_4344_);
lean_dec_ref(v_data_4343_);
lean_dec_ref(v_oldTraces_4342_);
v_a_4415_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4357_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4357_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4423_, lean_object* v_data_4424_, lean_object* v_ref_4425_, lean_object* v_msg_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4423_, v_data_4424_, v_ref_4425_, v_msg_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4432_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4433_; double v___x_4434_; 
v___x_4433_ = lean_unsigned_to_nat(0u);
v___x_4434_ = lean_float_of_nat(v___x_4433_);
return v___x_4434_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4437_ = l_Lean_stringToMessageData(v___x_4436_);
return v___x_4437_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4438_; double v___x_4439_; 
v___x_4438_ = lean_unsigned_to_nat(1000u);
v___x_4439_ = lean_float_of_nat(v___x_4438_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4440_, uint8_t v_collapsed_4441_, lean_object* v_tag_4442_, lean_object* v_opts_4443_, uint8_t v_clsEnabled_4444_, lean_object* v_oldTraces_4445_, lean_object* v_msg_4446_, lean_object* v_resStartStop_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v_fst_4455_; lean_object* v_snd_4456_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v_data_4460_; lean_object* v_fst_4463_; lean_object* v_snd_4464_; lean_object* v___x_4465_; uint8_t v___x_4466_; lean_object* v___y_4468_; lean_object* v_a_4469_; uint8_t v___y_4484_; double v___y_4515_; 
v_fst_4455_ = lean_ctor_get(v_resStartStop_4447_, 0);
lean_inc(v_fst_4455_);
v_snd_4456_ = lean_ctor_get(v_resStartStop_4447_, 1);
lean_inc(v_snd_4456_);
lean_dec_ref(v_resStartStop_4447_);
v_fst_4463_ = lean_ctor_get(v_snd_4456_, 0);
lean_inc(v_fst_4463_);
v_snd_4464_ = lean_ctor_get(v_snd_4456_, 1);
lean_inc(v_snd_4464_);
lean_dec(v_snd_4456_);
v___x_4465_ = l_Lean_trace_profiler;
v___x_4466_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4443_, v___x_4465_);
if (v___x_4466_ == 0)
{
v___y_4484_ = v___x_4466_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4521_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4443_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; lean_object* v___x_4523_; double v___x_4524_; double v___x_4525_; double v___x_4526_; 
v___x_4522_ = l_Lean_trace_profiler_threshold;
v___x_4523_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4443_, v___x_4522_);
v___x_4524_ = lean_float_of_nat(v___x_4523_);
v___x_4525_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4526_ = lean_float_div(v___x_4524_, v___x_4525_);
v___y_4515_ = v___x_4526_;
goto v___jp_4514_;
}
else
{
lean_object* v___x_4527_; lean_object* v___x_4528_; double v___x_4529_; 
v___x_4527_ = l_Lean_trace_profiler_threshold;
v___x_4528_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4443_, v___x_4527_);
v___x_4529_ = lean_float_of_nat(v___x_4528_);
v___y_4515_ = v___x_4529_;
goto v___jp_4514_;
}
}
v___jp_4457_:
{
lean_object* v___x_4461_; 
lean_inc(v___y_4459_);
v___x_4461_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4445_, v_data_4460_, v___y_4459_, v___y_4458_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v___x_4462_; 
lean_dec_ref_known(v___x_4461_, 1);
v___x_4462_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4455_);
return v___x_4462_;
}
else
{
lean_dec(v_fst_4455_);
return v___x_4461_;
}
}
v___jp_4467_:
{
uint8_t v_result_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; double v___x_4473_; lean_object* v_data_4474_; 
v_result_4470_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4455_);
v___x_4471_ = lean_box(v_result_4470_);
v___x_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
v___x_4473_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4442_);
lean_inc_ref(v___x_4472_);
lean_inc(v_cls_4440_);
v_data_4474_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4474_, 0, v_cls_4440_);
lean_ctor_set(v_data_4474_, 1, v___x_4472_);
lean_ctor_set(v_data_4474_, 2, v_tag_4442_);
lean_ctor_set_float(v_data_4474_, sizeof(void*)*3, v___x_4473_);
lean_ctor_set_float(v_data_4474_, sizeof(void*)*3 + 8, v___x_4473_);
lean_ctor_set_uint8(v_data_4474_, sizeof(void*)*3 + 16, v_collapsed_4441_);
if (v___x_4466_ == 0)
{
lean_dec_ref_known(v___x_4472_, 1);
lean_dec(v_snd_4464_);
lean_dec(v_fst_4463_);
lean_dec_ref(v_tag_4442_);
lean_dec(v_cls_4440_);
v___y_4458_ = v_a_4469_;
v___y_4459_ = v___y_4468_;
v_data_4460_ = v_data_4474_;
goto v___jp_4457_;
}
else
{
lean_object* v_data_4475_; double v___x_4476_; double v___x_4477_; 
lean_dec_ref_known(v_data_4474_, 3);
v_data_4475_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4475_, 0, v_cls_4440_);
lean_ctor_set(v_data_4475_, 1, v___x_4472_);
lean_ctor_set(v_data_4475_, 2, v_tag_4442_);
v___x_4476_ = lean_unbox_float(v_fst_4463_);
lean_dec(v_fst_4463_);
lean_ctor_set_float(v_data_4475_, sizeof(void*)*3, v___x_4476_);
v___x_4477_ = lean_unbox_float(v_snd_4464_);
lean_dec(v_snd_4464_);
lean_ctor_set_float(v_data_4475_, sizeof(void*)*3 + 8, v___x_4477_);
lean_ctor_set_uint8(v_data_4475_, sizeof(void*)*3 + 16, v_collapsed_4441_);
v___y_4458_ = v_a_4469_;
v___y_4459_ = v___y_4468_;
v_data_4460_ = v_data_4475_;
goto v___jp_4457_;
}
}
v___jp_4478_:
{
lean_object* v_ref_4479_; lean_object* v___x_4480_; 
v_ref_4479_ = lean_ctor_get(v___y_4452_, 5);
lean_inc(v___y_4453_);
lean_inc_ref(v___y_4452_);
lean_inc(v___y_4451_);
lean_inc_ref(v___y_4450_);
lean_inc(v___y_4449_);
lean_inc_ref(v___y_4448_);
lean_inc(v_fst_4455_);
v___x_4480_ = lean_apply_8(v_msg_4446_, v_fst_4455_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, lean_box(0));
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref_known(v___x_4480_, 1);
v___y_4468_ = v_ref_4479_;
v_a_4469_ = v_a_4481_;
goto v___jp_4467_;
}
else
{
lean_object* v___x_4482_; 
lean_dec_ref_known(v___x_4480_, 1);
v___x_4482_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4468_ = v_ref_4479_;
v_a_4469_ = v___x_4482_;
goto v___jp_4467_;
}
}
v___jp_4483_:
{
if (v_clsEnabled_4444_ == 0)
{
if (v___y_4484_ == 0)
{
lean_object* v___x_4485_; lean_object* v_traceState_4486_; lean_object* v_env_4487_; lean_object* v_nextMacroScope_4488_; lean_object* v_ngen_4489_; lean_object* v_auxDeclNGen_4490_; lean_object* v_cache_4491_; lean_object* v_messages_4492_; lean_object* v_infoState_4493_; lean_object* v_snapshotTasks_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v_snd_4464_);
lean_dec(v_fst_4463_);
lean_dec_ref(v_msg_4446_);
lean_dec_ref(v_tag_4442_);
lean_dec(v_cls_4440_);
v___x_4485_ = lean_st_ref_take(v___y_4453_);
v_traceState_4486_ = lean_ctor_get(v___x_4485_, 4);
v_env_4487_ = lean_ctor_get(v___x_4485_, 0);
v_nextMacroScope_4488_ = lean_ctor_get(v___x_4485_, 1);
v_ngen_4489_ = lean_ctor_get(v___x_4485_, 2);
v_auxDeclNGen_4490_ = lean_ctor_get(v___x_4485_, 3);
v_cache_4491_ = lean_ctor_get(v___x_4485_, 5);
v_messages_4492_ = lean_ctor_get(v___x_4485_, 6);
v_infoState_4493_ = lean_ctor_get(v___x_4485_, 7);
v_snapshotTasks_4494_ = lean_ctor_get(v___x_4485_, 8);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4496_ = v___x_4485_;
v_isShared_4497_ = v_isSharedCheck_4513_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_snapshotTasks_4494_);
lean_inc(v_infoState_4493_);
lean_inc(v_messages_4492_);
lean_inc(v_cache_4491_);
lean_inc(v_traceState_4486_);
lean_inc(v_auxDeclNGen_4490_);
lean_inc(v_ngen_4489_);
lean_inc(v_nextMacroScope_4488_);
lean_inc(v_env_4487_);
lean_dec(v___x_4485_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4513_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
uint64_t v_tid_4498_; lean_object* v_traces_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4512_; 
v_tid_4498_ = lean_ctor_get_uint64(v_traceState_4486_, sizeof(void*)*1);
v_traces_4499_ = lean_ctor_get(v_traceState_4486_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_traceState_4486_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4501_ = v_traceState_4486_;
v_isShared_4502_ = v_isSharedCheck_4512_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_traces_4499_);
lean_dec(v_traceState_4486_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4512_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4503_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4445_, v_traces_4499_);
lean_dec_ref(v_traces_4499_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v___x_4503_);
v___x_4505_ = v___x_4501_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4503_);
lean_ctor_set_uint64(v_reuseFailAlloc_4511_, sizeof(void*)*1, v_tid_4498_);
v___x_4505_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4507_; 
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 4, v___x_4505_);
v___x_4507_ = v___x_4496_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_env_4487_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_nextMacroScope_4488_);
lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_ngen_4489_);
lean_ctor_set(v_reuseFailAlloc_4510_, 3, v_auxDeclNGen_4490_);
lean_ctor_set(v_reuseFailAlloc_4510_, 4, v___x_4505_);
lean_ctor_set(v_reuseFailAlloc_4510_, 5, v_cache_4491_);
lean_ctor_set(v_reuseFailAlloc_4510_, 6, v_messages_4492_);
lean_ctor_set(v_reuseFailAlloc_4510_, 7, v_infoState_4493_);
lean_ctor_set(v_reuseFailAlloc_4510_, 8, v_snapshotTasks_4494_);
v___x_4507_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4508_ = lean_st_ref_set(v___y_4453_, v___x_4507_);
v___x_4509_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4455_);
return v___x_4509_;
}
}
}
}
}
else
{
goto v___jp_4478_;
}
}
else
{
goto v___jp_4478_;
}
}
v___jp_4514_:
{
double v___x_4516_; double v___x_4517_; double v___x_4518_; uint8_t v___x_4519_; 
v___x_4516_ = lean_unbox_float(v_snd_4464_);
v___x_4517_ = lean_unbox_float(v_fst_4463_);
v___x_4518_ = lean_float_sub(v___x_4516_, v___x_4517_);
v___x_4519_ = lean_float_decLt(v___y_4515_, v___x_4518_);
v___y_4484_ = v___x_4519_;
goto v___jp_4483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4530_, lean_object* v_collapsed_4531_, lean_object* v_tag_4532_, lean_object* v_opts_4533_, lean_object* v_clsEnabled_4534_, lean_object* v_oldTraces_4535_, lean_object* v_msg_4536_, lean_object* v_resStartStop_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
uint8_t v_collapsed_boxed_4545_; uint8_t v_clsEnabled_boxed_4546_; lean_object* v_res_4547_; 
v_collapsed_boxed_4545_ = lean_unbox(v_collapsed_4531_);
v_clsEnabled_boxed_4546_ = lean_unbox(v_clsEnabled_4534_);
v_res_4547_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4530_, v_collapsed_boxed_4545_, v_tag_4532_, v_opts_4533_, v_clsEnabled_boxed_4546_, v_oldTraces_4535_, v_msg_4536_, v_resStartStop_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec_ref(v_opts_4533_);
return v_res_4547_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4551_; double v___x_4552_; 
v___x_4551_ = lean_unsigned_to_nat(1000000000u);
v___x_4552_ = lean_float_of_nat(v___x_4551_);
return v___x_4552_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4562_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4563_ = l_Lean_Name_append(v___x_4562_, v___x_4561_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4564_, lean_object* v___x_4565_, lean_object* v_a_4566_, lean_object* v_b_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_a_4576_; uint8_t v___x_4580_; 
v___x_4580_ = lean_nat_dec_lt(v_a_4566_, v_upperBound_4564_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; 
lean_dec(v_a_4566_);
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v_b_4567_);
return v___x_4581_;
}
else
{
lean_object* v___x_4582_; lean_object* v_toSignature_4583_; lean_object* v_value_4584_; lean_object* v_name_4585_; lean_object* v_params_4586_; uint8_t v_safe_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
lean_dec_ref(v_b_4567_);
v___x_4582_ = lean_array_fget_borrowed(v___x_4565_, v_a_4566_);
v_toSignature_4583_ = lean_ctor_get(v___x_4582_, 0);
v_value_4584_ = lean_ctor_get(v___x_4582_, 1);
v_name_4585_ = lean_ctor_get(v_toSignature_4583_, 0);
v_params_4586_ = lean_ctor_get(v_toSignature_4583_, 3);
v_safe_4587_ = lean_ctor_get_uint8(v_toSignature_4583_, sizeof(void*)*4);
v___x_4588_ = lean_box(0);
v___x_4589_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4587_ == 0)
{
v_a_4576_ = v___x_4589_;
goto v___jp_4575_;
}
else
{
lean_object* v___x_4590_; 
v___x_4590_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4566_, v___y_4569_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___y_4593_; lean_object* v_decls_4623_; lean_object* v___f_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___y_4629_; lean_object* v___y_4630_; uint8_t v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v_a_4635_; lean_object* v___y_4648_; uint8_t v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v_a_4654_; lean_object* v___y_4664_; uint8_t v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4734_; uint8_t v___x_4743_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4590_, 1);
v_decls_4623_ = lean_ctor_get(v___y_4568_, 0);
lean_inc(v_name_4585_);
v___f_4624_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4624_, 0, v_name_4585_);
v___x_4625_ = lean_unsigned_to_nat(0u);
v___x_4626_ = lean_array_get_size(v_params_4586_);
lean_inc(v_a_4566_);
lean_inc_ref(v_decls_4623_);
v___x_4627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4627_, 0, v_decls_4623_);
lean_ctor_set(v___x_4627_, 1, v_a_4566_);
v___x_4743_ = lean_nat_dec_lt(v___x_4625_, v___x_4626_);
if (v___x_4743_ == 0)
{
goto v___jp_4717_;
}
else
{
uint8_t v___x_4744_; 
v___x_4744_ = lean_nat_dec_le(v___x_4626_, v___x_4626_);
if (v___x_4744_ == 0)
{
if (v___x_4743_ == 0)
{
goto v___jp_4717_;
}
else
{
size_t v___x_4745_; size_t v___x_4746_; lean_object* v___x_4747_; 
v___x_4745_ = ((size_t)0ULL);
v___x_4746_ = lean_usize_of_nat(v___x_4626_);
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4586_, v___x_4745_, v___x_4746_, v___x_4588_, v___x_4627_, v___y_4569_, v___y_4573_);
v___y_4734_ = v___x_4747_;
goto v___jp_4733_;
}
}
else
{
size_t v___x_4748_; size_t v___x_4749_; lean_object* v___x_4750_; 
v___x_4748_ = ((size_t)0ULL);
v___x_4749_ = lean_usize_of_nat(v___x_4626_);
v___x_4750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4586_, v___x_4748_, v___x_4749_, v___x_4588_, v___x_4627_, v___y_4569_, v___y_4573_);
v___y_4734_ = v___x_4750_;
goto v___jp_4733_;
}
}
v___jp_4592_:
{
if (lean_obj_tag(v___y_4593_) == 0)
{
lean_object* v___x_4594_; 
lean_dec_ref_known(v___y_4593_, 1);
v___x_4594_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4566_, v___y_4569_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4606_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4597_ = v___x_4594_;
v_isShared_4598_ = v_isSharedCheck_4606_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4594_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4606_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
uint8_t v___x_4599_; 
v___x_4599_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4591_, v_a_4595_);
lean_dec(v_a_4595_);
lean_dec(v_a_4591_);
if (v___x_4599_ == 0)
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4604_; 
lean_dec(v_a_4566_);
v___x_4600_ = lean_box(v_safe_4587_);
v___x_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
v___x_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
lean_ctor_set(v___x_4602_, 1, v___x_4588_);
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 0, v___x_4602_);
v___x_4604_ = v___x_4597_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
else
{
lean_del_object(v___x_4597_);
v_a_4576_ = v___x_4589_;
goto v___jp_4575_;
}
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_dec(v_a_4591_);
lean_dec(v_a_4566_);
v_a_4607_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4594_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4594_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec(v_a_4591_);
lean_dec(v_a_4566_);
v_a_4615_ = lean_ctor_get(v___y_4593_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___y_4593_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___y_4593_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___y_4593_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
v___jp_4628_:
{
lean_object* v___x_4636_; double v___x_4637_; double v___x_4638_; double v___x_4639_; double v___x_4640_; double v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4636_ = lean_io_mono_nanos_now();
v___x_4637_ = lean_float_of_nat(v___y_4630_);
v___x_4638_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4639_ = lean_float_div(v___x_4637_, v___x_4638_);
v___x_4640_ = lean_float_of_nat(v___x_4636_);
v___x_4641_ = lean_float_div(v___x_4640_, v___x_4638_);
v___x_4642_ = lean_box_float(v___x_4639_);
v___x_4643_ = lean_box_float(v___x_4641_);
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4642_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v_a_4635_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
lean_inc_ref(v___y_4629_);
lean_inc(v___y_4633_);
v___x_4646_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4633_, v_safe_4587_, v___y_4629_, v___y_4634_, v___y_4631_, v___y_4632_, v___f_4624_, v___x_4645_, v___x_4627_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec_ref_known(v___x_4627_, 2);
v___y_4593_ = v___x_4646_;
goto v___jp_4592_;
}
v___jp_4647_:
{
lean_object* v___x_4655_; double v___x_4656_; double v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4655_ = lean_io_get_num_heartbeats();
v___x_4656_ = lean_float_of_nat(v___y_4653_);
v___x_4657_ = lean_float_of_nat(v___x_4655_);
v___x_4658_ = lean_box_float(v___x_4656_);
v___x_4659_ = lean_box_float(v___x_4657_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4658_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v_a_4654_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
lean_inc_ref(v___y_4648_);
lean_inc(v___y_4651_);
v___x_4662_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4651_, v_safe_4587_, v___y_4648_, v___y_4652_, v___y_4649_, v___y_4650_, v___f_4624_, v___x_4661_, v___x_4627_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec_ref_known(v___x_4627_, 2);
v___y_4593_ = v___x_4662_;
goto v___jp_4592_;
}
v___jp_4663_:
{
lean_object* v___x_4669_; 
v___x_4669_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4573_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v___x_4669_, 1);
v___x_4671_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4672_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4668_, v___x_4671_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = lean_io_mono_nanos_now();
v___x_4674_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4666_, v___x_4627_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4674_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4674_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set_tag(v___x_4677_, 1);
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4675_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
v___y_4629_ = v___y_4664_;
v___y_4630_ = v___x_4673_;
v___y_4631_ = v___y_4665_;
v___y_4632_ = v_a_4670_;
v___y_4633_ = v___y_4667_;
v___y_4634_ = v___y_4668_;
v_a_4635_ = v___x_4680_;
goto v___jp_4628_;
}
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
v_a_4683_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4674_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4674_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
lean_ctor_set_tag(v___x_4685_, 0);
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
v___y_4629_ = v___y_4664_;
v___y_4630_ = v___x_4673_;
v___y_4631_ = v___y_4665_;
v___y_4632_ = v_a_4670_;
v___y_4633_ = v___y_4667_;
v___y_4634_ = v___y_4668_;
v_a_4635_ = v___x_4688_;
goto v___jp_4628_;
}
}
}
}
else
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = lean_io_get_num_heartbeats();
v___x_4692_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4666_, v___x_4627_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
lean_ctor_set_tag(v___x_4695_, 1);
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
v___y_4648_ = v___y_4664_;
v___y_4649_ = v___y_4665_;
v___y_4650_ = v_a_4670_;
v___y_4651_ = v___y_4667_;
v___y_4652_ = v___y_4668_;
v___y_4653_ = v___x_4691_;
v_a_4654_ = v___x_4698_;
goto v___jp_4647_;
}
}
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
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
lean_ctor_set_tag(v___x_4703_, 0);
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
v___y_4648_ = v___y_4664_;
v___y_4649_ = v___y_4665_;
v___y_4650_ = v_a_4670_;
v___y_4651_ = v___y_4667_;
v___y_4652_ = v___y_4668_;
v___y_4653_ = v___x_4691_;
v_a_4654_ = v___x_4706_;
goto v___jp_4647_;
}
}
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
lean_dec_ref(v___y_4666_);
lean_dec_ref_known(v___x_4627_, 2);
lean_dec_ref(v___f_4624_);
lean_dec(v_a_4591_);
lean_dec(v_a_4566_);
v_a_4709_ = lean_ctor_get(v___x_4669_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4669_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4669_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
v___jp_4717_:
{
if (lean_obj_tag(v_value_4584_) == 0)
{
lean_object* v_options_4718_; uint8_t v_hasTrace_4719_; 
v_options_4718_ = lean_ctor_get(v___y_4572_, 2);
v_hasTrace_4719_ = lean_ctor_get_uint8(v_options_4718_, sizeof(void*)*1);
if (v_hasTrace_4719_ == 0)
{
lean_object* v_code_4720_; lean_object* v___x_4721_; 
lean_dec_ref(v___f_4624_);
v_code_4720_ = lean_ctor_get(v_value_4584_, 0);
lean_inc_ref(v_code_4720_);
v___x_4721_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4720_, v___x_4627_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec_ref_known(v___x_4627_, 2);
v___y_4593_ = v___x_4721_;
goto v___jp_4592_;
}
else
{
lean_object* v_code_4722_; lean_object* v_inheritedTraceOptions_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; 
v_code_4722_ = lean_ctor_get(v_value_4584_, 0);
v_inheritedTraceOptions_4723_ = lean_ctor_get(v___y_4572_, 13);
v___x_4724_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4725_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4726_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4723_, v_options_4718_, v___x_4726_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4728_ = l_Lean_trace_profiler;
v___x_4729_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4718_, v___x_4728_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; 
lean_dec_ref(v___f_4624_);
lean_inc_ref(v_code_4722_);
v___x_4730_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4722_, v___x_4627_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec_ref_known(v___x_4627_, 2);
v___y_4593_ = v___x_4730_;
goto v___jp_4592_;
}
else
{
lean_inc_ref(v_code_4722_);
v___y_4664_ = v___x_4725_;
v___y_4665_ = v___x_4727_;
v___y_4666_ = v_code_4722_;
v___y_4667_ = v___x_4724_;
v___y_4668_ = v_options_4718_;
goto v___jp_4663_;
}
}
else
{
lean_inc_ref(v_code_4722_);
v___y_4664_ = v___x_4725_;
v___y_4665_ = v___x_4727_;
v___y_4666_ = v_code_4722_;
v___y_4667_ = v___x_4724_;
v___y_4668_ = v_options_4718_;
goto v___jp_4663_;
}
}
}
else
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
lean_dec_ref(v___f_4624_);
v___x_4731_ = lean_box(1);
v___x_4732_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4731_, v___x_4627_, v___y_4569_, v___y_4573_);
lean_dec_ref_known(v___x_4627_, 2);
v___y_4593_ = v___x_4732_;
goto v___jp_4592_;
}
}
v___jp_4733_:
{
if (lean_obj_tag(v___y_4734_) == 0)
{
lean_dec_ref_known(v___y_4734_, 1);
goto v___jp_4717_;
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_dec_ref_known(v___x_4627_, 2);
lean_dec_ref(v___f_4624_);
lean_dec(v_a_4591_);
lean_dec(v_a_4566_);
v_a_4735_ = lean_ctor_get(v___y_4734_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___y_4734_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___y_4734_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___y_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec(v_a_4566_);
v_a_4751_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4590_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4590_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
}
v___jp_4575_:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4577_ = lean_unsigned_to_nat(1u);
v___x_4578_ = lean_nat_add(v_a_4566_, v___x_4577_);
lean_dec(v_a_4566_);
lean_inc_ref(v_a_4576_);
v_a_4566_ = v___x_4578_;
v_b_4567_ = v_a_4576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4759_, lean_object* v___x_4760_, lean_object* v_a_4761_, lean_object* v_b_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4759_, v___x_4760_, v_a_4761_, v_b_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec_ref(v___x_4760_);
lean_dec(v_upperBound_4759_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_decls_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v_decls_4778_ = lean_ctor_get(v_a_4771_, 0);
v___x_4779_ = lean_array_get_size(v_decls_4778_);
v___x_4780_ = lean_unsigned_to_nat(0u);
v___x_4781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4779_, v_decls_4778_, v___x_4780_, v___x_4781_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4797_; 
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4785_ = v___x_4782_;
v_isShared_4786_ = v_isSharedCheck_4797_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4782_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4797_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v_fst_4787_; 
v_fst_4787_ = lean_ctor_get(v_a_4783_, 0);
lean_inc(v_fst_4787_);
lean_dec(v_a_4783_);
if (lean_obj_tag(v_fst_4787_) == 0)
{
uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4791_; 
v___x_4788_ = 0;
v___x_4789_ = lean_box(v___x_4788_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4789_);
v___x_4791_ = v___x_4785_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
else
{
lean_object* v_val_4793_; lean_object* v___x_4795_; 
v_val_4793_ = lean_ctor_get(v_fst_4787_, 0);
lean_inc(v_val_4793_);
lean_dec_ref_known(v_fst_4787_, 1);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v_val_4793_);
v___x_4795_ = v___x_4785_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_val_4793_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
v_a_4798_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4782_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4782_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_);
lean_dec(v_a_4811_);
lean_dec_ref(v_a_4810_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4814_, lean_object* v_x_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4815_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4824_, lean_object* v_x_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4824_, v_x_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4834_, lean_object* v___x_4835_, lean_object* v_inst_4836_, lean_object* v_R_4837_, lean_object* v_a_4838_, lean_object* v_b_4839_, lean_object* v_c_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4834_, v___x_4835_, v_a_4838_, v_b_4839_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4849_, lean_object* v___x_4850_, lean_object* v_inst_4851_, lean_object* v_R_4852_, lean_object* v_a_4853_, lean_object* v_b_4854_, lean_object* v_c_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4849_, v___x_4850_, v_inst_4851_, v_R_4852_, v_a_4853_, v_b_4854_, v_c_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec_ref(v___x_4850_);
lean_dec(v_upperBound_4849_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4864_, lean_object* v_data_4865_, lean_object* v_ref_4866_, lean_object* v_msg_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4864_, v_data_4865_, v_ref_4866_, v_msg_4867_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4876_, lean_object* v_data_4877_, lean_object* v_ref_4878_, lean_object* v_msg_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4876_, v_data_4877_, v_ref_4878_, v_msg_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
lean_dec(v___y_4885_);
lean_dec_ref(v___y_4884_);
lean_dec(v___y_4883_);
lean_dec_ref(v___y_4882_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4890_, lean_object* v_msg_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
lean_object* v_options_4897_; lean_object* v_ref_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; 
v_options_4897_ = lean_ctor_get(v___y_4894_, 2);
v_ref_4898_ = lean_ctor_get(v___y_4894_, 5);
v___x_4899_ = lean_st_ref_get(v___y_4895_);
v___x_4900_ = lean_st_ref_get(v___y_4893_);
v___x_4901_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4892_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4960_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4904_ = v___x_4901_;
v_isShared_4905_ = v_isSharedCheck_4960_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4960_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v_env_4906_; lean_object* v_lctx_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4958_; 
v_env_4906_ = lean_ctor_get(v___x_4899_, 0);
lean_inc_ref(v_env_4906_);
lean_dec(v___x_4899_);
v_lctx_4907_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4958_ == 0)
{
lean_object* v_unused_4959_; 
v_unused_4959_ = lean_ctor_get(v___x_4900_, 1);
lean_dec(v_unused_4959_);
v___x_4909_ = v___x_4900_;
v_isShared_4910_ = v_isSharedCheck_4958_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_lctx_4907_);
lean_dec(v___x_4900_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4958_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v_traceState_4913_; lean_object* v_env_4914_; lean_object* v_nextMacroScope_4915_; lean_object* v_ngen_4916_; lean_object* v_auxDeclNGen_4917_; lean_object* v_cache_4918_; lean_object* v_messages_4919_; lean_object* v_infoState_4920_; lean_object* v_snapshotTasks_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4957_; 
v___x_4911_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4912_ = lean_st_ref_take(v___y_4895_);
v_traceState_4913_ = lean_ctor_get(v___x_4912_, 4);
v_env_4914_ = lean_ctor_get(v___x_4912_, 0);
v_nextMacroScope_4915_ = lean_ctor_get(v___x_4912_, 1);
v_ngen_4916_ = lean_ctor_get(v___x_4912_, 2);
v_auxDeclNGen_4917_ = lean_ctor_get(v___x_4912_, 3);
v_cache_4918_ = lean_ctor_get(v___x_4912_, 5);
v_messages_4919_ = lean_ctor_get(v___x_4912_, 6);
v_infoState_4920_ = lean_ctor_get(v___x_4912_, 7);
v_snapshotTasks_4921_ = lean_ctor_get(v___x_4912_, 8);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4923_ = v___x_4912_;
v_isShared_4924_ = v_isSharedCheck_4957_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_snapshotTasks_4921_);
lean_inc(v_infoState_4920_);
lean_inc(v_messages_4919_);
lean_inc(v_cache_4918_);
lean_inc(v_traceState_4913_);
lean_inc(v_auxDeclNGen_4917_);
lean_inc(v_ngen_4916_);
lean_inc(v_nextMacroScope_4915_);
lean_inc(v_env_4914_);
lean_dec(v___x_4912_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4957_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
uint64_t v_tid_4925_; lean_object* v_traces_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4956_; 
v_tid_4925_ = lean_ctor_get_uint64(v_traceState_4913_, sizeof(void*)*1);
v_traces_4926_ = lean_ctor_get(v_traceState_4913_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v_traceState_4913_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4928_ = v_traceState_4913_;
v_isShared_4929_ = v_isSharedCheck_4956_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_traces_4926_);
lean_dec(v_traceState_4913_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4956_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
uint8_t v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4934_; 
v___x_4930_ = lean_unbox(v_a_4902_);
lean_dec(v_a_4902_);
v___x_4931_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4907_, v___x_4930_);
lean_dec_ref(v_lctx_4907_);
lean_inc_ref(v_options_4897_);
v___x_4932_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4932_, 0, v_env_4906_);
lean_ctor_set(v___x_4932_, 1, v___x_4911_);
lean_ctor_set(v___x_4932_, 2, v___x_4931_);
lean_ctor_set(v___x_4932_, 3, v_options_4897_);
if (v_isShared_4910_ == 0)
{
lean_ctor_set_tag(v___x_4909_, 3);
lean_ctor_set(v___x_4909_, 1, v_msg_4891_);
lean_ctor_set(v___x_4909_, 0, v___x_4932_);
v___x_4934_ = v___x_4909_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4932_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v_msg_4891_);
v___x_4934_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
lean_object* v___x_4935_; double v___x_4936_; uint8_t v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4945_; 
v___x_4935_ = lean_box(0);
v___x_4936_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4937_ = 0;
v___x_4938_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4939_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4939_, 0, v_cls_4890_);
lean_ctor_set(v___x_4939_, 1, v___x_4935_);
lean_ctor_set(v___x_4939_, 2, v___x_4938_);
lean_ctor_set_float(v___x_4939_, sizeof(void*)*3, v___x_4936_);
lean_ctor_set_float(v___x_4939_, sizeof(void*)*3 + 8, v___x_4936_);
lean_ctor_set_uint8(v___x_4939_, sizeof(void*)*3 + 16, v___x_4937_);
v___x_4940_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4941_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4939_);
lean_ctor_set(v___x_4941_, 1, v___x_4934_);
lean_ctor_set(v___x_4941_, 2, v___x_4940_);
lean_inc(v_ref_4898_);
v___x_4942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4942_, 0, v_ref_4898_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = l_Lean_PersistentArray_push___redArg(v_traces_4926_, v___x_4942_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4943_);
v___x_4945_ = v___x_4928_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4943_);
lean_ctor_set_uint64(v_reuseFailAlloc_4954_, sizeof(void*)*1, v_tid_4925_);
v___x_4945_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
lean_object* v___x_4947_; 
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 4, v___x_4945_);
v___x_4947_ = v___x_4923_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_env_4914_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v_nextMacroScope_4915_);
lean_ctor_set(v_reuseFailAlloc_4953_, 2, v_ngen_4916_);
lean_ctor_set(v_reuseFailAlloc_4953_, 3, v_auxDeclNGen_4917_);
lean_ctor_set(v_reuseFailAlloc_4953_, 4, v___x_4945_);
lean_ctor_set(v_reuseFailAlloc_4953_, 5, v_cache_4918_);
lean_ctor_set(v_reuseFailAlloc_4953_, 6, v_messages_4919_);
lean_ctor_set(v_reuseFailAlloc_4953_, 7, v_infoState_4920_);
lean_ctor_set(v_reuseFailAlloc_4953_, 8, v_snapshotTasks_4921_);
v___x_4947_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4951_; 
v___x_4948_ = lean_st_ref_set(v___y_4895_, v___x_4947_);
v___x_4949_ = lean_box(0);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 0, v___x_4949_);
v___x_4951_ = v___x_4904_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4949_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
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
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
lean_dec(v___x_4900_);
lean_dec(v___x_4899_);
lean_dec_ref(v_msg_4891_);
lean_dec(v_cls_4890_);
v_a_4961_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4901_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4901_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4969_, lean_object* v_msg_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4969_, v_msg_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4977_, lean_object* v_msg_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4977_, v_msg_4978_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4987_, lean_object* v_msg_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4987_, v_msg_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
return v_res_4996_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4997_ = lean_box(0);
v___x_4998_ = lean_unsigned_to_nat(16u);
v___x_4999_ = lean_mk_array(v___x_4998_, v___x_4997_);
return v___x_4999_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5000_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_5001_ = lean_unsigned_to_nat(0u);
v___x_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5001_);
lean_ctor_set(v___x_5002_, 1, v___x_5000_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_5003_, size_t v_i_5004_, lean_object* v_bs_5005_){
_start:
{
uint8_t v___x_5006_; 
v___x_5006_ = lean_usize_dec_lt(v_i_5004_, v_sz_5003_);
if (v___x_5006_ == 0)
{
return v_bs_5005_;
}
else
{
lean_object* v___x_5007_; lean_object* v_bs_x27_5008_; lean_object* v___x_5009_; size_t v___x_5010_; size_t v___x_5011_; lean_object* v___x_5012_; 
v___x_5007_ = lean_unsigned_to_nat(0u);
v_bs_x27_5008_ = lean_array_uset(v_bs_5005_, v_i_5004_, v___x_5007_);
v___x_5009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5010_ = ((size_t)1ULL);
v___x_5011_ = lean_usize_add(v_i_5004_, v___x_5010_);
v___x_5012_ = lean_array_uset(v_bs_x27_5008_, v_i_5004_, v___x_5009_);
v_i_5004_ = v___x_5011_;
v_bs_5005_ = v___x_5012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_5014_, lean_object* v_i_5015_, lean_object* v_bs_5016_){
_start:
{
size_t v_sz_boxed_5017_; size_t v_i_boxed_5018_; lean_object* v_res_5019_; 
v_sz_boxed_5017_ = lean_unbox_usize(v_sz_5014_);
lean_dec(v_sz_5014_);
v_i_boxed_5018_ = lean_unbox_usize(v_i_5015_);
lean_dec(v_i_5015_);
v_res_5019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_5017_, v_i_boxed_5018_, v_bs_5016_);
return v_res_5019_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5022_ = l_Lean_stringToMessageData(v___x_5021_);
return v___x_5022_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5024_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5025_ = l_Lean_stringToMessageData(v___x_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_){
_start:
{
lean_object* v___x_5037_; lean_object* v_decls_5038_; lean_object* v_funVals_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5078_; 
v___x_5037_ = lean_st_ref_take(v_a_5028_);
v_decls_5038_ = lean_ctor_get(v_a_5027_, 0);
v_funVals_5039_ = lean_ctor_get(v___x_5037_, 1);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5078_ == 0)
{
lean_object* v_unused_5079_; 
v_unused_5079_ = lean_ctor_get(v___x_5037_, 0);
lean_dec(v_unused_5079_);
v___x_5041_ = v___x_5037_;
v_isShared_5042_ = v_isSharedCheck_5078_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_funVals_5039_);
lean_dec(v___x_5037_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5078_;
goto v_resetjp_5040_;
}
v___jp_5034_:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5035_ = lean_box(0);
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
return v___x_5036_;
}
v_resetjp_5040_:
{
size_t v_sz_5043_; size_t v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5047_; 
v_sz_5043_ = lean_array_size(v_decls_5038_);
v___x_5044_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5038_);
v___x_5045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5043_, v___x_5044_, v_decls_5038_);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5045_);
v___x_5047_ = v___x_5041_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5045_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v_funVals_5039_);
v___x_5047_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5048_ = lean_st_ref_set(v_a_5028_, v___x_5047_);
v___x_5049_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; uint8_t v___x_5051_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5051_ = lean_unbox(v_a_5050_);
lean_dec(v_a_5050_);
if (v___x_5051_ == 0)
{
lean_object* v_options_5052_; uint8_t v_hasTrace_5053_; 
v_options_5052_ = lean_ctor_get(v_a_5031_, 2);
v_hasTrace_5053_ = lean_ctor_get_uint8(v_options_5052_, sizeof(void*)*1);
if (v_hasTrace_5053_ == 0)
{
lean_dec(v_n_5026_);
goto v___jp_5034_;
}
else
{
lean_object* v_inheritedTraceOptions_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; uint8_t v___x_5057_; 
v_inheritedTraceOptions_5054_ = lean_ctor_get(v_a_5031_, 13);
v___x_5055_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5056_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5054_, v_options_5052_, v___x_5056_);
if (v___x_5057_ == 0)
{
lean_dec(v_n_5026_);
goto v___jp_5034_;
}
else
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5058_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5059_ = l_Nat_reprFast(v_n_5026_);
v___x_5060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5059_);
v___x_5061_ = l_Lean_MessageData_ofFormat(v___x_5060_);
v___x_5062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5058_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
v___x_5063_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5062_);
lean_ctor_set(v___x_5064_, 1, v___x_5063_);
v___x_5065_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5055_, v___x_5064_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_dec_ref_known(v___x_5065_, 1);
goto v___jp_5034_;
}
else
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5066_ = lean_unsigned_to_nat(1u);
v___x_5067_ = lean_nat_add(v_n_5026_, v___x_5066_);
lean_dec(v_n_5026_);
v_n_5026_ = v___x_5067_;
goto _start;
}
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_dec(v_n_5026_);
v_a_5069_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5049_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5049_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_);
lean_dec(v_a_5086_);
lean_dec_ref(v_a_5085_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec(v_a_5082_);
lean_dec_ref(v_a_5081_);
return v_res_5088_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5089_; lean_object* v___x_5090_; 
v___x_5089_ = 0;
v___x_5090_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5089_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5091_){
_start:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5092_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5093_ = lean_panic_fn_borrowed(v___x_5092_, v_msg_5091_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5094_, lean_object* v_msg_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_){
_start:
{
lean_object* v_options_5101_; lean_object* v_ref_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v_options_5101_ = lean_ctor_get(v___y_5098_, 2);
v_ref_5102_ = lean_ctor_get(v___y_5098_, 5);
v___x_5103_ = lean_st_ref_get(v___y_5099_);
v___x_5104_ = lean_st_ref_get(v___y_5097_);
v___x_5105_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5096_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5164_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5108_ = v___x_5105_;
v_isShared_5109_ = v_isSharedCheck_5164_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5105_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5164_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v_env_5110_; lean_object* v_lctx_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5162_; 
v_env_5110_ = lean_ctor_get(v___x_5103_, 0);
lean_inc_ref(v_env_5110_);
lean_dec(v___x_5103_);
v_lctx_5111_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5162_ == 0)
{
lean_object* v_unused_5163_; 
v_unused_5163_ = lean_ctor_get(v___x_5104_, 1);
lean_dec(v_unused_5163_);
v___x_5113_ = v___x_5104_;
v_isShared_5114_ = v_isSharedCheck_5162_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_lctx_5111_);
lean_dec(v___x_5104_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5162_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v_traceState_5117_; lean_object* v_env_5118_; lean_object* v_nextMacroScope_5119_; lean_object* v_ngen_5120_; lean_object* v_auxDeclNGen_5121_; lean_object* v_cache_5122_; lean_object* v_messages_5123_; lean_object* v_infoState_5124_; lean_object* v_snapshotTasks_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5161_; 
v___x_5115_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_5116_ = lean_st_ref_take(v___y_5099_);
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
v___x_5134_ = lean_unbox(v_a_5106_);
lean_dec(v_a_5106_);
v___x_5135_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5111_, v___x_5134_);
lean_dec_ref(v_lctx_5111_);
lean_inc_ref(v_options_5101_);
v___x_5136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5136_, 0, v_env_5110_);
lean_ctor_set(v___x_5136_, 1, v___x_5115_);
lean_ctor_set(v___x_5136_, 2, v___x_5135_);
lean_ctor_set(v___x_5136_, 3, v_options_5101_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set_tag(v___x_5113_, 3);
lean_ctor_set(v___x_5113_, 1, v_msg_5095_);
lean_ctor_set(v___x_5113_, 0, v___x_5136_);
v___x_5138_ = v___x_5113_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5159_, 1, v_msg_5095_);
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
lean_ctor_set(v___x_5143_, 0, v_cls_5094_);
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
lean_inc(v_ref_5102_);
v___x_5146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5146_, 0, v_ref_5102_);
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
v___x_5152_ = lean_st_ref_set(v___y_5099_, v___x_5151_);
v___x_5153_ = lean_box(0);
if (v_isShared_5109_ == 0)
{
lean_ctor_set(v___x_5108_, 0, v___x_5153_);
v___x_5155_ = v___x_5108_;
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
lean_dec(v___x_5104_);
lean_dec(v___x_5103_);
lean_dec_ref(v_msg_5095_);
lean_dec(v_cls_5094_);
v_a_5165_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5105_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5105_);
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
lean_object* v_options_5393_; uint8_t v_hasTrace_5394_; 
v_options_5393_ = lean_ctor_get(v___y_5350_, 2);
v_hasTrace_5394_ = lean_ctor_get_uint8(v_options_5393_, sizeof(void*)*1);
if (v_hasTrace_5394_ == 0)
{
v___y_5388_ = v___y_5349_;
goto v___jp_5387_;
}
else
{
lean_object* v_inheritedTraceOptions_5395_; lean_object* v_cls_5396_; lean_object* v___x_5397_; uint8_t v___x_5398_; 
v_inheritedTraceOptions_5395_ = lean_ctor_get(v___y_5350_, 13);
v_cls_5396_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5397_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5398_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5395_, v_options_5393_, v___x_5397_);
if (v___x_5398_ == 0)
{
v___y_5388_ = v___y_5349_;
goto v___jp_5387_;
}
else
{
lean_object* v___x_5399_; 
lean_inc(v_discr_5344_);
v___x_5399_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5344_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v_a_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_a_5400_);
lean_dec_ref_known(v___x_5399_, 1);
v___x_5401_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5402_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5400_, v___x_5398_);
v___x_5403_ = lean_string_append(v___x_5401_, v___x_5402_);
lean_dec_ref(v___x_5402_);
v___x_5404_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5405_ = lean_string_append(v___x_5403_, v___x_5404_);
lean_inc(v_ctorName_5369_);
v___x_5406_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5369_, v___x_5398_);
v___x_5407_ = lean_string_append(v___x_5405_, v___x_5406_);
lean_dec_ref(v___x_5406_);
v___x_5408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5407_);
v___x_5409_ = l_Lean_MessageData_ofFormat(v___x_5408_);
v___x_5410_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5396_, v___x_5409_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5410_) == 0)
{
lean_dec_ref_known(v___x_5410_, 1);
v___y_5388_ = v___y_5349_;
goto v___jp_5387_;
}
else
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5418_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5413_ = v___x_5410_;
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5410_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5416_; 
if (v_isShared_5414_ == 0)
{
v___x_5416_ = v___x_5413_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_a_5411_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
}
}
else
{
lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5419_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5421_ = v___x_5399_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_dec(v___x_5399_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5424_; 
if (v_isShared_5422_ == 0)
{
v___x_5424_ = v___x_5421_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5419_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
}
}
else
{
lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5427_ = lean_unsigned_to_nat(0u);
v___x_5428_ = lean_array_get_size(v_params_5370_);
v___x_5429_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5345_, v_params_5370_, v___x_5427_, v___x_5428_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5443_; uint8_t v___x_5444_; lean_object* v_fst_5446_; lean_object* v_snd_5447_; lean_object* v___y_5460_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
lean_inc(v_a_5430_);
lean_dec_ref_known(v___x_5429_, 1);
v___x_5443_ = lean_array_get_size(v_a_5430_);
v___x_5444_ = lean_nat_dec_eq(v___x_5443_, v___x_5427_);
if (v___x_5444_ == 0)
{
if (v___x_5392_ == 0)
{
lean_dec(v_a_5430_);
goto v___jp_5431_;
}
else
{
lean_object* v___x_5472_; 
lean_inc_ref(v_code_5371_);
v___x_5472_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5345_, v_code_5371_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v_a_5473_; lean_object* v___x_5474_; uint8_t v___x_5475_; 
v_a_5473_ = lean_ctor_get(v___x_5472_, 0);
lean_inc(v_a_5473_);
lean_dec_ref_known(v___x_5472_, 1);
v___x_5474_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5475_ = lean_nat_dec_lt(v___x_5427_, v___x_5443_);
if (v___x_5475_ == 0)
{
lean_dec(v_a_5430_);
v_fst_5446_ = v_a_5473_;
v_snd_5447_ = v___x_5474_;
goto v___jp_5445_;
}
else
{
lean_object* v___x_5476_; uint8_t v___x_5477_; 
lean_inc(v_a_5473_);
v___x_5476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5476_, 0, v_a_5473_);
lean_ctor_set(v___x_5476_, 1, v___x_5474_);
v___x_5477_ = lean_nat_dec_le(v___x_5443_, v___x_5443_);
if (v___x_5477_ == 0)
{
if (v___x_5475_ == 0)
{
lean_dec_ref_known(v___x_5476_, 2);
lean_dec(v_a_5430_);
v_fst_5446_ = v_a_5473_;
v_snd_5447_ = v___x_5474_;
goto v___jp_5445_;
}
else
{
size_t v___x_5478_; size_t v___x_5479_; lean_object* v___x_5480_; 
lean_dec(v_a_5473_);
v___x_5478_ = ((size_t)0ULL);
v___x_5479_ = lean_usize_of_nat(v___x_5443_);
v___x_5480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5430_, v___x_5478_, v___x_5479_, v___x_5476_);
lean_dec(v_a_5430_);
v___y_5460_ = v___x_5480_;
goto v___jp_5459_;
}
}
else
{
size_t v___x_5481_; size_t v___x_5482_; lean_object* v___x_5483_; 
lean_dec(v_a_5473_);
v___x_5481_ = ((size_t)0ULL);
v___x_5482_ = lean_usize_of_nat(v___x_5443_);
v___x_5483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5430_, v___x_5481_, v___x_5482_, v___x_5476_);
lean_dec(v_a_5430_);
v___y_5460_ = v___x_5483_;
goto v___jp_5459_;
}
}
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5491_; 
lean_dec(v_a_5430_);
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5484_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5486_ = v___x_5472_;
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5472_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_a_5484_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
}
else
{
lean_dec(v_a_5430_);
goto v___jp_5431_;
}
v___jp_5431_:
{
lean_object* v___x_5432_; 
lean_inc_ref(v_code_5371_);
v___x_5432_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5345_, v_code_5371_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5434_; 
v_a_5433_ = lean_ctor_get(v___x_5432_, 0);
lean_inc(v_a_5433_);
lean_dec_ref_known(v___x_5432_, 1);
lean_inc_ref(v_a_5356_);
v___x_5434_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5356_, v_a_5433_);
v_a_5358_ = v___x_5434_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5442_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5435_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5437_ = v___x_5432_;
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___x_5432_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v___x_5440_; 
if (v_isShared_5438_ == 0)
{
v___x_5440_ = v___x_5437_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_a_5435_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
v___jp_5445_:
{
lean_object* v___x_5448_; 
v___x_5448_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5372_, v_fst_5446_, v_snd_5447_, v___x_5444_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
lean_dec_ref(v_snd_5447_);
if (lean_obj_tag(v___x_5448_) == 0)
{
lean_object* v_a_5449_; lean_object* v___x_5450_; 
v_a_5449_ = lean_ctor_get(v___x_5448_, 0);
lean_inc(v_a_5449_);
lean_dec_ref_known(v___x_5448_, 1);
lean_inc_ref(v_a_5356_);
v___x_5450_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5356_, v_a_5449_);
v_a_5358_ = v___x_5450_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5451_ = lean_ctor_get(v___x_5448_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5448_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5448_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5448_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5454_ == 0)
{
v___x_5456_ = v___x_5453_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
v___jp_5459_:
{
if (lean_obj_tag(v___y_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v_fst_5462_; lean_object* v_snd_5463_; 
v_a_5461_ = lean_ctor_get(v___y_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref_known(v___y_5460_, 1);
v_fst_5462_ = lean_ctor_get(v_a_5461_, 0);
lean_inc(v_fst_5462_);
v_snd_5463_ = lean_ctor_get(v_a_5461_, 1);
lean_inc(v_snd_5463_);
lean_dec(v_a_5461_);
v_fst_5446_ = v_fst_5462_;
v_snd_5447_ = v_snd_5463_;
goto v___jp_5445_;
}
else
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5464_ = lean_ctor_get(v___y_5460_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___y_5460_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___y_5460_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___y_5460_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5469_; 
if (v_isShared_5467_ == 0)
{
v___x_5469_ = v___x_5466_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
}
else
{
lean_object* v_a_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5499_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5492_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5494_ = v___x_5429_;
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_a_5492_);
lean_dec(v___x_5429_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v___x_5497_; 
if (v_isShared_5495_ == 0)
{
v___x_5497_ = v___x_5494_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_a_5492_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
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
lean_object* v_code_5500_; lean_object* v___x_5501_; 
v_code_5500_ = lean_ctor_get(v_a_5356_, 0);
lean_inc_ref(v_code_5500_);
v___x_5501_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5345_, v_code_5500_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5501_) == 0)
{
lean_object* v_a_5502_; lean_object* v___x_5503_; 
v_a_5502_ = lean_ctor_get(v___x_5501_, 0);
lean_inc(v_a_5502_);
lean_dec_ref_known(v___x_5501_, 1);
lean_inc_ref(v_a_5356_);
v___x_5503_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5356_, v_a_5502_);
v_a_5358_ = v___x_5503_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec_ref(v_as_5347_);
lean_dec(v_i_5346_);
lean_dec(v_discr_5344_);
lean_dec_ref(v_resultType_5342_);
v_a_5504_ = lean_ctor_get(v___x_5501_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5501_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___x_5501_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5501_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5512_, lean_object* v_code_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_){
_start:
{
lean_object* v___y_5520_; lean_object* v___y_5521_; uint8_t v___y_5522_; lean_object* v___y_5527_; lean_object* v___y_5528_; uint8_t v___y_5529_; lean_object* v_decl_5534_; lean_object* v_k_5535_; lean_object* v___y_5536_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v___y_5539_; 
switch(lean_obj_tag(v_code_5513_))
{
case 0:
{
lean_object* v_decl_5585_; lean_object* v_k_5586_; lean_object* v___x_5587_; 
v_decl_5585_ = lean_ctor_get(v_code_5513_, 0);
v_k_5586_ = lean_ctor_get(v_code_5513_, 1);
lean_inc_ref(v_k_5586_);
v___x_5587_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5512_, v_k_5586_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
if (lean_obj_tag(v___x_5587_) == 0)
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5614_; 
v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5587_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5590_ = v___x_5587_;
v_isShared_5591_ = v_isSharedCheck_5614_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5587_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5614_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
uint8_t v___y_5593_; size_t v___x_5609_; size_t v___x_5610_; uint8_t v___x_5611_; 
v___x_5609_ = lean_ptr_addr(v_k_5586_);
v___x_5610_ = lean_ptr_addr(v_a_5588_);
v___x_5611_ = lean_usize_dec_eq(v___x_5609_, v___x_5610_);
if (v___x_5611_ == 0)
{
v___y_5593_ = v___x_5611_;
goto v___jp_5592_;
}
else
{
size_t v___x_5612_; uint8_t v___x_5613_; 
v___x_5612_ = lean_ptr_addr(v_decl_5585_);
v___x_5613_ = lean_usize_dec_eq(v___x_5612_, v___x_5612_);
v___y_5593_ = v___x_5613_;
goto v___jp_5592_;
}
v___jp_5592_:
{
if (v___y_5593_ == 0)
{
lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5603_; 
lean_inc_ref(v_decl_5585_);
v_isSharedCheck_5603_ = !lean_is_exclusive(v_code_5513_);
if (v_isSharedCheck_5603_ == 0)
{
lean_object* v_unused_5604_; lean_object* v_unused_5605_; 
v_unused_5604_ = lean_ctor_get(v_code_5513_, 1);
lean_dec(v_unused_5604_);
v_unused_5605_ = lean_ctor_get(v_code_5513_, 0);
lean_dec(v_unused_5605_);
v___x_5595_ = v_code_5513_;
v_isShared_5596_ = v_isSharedCheck_5603_;
goto v_resetjp_5594_;
}
else
{
lean_dec(v_code_5513_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5603_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 1, v_a_5588_);
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_decl_5585_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v_a_5588_);
v___x_5598_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5600_; 
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 0, v___x_5598_);
v___x_5600_ = v___x_5590_;
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
lean_dec(v_a_5588_);
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 0, v_code_5513_);
v___x_5607_ = v___x_5590_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_code_5513_);
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
else
{
lean_dec_ref_known(v_code_5513_, 2);
return v___x_5587_;
}
}
case 1:
{
lean_object* v_decl_5615_; lean_object* v_k_5616_; 
v_decl_5615_ = lean_ctor_get(v_code_5513_, 0);
v_k_5616_ = lean_ctor_get(v_code_5513_, 1);
lean_inc_ref(v_k_5616_);
lean_inc_ref(v_decl_5615_);
v_decl_5534_ = v_decl_5615_;
v_k_5535_ = v_k_5616_;
v___y_5536_ = v_a_5514_;
v___y_5537_ = v_a_5515_;
v___y_5538_ = v_a_5516_;
v___y_5539_ = v_a_5517_;
goto v___jp_5533_;
}
case 2:
{
lean_object* v_decl_5617_; lean_object* v_k_5618_; 
v_decl_5617_ = lean_ctor_get(v_code_5513_, 0);
v_k_5618_ = lean_ctor_get(v_code_5513_, 1);
lean_inc_ref(v_k_5618_);
lean_inc_ref(v_decl_5617_);
v_decl_5534_ = v_decl_5617_;
v_k_5535_ = v_k_5618_;
v___y_5536_ = v_a_5514_;
v___y_5537_ = v_a_5515_;
v___y_5538_ = v_a_5516_;
v___y_5539_ = v_a_5517_;
goto v___jp_5533_;
}
case 4:
{
lean_object* v_cases_5619_; lean_object* v_typeName_5620_; lean_object* v_resultType_5621_; lean_object* v_discr_5622_; lean_object* v_alts_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5664_; 
v_cases_5619_ = lean_ctor_get(v_code_5513_, 0);
lean_inc_ref(v_cases_5619_);
v_typeName_5620_ = lean_ctor_get(v_cases_5619_, 0);
v_resultType_5621_ = lean_ctor_get(v_cases_5619_, 1);
v_discr_5622_ = lean_ctor_get(v_cases_5619_, 2);
v_alts_5623_ = lean_ctor_get(v_cases_5619_, 3);
v_isSharedCheck_5664_ = !lean_is_exclusive(v_cases_5619_);
if (v_isSharedCheck_5664_ == 0)
{
v___x_5625_ = v_cases_5619_;
v_isShared_5626_ = v_isSharedCheck_5664_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_alts_5623_);
lean_inc(v_discr_5622_);
lean_inc(v_resultType_5621_);
lean_inc(v_typeName_5620_);
lean_dec(v_cases_5619_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5664_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5627_; lean_object* v_discrVal_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5627_ = lean_box(0);
v_discrVal_5628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5512_, v_discr_5622_, v___x_5627_);
v___x_5629_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5623_);
lean_inc(v_discr_5622_);
lean_inc_ref(v_resultType_5621_);
v___x_5630_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5621_, v_discrVal_5628_, v_discr_5622_, v_assignment_5512_, v___x_5629_, v_alts_5623_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
lean_dec(v_discrVal_5628_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v_a_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5655_; 
v_a_5631_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5655_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5655_ == 0)
{
v___x_5633_ = v___x_5630_;
v_isShared_5634_ = v_isSharedCheck_5655_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_a_5631_);
lean_dec(v___x_5630_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5655_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
size_t v___x_5635_; size_t v___x_5636_; uint8_t v___x_5637_; 
v___x_5635_ = lean_ptr_addr(v_alts_5623_);
lean_dec_ref(v_alts_5623_);
v___x_5636_ = lean_ptr_addr(v_a_5631_);
v___x_5637_ = lean_usize_dec_eq(v___x_5635_, v___x_5636_);
if (v___x_5637_ == 0)
{
lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5650_; 
v_isSharedCheck_5650_ = !lean_is_exclusive(v_code_5513_);
if (v_isSharedCheck_5650_ == 0)
{
lean_object* v_unused_5651_; 
v_unused_5651_ = lean_ctor_get(v_code_5513_, 0);
lean_dec(v_unused_5651_);
v___x_5639_ = v_code_5513_;
v_isShared_5640_ = v_isSharedCheck_5650_;
goto v_resetjp_5638_;
}
else
{
lean_dec(v_code_5513_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5650_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 3, v_a_5631_);
v___x_5642_ = v___x_5625_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_typeName_5620_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v_resultType_5621_);
lean_ctor_set(v_reuseFailAlloc_5649_, 2, v_discr_5622_);
lean_ctor_set(v_reuseFailAlloc_5649_, 3, v_a_5631_);
v___x_5642_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
lean_object* v___x_5644_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 0, v___x_5642_);
v___x_5644_ = v___x_5639_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v___x_5642_);
v___x_5644_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
lean_object* v___x_5646_; 
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v___x_5644_);
v___x_5646_ = v___x_5633_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v___x_5644_);
v___x_5646_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
return v___x_5646_;
}
}
}
}
}
else
{
lean_object* v___x_5653_; 
lean_dec(v_a_5631_);
lean_del_object(v___x_5625_);
lean_dec(v_discr_5622_);
lean_dec_ref(v_resultType_5621_);
lean_dec(v_typeName_5620_);
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v_code_5513_);
v___x_5653_ = v___x_5633_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_code_5513_);
v___x_5653_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
return v___x_5653_;
}
}
}
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
lean_del_object(v___x_5625_);
lean_dec_ref(v_alts_5623_);
lean_dec(v_discr_5622_);
lean_dec_ref(v_resultType_5621_);
lean_dec(v_typeName_5620_);
lean_dec_ref_known(v_code_5513_, 1);
v_a_5656_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5630_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5630_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
}
default: 
{
lean_object* v___x_5665_; 
v___x_5665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5665_, 0, v_code_5513_);
return v___x_5665_;
}
}
v___jp_5519_:
{
if (v___y_5522_ == 0)
{
lean_object* v___x_5523_; lean_object* v___x_5524_; 
lean_dec_ref(v_code_5513_);
v___x_5523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5523_, 0, v___y_5520_);
lean_ctor_set(v___x_5523_, 1, v___y_5521_);
v___x_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
return v___x_5524_;
}
else
{
lean_object* v___x_5525_; 
lean_dec_ref(v___y_5521_);
lean_dec_ref(v___y_5520_);
v___x_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5525_, 0, v_code_5513_);
return v___x_5525_;
}
}
v___jp_5526_:
{
if (v___y_5529_ == 0)
{
lean_object* v___x_5530_; lean_object* v___x_5531_; 
lean_dec_ref(v_code_5513_);
v___x_5530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5530_, 0, v___y_5527_);
lean_ctor_set(v___x_5530_, 1, v___y_5528_);
v___x_5531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5530_);
return v___x_5531_;
}
else
{
lean_object* v___x_5532_; 
lean_dec_ref(v___y_5528_);
lean_dec_ref(v___y_5527_);
v___x_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5532_, 0, v_code_5513_);
return v___x_5532_;
}
}
v___jp_5533_:
{
lean_object* v_params_5540_; lean_object* v_type_5541_; lean_object* v_value_5542_; lean_object* v___x_5543_; 
v_params_5540_ = lean_ctor_get(v_decl_5534_, 2);
lean_inc_ref(v_params_5540_);
v_type_5541_ = lean_ctor_get(v_decl_5534_, 3);
lean_inc_ref(v_type_5541_);
v_value_5542_ = lean_ctor_get(v_decl_5534_, 4);
lean_inc_ref(v_value_5542_);
v___x_5543_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5512_, v_value_5542_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_);
if (lean_obj_tag(v___x_5543_) == 0)
{
lean_object* v_a_5544_; uint8_t v___x_5545_; lean_object* v___x_5546_; 
v_a_5544_ = lean_ctor_get(v___x_5543_, 0);
lean_inc(v_a_5544_);
lean_dec_ref_known(v___x_5543_, 1);
v___x_5545_ = 0;
v___x_5546_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5545_, v_decl_5534_, v_type_5541_, v_params_5540_, v_a_5544_, v___y_5537_);
if (lean_obj_tag(v___x_5546_) == 0)
{
lean_object* v_a_5547_; lean_object* v___x_5548_; 
v_a_5547_ = lean_ctor_get(v___x_5546_, 0);
lean_inc(v_a_5547_);
lean_dec_ref_known(v___x_5546_, 1);
v___x_5548_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5512_, v_k_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_);
if (lean_obj_tag(v___x_5548_) == 0)
{
switch(lean_obj_tag(v_code_5513_))
{
case 1:
{
lean_object* v_a_5549_; lean_object* v_decl_5550_; lean_object* v_k_5551_; size_t v___x_5552_; size_t v___x_5553_; uint8_t v___x_5554_; 
v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
lean_inc(v_a_5549_);
lean_dec_ref_known(v___x_5548_, 1);
v_decl_5550_ = lean_ctor_get(v_code_5513_, 0);
v_k_5551_ = lean_ctor_get(v_code_5513_, 1);
v___x_5552_ = lean_ptr_addr(v_k_5551_);
v___x_5553_ = lean_ptr_addr(v_a_5549_);
v___x_5554_ = lean_usize_dec_eq(v___x_5552_, v___x_5553_);
if (v___x_5554_ == 0)
{
v___y_5520_ = v_a_5547_;
v___y_5521_ = v_a_5549_;
v___y_5522_ = v___x_5554_;
goto v___jp_5519_;
}
else
{
size_t v___x_5555_; size_t v___x_5556_; uint8_t v___x_5557_; 
v___x_5555_ = lean_ptr_addr(v_decl_5550_);
v___x_5556_ = lean_ptr_addr(v_a_5547_);
v___x_5557_ = lean_usize_dec_eq(v___x_5555_, v___x_5556_);
v___y_5520_ = v_a_5547_;
v___y_5521_ = v_a_5549_;
v___y_5522_ = v___x_5557_;
goto v___jp_5519_;
}
}
case 2:
{
lean_object* v_a_5558_; lean_object* v_decl_5559_; lean_object* v_k_5560_; size_t v___x_5561_; size_t v___x_5562_; uint8_t v___x_5563_; 
v_a_5558_ = lean_ctor_get(v___x_5548_, 0);
lean_inc(v_a_5558_);
lean_dec_ref_known(v___x_5548_, 1);
v_decl_5559_ = lean_ctor_get(v_code_5513_, 0);
v_k_5560_ = lean_ctor_get(v_code_5513_, 1);
v___x_5561_ = lean_ptr_addr(v_k_5560_);
v___x_5562_ = lean_ptr_addr(v_a_5558_);
v___x_5563_ = lean_usize_dec_eq(v___x_5561_, v___x_5562_);
if (v___x_5563_ == 0)
{
v___y_5527_ = v_a_5547_;
v___y_5528_ = v_a_5558_;
v___y_5529_ = v___x_5563_;
goto v___jp_5526_;
}
else
{
size_t v___x_5564_; size_t v___x_5565_; uint8_t v___x_5566_; 
v___x_5564_ = lean_ptr_addr(v_decl_5559_);
v___x_5565_ = lean_ptr_addr(v_a_5547_);
v___x_5566_ = lean_usize_dec_eq(v___x_5564_, v___x_5565_);
v___y_5527_ = v_a_5547_;
v___y_5528_ = v_a_5558_;
v___y_5529_ = v___x_5566_;
goto v___jp_5526_;
}
}
default: 
{
lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5575_; 
lean_dec(v_a_5547_);
lean_dec_ref(v_code_5513_);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5548_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v___x_5548_, 0);
lean_dec(v_unused_5576_);
v___x_5568_ = v___x_5548_;
v_isShared_5569_ = v_isSharedCheck_5575_;
goto v_resetjp_5567_;
}
else
{
lean_dec(v___x_5548_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5575_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5573_; 
v___x_5570_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5571_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5570_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 0, v___x_5571_);
v___x_5573_ = v___x_5568_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v___x_5571_);
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
else
{
lean_dec(v_a_5547_);
lean_dec_ref(v_code_5513_);
return v___x_5548_;
}
}
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5584_; 
lean_dec_ref(v_k_5535_);
lean_dec_ref(v_code_5513_);
v_a_5577_ = lean_ctor_get(v___x_5546_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5546_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5579_ = v___x_5546_;
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5546_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5577_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
else
{
lean_dec_ref(v_type_5541_);
lean_dec_ref(v_params_5540_);
lean_dec_ref(v_k_5535_);
lean_dec_ref(v_decl_5534_);
lean_dec_ref(v_code_5513_);
return v___x_5543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5666_, lean_object* v_code_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5666_, v_code_5667_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_);
lean_dec(v_a_5671_);
lean_dec_ref(v_a_5670_);
lean_dec(v_a_5669_);
lean_dec_ref(v_a_5668_);
lean_dec_ref(v_assignment_5666_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5674_, lean_object* v_discrVal_5675_, lean_object* v_discr_5676_, lean_object* v_assignment_5677_, lean_object* v_i_5678_, lean_object* v_as_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5674_, v_discrVal_5675_, v_discr_5676_, v_assignment_5677_, v_i_5678_, v_as_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec_ref(v_assignment_5677_);
lean_dec(v_discrVal_5675_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5686_, lean_object* v_m_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v___x_5689_; 
v___x_5689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5687_, v_a_5688_);
return v___x_5689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5690_, lean_object* v_m_5691_, lean_object* v_a_5692_){
_start:
{
lean_object* v_res_5693_; 
v_res_5693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5690_, v_m_5691_, v_a_5692_);
lean_dec(v_a_5692_);
lean_dec_ref(v_m_5691_);
return v_res_5693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5694_, size_t v_i_5695_, size_t v_stop_5696_, lean_object* v_b_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_){
_start:
{
lean_object* v___x_5703_; 
v___x_5703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5694_, v_i_5695_, v_stop_5696_, v_b_5697_);
return v___x_5703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5704_, lean_object* v_i_5705_, lean_object* v_stop_5706_, lean_object* v_b_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_){
_start:
{
size_t v_i_boxed_5713_; size_t v_stop_boxed_5714_; lean_object* v_res_5715_; 
v_i_boxed_5713_ = lean_unbox_usize(v_i_5705_);
lean_dec(v_i_5705_);
v_stop_boxed_5714_ = lean_unbox_usize(v_stop_5706_);
lean_dec(v_stop_5706_);
v_res_5715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5704_, v_i_boxed_5713_, v_stop_boxed_5714_, v_b_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
lean_dec(v___y_5711_);
lean_dec_ref(v___y_5710_);
lean_dec(v___y_5709_);
lean_dec_ref(v___y_5708_);
lean_dec_ref(v_as_5704_);
return v_res_5715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5716_, lean_object* v_a_5717_, lean_object* v_x_5718_){
_start:
{
lean_object* v___x_5719_; 
v___x_5719_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5717_, v_x_5718_);
return v___x_5719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5720_, lean_object* v_a_5721_, lean_object* v_x_5722_){
_start:
{
lean_object* v_res_5723_; 
v_res_5723_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5720_, v_a_5721_, v_x_5722_);
lean_dec(v_x_5722_);
lean_dec(v_a_5721_);
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5724_, lean_object* v_v_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
if (lean_obj_tag(v_v_5725_) == 0)
{
lean_object* v_code_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5755_; 
v_code_5731_ = lean_ctor_get(v_v_5725_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_v_5725_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5733_ = v_v_5725_;
v_isShared_5734_ = v_isSharedCheck_5755_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_code_5731_);
lean_dec(v_v_5725_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5755_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5735_; 
lean_inc(v___y_5729_);
lean_inc_ref(v___y_5728_);
lean_inc(v___y_5727_);
lean_inc_ref(v___y_5726_);
v___x_5735_ = lean_apply_6(v_f_5724_, v_code_5731_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, lean_box(0));
if (lean_obj_tag(v___x_5735_) == 0)
{
lean_object* v_a_5736_; lean_object* v___x_5738_; uint8_t v_isShared_5739_; uint8_t v_isSharedCheck_5746_; 
v_a_5736_ = lean_ctor_get(v___x_5735_, 0);
v_isSharedCheck_5746_ = !lean_is_exclusive(v___x_5735_);
if (v_isSharedCheck_5746_ == 0)
{
v___x_5738_ = v___x_5735_;
v_isShared_5739_ = v_isSharedCheck_5746_;
goto v_resetjp_5737_;
}
else
{
lean_inc(v_a_5736_);
lean_dec(v___x_5735_);
v___x_5738_ = lean_box(0);
v_isShared_5739_ = v_isSharedCheck_5746_;
goto v_resetjp_5737_;
}
v_resetjp_5737_:
{
lean_object* v___x_5741_; 
if (v_isShared_5734_ == 0)
{
lean_ctor_set(v___x_5733_, 0, v_a_5736_);
v___x_5741_ = v___x_5733_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5736_);
v___x_5741_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
lean_object* v___x_5743_; 
if (v_isShared_5739_ == 0)
{
lean_ctor_set(v___x_5738_, 0, v___x_5741_);
v___x_5743_ = v___x_5738_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v___x_5741_);
v___x_5743_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
return v___x_5743_;
}
}
}
}
else
{
lean_object* v_a_5747_; lean_object* v___x_5749_; uint8_t v_isShared_5750_; uint8_t v_isSharedCheck_5754_; 
lean_del_object(v___x_5733_);
v_a_5747_ = lean_ctor_get(v___x_5735_, 0);
v_isSharedCheck_5754_ = !lean_is_exclusive(v___x_5735_);
if (v_isSharedCheck_5754_ == 0)
{
v___x_5749_ = v___x_5735_;
v_isShared_5750_ = v_isSharedCheck_5754_;
goto v_resetjp_5748_;
}
else
{
lean_inc(v_a_5747_);
lean_dec(v___x_5735_);
v___x_5749_ = lean_box(0);
v_isShared_5750_ = v_isSharedCheck_5754_;
goto v_resetjp_5748_;
}
v_resetjp_5748_:
{
lean_object* v___x_5752_; 
if (v_isShared_5750_ == 0)
{
v___x_5752_ = v___x_5749_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_a_5747_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
}
}
else
{
lean_object* v___x_5756_; 
lean_dec_ref(v_f_5724_);
v___x_5756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5756_, 0, v_v_5725_);
return v___x_5756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5757_, lean_object* v_v_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5757_, v_v_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5765_, lean_object* v_f_5766_, lean_object* v_v_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_){
_start:
{
lean_object* v___x_5773_; 
v___x_5773_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5766_, v_v_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_);
return v___x_5773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5774_, lean_object* v_f_5775_, lean_object* v_v_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_){
_start:
{
uint8_t v_pu_boxed_5782_; lean_object* v_res_5783_; 
v_pu_boxed_5782_ = lean_unbox(v_pu_5774_);
v_res_5783_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5782_, v_f_5775_, v_v_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v___y_5778_);
lean_dec_ref(v___y_5777_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5784_, lean_object* v_x_5785_){
_start:
{
if (lean_obj_tag(v_x_5785_) == 0)
{
return v_x_5784_;
}
else
{
lean_object* v_key_5786_; lean_object* v_value_5787_; lean_object* v_tail_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; 
v_key_5786_ = lean_ctor_get(v_x_5785_, 0);
v_value_5787_ = lean_ctor_get(v_x_5785_, 1);
v_tail_5788_ = lean_ctor_get(v_x_5785_, 2);
lean_inc(v_value_5787_);
lean_inc(v_key_5786_);
v___x_5789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5789_, 0, v_key_5786_);
lean_ctor_set(v___x_5789_, 1, v_value_5787_);
v___x_5790_ = lean_array_push(v_x_5784_, v___x_5789_);
v_x_5784_ = v___x_5790_;
v_x_5785_ = v_tail_5788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5792_, lean_object* v_x_5793_){
_start:
{
lean_object* v_res_5794_; 
v_res_5794_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5792_, v_x_5793_);
lean_dec(v_x_5793_);
return v_res_5794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5795_, size_t v_i_5796_, size_t v_stop_5797_, lean_object* v_b_5798_){
_start:
{
uint8_t v___x_5799_; 
v___x_5799_ = lean_usize_dec_eq(v_i_5796_, v_stop_5797_);
if (v___x_5799_ == 0)
{
lean_object* v___x_5800_; lean_object* v___x_5801_; size_t v___x_5802_; size_t v___x_5803_; 
v___x_5800_ = lean_array_uget_borrowed(v_as_5795_, v_i_5796_);
v___x_5801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5798_, v___x_5800_);
v___x_5802_ = ((size_t)1ULL);
v___x_5803_ = lean_usize_add(v_i_5796_, v___x_5802_);
v_i_5796_ = v___x_5803_;
v_b_5798_ = v___x_5801_;
goto _start;
}
else
{
return v_b_5798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5805_, lean_object* v_i_5806_, lean_object* v_stop_5807_, lean_object* v_b_5808_){
_start:
{
size_t v_i_boxed_5809_; size_t v_stop_boxed_5810_; lean_object* v_res_5811_; 
v_i_boxed_5809_ = lean_unbox_usize(v_i_5806_);
lean_dec(v_i_5806_);
v_stop_boxed_5810_ = lean_unbox_usize(v_stop_5807_);
lean_dec(v_stop_5807_);
v_res_5811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5805_, v_i_boxed_5809_, v_stop_boxed_5810_, v_b_5808_);
lean_dec_ref(v_as_5805_);
return v_res_5811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5812_, size_t v_sz_5813_, size_t v_i_5814_, lean_object* v_bs_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_){
_start:
{
uint8_t v___x_5821_; 
v___x_5821_ = lean_usize_dec_lt(v_i_5814_, v_sz_5813_);
if (v___x_5821_ == 0)
{
lean_object* v___x_5822_; 
v___x_5822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5822_, 0, v_bs_5815_);
return v___x_5822_;
}
else
{
lean_object* v_v_5823_; lean_object* v_fst_5824_; lean_object* v_snd_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5849_; 
v_v_5823_ = lean_array_uget(v_bs_5815_, v_i_5814_);
v_fst_5824_ = lean_ctor_get(v_v_5823_, 0);
v_snd_5825_ = lean_ctor_get(v_v_5823_, 1);
v_isSharedCheck_5849_ = !lean_is_exclusive(v_v_5823_);
if (v_isSharedCheck_5849_ == 0)
{
v___x_5827_ = v_v_5823_;
v_isShared_5828_ = v_isSharedCheck_5849_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_snd_5825_);
lean_inc(v_fst_5824_);
lean_dec(v_v_5823_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5849_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v___x_5829_; 
v___x_5829_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5824_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_);
if (lean_obj_tag(v___x_5829_) == 0)
{
lean_object* v_a_5830_; lean_object* v___x_5831_; lean_object* v_bs_x27_5832_; lean_object* v___x_5833_; lean_object* v___x_5835_; 
v_a_5830_ = lean_ctor_get(v___x_5829_, 0);
lean_inc(v_a_5830_);
lean_dec_ref_known(v___x_5829_, 1);
v___x_5831_ = lean_unsigned_to_nat(0u);
v_bs_x27_5832_ = lean_array_uset(v_bs_5815_, v_i_5814_, v___x_5831_);
v___x_5833_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5830_, v_a_5812_);
if (v_isShared_5828_ == 0)
{
lean_ctor_set(v___x_5827_, 0, v___x_5833_);
v___x_5835_ = v___x_5827_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5840_; 
v_reuseFailAlloc_5840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5840_, 0, v___x_5833_);
lean_ctor_set(v_reuseFailAlloc_5840_, 1, v_snd_5825_);
v___x_5835_ = v_reuseFailAlloc_5840_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
size_t v___x_5836_; size_t v___x_5837_; lean_object* v___x_5838_; 
v___x_5836_ = ((size_t)1ULL);
v___x_5837_ = lean_usize_add(v_i_5814_, v___x_5836_);
v___x_5838_ = lean_array_uset(v_bs_x27_5832_, v_i_5814_, v___x_5835_);
v_i_5814_ = v___x_5837_;
v_bs_5815_ = v___x_5838_;
goto _start;
}
}
else
{
lean_object* v_a_5841_; lean_object* v___x_5843_; uint8_t v_isShared_5844_; uint8_t v_isSharedCheck_5848_; 
lean_del_object(v___x_5827_);
lean_dec(v_snd_5825_);
lean_dec_ref(v_bs_5815_);
v_a_5841_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5848_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5848_ == 0)
{
v___x_5843_ = v___x_5829_;
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
else
{
lean_inc(v_a_5841_);
lean_dec(v___x_5829_);
v___x_5843_ = lean_box(0);
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
v_resetjp_5842_:
{
lean_object* v___x_5846_; 
if (v_isShared_5844_ == 0)
{
v___x_5846_ = v___x_5843_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_a_5841_);
v___x_5846_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
return v___x_5846_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5850_, lean_object* v_sz_5851_, lean_object* v_i_5852_, lean_object* v_bs_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_){
_start:
{
uint8_t v_a_2702__boxed_5859_; size_t v_sz_boxed_5860_; size_t v_i_boxed_5861_; lean_object* v_res_5862_; 
v_a_2702__boxed_5859_ = lean_unbox(v_a_5850_);
v_sz_boxed_5860_ = lean_unbox_usize(v_sz_5851_);
lean_dec(v_sz_5851_);
v_i_boxed_5861_ = lean_unbox_usize(v_i_5852_);
lean_dec(v_i_5852_);
v_res_5862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2702__boxed_5859_, v_sz_boxed_5860_, v_i_boxed_5861_, v_bs_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_);
lean_dec(v___y_5857_);
lean_dec_ref(v___y_5856_);
lean_dec(v___y_5855_);
lean_dec_ref(v___y_5854_);
return v_res_5862_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5863_){
_start:
{
lean_object* v_fst_5864_; lean_object* v_snd_5865_; lean_object* v___x_5867_; uint8_t v_isShared_5868_; uint8_t v_isSharedCheck_5888_; 
v_fst_5864_ = lean_ctor_get(v_x_5863_, 0);
v_snd_5865_ = lean_ctor_get(v_x_5863_, 1);
v_isSharedCheck_5888_ = !lean_is_exclusive(v_x_5863_);
if (v_isSharedCheck_5888_ == 0)
{
v___x_5867_ = v_x_5863_;
v_isShared_5868_ = v_isSharedCheck_5888_;
goto v_resetjp_5866_;
}
else
{
lean_inc(v_snd_5865_);
lean_inc(v_fst_5864_);
lean_dec(v_x_5863_);
v___x_5867_ = lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5888_;
goto v_resetjp_5866_;
}
v_resetjp_5866_:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5873_; 
v___x_5869_ = l_String_quote(v_fst_5864_);
v___x_5870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5870_, 0, v___x_5869_);
v___x_5871_ = lean_box(0);
if (v_isShared_5868_ == 0)
{
lean_ctor_set_tag(v___x_5867_, 1);
lean_ctor_set(v___x_5867_, 1, v___x_5871_);
lean_ctor_set(v___x_5867_, 0, v___x_5870_);
v___x_5873_ = v___x_5867_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5887_; 
v_reuseFailAlloc_5887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5887_, 0, v___x_5870_);
lean_ctor_set(v_reuseFailAlloc_5887_, 1, v___x_5871_);
v___x_5873_ = v_reuseFailAlloc_5887_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; uint8_t v___x_5885_; lean_object* v___x_5886_; 
v___x_5874_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5865_);
v___x_5875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
lean_ctor_set(v___x_5875_, 1, v___x_5873_);
v___x_5876_ = l_List_reverse___redArg(v___x_5875_);
v___x_5877_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5878_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5876_, v___x_5877_);
v___x_5879_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5880_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5880_);
lean_ctor_set(v___x_5881_, 1, v___x_5878_);
v___x_5882_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5881_);
lean_ctor_set(v___x_5883_, 1, v___x_5882_);
v___x_5884_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5884_, 0, v___x_5879_);
lean_ctor_set(v___x_5884_, 1, v___x_5883_);
v___x_5885_ = 0;
v___x_5886_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5886_, 0, v___x_5884_);
lean_ctor_set_uint8(v___x_5886_, sizeof(void*)*1, v___x_5885_);
return v___x_5886_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5889_, lean_object* v_x_5890_, lean_object* v_x_5891_){
_start:
{
if (lean_obj_tag(v_x_5891_) == 0)
{
lean_dec(v_x_5889_);
return v_x_5890_;
}
else
{
lean_object* v_head_5892_; lean_object* v_tail_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5903_; 
v_head_5892_ = lean_ctor_get(v_x_5891_, 0);
v_tail_5893_ = lean_ctor_get(v_x_5891_, 1);
v_isSharedCheck_5903_ = !lean_is_exclusive(v_x_5891_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5895_ = v_x_5891_;
v_isShared_5896_ = v_isSharedCheck_5903_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_tail_5893_);
lean_inc(v_head_5892_);
lean_dec(v_x_5891_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5903_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v___x_5898_; 
lean_inc(v_x_5889_);
if (v_isShared_5896_ == 0)
{
lean_ctor_set_tag(v___x_5895_, 5);
lean_ctor_set(v___x_5895_, 1, v_x_5889_);
lean_ctor_set(v___x_5895_, 0, v_x_5890_);
v___x_5898_ = v___x_5895_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_x_5890_);
lean_ctor_set(v_reuseFailAlloc_5902_, 1, v_x_5889_);
v___x_5898_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5899_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5892_);
v___x_5900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5898_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v_x_5890_ = v___x_5900_;
v_x_5891_ = v_tail_5893_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5904_, lean_object* v_x_5905_, lean_object* v_x_5906_){
_start:
{
if (lean_obj_tag(v_x_5906_) == 0)
{
lean_dec(v_x_5904_);
return v_x_5905_;
}
else
{
lean_object* v_head_5907_; lean_object* v_tail_5908_; lean_object* v___x_5910_; uint8_t v_isShared_5911_; uint8_t v_isSharedCheck_5918_; 
v_head_5907_ = lean_ctor_get(v_x_5906_, 0);
v_tail_5908_ = lean_ctor_get(v_x_5906_, 1);
v_isSharedCheck_5918_ = !lean_is_exclusive(v_x_5906_);
if (v_isSharedCheck_5918_ == 0)
{
v___x_5910_ = v_x_5906_;
v_isShared_5911_ = v_isSharedCheck_5918_;
goto v_resetjp_5909_;
}
else
{
lean_inc(v_tail_5908_);
lean_inc(v_head_5907_);
lean_dec(v_x_5906_);
v___x_5910_ = lean_box(0);
v_isShared_5911_ = v_isSharedCheck_5918_;
goto v_resetjp_5909_;
}
v_resetjp_5909_:
{
lean_object* v___x_5913_; 
lean_inc(v_x_5904_);
if (v_isShared_5911_ == 0)
{
lean_ctor_set_tag(v___x_5910_, 5);
lean_ctor_set(v___x_5910_, 1, v_x_5904_);
lean_ctor_set(v___x_5910_, 0, v_x_5905_);
v___x_5913_ = v___x_5910_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5917_; 
v_reuseFailAlloc_5917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_x_5905_);
lean_ctor_set(v_reuseFailAlloc_5917_, 1, v_x_5904_);
v___x_5913_ = v_reuseFailAlloc_5917_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; 
v___x_5914_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5907_);
v___x_5915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5904_, v___x_5915_, v_tail_5908_);
return v___x_5916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5919_, lean_object* v_x_5920_){
_start:
{
if (lean_obj_tag(v_x_5919_) == 0)
{
lean_object* v___x_5921_; 
lean_dec(v_x_5920_);
v___x_5921_ = lean_box(0);
return v___x_5921_;
}
else
{
lean_object* v_tail_5922_; 
v_tail_5922_ = lean_ctor_get(v_x_5919_, 1);
if (lean_obj_tag(v_tail_5922_) == 0)
{
lean_object* v_head_5923_; lean_object* v___x_5924_; 
lean_dec(v_x_5920_);
v_head_5923_ = lean_ctor_get(v_x_5919_, 0);
lean_inc(v_head_5923_);
lean_dec_ref_known(v_x_5919_, 2);
v___x_5924_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5923_);
return v___x_5924_;
}
else
{
lean_object* v_head_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
lean_inc(v_tail_5922_);
v_head_5925_ = lean_ctor_get(v_x_5919_, 0);
lean_inc(v_head_5925_);
lean_dec_ref_known(v_x_5919_, 2);
v___x_5926_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5925_);
v___x_5927_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5920_, v___x_5926_, v_tail_5922_);
return v___x_5927_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5929_; lean_object* v___x_5930_; 
v___x_5929_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5930_ = lean_string_length(v___x_5929_);
return v___x_5930_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5932_ = lean_nat_to_int(v___x_5931_);
return v___x_5932_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5938_){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; uint8_t v___x_5941_; 
v___x_5939_ = lean_array_get_size(v_xs_5938_);
v___x_5940_ = lean_unsigned_to_nat(0u);
v___x_5941_ = lean_nat_dec_eq(v___x_5939_, v___x_5940_);
if (v___x_5941_ == 0)
{
lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; 
v___x_5942_ = lean_array_to_list(v_xs_5938_);
v___x_5943_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5944_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5942_, v___x_5943_);
v___x_5945_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5946_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
lean_ctor_set(v___x_5947_, 1, v___x_5944_);
v___x_5948_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5947_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5945_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = l_Std_Format_fill(v___x_5950_);
return v___x_5951_;
}
else
{
lean_object* v___x_5952_; 
lean_dec_ref(v_xs_5938_);
v___x_5952_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_5952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_5955_, lean_object* v_decl_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_){
_start:
{
lean_object* v___y_5963_; lean_object* v___y_5964_; lean_object* v___y_5965_; lean_object* v___y_5966_; lean_object* v_options_5996_; uint8_t v_hasTrace_5997_; 
v_options_5996_ = lean_ctor_get(v_a_5959_, 2);
v_hasTrace_5997_ = lean_ctor_get_uint8(v_options_5996_, sizeof(void*)*1);
if (v_hasTrace_5997_ == 0)
{
v___y_5963_ = v_a_5957_;
v___y_5964_ = v_a_5958_;
v___y_5965_ = v_a_5959_;
v___y_5966_ = v_a_5960_;
goto v___jp_5962_;
}
else
{
lean_object* v_inheritedTraceOptions_5998_; lean_object* v_cls_5999_; uint8_t v___y_6001_; lean_object* v___y_6002_; lean_object* v___x_6038_; uint8_t v___x_6039_; 
v_inheritedTraceOptions_5998_ = lean_ctor_get(v_a_5959_, 13);
v_cls_5999_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6038_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5998_, v_options_5996_, v___x_6038_);
if (v___x_6039_ == 0)
{
v___y_5963_ = v_a_5957_;
v___y_5964_ = v_a_5958_;
v___y_5965_ = v_a_5959_;
v___y_5966_ = v_a_5960_;
goto v___jp_5962_;
}
else
{
lean_object* v_size_6040_; lean_object* v_buckets_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; uint8_t v___x_6045_; 
v_size_6040_ = lean_ctor_get(v_assignment_5955_, 0);
v_buckets_6041_ = lean_ctor_get(v_assignment_5955_, 1);
v___x_6042_ = lean_mk_empty_array_with_capacity(v_size_6040_);
v___x_6043_ = lean_unsigned_to_nat(0u);
v___x_6044_ = lean_array_get_size(v_buckets_6041_);
v___x_6045_ = lean_nat_dec_lt(v___x_6043_, v___x_6044_);
if (v___x_6045_ == 0)
{
v___y_6001_ = v___x_6039_;
v___y_6002_ = v___x_6042_;
goto v___jp_6000_;
}
else
{
uint8_t v___x_6046_; 
v___x_6046_ = lean_nat_dec_le(v___x_6044_, v___x_6044_);
if (v___x_6046_ == 0)
{
if (v___x_6045_ == 0)
{
v___y_6001_ = v___x_6039_;
v___y_6002_ = v___x_6042_;
goto v___jp_6000_;
}
else
{
size_t v___x_6047_; size_t v___x_6048_; lean_object* v___x_6049_; 
v___x_6047_ = ((size_t)0ULL);
v___x_6048_ = lean_usize_of_nat(v___x_6044_);
v___x_6049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6041_, v___x_6047_, v___x_6048_, v___x_6042_);
v___y_6001_ = v___x_6039_;
v___y_6002_ = v___x_6049_;
goto v___jp_6000_;
}
}
else
{
size_t v___x_6050_; size_t v___x_6051_; lean_object* v___x_6052_; 
v___x_6050_ = ((size_t)0ULL);
v___x_6051_ = lean_usize_of_nat(v___x_6044_);
v___x_6052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6041_, v___x_6050_, v___x_6051_, v___x_6042_);
v___y_6001_ = v___x_6039_;
v___y_6002_ = v___x_6052_;
goto v___jp_6000_;
}
}
}
v___jp_6000_:
{
size_t v_sz_6003_; size_t v___x_6004_; lean_object* v___x_6005_; 
v_sz_6003_ = lean_array_size(v___y_6002_);
v___x_6004_ = ((size_t)0ULL);
v___x_6005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6001_, v_sz_6003_, v___x_6004_, v___y_6002_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_);
if (lean_obj_tag(v___x_6005_) == 0)
{
lean_object* v_toSignature_6006_; lean_object* v_a_6007_; lean_object* v_name_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v_toSignature_6006_ = lean_ctor_get(v_decl_5956_, 0);
v_a_6007_ = lean_ctor_get(v___x_6005_, 0);
lean_inc(v_a_6007_);
lean_dec_ref_known(v___x_6005_, 1);
v_name_6008_ = lean_ctor_get(v_toSignature_6006_, 0);
v___x_6009_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6008_);
v___x_6010_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6008_, v___y_6001_);
v___x_6011_ = lean_string_append(v___x_6009_, v___x_6010_);
lean_dec_ref(v___x_6010_);
v___x_6012_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6013_ = lean_string_append(v___x_6011_, v___x_6012_);
v___x_6014_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6007_);
v___x_6015_ = l_Std_Format_defWidth;
v___x_6016_ = lean_unsigned_to_nat(0u);
v___x_6017_ = l_Std_Format_pretty(v___x_6014_, v___x_6015_, v___x_6016_, v___x_6016_);
v___x_6018_ = lean_string_append(v___x_6013_, v___x_6017_);
lean_dec_ref(v___x_6017_);
v___x_6019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
v___x_6020_ = l_Lean_MessageData_ofFormat(v___x_6019_);
v___x_6021_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5999_, v___x_6020_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_);
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_dec_ref_known(v___x_6021_, 1);
v___y_5963_ = v_a_5957_;
v___y_5964_ = v_a_5958_;
v___y_5965_ = v_a_5959_;
v___y_5966_ = v_a_5960_;
goto v___jp_5962_;
}
else
{
lean_object* v_a_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6029_; 
lean_dec_ref(v_decl_5956_);
lean_dec_ref(v_assignment_5955_);
v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6029_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6029_ == 0)
{
v___x_6024_ = v___x_6021_;
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_a_6022_);
lean_dec(v___x_6021_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6027_; 
if (v_isShared_6025_ == 0)
{
v___x_6027_ = v___x_6024_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6028_; 
v_reuseFailAlloc_6028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
v___x_6027_ = v_reuseFailAlloc_6028_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
return v___x_6027_;
}
}
}
}
else
{
lean_object* v_a_6030_; lean_object* v___x_6032_; uint8_t v_isShared_6033_; uint8_t v_isSharedCheck_6037_; 
lean_dec_ref(v_decl_5956_);
lean_dec_ref(v_assignment_5955_);
v_a_6030_ = lean_ctor_get(v___x_6005_, 0);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_6005_);
if (v_isSharedCheck_6037_ == 0)
{
v___x_6032_ = v___x_6005_;
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
else
{
lean_inc(v_a_6030_);
lean_dec(v___x_6005_);
v___x_6032_ = lean_box(0);
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
v_resetjp_6031_:
{
lean_object* v___x_6035_; 
if (v_isShared_6033_ == 0)
{
v___x_6035_ = v___x_6032_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
v___x_6035_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
return v___x_6035_;
}
}
}
}
}
v___jp_5962_:
{
lean_object* v_toSignature_5967_; lean_object* v_value_5968_; uint8_t v_recursive_5969_; lean_object* v_inlineAttr_x3f_5970_; lean_object* v___x_5972_; uint8_t v_isShared_5973_; uint8_t v_isSharedCheck_5995_; 
v_toSignature_5967_ = lean_ctor_get(v_decl_5956_, 0);
v_value_5968_ = lean_ctor_get(v_decl_5956_, 1);
v_recursive_5969_ = lean_ctor_get_uint8(v_decl_5956_, sizeof(void*)*3);
v_inlineAttr_x3f_5970_ = lean_ctor_get(v_decl_5956_, 2);
v_isSharedCheck_5995_ = !lean_is_exclusive(v_decl_5956_);
if (v_isSharedCheck_5995_ == 0)
{
v___x_5972_ = v_decl_5956_;
v_isShared_5973_ = v_isSharedCheck_5995_;
goto v_resetjp_5971_;
}
else
{
lean_inc(v_inlineAttr_x3f_5970_);
lean_inc(v_value_5968_);
lean_inc(v_toSignature_5967_);
lean_dec(v_decl_5956_);
v___x_5972_ = lean_box(0);
v_isShared_5973_ = v_isSharedCheck_5995_;
goto v_resetjp_5971_;
}
v_resetjp_5971_:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5974_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_5974_, 0, v_assignment_5955_);
v___x_5975_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_5974_, v_value_5968_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
if (lean_obj_tag(v___x_5975_) == 0)
{
lean_object* v_a_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_5986_; 
v_a_5976_ = lean_ctor_get(v___x_5975_, 0);
v_isSharedCheck_5986_ = !lean_is_exclusive(v___x_5975_);
if (v_isSharedCheck_5986_ == 0)
{
v___x_5978_ = v___x_5975_;
v_isShared_5979_ = v_isSharedCheck_5986_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_a_5976_);
lean_dec(v___x_5975_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_5986_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5981_; 
if (v_isShared_5973_ == 0)
{
lean_ctor_set(v___x_5972_, 1, v_a_5976_);
v___x_5981_ = v___x_5972_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_toSignature_5967_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_a_5976_);
lean_ctor_set(v_reuseFailAlloc_5985_, 2, v_inlineAttr_x3f_5970_);
lean_ctor_set_uint8(v_reuseFailAlloc_5985_, sizeof(void*)*3, v_recursive_5969_);
v___x_5981_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
lean_object* v___x_5983_; 
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 0, v___x_5981_);
v___x_5983_ = v___x_5978_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v___x_5981_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
return v___x_5983_;
}
}
}
}
else
{
lean_object* v_a_5987_; lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_5994_; 
lean_del_object(v___x_5972_);
lean_dec(v_inlineAttr_x3f_5970_);
lean_dec_ref(v_toSignature_5967_);
v_a_5987_ = lean_ctor_get(v___x_5975_, 0);
v_isSharedCheck_5994_ = !lean_is_exclusive(v___x_5975_);
if (v_isSharedCheck_5994_ == 0)
{
v___x_5989_ = v___x_5975_;
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
else
{
lean_inc(v_a_5987_);
lean_dec(v___x_5975_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
lean_object* v___x_5992_; 
if (v_isShared_5990_ == 0)
{
v___x_5992_ = v___x_5989_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_a_5987_);
v___x_5992_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
return v___x_5992_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6053_, lean_object* v_decl_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_){
_start:
{
lean_object* v_res_6060_; 
v_res_6060_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6053_, v_decl_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_);
lean_dec(v_a_6058_);
lean_dec_ref(v_a_6057_);
lean_dec(v_a_6056_);
lean_dec_ref(v_a_6055_);
return v_res_6060_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6061_, lean_object* v_x_6062_){
_start:
{
lean_object* v___x_6063_; 
v___x_6063_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6061_);
return v___x_6063_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6064_, lean_object* v_x_6065_){
_start:
{
lean_object* v_res_6066_; 
v_res_6066_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6064_, v_x_6065_);
lean_dec(v_x_6065_);
return v_res_6066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6067_, size_t v_i_6068_, lean_object* v_bs_6069_){
_start:
{
uint8_t v___x_6070_; 
v___x_6070_ = lean_usize_dec_lt(v_i_6068_, v_sz_6067_);
if (v___x_6070_ == 0)
{
return v_bs_6069_;
}
else
{
lean_object* v_v_6071_; lean_object* v_toSignature_6072_; lean_object* v_name_6073_; lean_object* v___x_6074_; lean_object* v_bs_x27_6075_; size_t v___x_6076_; size_t v___x_6077_; lean_object* v___x_6078_; 
v_v_6071_ = lean_array_uget_borrowed(v_bs_6069_, v_i_6068_);
v_toSignature_6072_ = lean_ctor_get(v_v_6071_, 0);
v_name_6073_ = lean_ctor_get(v_toSignature_6072_, 0);
lean_inc(v_name_6073_);
v___x_6074_ = lean_unsigned_to_nat(0u);
v_bs_x27_6075_ = lean_array_uset(v_bs_6069_, v_i_6068_, v___x_6074_);
v___x_6076_ = ((size_t)1ULL);
v___x_6077_ = lean_usize_add(v_i_6068_, v___x_6076_);
v___x_6078_ = lean_array_uset(v_bs_x27_6075_, v_i_6068_, v_name_6073_);
v_i_6068_ = v___x_6077_;
v_bs_6069_ = v___x_6078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6080_, lean_object* v_i_6081_, lean_object* v_bs_6082_){
_start:
{
size_t v_sz_boxed_6083_; size_t v_i_boxed_6084_; lean_object* v_res_6085_; 
v_sz_boxed_6083_ = lean_unbox_usize(v_sz_6080_);
lean_dec(v_sz_6080_);
v_i_boxed_6084_ = lean_unbox_usize(v_i_6081_);
lean_dec(v_i_6081_);
v_res_6085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6083_, v_i_boxed_6084_, v_bs_6082_);
return v_res_6085_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6086_, lean_object* v_a_6087_){
_start:
{
if (lean_obj_tag(v_a_6086_) == 0)
{
lean_object* v___x_6088_; 
v___x_6088_ = l_List_reverse___redArg(v_a_6087_);
return v___x_6088_;
}
else
{
lean_object* v_head_6089_; lean_object* v_tail_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6099_; 
v_head_6089_ = lean_ctor_get(v_a_6086_, 0);
v_tail_6090_ = lean_ctor_get(v_a_6086_, 1);
v_isSharedCheck_6099_ = !lean_is_exclusive(v_a_6086_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_6092_ = v_a_6086_;
v_isShared_6093_ = v_isSharedCheck_6099_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_tail_6090_);
lean_inc(v_head_6089_);
lean_dec(v_a_6086_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6099_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v___x_6094_; lean_object* v___x_6096_; 
v___x_6094_ = l_Lean_MessageData_ofName(v_head_6089_);
if (v_isShared_6093_ == 0)
{
lean_ctor_set(v___x_6092_, 1, v_a_6087_);
lean_ctor_set(v___x_6092_, 0, v___x_6094_);
v___x_6096_ = v___x_6092_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v___x_6094_);
lean_ctor_set(v_reuseFailAlloc_6098_, 1, v_a_6087_);
v___x_6096_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
v_a_6086_ = v_tail_6090_;
v_a_6087_ = v___x_6096_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6101_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6102_ = l_Lean_stringToMessageData(v___x_6101_);
return v___x_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6103_, lean_object* v_x_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_){
_start:
{
lean_object* v___x_6112_; size_t v_sz_6113_; size_t v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; 
v___x_6112_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6113_ = lean_array_size(v___y_6103_);
v___x_6114_ = ((size_t)0ULL);
v___x_6115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6113_, v___x_6114_, v___y_6103_);
v___x_6116_ = lean_array_to_list(v___x_6115_);
v___x_6117_ = lean_box(0);
v___x_6118_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6116_, v___x_6117_);
v___x_6119_ = l_Lean_MessageData_ofList(v___x_6118_);
v___x_6120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6112_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
v___x_6121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
return v___x_6121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6122_, lean_object* v_x_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_){
_start:
{
lean_object* v_res_6131_; 
v_res_6131_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6122_, v_x_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec_ref(v___y_6126_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec_ref(v_x_6123_);
return v_res_6131_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6132_; lean_object* v___x_6133_; 
v___x_6132_ = 0;
v___x_6133_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6132_);
return v___x_6133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6134_, lean_object* v_n_6135_, lean_object* v_j_6136_, lean_object* v_a_6137_){
_start:
{
lean_object* v_zero_6138_; uint8_t v_isZero_6139_; 
v_zero_6138_ = lean_unsigned_to_nat(0u);
v_isZero_6139_ = lean_nat_dec_eq(v_j_6136_, v_zero_6138_);
if (v_isZero_6139_ == 1)
{
lean_dec(v_j_6136_);
return v_a_6137_;
}
else
{
lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v_toSignature_6143_; uint8_t v_safe_6144_; lean_object* v_one_6145_; lean_object* v_n_6146_; 
v___x_6140_ = lean_nat_sub(v_n_6135_, v_j_6136_);
v___x_6141_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6142_ = lean_array_get_borrowed(v___x_6141_, v___y_6134_, v___x_6140_);
lean_dec(v___x_6140_);
v_toSignature_6143_ = lean_ctor_get(v___x_6142_, 0);
v_safe_6144_ = lean_ctor_get_uint8(v_toSignature_6143_, sizeof(void*)*4);
v_one_6145_ = lean_unsigned_to_nat(1u);
v_n_6146_ = lean_nat_sub(v_j_6136_, v_one_6145_);
lean_dec(v_j_6136_);
if (v_safe_6144_ == 0)
{
lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6147_ = lean_box(1);
v___x_6148_ = lean_array_push(v_a_6137_, v___x_6147_);
v_j_6136_ = v_n_6146_;
v_a_6137_ = v___x_6148_;
goto _start;
}
else
{
lean_object* v___x_6150_; lean_object* v___x_6151_; 
v___x_6150_ = lean_box(0);
v___x_6151_ = lean_array_push(v_a_6137_, v___x_6150_);
v_j_6136_ = v_n_6146_;
v_a_6137_ = v___x_6151_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6153_, lean_object* v_n_6154_, lean_object* v_j_6155_, lean_object* v_a_6156_){
_start:
{
lean_object* v_res_6157_; 
v_res_6157_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6153_, v_n_6154_, v_j_6155_, v_a_6156_);
lean_dec(v_n_6154_);
lean_dec_ref(v___y_6153_);
return v_res_6157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6158_, size_t v_sz_6159_, size_t v_i_6160_, lean_object* v_bs_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_){
_start:
{
uint8_t v___x_6167_; 
v___x_6167_ = lean_usize_dec_lt(v_i_6160_, v_sz_6159_);
if (v___x_6167_ == 0)
{
lean_object* v___x_6168_; 
v___x_6168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6168_, 0, v_bs_6161_);
return v___x_6168_;
}
else
{
lean_object* v_v_6169_; lean_object* v_toSignature_6170_; uint8_t v_safe_6171_; lean_object* v___x_6172_; lean_object* v_bs_x27_6173_; lean_object* v_a_6175_; 
v_v_6169_ = lean_array_uget(v_bs_6161_, v_i_6160_);
v_toSignature_6170_ = lean_ctor_get(v_v_6169_, 0);
v_safe_6171_ = lean_ctor_get_uint8(v_toSignature_6170_, sizeof(void*)*4);
v___x_6172_ = lean_unsigned_to_nat(0u);
v_bs_x27_6173_ = lean_array_uset(v_bs_6161_, v_i_6160_, v___x_6172_);
if (v_safe_6171_ == 0)
{
v_a_6175_ = v_v_6169_;
goto v___jp_6174_;
}
else
{
lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; 
v___x_6180_ = lean_usize_to_nat(v_i_6160_);
v___x_6181_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6182_ = lean_array_get_borrowed(v___x_6181_, v___x_6158_, v___x_6180_);
lean_dec(v___x_6180_);
lean_inc(v___x_6182_);
v___x_6183_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6182_, v_v_6169_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
if (lean_obj_tag(v___x_6183_) == 0)
{
lean_object* v_a_6184_; 
v_a_6184_ = lean_ctor_get(v___x_6183_, 0);
lean_inc(v_a_6184_);
lean_dec_ref_known(v___x_6183_, 1);
v_a_6175_ = v_a_6184_;
goto v___jp_6174_;
}
else
{
lean_object* v_a_6185_; lean_object* v___x_6187_; uint8_t v_isShared_6188_; uint8_t v_isSharedCheck_6192_; 
lean_dec_ref(v_bs_x27_6173_);
v_a_6185_ = lean_ctor_get(v___x_6183_, 0);
v_isSharedCheck_6192_ = !lean_is_exclusive(v___x_6183_);
if (v_isSharedCheck_6192_ == 0)
{
v___x_6187_ = v___x_6183_;
v_isShared_6188_ = v_isSharedCheck_6192_;
goto v_resetjp_6186_;
}
else
{
lean_inc(v_a_6185_);
lean_dec(v___x_6183_);
v___x_6187_ = lean_box(0);
v_isShared_6188_ = v_isSharedCheck_6192_;
goto v_resetjp_6186_;
}
v_resetjp_6186_:
{
lean_object* v___x_6190_; 
if (v_isShared_6188_ == 0)
{
v___x_6190_ = v___x_6187_;
goto v_reusejp_6189_;
}
else
{
lean_object* v_reuseFailAlloc_6191_; 
v_reuseFailAlloc_6191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6191_, 0, v_a_6185_);
v___x_6190_ = v_reuseFailAlloc_6191_;
goto v_reusejp_6189_;
}
v_reusejp_6189_:
{
return v___x_6190_;
}
}
}
}
v___jp_6174_:
{
size_t v___x_6176_; size_t v___x_6177_; lean_object* v___x_6178_; 
v___x_6176_ = ((size_t)1ULL);
v___x_6177_ = lean_usize_add(v_i_6160_, v___x_6176_);
v___x_6178_ = lean_array_uset(v_bs_x27_6173_, v_i_6160_, v_a_6175_);
v_i_6160_ = v___x_6177_;
v_bs_6161_ = v___x_6178_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6193_, lean_object* v_sz_6194_, lean_object* v_i_6195_, lean_object* v_bs_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_){
_start:
{
size_t v_sz_boxed_6202_; size_t v_i_boxed_6203_; lean_object* v_res_6204_; 
v_sz_boxed_6202_ = lean_unbox_usize(v_sz_6194_);
lean_dec(v_sz_6194_);
v_i_boxed_6203_ = lean_unbox_usize(v_i_6195_);
lean_dec(v_i_6195_);
v_res_6204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6193_, v_sz_boxed_6202_, v_i_boxed_6203_, v_bs_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6199_);
lean_dec(v___y_6198_);
lean_dec_ref(v___y_6197_);
lean_dec_ref(v___x_6193_);
return v_res_6204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6207_, lean_object* v_pivot_6208_, lean_object* v_as_6209_, lean_object* v_i_6210_, lean_object* v_k_6211_){
_start:
{
uint8_t v___x_6212_; 
v___x_6212_ = lean_nat_dec_lt(v_k_6211_, v_hi_6207_);
if (v___x_6212_ == 0)
{
lean_object* v___x_6213_; lean_object* v___x_6214_; 
lean_dec(v_k_6211_);
lean_dec_ref(v_pivot_6208_);
v___x_6213_ = lean_array_fswap(v_as_6209_, v_i_6210_, v_hi_6207_);
v___x_6214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6214_, 0, v_i_6210_);
lean_ctor_set(v___x_6214_, 1, v___x_6213_);
return v___x_6214_;
}
else
{
lean_object* v___x_6215_; lean_object* v_toSignature_6216_; lean_object* v_toSignature_6217_; lean_object* v_name_6218_; lean_object* v_name_6219_; uint8_t v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; uint8_t v___x_6230_; 
v___x_6215_ = lean_array_fget_borrowed(v_as_6209_, v_k_6211_);
v_toSignature_6216_ = lean_ctor_get(v___x_6215_, 0);
v_toSignature_6217_ = lean_ctor_get(v_pivot_6208_, 0);
v_name_6218_ = lean_ctor_get(v_toSignature_6216_, 0);
v_name_6219_ = lean_ctor_get(v_toSignature_6217_, 0);
v___x_6220_ = 0;
v___x_6221_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6220_, v___x_6215_);
v___x_6222_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6223_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6224_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6218_);
v___x_6225_ = l_Lean_Name_toString(v_name_6218_, v___x_6212_);
v___x_6226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6221_);
lean_ctor_set(v___x_6226_, 1, v___x_6225_);
v___x_6227_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6220_, v_pivot_6208_);
lean_inc(v_name_6219_);
v___x_6228_ = l_Lean_Name_toString(v_name_6219_, v___x_6212_);
v___x_6229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6227_);
lean_ctor_set(v___x_6229_, 1, v___x_6228_);
v___x_6230_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6222_, v___x_6223_, v___x_6224_, v___x_6226_, v___x_6229_);
if (v___x_6230_ == 0)
{
lean_object* v___x_6231_; lean_object* v___x_6232_; 
v___x_6231_ = lean_unsigned_to_nat(1u);
v___x_6232_ = lean_nat_add(v_k_6211_, v___x_6231_);
lean_dec(v_k_6211_);
v_k_6211_ = v___x_6232_;
goto _start;
}
else
{
lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; 
v___x_6234_ = lean_array_fswap(v_as_6209_, v_i_6210_, v_k_6211_);
v___x_6235_ = lean_unsigned_to_nat(1u);
v___x_6236_ = lean_nat_add(v_i_6210_, v___x_6235_);
lean_dec(v_i_6210_);
v___x_6237_ = lean_nat_add(v_k_6211_, v___x_6235_);
lean_dec(v_k_6211_);
v_as_6209_ = v___x_6234_;
v_i_6210_ = v___x_6236_;
v_k_6211_ = v___x_6237_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6239_, lean_object* v_pivot_6240_, lean_object* v_as_6241_, lean_object* v_i_6242_, lean_object* v_k_6243_){
_start:
{
lean_object* v_res_6244_; 
v_res_6244_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6239_, v_pivot_6240_, v_as_6241_, v_i_6242_, v_k_6243_);
lean_dec(v_hi_6239_);
return v_res_6244_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6245_, lean_object* v_l_6246_, lean_object* v_r_6247_){
_start:
{
lean_object* v_toSignature_6248_; lean_object* v_toSignature_6249_; lean_object* v_name_6250_; lean_object* v_name_6251_; uint8_t v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; uint8_t v___x_6262_; 
v_toSignature_6248_ = lean_ctor_get(v_l_6246_, 0);
v_toSignature_6249_ = lean_ctor_get(v_r_6247_, 0);
v_name_6250_ = lean_ctor_get(v_toSignature_6248_, 0);
lean_inc(v_name_6250_);
v_name_6251_ = lean_ctor_get(v_toSignature_6249_, 0);
lean_inc(v_name_6251_);
v___x_6252_ = 0;
v___x_6253_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6252_, v_l_6246_);
lean_dec_ref(v_l_6246_);
v___x_6254_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6255_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6256_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6257_ = l_Lean_Name_toString(v_name_6250_, v___x_6245_);
v___x_6258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6258_, 0, v___x_6253_);
lean_ctor_set(v___x_6258_, 1, v___x_6257_);
v___x_6259_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6252_, v_r_6247_);
lean_dec_ref(v_r_6247_);
v___x_6260_ = l_Lean_Name_toString(v_name_6251_, v___x_6245_);
v___x_6261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6261_, 0, v___x_6259_);
lean_ctor_set(v___x_6261_, 1, v___x_6260_);
v___x_6262_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6254_, v___x_6255_, v___x_6256_, v___x_6258_, v___x_6261_);
return v___x_6262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6263_, lean_object* v_l_6264_, lean_object* v_r_6265_){
_start:
{
uint8_t v___x_13129__boxed_6266_; uint8_t v_res_6267_; lean_object* v_r_6268_; 
v___x_13129__boxed_6266_ = lean_unbox(v___x_6263_);
v_res_6267_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13129__boxed_6266_, v_l_6264_, v_r_6265_);
v_r_6268_ = lean_box(v_res_6267_);
return v_r_6268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6269_, lean_object* v_as_6270_, lean_object* v_lo_6271_, lean_object* v_hi_6272_){
_start:
{
lean_object* v___y_6274_; uint8_t v___x_6284_; 
v___x_6284_ = lean_nat_dec_lt(v_lo_6271_, v_hi_6272_);
if (v___x_6284_ == 0)
{
lean_dec(v_lo_6271_);
return v_as_6270_;
}
else
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v_mid_6287_; lean_object* v___y_6289_; lean_object* v___y_6295_; lean_object* v___x_6300_; lean_object* v___x_6301_; uint8_t v___x_6302_; 
v___x_6285_ = lean_nat_add(v_lo_6271_, v_hi_6272_);
v___x_6286_ = lean_unsigned_to_nat(1u);
v_mid_6287_ = lean_nat_shiftr(v___x_6285_, v___x_6286_);
lean_dec(v___x_6285_);
v___x_6300_ = lean_array_fget_borrowed(v_as_6270_, v_mid_6287_);
v___x_6301_ = lean_array_fget_borrowed(v_as_6270_, v_lo_6271_);
lean_inc(v___x_6301_);
lean_inc(v___x_6300_);
v___x_6302_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6284_, v___x_6300_, v___x_6301_);
if (v___x_6302_ == 0)
{
v___y_6295_ = v_as_6270_;
goto v___jp_6294_;
}
else
{
lean_object* v___x_6303_; 
v___x_6303_ = lean_array_fswap(v_as_6270_, v_lo_6271_, v_mid_6287_);
v___y_6295_ = v___x_6303_;
goto v___jp_6294_;
}
v___jp_6288_:
{
lean_object* v___x_6290_; lean_object* v___x_6291_; uint8_t v___x_6292_; 
v___x_6290_ = lean_array_fget_borrowed(v___y_6289_, v_mid_6287_);
v___x_6291_ = lean_array_fget_borrowed(v___y_6289_, v_hi_6272_);
lean_inc(v___x_6291_);
lean_inc(v___x_6290_);
v___x_6292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6284_, v___x_6290_, v___x_6291_);
if (v___x_6292_ == 0)
{
lean_dec(v_mid_6287_);
v___y_6274_ = v___y_6289_;
goto v___jp_6273_;
}
else
{
lean_object* v___x_6293_; 
v___x_6293_ = lean_array_fswap(v___y_6289_, v_mid_6287_, v_hi_6272_);
lean_dec(v_mid_6287_);
v___y_6274_ = v___x_6293_;
goto v___jp_6273_;
}
}
v___jp_6294_:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; uint8_t v___x_6298_; 
v___x_6296_ = lean_array_fget_borrowed(v___y_6295_, v_hi_6272_);
v___x_6297_ = lean_array_fget_borrowed(v___y_6295_, v_lo_6271_);
lean_inc(v___x_6297_);
lean_inc(v___x_6296_);
v___x_6298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6284_, v___x_6296_, v___x_6297_);
if (v___x_6298_ == 0)
{
v___y_6289_ = v___y_6295_;
goto v___jp_6288_;
}
else
{
lean_object* v___x_6299_; 
v___x_6299_ = lean_array_fswap(v___y_6295_, v_lo_6271_, v_hi_6272_);
v___y_6289_ = v___x_6299_;
goto v___jp_6288_;
}
}
}
v___jp_6273_:
{
lean_object* v_pivot_6275_; lean_object* v___x_6276_; lean_object* v_fst_6277_; lean_object* v_snd_6278_; uint8_t v___x_6279_; 
v_pivot_6275_ = lean_array_fget(v___y_6274_, v_hi_6272_);
lean_inc_n(v_lo_6271_, 2);
v___x_6276_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6272_, v_pivot_6275_, v___y_6274_, v_lo_6271_, v_lo_6271_);
v_fst_6277_ = lean_ctor_get(v___x_6276_, 0);
lean_inc(v_fst_6277_);
v_snd_6278_ = lean_ctor_get(v___x_6276_, 1);
lean_inc(v_snd_6278_);
lean_dec_ref(v___x_6276_);
v___x_6279_ = lean_nat_dec_le(v_hi_6272_, v_fst_6277_);
if (v___x_6279_ == 0)
{
lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; 
v___x_6280_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6269_, v_snd_6278_, v_lo_6271_, v_fst_6277_);
v___x_6281_ = lean_unsigned_to_nat(1u);
v___x_6282_ = lean_nat_add(v_fst_6277_, v___x_6281_);
lean_dec(v_fst_6277_);
v_as_6270_ = v___x_6280_;
v_lo_6271_ = v___x_6282_;
goto _start;
}
else
{
lean_dec(v_fst_6277_);
lean_dec(v_lo_6271_);
return v_snd_6278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6304_, lean_object* v_as_6305_, lean_object* v_lo_6306_, lean_object* v_hi_6307_){
_start:
{
lean_object* v_res_6308_; 
v_res_6308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6304_, v_as_6305_, v_lo_6306_, v_hi_6307_);
lean_dec(v_hi_6307_);
lean_dec(v_n_6304_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6309_, lean_object* v___x_6310_, lean_object* v_n_6311_, lean_object* v_j_6312_, lean_object* v_a_6313_){
_start:
{
lean_object* v_zero_6314_; uint8_t v_isZero_6315_; 
v_zero_6314_ = lean_unsigned_to_nat(0u);
v_isZero_6315_ = lean_nat_dec_eq(v_j_6312_, v_zero_6314_);
if (v_isZero_6315_ == 1)
{
lean_dec(v_j_6312_);
return v_a_6313_;
}
else
{
lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v_toSignature_6318_; lean_object* v_name_6319_; lean_object* v___x_6320_; lean_object* v_one_6321_; lean_object* v_n_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; 
v___x_6316_ = lean_nat_sub(v_n_6311_, v_j_6312_);
v___x_6317_ = lean_array_fget_borrowed(v___y_6309_, v___x_6316_);
v_toSignature_6318_ = lean_ctor_get(v___x_6317_, 0);
v_name_6319_ = lean_ctor_get(v_toSignature_6318_, 0);
v___x_6320_ = lean_box(0);
v_one_6321_ = lean_unsigned_to_nat(1u);
v_n_6322_ = lean_nat_sub(v_j_6312_, v_one_6321_);
lean_dec(v_j_6312_);
v___x_6323_ = lean_array_get_borrowed(v___x_6320_, v___x_6310_, v___x_6316_);
lean_dec(v___x_6316_);
lean_inc(v___x_6323_);
lean_inc(v_name_6319_);
v___x_6324_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6313_, v_name_6319_, v___x_6323_);
v_j_6312_ = v_n_6322_;
v_a_6313_ = v___x_6324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6326_, lean_object* v___x_6327_, lean_object* v_n_6328_, lean_object* v_j_6329_, lean_object* v_a_6330_){
_start:
{
lean_object* v_res_6331_; 
v_res_6331_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6326_, v___x_6327_, v_n_6328_, v_j_6329_, v_a_6330_);
lean_dec(v_n_6328_);
lean_dec_ref(v___x_6327_);
lean_dec_ref(v___y_6326_);
return v_res_6331_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6332_; 
v___x_6332_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6332_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; 
v___x_6333_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6334_, 0, v___x_6333_);
return v___x_6334_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6335_; lean_object* v___x_6336_; 
v___x_6335_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6336_, 0, v___x_6335_);
lean_ctor_set(v___x_6336_, 1, v___x_6335_);
return v___x_6336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_){
_start:
{
lean_object* v___y_6346_; lean_object* v___y_6347_; size_t v___y_6348_; size_t v___y_6349_; lean_object* v___y_6350_; lean_object* v___y_6351_; lean_object* v___y_6385_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v___y_6388_; lean_object* v___y_6389_; lean_object* v___y_6390_; lean_object* v___y_6391_; lean_object* v___y_6392_; uint8_t v___y_6393_; lean_object* v___y_6394_; size_t v___y_6395_; size_t v___y_6396_; uint8_t v___y_6397_; lean_object* v___y_6398_; lean_object* v_a_6399_; lean_object* v___y_6409_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v___y_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; uint8_t v___y_6417_; lean_object* v___y_6418_; size_t v___y_6419_; size_t v___y_6420_; uint8_t v___y_6421_; lean_object* v___y_6422_; lean_object* v_a_6423_; lean_object* v___x_6435_; lean_object* v___y_6437_; lean_object* v___y_6438_; lean_object* v___y_6439_; lean_object* v___y_6440_; lean_object* v___y_6441_; lean_object* v___y_6442_; uint8_t v___y_6443_; lean_object* v___y_6444_; size_t v___y_6445_; size_t v___y_6446_; uint8_t v___y_6447_; lean_object* v___y_6448_; lean_object* v___y_6490_; lean_object* v___x_6512_; lean_object* v___y_6514_; lean_object* v___y_6515_; uint8_t v___x_6517_; 
v___x_6435_ = lean_unsigned_to_nat(0u);
v___x_6512_ = lean_array_get_size(v_decls_6339_);
v___x_6517_ = lean_nat_dec_eq(v___x_6512_, v___x_6435_);
if (v___x_6517_ == 0)
{
lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___y_6521_; uint8_t v___x_6523_; 
v___x_6518_ = lean_unsigned_to_nat(1u);
v___x_6519_ = lean_nat_sub(v___x_6512_, v___x_6518_);
v___x_6523_ = lean_nat_dec_le(v___x_6435_, v___x_6519_);
if (v___x_6523_ == 0)
{
lean_inc(v___x_6519_);
v___y_6521_ = v___x_6519_;
goto v___jp_6520_;
}
else
{
v___y_6521_ = v___x_6435_;
goto v___jp_6520_;
}
v___jp_6520_:
{
uint8_t v___x_6522_; 
v___x_6522_ = lean_nat_dec_le(v___y_6521_, v___x_6519_);
if (v___x_6522_ == 0)
{
lean_dec(v___x_6519_);
lean_inc(v___y_6521_);
v___y_6514_ = v___y_6521_;
v___y_6515_ = v___y_6521_;
goto v___jp_6513_;
}
else
{
v___y_6514_ = v___y_6521_;
v___y_6515_ = v___x_6519_;
goto v___jp_6513_;
}
}
}
else
{
v___y_6490_ = v_decls_6339_;
goto v___jp_6489_;
}
v___jp_6345_:
{
if (lean_obj_tag(v___y_6351_) == 0)
{
lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v_assignments_6354_; lean_object* v_funVals_6355_; lean_object* v_env_6356_; lean_object* v_nextMacroScope_6357_; lean_object* v_ngen_6358_; lean_object* v_auxDeclNGen_6359_; lean_object* v_traceState_6360_; lean_object* v_messages_6361_; lean_object* v_infoState_6362_; lean_object* v_snapshotTasks_6363_; lean_object* v___x_6365_; uint8_t v_isShared_6366_; uint8_t v_isSharedCheck_6374_; 
lean_dec_ref_known(v___y_6351_, 1);
v___x_6352_ = lean_st_ref_get(v___y_6350_);
lean_dec(v___y_6350_);
v___x_6353_ = lean_st_ref_take(v_a_6343_);
v_assignments_6354_ = lean_ctor_get(v___x_6352_, 0);
lean_inc_ref(v_assignments_6354_);
v_funVals_6355_ = lean_ctor_get(v___x_6352_, 1);
lean_inc_ref(v_funVals_6355_);
lean_dec(v___x_6352_);
v_env_6356_ = lean_ctor_get(v___x_6353_, 0);
v_nextMacroScope_6357_ = lean_ctor_get(v___x_6353_, 1);
v_ngen_6358_ = lean_ctor_get(v___x_6353_, 2);
v_auxDeclNGen_6359_ = lean_ctor_get(v___x_6353_, 3);
v_traceState_6360_ = lean_ctor_get(v___x_6353_, 4);
v_messages_6361_ = lean_ctor_get(v___x_6353_, 6);
v_infoState_6362_ = lean_ctor_get(v___x_6353_, 7);
v_snapshotTasks_6363_ = lean_ctor_get(v___x_6353_, 8);
v_isSharedCheck_6374_ = !lean_is_exclusive(v___x_6353_);
if (v_isSharedCheck_6374_ == 0)
{
lean_object* v_unused_6375_; 
v_unused_6375_ = lean_ctor_get(v___x_6353_, 5);
lean_dec(v_unused_6375_);
v___x_6365_ = v___x_6353_;
v_isShared_6366_ = v_isSharedCheck_6374_;
goto v_resetjp_6364_;
}
else
{
lean_inc(v_snapshotTasks_6363_);
lean_inc(v_infoState_6362_);
lean_inc(v_messages_6361_);
lean_inc(v_traceState_6360_);
lean_inc(v_auxDeclNGen_6359_);
lean_inc(v_ngen_6358_);
lean_inc(v_nextMacroScope_6357_);
lean_inc(v_env_6356_);
lean_dec(v___x_6353_);
v___x_6365_ = lean_box(0);
v_isShared_6366_ = v_isSharedCheck_6374_;
goto v_resetjp_6364_;
}
v_resetjp_6364_:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6370_; 
lean_inc(v___y_6347_);
v___x_6367_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6346_, v_funVals_6355_, v___y_6347_, v___y_6347_, v_env_6356_);
lean_dec(v___y_6347_);
lean_dec_ref(v_funVals_6355_);
v___x_6368_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6366_ == 0)
{
lean_ctor_set(v___x_6365_, 5, v___x_6368_);
lean_ctor_set(v___x_6365_, 0, v___x_6367_);
v___x_6370_ = v___x_6365_;
goto v_reusejp_6369_;
}
else
{
lean_object* v_reuseFailAlloc_6373_; 
v_reuseFailAlloc_6373_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6373_, 0, v___x_6367_);
lean_ctor_set(v_reuseFailAlloc_6373_, 1, v_nextMacroScope_6357_);
lean_ctor_set(v_reuseFailAlloc_6373_, 2, v_ngen_6358_);
lean_ctor_set(v_reuseFailAlloc_6373_, 3, v_auxDeclNGen_6359_);
lean_ctor_set(v_reuseFailAlloc_6373_, 4, v_traceState_6360_);
lean_ctor_set(v_reuseFailAlloc_6373_, 5, v___x_6368_);
lean_ctor_set(v_reuseFailAlloc_6373_, 6, v_messages_6361_);
lean_ctor_set(v_reuseFailAlloc_6373_, 7, v_infoState_6362_);
lean_ctor_set(v_reuseFailAlloc_6373_, 8, v_snapshotTasks_6363_);
v___x_6370_ = v_reuseFailAlloc_6373_;
goto v_reusejp_6369_;
}
v_reusejp_6369_:
{
lean_object* v___x_6371_; lean_object* v___x_6372_; 
v___x_6371_ = lean_st_ref_set(v_a_6343_, v___x_6370_);
v___x_6372_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6354_, v___y_6349_, v___y_6348_, v___y_6346_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
lean_dec_ref(v_assignments_6354_);
return v___x_6372_;
}
}
}
else
{
lean_object* v_a_6376_; lean_object* v___x_6378_; uint8_t v_isShared_6379_; uint8_t v_isSharedCheck_6383_; 
lean_dec(v___y_6350_);
lean_dec(v___y_6347_);
lean_dec_ref(v___y_6346_);
v_a_6376_ = lean_ctor_get(v___y_6351_, 0);
v_isSharedCheck_6383_ = !lean_is_exclusive(v___y_6351_);
if (v_isSharedCheck_6383_ == 0)
{
v___x_6378_ = v___y_6351_;
v_isShared_6379_ = v_isSharedCheck_6383_;
goto v_resetjp_6377_;
}
else
{
lean_inc(v_a_6376_);
lean_dec(v___y_6351_);
v___x_6378_ = lean_box(0);
v_isShared_6379_ = v_isSharedCheck_6383_;
goto v_resetjp_6377_;
}
v_resetjp_6377_:
{
lean_object* v___x_6381_; 
if (v_isShared_6379_ == 0)
{
v___x_6381_ = v___x_6378_;
goto v_reusejp_6380_;
}
else
{
lean_object* v_reuseFailAlloc_6382_; 
v_reuseFailAlloc_6382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_a_6376_);
v___x_6381_ = v_reuseFailAlloc_6382_;
goto v_reusejp_6380_;
}
v_reusejp_6380_:
{
return v___x_6381_;
}
}
}
}
v___jp_6384_:
{
lean_object* v___x_6400_; double v___x_6401_; double v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6400_ = lean_io_get_num_heartbeats();
v___x_6401_ = lean_float_of_nat(v___y_6388_);
v___x_6402_ = lean_float_of_nat(v___x_6400_);
v___x_6403_ = lean_box_float(v___x_6401_);
v___x_6404_ = lean_box_float(v___x_6402_);
v___x_6405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6405_, 0, v___x_6403_);
lean_ctor_set(v___x_6405_, 1, v___x_6404_);
v___x_6406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6406_, 0, v_a_6399_);
lean_ctor_set(v___x_6406_, 1, v___x_6405_);
lean_inc_ref(v___y_6391_);
lean_inc(v___y_6392_);
v___x_6407_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6392_, v___y_6393_, v___y_6391_, v___y_6398_, v___y_6397_, v___y_6389_, v___y_6385_, v___x_6406_, v___y_6394_, v___y_6387_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
lean_dec_ref(v___y_6394_);
v___y_6346_ = v___y_6386_;
v___y_6347_ = v___y_6390_;
v___y_6348_ = v___y_6395_;
v___y_6349_ = v___y_6396_;
v___y_6350_ = v___y_6387_;
v___y_6351_ = v___x_6407_;
goto v___jp_6345_;
}
v___jp_6408_:
{
lean_object* v___x_6424_; double v___x_6425_; double v___x_6426_; double v___x_6427_; double v___x_6428_; double v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6424_ = lean_io_mono_nanos_now();
v___x_6425_ = lean_float_of_nat(v___y_6414_);
v___x_6426_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6427_ = lean_float_div(v___x_6425_, v___x_6426_);
v___x_6428_ = lean_float_of_nat(v___x_6424_);
v___x_6429_ = lean_float_div(v___x_6428_, v___x_6426_);
v___x_6430_ = lean_box_float(v___x_6427_);
v___x_6431_ = lean_box_float(v___x_6429_);
v___x_6432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6432_, 0, v___x_6430_);
lean_ctor_set(v___x_6432_, 1, v___x_6431_);
v___x_6433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6433_, 0, v_a_6423_);
lean_ctor_set(v___x_6433_, 1, v___x_6432_);
lean_inc_ref(v___y_6415_);
lean_inc(v___y_6416_);
v___x_6434_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6416_, v___y_6417_, v___y_6415_, v___y_6422_, v___y_6421_, v___y_6412_, v___y_6409_, v___x_6433_, v___y_6418_, v___y_6411_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
lean_dec_ref(v___y_6418_);
v___y_6346_ = v___y_6410_;
v___y_6347_ = v___y_6413_;
v___y_6348_ = v___y_6419_;
v___y_6349_ = v___y_6420_;
v___y_6350_ = v___y_6411_;
v___y_6351_ = v___x_6434_;
goto v___jp_6345_;
}
v___jp_6436_:
{
lean_object* v___x_6449_; lean_object* v_a_6450_; lean_object* v___x_6451_; uint8_t v___x_6452_; 
v___x_6449_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6343_);
v_a_6450_ = lean_ctor_get(v___x_6449_, 0);
lean_inc(v_a_6450_);
lean_dec_ref(v___x_6449_);
v___x_6451_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6452_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6448_, v___x_6451_);
if (v___x_6452_ == 0)
{
lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6453_ = lean_io_mono_nanos_now();
v___x_6454_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6435_, v___y_6444_, v___y_6439_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
if (lean_obj_tag(v___x_6454_) == 0)
{
lean_object* v_a_6455_; lean_object* v___x_6457_; uint8_t v_isShared_6458_; uint8_t v_isSharedCheck_6462_; 
v_a_6455_ = lean_ctor_get(v___x_6454_, 0);
v_isSharedCheck_6462_ = !lean_is_exclusive(v___x_6454_);
if (v_isSharedCheck_6462_ == 0)
{
v___x_6457_ = v___x_6454_;
v_isShared_6458_ = v_isSharedCheck_6462_;
goto v_resetjp_6456_;
}
else
{
lean_inc(v_a_6455_);
lean_dec(v___x_6454_);
v___x_6457_ = lean_box(0);
v_isShared_6458_ = v_isSharedCheck_6462_;
goto v_resetjp_6456_;
}
v_resetjp_6456_:
{
lean_object* v___x_6460_; 
if (v_isShared_6458_ == 0)
{
lean_ctor_set_tag(v___x_6457_, 1);
v___x_6460_ = v___x_6457_;
goto v_reusejp_6459_;
}
else
{
lean_object* v_reuseFailAlloc_6461_; 
v_reuseFailAlloc_6461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6455_);
v___x_6460_ = v_reuseFailAlloc_6461_;
goto v_reusejp_6459_;
}
v_reusejp_6459_:
{
v___y_6409_ = v___y_6437_;
v___y_6410_ = v___y_6438_;
v___y_6411_ = v___y_6439_;
v___y_6412_ = v_a_6450_;
v___y_6413_ = v___y_6440_;
v___y_6414_ = v___x_6453_;
v___y_6415_ = v___y_6441_;
v___y_6416_ = v___y_6442_;
v___y_6417_ = v___y_6443_;
v___y_6418_ = v___y_6444_;
v___y_6419_ = v___y_6445_;
v___y_6420_ = v___y_6446_;
v___y_6421_ = v___y_6447_;
v___y_6422_ = v___y_6448_;
v_a_6423_ = v___x_6460_;
goto v___jp_6408_;
}
}
}
else
{
lean_object* v_a_6463_; lean_object* v___x_6465_; uint8_t v_isShared_6466_; uint8_t v_isSharedCheck_6470_; 
v_a_6463_ = lean_ctor_get(v___x_6454_, 0);
v_isSharedCheck_6470_ = !lean_is_exclusive(v___x_6454_);
if (v_isSharedCheck_6470_ == 0)
{
v___x_6465_ = v___x_6454_;
v_isShared_6466_ = v_isSharedCheck_6470_;
goto v_resetjp_6464_;
}
else
{
lean_inc(v_a_6463_);
lean_dec(v___x_6454_);
v___x_6465_ = lean_box(0);
v_isShared_6466_ = v_isSharedCheck_6470_;
goto v_resetjp_6464_;
}
v_resetjp_6464_:
{
lean_object* v___x_6468_; 
if (v_isShared_6466_ == 0)
{
lean_ctor_set_tag(v___x_6465_, 0);
v___x_6468_ = v___x_6465_;
goto v_reusejp_6467_;
}
else
{
lean_object* v_reuseFailAlloc_6469_; 
v_reuseFailAlloc_6469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6469_, 0, v_a_6463_);
v___x_6468_ = v_reuseFailAlloc_6469_;
goto v_reusejp_6467_;
}
v_reusejp_6467_:
{
v___y_6409_ = v___y_6437_;
v___y_6410_ = v___y_6438_;
v___y_6411_ = v___y_6439_;
v___y_6412_ = v_a_6450_;
v___y_6413_ = v___y_6440_;
v___y_6414_ = v___x_6453_;
v___y_6415_ = v___y_6441_;
v___y_6416_ = v___y_6442_;
v___y_6417_ = v___y_6443_;
v___y_6418_ = v___y_6444_;
v___y_6419_ = v___y_6445_;
v___y_6420_ = v___y_6446_;
v___y_6421_ = v___y_6447_;
v___y_6422_ = v___y_6448_;
v_a_6423_ = v___x_6468_;
goto v___jp_6408_;
}
}
}
}
else
{
lean_object* v___x_6471_; lean_object* v___x_6472_; 
v___x_6471_ = lean_io_get_num_heartbeats();
v___x_6472_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6435_, v___y_6444_, v___y_6439_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
if (lean_obj_tag(v___x_6472_) == 0)
{
lean_object* v_a_6473_; lean_object* v___x_6475_; uint8_t v_isShared_6476_; uint8_t v_isSharedCheck_6480_; 
v_a_6473_ = lean_ctor_get(v___x_6472_, 0);
v_isSharedCheck_6480_ = !lean_is_exclusive(v___x_6472_);
if (v_isSharedCheck_6480_ == 0)
{
v___x_6475_ = v___x_6472_;
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
else
{
lean_inc(v_a_6473_);
lean_dec(v___x_6472_);
v___x_6475_ = lean_box(0);
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
v_resetjp_6474_:
{
lean_object* v___x_6478_; 
if (v_isShared_6476_ == 0)
{
lean_ctor_set_tag(v___x_6475_, 1);
v___x_6478_ = v___x_6475_;
goto v_reusejp_6477_;
}
else
{
lean_object* v_reuseFailAlloc_6479_; 
v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_a_6473_);
v___x_6478_ = v_reuseFailAlloc_6479_;
goto v_reusejp_6477_;
}
v_reusejp_6477_:
{
v___y_6385_ = v___y_6437_;
v___y_6386_ = v___y_6438_;
v___y_6387_ = v___y_6439_;
v___y_6388_ = v___x_6471_;
v___y_6389_ = v_a_6450_;
v___y_6390_ = v___y_6440_;
v___y_6391_ = v___y_6441_;
v___y_6392_ = v___y_6442_;
v___y_6393_ = v___y_6443_;
v___y_6394_ = v___y_6444_;
v___y_6395_ = v___y_6445_;
v___y_6396_ = v___y_6446_;
v___y_6397_ = v___y_6447_;
v___y_6398_ = v___y_6448_;
v_a_6399_ = v___x_6478_;
goto v___jp_6384_;
}
}
}
else
{
lean_object* v_a_6481_; lean_object* v___x_6483_; uint8_t v_isShared_6484_; uint8_t v_isSharedCheck_6488_; 
v_a_6481_ = lean_ctor_get(v___x_6472_, 0);
v_isSharedCheck_6488_ = !lean_is_exclusive(v___x_6472_);
if (v_isSharedCheck_6488_ == 0)
{
v___x_6483_ = v___x_6472_;
v_isShared_6484_ = v_isSharedCheck_6488_;
goto v_resetjp_6482_;
}
else
{
lean_inc(v_a_6481_);
lean_dec(v___x_6472_);
v___x_6483_ = lean_box(0);
v_isShared_6484_ = v_isSharedCheck_6488_;
goto v_resetjp_6482_;
}
v_resetjp_6482_:
{
lean_object* v___x_6486_; 
if (v_isShared_6484_ == 0)
{
lean_ctor_set_tag(v___x_6483_, 0);
v___x_6486_ = v___x_6483_;
goto v_reusejp_6485_;
}
else
{
lean_object* v_reuseFailAlloc_6487_; 
v_reuseFailAlloc_6487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6487_, 0, v_a_6481_);
v___x_6486_ = v_reuseFailAlloc_6487_;
goto v_reusejp_6485_;
}
v_reusejp_6485_:
{
v___y_6385_ = v___y_6437_;
v___y_6386_ = v___y_6438_;
v___y_6387_ = v___y_6439_;
v___y_6388_ = v___x_6471_;
v___y_6389_ = v_a_6450_;
v___y_6390_ = v___y_6440_;
v___y_6391_ = v___y_6441_;
v___y_6392_ = v___y_6442_;
v___y_6393_ = v___y_6443_;
v___y_6394_ = v___y_6444_;
v___y_6395_ = v___y_6445_;
v___y_6396_ = v___y_6446_;
v___y_6397_ = v___y_6447_;
v___y_6398_ = v___y_6448_;
v_a_6399_ = v___x_6486_;
goto v___jp_6384_;
}
}
}
}
}
v___jp_6489_:
{
size_t v_sz_6491_; size_t v___x_6492_; lean_object* v_assignments_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v_funVals_6496_; lean_object* v_state_6497_; lean_object* v___x_6498_; lean_object* v_options_6499_; lean_object* v_inheritedTraceOptions_6500_; uint8_t v_hasTrace_6501_; lean_object* v_ctx_6502_; 
v_sz_6491_ = lean_array_size(v___y_6490_);
v___x_6492_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6490_, 2);
v_assignments_6493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6491_, v___x_6492_, v___y_6490_);
v___x_6494_ = lean_array_get_size(v___y_6490_);
v___x_6495_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6496_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6490_, v___x_6494_, v___x_6494_, v___x_6495_);
v_state_6497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6497_, 0, v_assignments_6493_);
lean_ctor_set(v_state_6497_, 1, v_funVals_6496_);
v___x_6498_ = lean_st_mk_ref(v_state_6497_);
v_options_6499_ = lean_ctor_get(v_a_6342_, 2);
v_inheritedTraceOptions_6500_ = lean_ctor_get(v_a_6342_, 13);
v_hasTrace_6501_ = lean_ctor_get_uint8(v_options_6499_, sizeof(void*)*1);
v_ctx_6502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6502_, 0, v___y_6490_);
lean_ctor_set(v_ctx_6502_, 1, v___x_6435_);
if (v_hasTrace_6501_ == 0)
{
lean_object* v___x_6503_; 
v___x_6503_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6435_, v_ctx_6502_, v___x_6498_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
lean_dec_ref_known(v_ctx_6502_, 2);
v___y_6346_ = v___y_6490_;
v___y_6347_ = v___x_6494_;
v___y_6348_ = v___x_6492_;
v___y_6349_ = v_sz_6491_;
v___y_6350_ = v___x_6498_;
v___y_6351_ = v___x_6503_;
goto v___jp_6345_;
}
else
{
lean_object* v___f_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; uint8_t v___x_6508_; 
lean_inc_ref(v___y_6490_);
v___f_6504_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6504_, 0, v___y_6490_);
v___x_6505_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6506_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6507_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6508_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6500_, v_options_6499_, v___x_6507_);
if (v___x_6508_ == 0)
{
lean_object* v___x_6509_; uint8_t v___x_6510_; 
v___x_6509_ = l_Lean_trace_profiler;
v___x_6510_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6499_, v___x_6509_);
if (v___x_6510_ == 0)
{
lean_object* v___x_6511_; 
lean_dec_ref(v___f_6504_);
v___x_6511_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6435_, v_ctx_6502_, v___x_6498_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
lean_dec_ref_known(v_ctx_6502_, 2);
v___y_6346_ = v___y_6490_;
v___y_6347_ = v___x_6494_;
v___y_6348_ = v___x_6492_;
v___y_6349_ = v_sz_6491_;
v___y_6350_ = v___x_6498_;
v___y_6351_ = v___x_6511_;
goto v___jp_6345_;
}
else
{
v___y_6437_ = v___f_6504_;
v___y_6438_ = v___y_6490_;
v___y_6439_ = v___x_6498_;
v___y_6440_ = v___x_6494_;
v___y_6441_ = v___x_6506_;
v___y_6442_ = v___x_6505_;
v___y_6443_ = v_hasTrace_6501_;
v___y_6444_ = v_ctx_6502_;
v___y_6445_ = v___x_6492_;
v___y_6446_ = v_sz_6491_;
v___y_6447_ = v___x_6508_;
v___y_6448_ = v_options_6499_;
goto v___jp_6436_;
}
}
else
{
v___y_6437_ = v___f_6504_;
v___y_6438_ = v___y_6490_;
v___y_6439_ = v___x_6498_;
v___y_6440_ = v___x_6494_;
v___y_6441_ = v___x_6506_;
v___y_6442_ = v___x_6505_;
v___y_6443_ = v_hasTrace_6501_;
v___y_6444_ = v_ctx_6502_;
v___y_6445_ = v___x_6492_;
v___y_6446_ = v_sz_6491_;
v___y_6447_ = v___x_6508_;
v___y_6448_ = v_options_6499_;
goto v___jp_6436_;
}
}
}
v___jp_6513_:
{
lean_object* v___x_6516_; 
v___x_6516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6512_, v_decls_6339_, v___y_6514_, v___y_6515_);
lean_dec(v___y_6515_);
v___y_6490_ = v___x_6516_;
goto v___jp_6489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6524_, lean_object* v_a_6525_, lean_object* v_a_6526_, lean_object* v_a_6527_, lean_object* v_a_6528_, lean_object* v_a_6529_){
_start:
{
lean_object* v_res_6530_; 
v_res_6530_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6524_, v_a_6525_, v_a_6526_, v_a_6527_, v_a_6528_);
lean_dec(v_a_6528_);
lean_dec_ref(v_a_6527_);
lean_dec(v_a_6526_);
lean_dec_ref(v_a_6525_);
return v_res_6530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6531_, lean_object* v_n_6532_, lean_object* v_j_6533_, lean_object* v_a_6534_, lean_object* v_a_6535_){
_start:
{
lean_object* v___x_6536_; 
v___x_6536_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6531_, v_n_6532_, v_j_6533_, v_a_6535_);
return v___x_6536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6537_, lean_object* v_n_6538_, lean_object* v_j_6539_, lean_object* v_a_6540_, lean_object* v_a_6541_){
_start:
{
lean_object* v_res_6542_; 
v_res_6542_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6537_, v_n_6538_, v_j_6539_, v_a_6540_, v_a_6541_);
lean_dec(v_n_6538_);
lean_dec_ref(v___y_6537_);
return v_res_6542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6543_, lean_object* v___x_6544_, lean_object* v_n_6545_, lean_object* v_j_6546_, lean_object* v_a_6547_, lean_object* v_a_6548_){
_start:
{
lean_object* v___x_6549_; 
v___x_6549_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6543_, v___x_6544_, v_n_6545_, v_j_6546_, v_a_6548_);
return v___x_6549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6550_, lean_object* v___x_6551_, lean_object* v_n_6552_, lean_object* v_j_6553_, lean_object* v_a_6554_, lean_object* v_a_6555_){
_start:
{
lean_object* v_res_6556_; 
v_res_6556_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6550_, v___x_6551_, v_n_6552_, v_j_6553_, v_a_6554_, v_a_6555_);
lean_dec(v_n_6552_);
lean_dec_ref(v___x_6551_);
lean_dec_ref(v___y_6550_);
return v_res_6556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6557_, lean_object* v_as_6558_, size_t v_sz_6559_, size_t v_i_6560_, lean_object* v_bs_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_){
_start:
{
lean_object* v___x_6567_; 
v___x_6567_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6557_, v_sz_6559_, v_i_6560_, v_bs_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_);
return v___x_6567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6568_, lean_object* v_as_6569_, lean_object* v_sz_6570_, lean_object* v_i_6571_, lean_object* v_bs_6572_, lean_object* v___y_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_){
_start:
{
size_t v_sz_boxed_6578_; size_t v_i_boxed_6579_; lean_object* v_res_6580_; 
v_sz_boxed_6578_ = lean_unbox_usize(v_sz_6570_);
lean_dec(v_sz_6570_);
v_i_boxed_6579_ = lean_unbox_usize(v_i_6571_);
lean_dec(v_i_6571_);
v_res_6580_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6568_, v_as_6569_, v_sz_boxed_6578_, v_i_boxed_6579_, v_bs_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_);
lean_dec(v___y_6576_);
lean_dec_ref(v___y_6575_);
lean_dec(v___y_6574_);
lean_dec_ref(v___y_6573_);
lean_dec_ref(v_as_6569_);
lean_dec_ref(v___x_6568_);
return v_res_6580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6581_, lean_object* v_as_6582_, lean_object* v_lo_6583_, lean_object* v_hi_6584_, lean_object* v_w_6585_, lean_object* v_hlo_6586_, lean_object* v_hhi_6587_){
_start:
{
lean_object* v___x_6588_; 
v___x_6588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6581_, v_as_6582_, v_lo_6583_, v_hi_6584_);
return v___x_6588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6589_, lean_object* v_as_6590_, lean_object* v_lo_6591_, lean_object* v_hi_6592_, lean_object* v_w_6593_, lean_object* v_hlo_6594_, lean_object* v_hhi_6595_){
_start:
{
lean_object* v_res_6596_; 
v_res_6596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6589_, v_as_6590_, v_lo_6591_, v_hi_6592_, v_w_6593_, v_hlo_6594_, v_hhi_6595_);
lean_dec(v_hi_6592_);
lean_dec(v_n_6589_);
return v_res_6596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6597_, lean_object* v_lo_6598_, lean_object* v_hi_6599_, lean_object* v_hhi_6600_, lean_object* v_pivot_6601_, lean_object* v_as_6602_, lean_object* v_i_6603_, lean_object* v_k_6604_, lean_object* v_ilo_6605_, lean_object* v_ik_6606_, lean_object* v_w_6607_){
_start:
{
lean_object* v___x_6608_; 
v___x_6608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6599_, v_pivot_6601_, v_as_6602_, v_i_6603_, v_k_6604_);
return v___x_6608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6609_, lean_object* v_lo_6610_, lean_object* v_hi_6611_, lean_object* v_hhi_6612_, lean_object* v_pivot_6613_, lean_object* v_as_6614_, lean_object* v_i_6615_, lean_object* v_k_6616_, lean_object* v_ilo_6617_, lean_object* v_ik_6618_, lean_object* v_w_6619_){
_start:
{
lean_object* v_res_6620_; 
v_res_6620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6609_, v_lo_6610_, v_hi_6611_, v_hhi_6612_, v_pivot_6613_, v_as_6614_, v_i_6615_, v_k_6616_, v_ilo_6617_, v_ik_6618_, v_w_6619_);
lean_dec(v_hi_6611_);
lean_dec(v_lo_6610_);
lean_dec(v_n_6609_);
return v_res_6620_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; 
v___x_6680_ = lean_unsigned_to_nat(3955956072u);
v___x_6681_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6682_ = l_Lean_Name_num___override(v___x_6681_, v___x_6680_);
return v___x_6682_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; 
v___x_6684_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6685_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6686_ = l_Lean_Name_str___override(v___x_6685_, v___x_6684_);
return v___x_6686_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v___x_6688_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6689_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6690_ = l_Lean_Name_str___override(v___x_6689_, v___x_6688_);
return v___x_6690_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; 
v___x_6691_ = lean_unsigned_to_nat(2u);
v___x_6692_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6693_ = l_Lean_Name_num___override(v___x_6692_, v___x_6691_);
return v___x_6693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6695_; uint8_t v___x_6696_; lean_object* v___x_6697_; lean_object* v___x_6698_; 
v___x_6695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6696_ = 1;
v___x_6697_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6698_ = l_Lean_registerTraceClass(v___x_6695_, v___x_6696_, v___x_6697_);
return v___x_6698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6699_){
_start:
{
lean_object* v_res_6700_; 
v_res_6700_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6700_;
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
