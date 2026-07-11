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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___closed__0_value;
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
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0;
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(lean_object* v_v_331_){
_start:
{
lean_object* v___x_332_; uint8_t v___x_333_; uint8_t v___x_334_; 
v___x_332_ = lean_box(1);
v___x_333_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_v_331_, v___x_332_);
v___x_334_ = lean_bool_not(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed(lean_object* v_v_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(v_v_335_);
lean_dec(v_v_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(lean_object* v_value_339_){
_start:
{
if (lean_obj_tag(v_value_339_) == 2)
{
lean_object* v_vs_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_367_; 
v_vs_340_ = lean_ctor_get(v_value_339_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_value_339_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v_value_339_, 0);
lean_dec(v_unused_368_);
v___x_342_ = v_value_339_;
v_isShared_343_ = v_isSharedCheck_367_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_vs_340_);
lean_dec(v_value_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_367_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___x_354_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_array_get_size(v_vs_340_);
v___f_346_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_347_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_348_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_349_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_350_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_351_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_352_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 0);
lean_ctor_set(v___x_342_, 1, v___f_347_);
lean_ctor_set(v___x_342_, 0, v___f_346_);
v___x_354_ = v___x_342_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___f_346_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___f_347_);
v___x_354_ = v_reuseFailAlloc_366_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___f_348_);
lean_ctor_set(v___x_355_, 2, v___f_349_);
lean_ctor_set(v___x_355_, 3, v___f_350_);
lean_ctor_set(v___x_355_, 4, v___f_351_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___f_352_);
v___x_357_ = lean_nat_dec_lt(v___x_344_, v___x_345_);
if (v___x_357_ == 0)
{
uint8_t v___x_358_; 
lean_dec_ref_known(v___x_356_, 2);
lean_dec_ref(v_vs_340_);
v___x_358_ = lean_bool_not(v___x_357_);
return v___x_358_;
}
else
{
if (v___x_357_ == 0)
{
uint8_t v___x_359_; 
lean_dec_ref_known(v___x_356_, 2);
lean_dec_ref(v_vs_340_);
v___x_359_ = lean_bool_not(v___x_357_);
return v___x_359_;
}
else
{
lean_object* v___f_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; uint8_t v___x_365_; 
v___f_360_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___closed__0));
v___x_361_ = ((size_t)0ULL);
v___x_362_ = lean_usize_of_nat(v___x_345_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_356_, v___f_360_, v_vs_340_, v___x_361_, v___x_362_);
v___x_364_ = lean_unbox(v___x_363_);
lean_dec(v___x_363_);
v___x_365_ = lean_bool_not(v___x_364_);
return v___x_365_;
}
}
}
}
}
else
{
uint8_t v___x_369_; 
lean_dec(v_value_339_);
v___x_369_ = 0;
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___boxed(lean_object* v_value_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(v_value_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(lean_object* v_msg_373_){
_start:
{
lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___f_374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_379_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_380_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___f_374_);
lean_ctor_set(v___x_381_, 1, v___f_375_);
v___x_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___f_376_);
lean_ctor_set(v___x_382_, 2, v___f_377_);
lean_ctor_set(v___x_382_, 3, v___f_378_);
lean_ctor_set(v___x_382_, 4, v___f_379_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___f_380_);
v___x_384_ = lean_box(0);
v___x_385_ = l_instInhabitedOfMonad___redArg(v___x_383_, v___x_384_);
v___x_386_ = lean_panic_fn_borrowed(v___x_385_, v_msg_373_);
lean_dec(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(lean_object* v_as_387_, size_t v_i_388_, size_t v_stop_389_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = lean_usize_dec_eq(v_i_388_, v_stop_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; uint8_t v___x_394_; 
v___x_391_ = lean_array_uget_borrowed(v_as_387_, v_i_388_);
v___x_392_ = lean_box(1);
v___x_393_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_391_, v___x_392_);
v___x_394_ = lean_bool_not(v___x_393_);
if (v___x_394_ == 0)
{
size_t v___x_395_; size_t v___x_396_; 
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_388_, v___x_395_);
v_i_388_ = v___x_396_;
goto _start;
}
else
{
return v___x_394_;
}
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0___boxed(lean_object* v_as_399_, lean_object* v_i_400_, lean_object* v_stop_401_){
_start:
{
size_t v_i_boxed_402_; size_t v_stop_boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_i_boxed_402_ = lean_unbox_usize(v_i_400_);
lean_dec(v_i_400_);
v_stop_boxed_403_ = lean_unbox_usize(v_stop_401_);
lean_dec(v_stop_401_);
v_res_404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_as_399_, v_i_boxed_402_, v_stop_boxed_403_);
lean_dec_ref(v_as_399_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 1;
return v___x_407_;
}
else
{
lean_object* v_head_408_; lean_object* v_tail_409_; uint8_t v___y_411_; 
v_head_408_ = lean_ctor_get(v_x_406_, 0);
v_tail_409_ = lean_ctor_get(v_x_406_, 1);
if (lean_obj_tag(v_head_408_) == 2)
{
lean_object* v_vs_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_vs_413_ = lean_ctor_get(v_head_408_, 1);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_vs_413_);
v___x_416_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = lean_bool_not(v___x_416_);
v___y_411_ = v___x_417_;
goto v___jp_410_;
}
else
{
if (v___x_416_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = lean_bool_not(v___x_416_);
v___y_411_ = v___x_418_;
goto v___jp_410_;
}
else
{
size_t v___x_419_; size_t v___x_420_; uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_419_ = ((size_t)0ULL);
v___x_420_ = lean_usize_of_nat(v___x_415_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_413_, v___x_419_, v___x_420_);
v___x_422_ = lean_bool_not(v___x_421_);
v___y_411_ = v___x_422_;
goto v___jp_410_;
}
}
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
v___jp_410_:
{
if (v___y_411_ == 0)
{
return v___y_411_;
}
else
{
v_x_406_ = v_tail_409_;
goto _start;
}
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
lean_object* v___y_514_; lean_object* v___y_515_; uint8_t v___y_516_; lean_object* v___y_521_; lean_object* v_i_522_; lean_object* v_vs_523_; 
switch(lean_obj_tag(v_v1_511_))
{
case 0:
{
switch(lean_obj_tag(v_v2_512_))
{
case 2:
{
lean_object* v_i_533_; lean_object* v_vs_534_; 
v_i_533_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_i_533_);
v_vs_534_ = lean_ctor_get(v_v2_512_, 1);
lean_inc_ref(v_vs_534_);
v___y_521_ = v_v2_512_;
v_i_522_ = v_i_533_;
v_vs_523_ = v_vs_534_;
goto v___jp_520_;
}
case 3:
{
lean_object* v_vs_535_; lean_object* v___x_536_; 
v_vs_535_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_vs_535_);
lean_dec_ref_known(v_v2_512_, 1);
v___x_536_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v_vs_535_);
return v___x_536_;
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
lean_object* v_i_537_; lean_object* v_vs_538_; 
v_i_537_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_i_537_);
v_vs_538_ = lean_ctor_get(v_v1_511_, 1);
lean_inc_ref(v_vs_538_);
v___y_521_ = v_v1_511_;
v_i_522_ = v_i_537_;
v_vs_523_ = v_vs_538_;
goto v___jp_520_;
}
case 1:
{
lean_dec_ref_known(v_v1_511_, 2);
lean_dec_ref(v_env_510_);
return v_v2_512_;
}
case 2:
{
lean_object* v_i_539_; lean_object* v_vs_540_; lean_object* v_i_541_; lean_object* v_vs_542_; uint8_t v___x_543_; 
v_i_539_ = lean_ctor_get(v_v1_511_, 0);
v_vs_540_ = lean_ctor_get(v_v1_511_, 1);
v_i_541_ = lean_ctor_get(v_v2_512_, 0);
v_vs_542_ = lean_ctor_get(v_v2_512_, 1);
v___x_543_ = lean_name_eq(v_i_539_, v_i_541_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_545_, 0, v_v2_512_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_546_, 0, v_v1_511_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_546_);
return v___x_547_;
}
else
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_557_; 
lean_inc_ref(v_vs_542_);
lean_inc_ref(v_vs_540_);
lean_inc(v_i_539_);
lean_dec_ref_known(v_v1_511_, 2);
v_isSharedCheck_557_ = !lean_is_exclusive(v_v2_512_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_558_ = lean_ctor_get(v_v2_512_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_v2_512_, 0);
lean_dec(v_unused_559_);
v___x_549_ = v_v2_512_;
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_v2_512_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
lean_inc_ref(v_env_510_);
v___x_553_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_510_, v_vs_540_, v_vs_542_, v___x_551_, v___x_552_);
lean_dec_ref(v_vs_542_);
lean_dec_ref(v_vs_540_);
lean_inc_ref(v___x_553_);
lean_inc(v_i_539_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_553_);
lean_ctor_set(v___x_549_, 0, v_i_539_);
v___x_555_ = v___x_549_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_i_539_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v___y_521_ = v___x_555_;
v_i_522_ = v_i_539_;
v_vs_523_ = v___x_553_;
goto v___jp_520_;
}
}
}
}
default: 
{
lean_object* v_vs_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_vs_560_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_vs_560_);
lean_dec_ref_known(v_v2_512_, 1);
lean_inc_ref(v_env_510_);
v___x_561_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_510_, v_vs_560_, v_v1_511_);
v___x_562_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_561_);
return v___x_562_;
}
}
}
default: 
{
switch(lean_obj_tag(v_v2_512_))
{
case 0:
{
lean_object* v_vs_563_; lean_object* v___x_564_; 
v_vs_563_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_vs_563_);
lean_dec_ref_known(v_v1_511_, 1);
v___x_564_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v_vs_563_);
return v___x_564_;
}
case 1:
{
lean_dec_ref_known(v_v1_511_, 1);
lean_dec_ref(v_env_510_);
return v_v2_512_;
}
case 3:
{
lean_object* v_vs_565_; lean_object* v_vs_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_vs_565_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_vs_565_);
lean_dec_ref_known(v_v1_511_, 1);
v_vs_566_ = lean_ctor_get(v_v2_512_, 0);
lean_inc(v_vs_566_);
lean_dec_ref_known(v_v2_512_, 1);
lean_inc_ref(v_env_510_);
v___x_567_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(v_env_510_, v_vs_566_, v_vs_565_);
v___x_568_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_567_);
return v___x_568_;
}
default: 
{
lean_object* v_vs_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_vs_569_ = lean_ctor_get(v_v1_511_, 0);
lean_inc(v_vs_569_);
lean_dec_ref_known(v_v1_511_, 1);
lean_inc_ref(v_env_510_);
v___x_570_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_510_, v_vs_569_, v_v2_512_);
v___x_571_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_510_, v___x_570_);
return v___x_571_;
}
}
}
}
v___jp_513_:
{
if (v___y_516_ == 0)
{
lean_dec(v___y_514_);
lean_dec_ref(v_env_510_);
return v___y_515_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v___y_514_, v_env_510_, v___x_517_);
if (v___x_518_ == 0)
{
return v___y_515_;
}
else
{
lean_object* v___x_519_; 
lean_dec(v___y_515_);
v___x_519_ = lean_box(1);
return v___x_519_;
}
}
}
v___jp_520_:
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_array_get_size(v_vs_523_);
v___x_526_ = lean_nat_dec_lt(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
lean_dec_ref(v_vs_523_);
v___x_527_ = lean_bool_not(v___x_526_);
v___y_514_ = v_i_522_;
v___y_515_ = v___y_521_;
v___y_516_ = v___x_527_;
goto v___jp_513_;
}
else
{
if (v___x_526_ == 0)
{
uint8_t v___x_528_; 
lean_dec_ref(v_vs_523_);
v___x_528_ = lean_bool_not(v___x_526_);
v___y_514_ = v_i_522_;
v___y_515_ = v___y_521_;
v___y_516_ = v___x_528_;
goto v___jp_513_;
}
else
{
size_t v___x_529_; size_t v___x_530_; uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_525_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_523_, v___x_529_, v___x_530_);
lean_dec_ref(v_vs_523_);
v___x_532_ = lean_bool_not(v___x_531_);
v___y_514_ = v_i_522_;
v___y_515_ = v___y_521_;
v___y_516_ = v___x_532_;
goto v___jp_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(lean_object* v_env_572_, lean_object* v_as_573_, lean_object* v_bs_574_, lean_object* v_i_575_, lean_object* v_cs_576_){
_start:
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_array_get_size(v_as_573_);
v___x_578_ = lean_nat_dec_lt(v_i_575_, v___x_577_);
if (v___x_578_ == 0)
{
lean_dec(v_i_575_);
lean_dec_ref(v_env_572_);
return v_cs_576_;
}
else
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_array_get_size(v_bs_574_);
v___x_580_ = lean_nat_dec_lt(v_i_575_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_i_575_);
lean_dec_ref(v_env_572_);
return v_cs_576_;
}
else
{
lean_object* v_a_581_; lean_object* v_b_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_581_ = lean_array_fget_borrowed(v_as_573_, v_i_575_);
v_b_582_ = lean_array_fget_borrowed(v_bs_574_, v_i_575_);
lean_inc(v_b_582_);
lean_inc(v_a_581_);
lean_inc_ref(v_env_572_);
v___x_583_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_572_, v_a_581_, v_b_582_);
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_add(v_i_575_, v___x_584_);
lean_dec(v_i_575_);
v___x_586_ = lean_array_push(v_cs_576_, v___x_583_);
v_i_575_ = v___x_585_;
v_cs_576_ = v___x_586_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(lean_object* v_env_588_, lean_object* v_vs_589_, lean_object* v_v_590_){
_start:
{
if (lean_obj_tag(v_vs_589_) == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_env_588_);
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v_v_590_);
lean_ctor_set(v___x_609_, 1, v_vs_589_);
return v___x_609_;
}
else
{
lean_object* v_head_610_; 
v_head_610_ = lean_ctor_get(v_vs_589_, 0);
if (lean_obj_tag(v_head_610_) == 2)
{
if (lean_obj_tag(v_v_590_) == 2)
{
lean_object* v_tail_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_639_; 
lean_inc_ref(v_head_610_);
v_tail_611_ = lean_ctor_get(v_vs_589_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_vs_589_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v_vs_589_, 0);
lean_dec(v_unused_640_);
v___x_613_ = v_vs_589_;
v_isShared_614_ = v_isSharedCheck_639_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_tail_611_);
lean_dec(v_vs_589_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_639_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_i_615_; lean_object* v_vs_616_; lean_object* v_i_617_; lean_object* v_vs_618_; uint8_t v___x_619_; 
v_i_615_ = lean_ctor_get(v_head_610_, 0);
v_vs_616_ = lean_ctor_get(v_head_610_, 1);
v_i_617_ = lean_ctor_get(v_v_590_, 0);
v_vs_618_ = lean_ctor_get(v_v_590_, 1);
v___x_619_ = lean_name_eq(v_i_615_, v_i_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_588_, v_tail_611_, v_v_590_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_620_);
v___x_622_ = v___x_613_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_head_610_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_636_; 
lean_inc_ref(v_vs_618_);
lean_inc_ref(v_vs_616_);
lean_inc(v_i_615_);
lean_dec_ref_known(v_head_610_, 2);
v_isSharedCheck_636_ = !lean_is_exclusive(v_v_590_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_637_ = lean_ctor_get(v_v_590_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_v_590_, 0);
lean_dec(v_unused_638_);
v___x_625_ = v_v_590_;
v_isShared_626_ = v_isSharedCheck_636_;
goto v_resetjp_624_;
}
else
{
lean_dec(v_v_590_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_636_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
v___x_629_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_588_, v_vs_616_, v_vs_618_, v___x_627_, v___x_628_);
lean_dec_ref(v_vs_618_);
lean_dec_ref(v_vs_616_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_629_);
lean_ctor_set(v___x_625_, 0, v_i_615_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_i_615_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_631_);
v___x_633_ = v___x_613_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_tail_611_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_588_);
goto v___jp_591_;
}
}
else
{
lean_dec_ref(v_env_588_);
goto v___jp_591_;
}
}
v___jp_591_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_592_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_593_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0));
v___x_594_ = lean_unsigned_to_nat(92u);
v___x_595_ = lean_unsigned_to_nat(12u);
v___x_596_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1));
v___x_597_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_590_);
v___x_598_ = l_Std_Format_defWidth;
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = l_Std_Format_pretty(v___x_597_, v___x_598_, v___x_599_, v___x_599_);
v___x_601_ = lean_string_append(v___x_596_, v___x_600_);
lean_dec_ref(v___x_600_);
v___x_602_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2));
v___x_603_ = lean_string_append(v___x_601_, v___x_602_);
v___x_604_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_vs_589_);
v___x_605_ = l_Std_Format_pretty(v___x_604_, v___x_598_, v___x_599_, v___x_599_);
v___x_606_ = lean_string_append(v___x_603_, v___x_605_);
lean_dec_ref(v___x_605_);
v___x_607_ = l_mkPanicMessageWithDecl(v___x_592_, v___x_593_, v___x_594_, v___x_595_, v___x_606_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(v___x_607_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(lean_object* v_env_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_dec_ref(v_env_641_);
return v_x_642_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v___x_646_; 
v_head_644_ = lean_ctor_get(v_x_643_, 0);
lean_inc(v_head_644_);
v_tail_645_ = lean_ctor_get(v_x_643_, 1);
lean_inc(v_tail_645_);
lean_dec_ref_known(v_x_643_, 2);
lean_inc_ref(v_env_641_);
v___x_646_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_641_, v_x_642_, v_head_644_);
v_x_642_ = v___x_646_;
v_x_643_ = v_tail_645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2___boxed(lean_object* v_env_648_, lean_object* v_as_649_, lean_object* v_bs_650_, lean_object* v_i_651_, lean_object* v_cs_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_648_, v_as_649_, v_bs_650_, v_i_651_, v_cs_652_);
lean_dec_ref(v_bs_650_);
lean_dec_ref(v_as_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(lean_object* v_a_654_, lean_object* v_n_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_a_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___boxed(lean_object* v_a_657_, lean_object* v_n_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(v_a_657_, v_n_658_);
lean_dec(v_n_658_);
return v_res_659_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(lean_object* v_a_660_, lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
uint8_t v___x_662_; 
v___x_662_ = 0;
return v___x_662_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; uint8_t v___x_665_; 
v_head_663_ = lean_ctor_get(v_x_661_, 0);
v_tail_664_ = lean_ctor_get(v_x_661_, 1);
v___x_665_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_660_, v_head_663_);
if (v___x_665_ == 0)
{
v_x_661_ = v_tail_664_;
goto _start;
}
else
{
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object* v_a_667_, lean_object* v_x_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v_a_667_, v_x_668_);
lean_dec(v_x_668_);
lean_dec(v_a_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(lean_object* v_env_671_, lean_object* v_forbiddenTypes_x27_672_, lean_object* v_n_673_, size_t v_sz_674_, size_t v_i_675_, lean_object* v_bs_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_lt(v_i_675_, v_sz_674_);
if (v___x_677_ == 0)
{
lean_dec(v_forbiddenTypes_x27_672_);
lean_dec_ref(v_env_671_);
return v_bs_676_;
}
else
{
lean_object* v_v_678_; lean_object* v___x_679_; lean_object* v_bs_x27_680_; lean_object* v___x_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v_v_678_ = lean_array_uget(v_bs_676_, v_i_675_);
v___x_679_ = lean_unsigned_to_nat(0u);
v_bs_x27_680_ = lean_array_uset(v_bs_676_, v_i_675_, v___x_679_);
lean_inc(v_forbiddenTypes_x27_672_);
lean_inc_ref(v_env_671_);
v___x_681_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_671_, v_v_678_, v_forbiddenTypes_x27_672_, v_n_673_);
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_add(v_i_675_, v___x_682_);
v___x_684_ = lean_array_uset(v_bs_x27_680_, v_i_675_, v___x_681_);
v_i_675_ = v___x_683_;
v_bs_676_ = v___x_684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(lean_object* v_env_686_, lean_object* v_v_687_, lean_object* v_forbiddenTypes_688_, lean_object* v_remainingDepth_689_){
_start:
{
lean_object* v_zero_690_; uint8_t v_isZero_691_; 
v_zero_690_ = lean_unsigned_to_nat(0u);
v_isZero_691_ = lean_nat_dec_eq(v_remainingDepth_689_, v_zero_690_);
if (v_isZero_691_ == 1)
{
lean_object* v___x_692_; 
lean_dec(v_forbiddenTypes_688_);
lean_dec(v_v_687_);
lean_dec_ref(v_env_686_);
v___x_692_ = lean_box(1);
return v___x_692_;
}
else
{
lean_object* v_one_693_; lean_object* v_n_694_; 
v_one_693_ = lean_unsigned_to_nat(1u);
v_n_694_ = lean_nat_sub(v_remainingDepth_689_, v_one_693_);
switch(lean_obj_tag(v_v_687_))
{
case 2:
{
lean_object* v_i_695_; lean_object* v_vs_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_715_; 
v_i_695_ = lean_ctor_get(v_v_687_, 0);
v_vs_696_ = lean_ctor_get(v_v_687_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_v_687_);
if (v_isSharedCheck_715_ == 0)
{
v___x_698_ = v_v_687_;
v_isShared_699_ = v_isSharedCheck_715_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_vs_696_);
lean_inc(v_i_695_);
lean_dec(v_v_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_715_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_forbiddenTypes_x27_701_; lean_object* v_induct_708_; lean_object* v_toConstantVal_709_; uint8_t v_isRec_710_; lean_object* v_name_711_; uint8_t v___x_712_; 
lean_inc_ref(v_env_686_);
lean_inc(v_i_695_);
v_induct_708_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_i_695_, v_env_686_);
v_toConstantVal_709_ = lean_ctor_get(v_induct_708_, 0);
lean_inc_ref(v_toConstantVal_709_);
v_isRec_710_ = lean_ctor_get_uint8(v_induct_708_, sizeof(void*)*6);
lean_dec_ref(v_induct_708_);
v_name_711_ = lean_ctor_get(v_toConstantVal_709_, 0);
lean_inc(v_name_711_);
lean_dec_ref(v_toConstantVal_709_);
v___x_712_ = l_Lean_NameSet_contains(v_forbiddenTypes_688_, v_name_711_);
if (v___x_712_ == 0)
{
if (v_isRec_710_ == 0)
{
lean_dec(v_name_711_);
v_forbiddenTypes_x27_701_ = v_forbiddenTypes_688_;
goto v___jp_700_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_NameSet_insert(v_forbiddenTypes_688_, v_name_711_);
v_forbiddenTypes_x27_701_ = v___x_713_;
goto v___jp_700_;
}
}
else
{
lean_object* v___x_714_; 
lean_dec(v_name_711_);
lean_del_object(v___x_698_);
lean_dec_ref(v_vs_696_);
lean_dec(v_i_695_);
lean_dec(v_n_694_);
lean_dec(v_forbiddenTypes_688_);
lean_dec_ref(v_env_686_);
v___x_714_ = lean_box(1);
return v___x_714_;
}
v___jp_700_:
{
size_t v_sz_702_; size_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v_sz_702_ = lean_array_size(v_vs_696_);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_686_, v_forbiddenTypes_x27_701_, v_n_694_, v_sz_702_, v___x_703_, v_vs_696_);
lean_dec(v_n_694_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_704_);
v___x_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_i_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
case 3:
{
lean_object* v_vs_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_727_; 
v_vs_716_ = lean_ctor_get(v_v_687_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_v_687_);
if (v_isSharedCheck_727_ == 0)
{
v___x_718_ = v_v_687_;
v_isShared_719_ = v_isSharedCheck_727_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_vs_716_);
lean_dec(v_v_687_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_727_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v_vs_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_720_ = lean_box(0);
v_vs_721_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_686_, v_forbiddenTypes_688_, v_n_694_, v_vs_716_, v___x_720_);
lean_dec(v_n_694_);
v___x_722_ = lean_box(1);
v___x_723_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v___x_722_, v_vs_721_);
if (v___x_723_ == 0)
{
lean_object* v___x_725_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_vs_721_);
v___x_725_ = v___x_718_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_vs_721_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_dec(v_vs_721_);
lean_del_object(v___x_718_);
return v___x_722_;
}
}
}
default: 
{
lean_dec(v_n_694_);
lean_dec(v_forbiddenTypes_688_);
lean_dec_ref(v_env_686_);
return v_v_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(lean_object* v_env_728_, lean_object* v_forbiddenTypes_729_, lean_object* v_n_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v___x_733_; 
lean_dec(v_forbiddenTypes_729_);
lean_dec_ref(v_env_728_);
v___x_733_ = l_List_reverse___redArg(v_a_732_);
return v___x_733_;
}
else
{
lean_object* v_head_734_; lean_object* v_tail_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_744_; 
v_head_734_ = lean_ctor_get(v_a_731_, 0);
v_tail_735_ = lean_ctor_get(v_a_731_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_731_);
if (v_isSharedCheck_744_ == 0)
{
v___x_737_ = v_a_731_;
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_tail_735_);
lean_inc(v_head_734_);
lean_dec(v_a_731_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_inc(v_forbiddenTypes_729_);
lean_inc_ref(v_env_728_);
v___x_739_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_728_, v_head_734_, v_forbiddenTypes_729_, v_n_730_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v_a_732_);
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_a_732_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
v_a_731_ = v_tail_735_;
v_a_732_ = v___x_741_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object* v_env_745_, lean_object* v_forbiddenTypes_746_, lean_object* v_n_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_745_, v_forbiddenTypes_746_, v_n_747_, v_a_748_, v_a_749_);
lean_dec(v_n_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object* v_env_751_, lean_object* v_forbiddenTypes_x27_752_, lean_object* v_n_753_, lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_bs_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_758_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_751_, v_forbiddenTypes_x27_752_, v_n_753_, v_sz_boxed_757_, v_i_boxed_758_, v_bs_756_);
lean_dec(v_n_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___boxed(lean_object* v_env_760_, lean_object* v_v_761_, lean_object* v_forbiddenTypes_762_, lean_object* v_remainingDepth_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_760_, v_v_761_, v_forbiddenTypes_762_, v_remainingDepth_763_);
lean_dec(v_remainingDepth_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(lean_object* v_env_765_, lean_object* v_v_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = l_Lean_NameSet_empty;
v___x_768_ = lean_unsigned_to_nat(8u);
v___x_769_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_765_, v_v_766_, v___x_767_, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(lean_object* v_env_770_, lean_object* v_v1_771_, lean_object* v_v2_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_inc_ref(v_env_770_);
v___x_773_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_770_, v_v1_771_, v_v2_772_);
v___x_774_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(v_env_770_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
uint8_t v___x_777_; 
v___x_777_ = 0;
return v___x_777_;
}
else
{
lean_object* v_head_778_; lean_object* v_tail_779_; uint8_t v___x_780_; 
v_head_778_ = lean_ctor_get(v_x_776_, 0);
v_tail_779_ = lean_ctor_get(v_x_776_, 1);
v___x_780_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_head_778_, v_x_775_);
if (v___x_780_ == 0)
{
v_x_776_ = v_tail_779_;
goto _start;
}
else
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
switch(lean_obj_tag(v_x_782_))
{
case 2:
{
lean_object* v_i_784_; uint8_t v___x_785_; 
v_i_784_ = lean_ctor_get(v_x_782_, 0);
v___x_785_ = lean_name_eq(v_i_784_, v_x_783_);
return v___x_785_;
}
case 3:
{
lean_object* v_vs_786_; uint8_t v___x_787_; 
v_vs_786_ = lean_ctor_get(v_x_782_, 0);
v___x_787_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_783_, v_vs_786_);
return v___x_787_;
}
default: 
{
uint8_t v___x_788_; 
v___x_788_ = 1;
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_x_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec(v_x_789_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0___boxed(lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_793_, v_x_794_);
lean_dec(v_x_794_);
lean_dec(v_x_793_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(lean_object* v_x_800_, lean_object* v_as_x27_801_, lean_object* v_b_802_){
_start:
{
if (lean_obj_tag(v_as_x27_801_) == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_b_802_);
return v___x_803_;
}
else
{
lean_object* v_head_804_; lean_object* v_tail_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref(v_b_802_);
v_head_804_ = lean_ctor_get(v_as_x27_801_, 0);
v_tail_805_ = lean_ctor_get(v_as_x27_801_, 1);
v___x_806_ = lean_box(0);
v___x_807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_804_) == 2)
{
lean_object* v_i_808_; lean_object* v_vs_809_; uint8_t v___x_810_; 
v_i_808_ = lean_ctor_get(v_head_804_, 0);
v_vs_809_ = lean_ctor_get(v_head_804_, 1);
v___x_810_ = lean_name_eq(v_i_808_, v_x_800_);
if (v___x_810_ == 0)
{
v_as_x27_801_ = v_tail_805_;
v_b_802_ = v___x_807_;
goto _start;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_inc_ref(v_vs_809_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v_vs_809_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_806_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
else
{
v_as_x27_801_ = v_tail_805_;
v_b_802_ = v___x_807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___boxed(lean_object* v_x_816_, lean_object* v_as_x27_817_, lean_object* v_b_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_816_, v_as_x27_817_, v_b_818_);
lean_dec(v_as_x27_817_);
lean_dec(v_x_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
switch(lean_obj_tag(v_x_820_))
{
case 2:
{
lean_object* v_i_822_; lean_object* v_vs_823_; uint8_t v___x_824_; 
v_i_822_ = lean_ctor_get(v_x_820_, 0);
v_vs_823_ = lean_ctor_get(v_x_820_, 1);
v___x_824_ = lean_name_eq(v_i_822_, v_x_821_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v___x_826_; 
lean_inc_ref(v_vs_823_);
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v_vs_823_);
return v___x_826_;
}
}
case 3:
{
lean_object* v_vs_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_val_831_; lean_object* v_fst_832_; 
v_vs_827_ = lean_ctor_get(v_x_820_, 0);
v___x_828_ = lean_box(0);
v___x_829_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
v___x_830_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_821_, v_vs_827_, v___x_829_);
v_val_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_831_);
lean_dec(v___x_830_);
v_fst_832_ = lean_ctor_get(v_val_831_, 0);
lean_inc(v_fst_832_);
lean_dec(v_val_831_);
if (lean_obj_tag(v_fst_832_) == 0)
{
return v___x_828_;
}
else
{
return v_fst_832_;
}
}
default: 
{
lean_object* v___x_833_; 
v___x_833_ = lean_box(0);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs___boxed(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_x_834_, v_x_835_);
lean_dec(v_x_835_);
lean_dec(v_x_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(lean_object* v_x_837_, lean_object* v_as_838_, lean_object* v_as_x27_839_, lean_object* v_b_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_837_, v_as_x27_839_, v_b_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___boxed(lean_object* v_x_843_, lean_object* v_as_844_, lean_object* v_as_x27_845_, lean_object* v_b_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(v_x_843_, v_as_844_, v_as_x27_845_, v_b_846_, v_a_847_);
lean_dec(v_as_x27_845_);
lean_dec(v_as_844_);
lean_dec(v_x_843_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(lean_object* v_a_861_){
_start:
{
lean_object* v_zero_862_; uint8_t v_isZero_863_; 
v_zero_862_ = lean_unsigned_to_nat(0u);
v_isZero_863_ = lean_nat_dec_eq(v_a_861_, v_zero_862_);
if (v_isZero_863_ == 1)
{
lean_object* v___x_864_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3));
return v___x_864_;
}
else
{
lean_object* v_one_865_; lean_object* v_n_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_one_865_ = lean_unsigned_to_nat(1u);
v_n_866_ = lean_nat_sub(v_a_861_, v_one_865_);
v___x_867_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5));
v___x_868_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_866_);
lean_dec(v_n_866_);
v___x_869_ = lean_mk_empty_array_with_capacity(v_one_865_);
v___x_870_ = lean_array_push(v___x_869_, v___x_868_);
v___x_871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_867_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___boxed(lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_a_872_);
lean_dec(v_a_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(lean_object* v_n_874_){
_start:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(8u);
v___x_876_ = lean_nat_dec_lt(v___x_875_, v_n_874_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_874_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; 
v___x_878_ = lean_box(1);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat___boxed(lean_object* v_n_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_n_879_);
lean_dec(v_n_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v_val_882_; lean_object* v___x_883_; 
v_val_882_ = lean_ctor_get(v_x_881_, 0);
v___x_883_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_val_882_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = lean_box(1);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit___boxed(lean_object* v_x_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_x_885_);
lean_dec_ref(v_x_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(lean_object* v_env_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
switch(lean_obj_tag(v_x_888_))
{
case 2:
{
lean_object* v_vs_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
lean_dec_ref(v_env_887_);
v_vs_890_ = lean_ctor_get(v_x_888_, 1);
v___x_891_ = lean_array_get_size(v_vs_890_);
v___x_892_ = lean_nat_dec_lt(v_x_889_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_box(0);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_array_fget_borrowed(v_vs_890_, v_x_889_);
lean_inc(v___x_894_);
return v___x_894_;
}
}
case 3:
{
lean_object* v_vs_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_vs_895_ = lean_ctor_get(v_x_888_, 0);
v___x_896_ = lean_box(0);
v___x_897_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_887_, v_x_889_, v___x_896_, v_vs_895_);
return v___x_897_;
}
default: 
{
lean_dec_ref(v_env_887_);
lean_inc(v_x_888_);
return v_x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(lean_object* v_env_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_dec_ref(v_env_898_);
return v_x_900_;
}
else
{
lean_object* v_head_902_; lean_object* v_tail_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_head_902_ = lean_ctor_get(v_x_901_, 0);
v_tail_903_ = lean_ctor_get(v_x_901_, 1);
lean_inc_ref_n(v_env_898_, 2);
v___x_904_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_898_, v_head_902_, v_x_899_);
v___x_905_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_898_, v_x_900_, v___x_904_);
v_x_900_ = v___x_905_;
v_x_901_ = v_tail_903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0___boxed(lean_object* v_env_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_907_, v_x_908_, v_x_909_, v_x_910_);
lean_dec(v_x_910_);
lean_dec(v_x_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj___boxed(lean_object* v_env_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_912_, v_x_913_, v_x_914_);
lean_dec(v_x_914_);
lean_dec(v_x_913_);
return v_res_915_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(lean_object* v_x_916_){
_start:
{
if (lean_obj_tag(v_x_916_) == 2)
{
lean_object* v_vs_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_vs_917_ = lean_ctor_get(v_x_916_, 1);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_array_get_size(v_vs_917_);
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
v___x_921_ = lean_bool_not(v___x_920_);
return v___x_921_;
}
else
{
if (v___x_920_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = lean_bool_not(v___x_920_);
return v___x_922_;
}
else
{
size_t v___x_923_; size_t v___x_924_; uint8_t v___x_925_; uint8_t v___x_926_; 
v___x_923_ = ((size_t)0ULL);
v___x_924_ = lean_usize_of_nat(v___x_919_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_vs_917_, v___x_923_, v___x_924_);
v___x_926_ = lean_bool_not(v___x_925_);
return v___x_926_;
}
}
}
else
{
uint8_t v___x_927_; 
v___x_927_ = 0;
return v___x_927_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(lean_object* v_as_928_, size_t v_i_929_, size_t v_stop_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_eq(v_i_929_, v_stop_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_array_uget_borrowed(v_as_928_, v_i_929_);
v___x_933_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v___x_932_);
v___x_934_ = lean_bool_not(v___x_933_);
if (v___x_934_ == 0)
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_929_, v___x_935_);
v_i_929_ = v___x_936_;
goto _start;
}
else
{
return v___x_934_;
}
}
else
{
uint8_t v___x_938_; 
v___x_938_ = 0;
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0___boxed(lean_object* v_as_939_, lean_object* v_i_940_, lean_object* v_stop_941_){
_start:
{
size_t v_i_boxed_942_; size_t v_stop_boxed_943_; uint8_t v_res_944_; lean_object* v_r_945_; 
v_i_boxed_942_ = lean_unbox_usize(v_i_940_);
lean_dec(v_i_940_);
v_stop_boxed_943_ = lean_unbox_usize(v_stop_941_);
lean_dec(v_stop_941_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_as_939_, v_i_boxed_942_, v_stop_boxed_943_);
lean_dec_ref(v_as_939_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral___boxed(lean_object* v_x_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_x_946_);
lean_dec(v_x_946_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(lean_object* v_msg_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_panic_fn_borrowed(v___x_950_, v_msg_949_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_954_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1));
v___x_955_ = lean_unsigned_to_nat(9u);
v___x_956_ = lean_unsigned_to_nat(271u);
v___x_957_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0));
v___x_958_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_959_ = l_mkPanicMessageWithDecl(v___x_958_, v___x_957_, v___x_956_, v___x_955_, v___x_954_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(lean_object* v_a_960_){
_start:
{
if (lean_obj_tag(v_a_960_) == 2)
{
lean_object* v_i_964_; 
v_i_964_ = lean_ctor_get(v_a_960_, 0);
if (lean_obj_tag(v_i_964_) == 1)
{
lean_object* v_pre_965_; 
v_pre_965_ = lean_ctor_get(v_i_964_, 0);
if (lean_obj_tag(v_pre_965_) == 1)
{
lean_object* v_pre_966_; 
v_pre_966_ = lean_ctor_get(v_pre_965_, 0);
if (lean_obj_tag(v_pre_966_) == 0)
{
lean_object* v_vs_967_; lean_object* v_str_968_; lean_object* v_str_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_vs_967_ = lean_ctor_get(v_a_960_, 1);
v_str_968_ = lean_ctor_get(v_i_964_, 1);
v_str_969_ = lean_ctor_get(v_pre_965_, 1);
v___x_970_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_971_ = lean_string_dec_eq(v_str_969_, v___x_970_);
if (v___x_971_ == 0)
{
goto v___jp_961_;
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_973_ = lean_string_dec_eq(v_str_968_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_975_ = lean_string_dec_eq(v_str_968_, v___x_974_);
if (v___x_975_ == 0)
{
goto v___jp_961_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_976_ = lean_array_get_size(v_vs_967_);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_dec_eq(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
goto v___jp_961_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_array_fget_borrowed(v_vs_967_, v___x_979_);
v___x_981_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_980_);
v___x_982_ = lean_nat_add(v___x_981_, v___x_977_);
lean_dec(v___x_981_);
return v___x_982_;
}
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_array_get_size(v_vs_967_);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_nat_dec_eq(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
goto v___jp_961_;
}
else
{
return v___x_984_;
}
}
}
}
else
{
goto v___jp_961_;
}
}
else
{
goto v___jp_961_;
}
}
else
{
goto v___jp_961_;
}
}
else
{
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2);
v___x_963_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(v___x_962_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___boxed(lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v_a_986_);
lean_dec(v_a_986_);
return v_res_987_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_instMonadEIO(lean_box(0));
return v___x_988_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3(void){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Array_instInhabited(lean_box(0));
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(lean_object* v_msg_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_toApplicative_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1035_; 
v___x_998_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0);
v___x_999_ = l_StateRefT_x27_instMonad___redArg(v___x_998_);
v_toApplicative_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v___x_999_, 1);
lean_dec(v_unused_1036_);
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1035_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_toApplicative_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1035_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_toFunctor_1004_; lean_object* v_toSeq_1005_; lean_object* v_toSeqLeft_1006_; lean_object* v_toSeqRight_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1033_; 
v_toFunctor_1004_ = lean_ctor_get(v_toApplicative_1000_, 0);
v_toSeq_1005_ = lean_ctor_get(v_toApplicative_1000_, 2);
v_toSeqLeft_1006_ = lean_ctor_get(v_toApplicative_1000_, 3);
v_toSeqRight_1007_ = lean_ctor_get(v_toApplicative_1000_, 4);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_toApplicative_1000_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_toApplicative_1000_, 1);
lean_dec(v_unused_1034_);
v___x_1009_ = v_toApplicative_1000_;
v_isShared_1010_ = v_isSharedCheck_1033_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_toSeqRight_1007_);
lean_inc(v_toSeqLeft_1006_);
lean_inc(v_toSeq_1005_);
lean_inc(v_toFunctor_1004_);
lean_dec(v_toApplicative_1000_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1033_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1020_; 
v___f_1011_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1));
v___f_1012_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1004_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toFunctor_1004_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toFunctor_1004_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___f_1013_);
lean_ctor_set(v___x_1015_, 1, v___f_1014_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toSeqRight_1007_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toSeqLeft_1006_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeq_1005_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___f_1016_);
lean_ctor_set(v___x_1009_, 3, v___f_1017_);
lean_ctor_set(v___x_1009_, 2, v___f_1018_);
lean_ctor_set(v___x_1009_, 1, v___f_1011_);
lean_ctor_set(v___x_1009_, 0, v___x_1015_);
v___x_1020_ = v___x_1009_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___f_1011_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v___f_1018_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v___f_1017_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v___f_1016_);
v___x_1020_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v___f_1012_);
lean_ctor_set(v___x_1002_, 0, v___x_1020_);
v___x_1022_ = v___x_1002_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___f_1012_);
v___x_1022_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___x_1979__overap_1029_; lean_object* v___x_1030_; 
v___x_1023_ = l_StateRefT_x27_instMonad___redArg(v___x_1022_);
v___x_1024_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_instInhabitedOfMonad___redArg(v___x_1023_, v___x_1026_);
v___f_1028_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
v___x_1979__overap_1029_ = lean_panic_fn_borrowed(v___f_1028_, v_msg_992_);
lean_dec_ref(v___f_1028_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
v___x_1030_ = lean_apply_5(v___x_1979__overap_1029_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, lean_box(0));
return v___x_1030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v_msg_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object* v_as_1044_, size_t v_i_1045_, size_t v_stop_1046_, lean_object* v_b_1047_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_usize_dec_eq(v_i_1045_, v_stop_1046_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v_fst_1050_; lean_object* v_snd_1051_; lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1066_; 
v___x_1049_ = lean_array_uget_borrowed(v_as_1044_, v_i_1045_);
v_fst_1050_ = lean_ctor_get(v___x_1049_, 0);
v_snd_1051_ = lean_ctor_get(v___x_1049_, 1);
v_fst_1052_ = lean_ctor_get(v_b_1047_, 0);
v_snd_1053_ = lean_ctor_get(v_b_1047_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_b_1047_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1055_ = v_b_1047_;
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snd_1053_);
lean_inc(v_fst_1052_);
lean_dec(v_b_1047_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1057_ = l_Array_append___redArg(v_fst_1052_, v_fst_1050_);
lean_inc(v_snd_1051_);
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_snd_1051_);
v___x_1059_ = lean_array_push(v_snd_1053_, v___x_1058_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1059_);
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1061_ = v___x_1055_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
size_t v___x_1062_; size_t v___x_1063_; 
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1045_, v___x_1062_);
v_i_1045_ = v___x_1063_;
v_b_1047_ = v___x_1061_;
goto _start;
}
}
}
else
{
return v_b_1047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object* v_as_1067_, lean_object* v_i_1068_, lean_object* v_stop_1069_, lean_object* v_b_1070_){
_start:
{
size_t v_i_boxed_1071_; size_t v_stop_boxed_1072_; lean_object* v_res_1073_; 
v_i_boxed_1071_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_stop_boxed_1072_ = lean_unbox_usize(v_stop_1069_);
lean_dec(v_stop_1069_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_as_1067_, v_i_boxed_1071_, v_stop_boxed_1072_, v_b_1070_);
lean_dec_ref(v_as_1067_);
return v_res_1073_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1078_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1079_ = lean_unsigned_to_nat(65u);
v___x_1080_ = lean_unsigned_to_nat(258u);
v___x_1081_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1082_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1083_ = l_mkPanicMessageWithDecl(v___x_1082_, v___x_1081_, v___x_1080_, v___x_1079_, v___x_1078_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1090_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1091_ = lean_unsigned_to_nat(9u);
v___x_1092_ = lean_unsigned_to_nat(266u);
v___x_1093_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1094_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1095_ = l_mkPanicMessageWithDecl(v___x_1094_, v___x_1093_, v___x_1092_, v___x_1091_, v___x_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; 
if (lean_obj_tag(v_a_1096_) == 2)
{
lean_object* v_i_1151_; lean_object* v_vs_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1273_; 
v_i_1151_ = lean_ctor_get(v_a_1096_, 0);
v_vs_1152_ = lean_ctor_get(v_a_1096_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_a_1096_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1154_ = v_a_1096_;
v_isShared_1155_ = v_isSharedCheck_1273_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_vs_1152_);
lean_inc(v_i_1151_);
lean_dec(v_a_1096_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1273_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_ctorName_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; 
if (lean_obj_tag(v_i_1151_) == 1)
{
lean_object* v_pre_1195_; 
v_pre_1195_ = lean_ctor_get(v_i_1151_, 0);
if (lean_obj_tag(v_pre_1195_) == 1)
{
lean_object* v_pre_1196_; 
v_pre_1196_ = lean_ctor_get(v_pre_1195_, 0);
if (lean_obj_tag(v_pre_1196_) == 0)
{
lean_object* v_str_1197_; lean_object* v_str_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_str_1197_ = lean_ctor_get(v_i_1151_, 1);
v_str_1198_ = lean_ctor_get(v_pre_1195_, 1);
v___x_1199_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_1200_ = lean_string_dec_eq(v_str_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
v_ctorName_1157_ = v_i_1151_;
v___y_1158_ = v_a_1097_;
v___y_1159_ = v_a_1098_;
v___y_1160_ = v_a_1099_;
v___y_1161_ = v_a_1100_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
lean_inc_ref(v_str_1197_);
lean_inc(v_pre_1196_);
lean_dec_ref_known(v_i_1151_, 2);
v___x_1201_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_1202_ = lean_string_dec_eq(v_str_1197_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_1204_ = lean_string_dec_eq(v_str_1197_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = l_Lean_Name_str___override(v_pre_1196_, v___x_1199_);
v___x_1206_ = l_Lean_Name_str___override(v___x_1205_, v_str_1197_);
v_ctorName_1157_ = v___x_1206_;
v___y_1158_ = v_a_1097_;
v___y_1159_ = v_a_1098_;
v___y_1160_ = v_a_1099_;
v___y_1161_ = v_a_1100_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
lean_dec_ref(v_str_1197_);
v___x_1207_ = lean_array_get_size(v_vs_1152_);
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_dec_eq(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = l_Lean_Name_str___override(v_pre_1196_, v___x_1199_);
v___x_1211_ = l_Lean_Name_str___override(v___x_1210_, v___x_1203_);
v_ctorName_1157_ = v___x_1211_;
v___y_1158_ = v_a_1097_;
v___y_1159_ = v_a_1098_;
v___y_1160_ = v_a_1099_;
v___y_1161_ = v_a_1100_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_val_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_del_object(v___x_1154_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_array_fget(v_vs_1152_, v___x_1212_);
lean_dec_ref(v_vs_1152_);
v___x_1214_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_1213_);
lean_dec(v___x_1213_);
v_val_1215_ = lean_nat_add(v___x_1214_, v___x_1208_);
lean_dec(v___x_1214_);
v___x_1216_ = 0;
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_val_1215_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
v___x_1219_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1220_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1216_, v___x_1218_, v___x_1219_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1233_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1233_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1233_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_fvarId_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_fvarId_1225_ = lean_ctor_get(v_a_1221_, 0);
lean_inc(v_fvarId_1225_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1221_);
v___x_1227_ = lean_mk_empty_array_with_capacity(v___x_1208_);
v___x_1228_ = lean_array_push(v___x_1227_, v___x_1226_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_fvarId_1225_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1229_);
v___x_1231_ = v___x_1223_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1220_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1220_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
lean_dec_ref(v_str_1197_);
v___x_1242_ = lean_array_get_size(v_vs_1152_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_nat_dec_eq(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = l_Lean_Name_str___override(v_pre_1196_, v___x_1199_);
v___x_1246_ = l_Lean_Name_str___override(v___x_1245_, v___x_1201_);
v_ctorName_1157_ = v___x_1246_;
v___y_1158_ = v_a_1097_;
v___y_1159_ = v_a_1098_;
v___y_1160_ = v_a_1099_;
v___y_1161_ = v_a_1100_;
goto v___jp_1156_;
}
else
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_del_object(v___x_1154_);
lean_dec_ref(v_vs_1152_);
v___x_1247_ = 0;
v___x_1248_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6));
v___x_1249_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1250_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1247_, v___x_1248_, v___x_1249_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1264_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1264_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1264_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_fvarId_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v_fvarId_1255_ = lean_ctor_get(v_a_1251_, 0);
lean_inc(v_fvarId_1255_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_a_1251_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_mk_empty_array_with_capacity(v___x_1257_);
v___x_1259_ = lean_array_push(v___x_1258_, v___x_1256_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_fvarId_1255_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1260_);
v___x_1262_ = v___x_1253_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_a_1265_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1250_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1250_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
}
else
{
v_ctorName_1157_ = v_i_1151_;
v___y_1158_ = v_a_1097_;
v___y_1159_ = v_a_1098_;
v___y_1160_ = v_a_1099_;
v___y_1161_ = v_a_1100_;
goto v___jp_1156_;
}
}
else
{
v_ctorName_1157_ = v_i_1151_;
v___y_1158_ = v_a_1097_;
v___y_1159_ = v_a_1098_;
v___y_1160_ = v_a_1099_;
v___y_1161_ = v_a_1100_;
goto v___jp_1156_;
}
}
else
{
v_ctorName_1157_ = v_i_1151_;
v___y_1158_ = v_a_1097_;
v___y_1159_ = v_a_1098_;
v___y_1160_ = v_a_1099_;
v___y_1161_ = v_a_1100_;
goto v___jp_1156_;
}
v___jp_1156_:
{
lean_object* v___x_1162_; lean_object* v_env_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_st_ref_get(v___y_1161_);
v_env_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc_ref(v_env_1163_);
lean_dec(v___x_1162_);
v___x_1164_ = 0;
lean_inc(v_ctorName_1157_);
v___x_1165_ = l_Lean_Environment_find_x3f(v_env_1163_, v_ctorName_1157_, v___x_1164_);
if (lean_obj_tag(v___x_1165_) == 1)
{
lean_object* v_val_1166_; 
v_val_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___x_1165_, 1);
if (lean_obj_tag(v_val_1166_) == 6)
{
lean_object* v_val_1167_; size_t v_sz_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
v_val_1167_ = lean_ctor_get(v_val_1166_, 0);
lean_inc_ref(v_val_1167_);
lean_dec_ref_known(v_val_1166_, 1);
v_sz_1168_ = lean_array_size(v_vs_1152_);
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_1168_, v___x_1169_, v_vs_1152_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_numParams_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v_numParams_1172_ = lean_ctor_get(v_val_1167_, 3);
lean_inc(v_numParams_1172_);
lean_dec_ref(v_val_1167_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4));
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_mk_array(v_numParams_1172_, v___x_1175_);
v___x_1177_ = lean_array_get_size(v_a_1171_);
v___x_1178_ = lean_nat_dec_lt(v___x_1173_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_a_1171_);
lean_del_object(v___x_1154_);
v___y_1103_ = v___y_1158_;
v___y_1104_ = v___y_1160_;
v___y_1105_ = v_ctorName_1157_;
v___y_1106_ = v___y_1159_;
v___y_1107_ = v___y_1161_;
v_fst_1108_ = v___x_1174_;
v_snd_1109_ = v___x_1176_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1180_; 
lean_inc_ref(v___x_1176_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 0);
lean_ctor_set(v___x_1154_, 1, v___x_1176_);
lean_ctor_set(v___x_1154_, 0, v___x_1174_);
v___x_1180_ = v___x_1154_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1176_);
v___x_1180_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_nat_dec_le(v___x_1177_, v___x_1177_);
if (v___x_1181_ == 0)
{
if (v___x_1178_ == 0)
{
lean_dec_ref(v___x_1180_);
lean_dec(v_a_1171_);
v___y_1103_ = v___y_1158_;
v___y_1104_ = v___y_1160_;
v___y_1105_ = v_ctorName_1157_;
v___y_1106_ = v___y_1159_;
v___y_1107_ = v___y_1161_;
v_fst_1108_ = v___x_1174_;
v_snd_1109_ = v___x_1176_;
goto v___jp_1102_;
}
else
{
size_t v___x_1182_; lean_object* v___x_1183_; 
lean_dec_ref(v___x_1176_);
v___x_1182_ = lean_usize_of_nat(v___x_1177_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1171_, v___x_1169_, v___x_1182_, v___x_1180_);
lean_dec(v_a_1171_);
v___y_1136_ = v___y_1158_;
v___y_1137_ = v___y_1160_;
v___y_1138_ = v_ctorName_1157_;
v___y_1139_ = v___y_1159_;
v___y_1140_ = v___y_1161_;
v___y_1141_ = v___x_1183_;
goto v___jp_1135_;
}
}
else
{
size_t v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v___x_1176_);
v___x_1184_ = lean_usize_of_nat(v___x_1177_);
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1171_, v___x_1169_, v___x_1184_, v___x_1180_);
lean_dec(v_a_1171_);
v___y_1136_ = v___y_1158_;
v___y_1137_ = v___y_1160_;
v___y_1138_ = v_ctorName_1157_;
v___y_1139_ = v___y_1159_;
v___y_1140_ = v___y_1161_;
v___y_1141_ = v___x_1185_;
goto v___jp_1135_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_val_1167_);
lean_dec(v_ctorName_1157_);
lean_del_object(v___x_1154_);
v_a_1187_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1170_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1170_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_dec(v_val_1166_);
lean_dec(v_ctorName_1157_);
lean_del_object(v___x_1154_);
lean_dec_ref(v_vs_1152_);
v___y_1145_ = v___y_1158_;
v___y_1146_ = v___y_1159_;
v___y_1147_ = v___y_1160_;
v___y_1148_ = v___y_1161_;
goto v___jp_1144_;
}
}
else
{
lean_dec(v___x_1165_);
lean_dec(v_ctorName_1157_);
lean_del_object(v___x_1154_);
lean_dec_ref(v_vs_1152_);
v___y_1145_ = v___y_1158_;
v___y_1146_ = v___y_1159_;
v___y_1147_ = v___y_1160_;
v___y_1148_ = v___y_1161_;
goto v___jp_1144_;
}
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec(v_a_1096_);
v___x_1274_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7);
v___x_1275_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1274_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1275_;
}
v___jp_1102_:
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1110_ = 0;
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1105_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
lean_ctor_set(v___x_1112_, 2, v_snd_1109_);
v___x_1113_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1114_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1110_, v___x_1112_, v___x_1113_, v___y_1103_, v___y_1106_, v___y_1104_, v___y_1107_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1126_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_fvarId_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v_fvarId_1119_ = lean_ctor_get(v_a_1115_, 0);
lean_inc(v_fvarId_1119_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_a_1115_);
v___x_1121_ = lean_array_push(v_fst_1108_, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_fvarId_1119_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1122_);
v___x_1124_ = v___x_1117_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v_fst_1108_);
v_a_1127_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1114_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1114_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
v___jp_1135_:
{
lean_object* v_fst_1142_; lean_object* v_snd_1143_; 
v_fst_1142_ = lean_ctor_get(v___y_1141_, 0);
lean_inc(v_fst_1142_);
v_snd_1143_ = lean_ctor_get(v___y_1141_, 1);
lean_inc(v_snd_1143_);
lean_dec_ref(v___y_1141_);
v___y_1103_ = v___y_1136_;
v___y_1104_ = v___y_1137_;
v___y_1105_ = v___y_1138_;
v___y_1106_ = v___y_1139_;
v___y_1107_ = v___y_1140_;
v_fst_1108_ = v_fst_1142_;
v_snd_1109_ = v_snd_1143_;
goto v___jp_1102_;
}
v___jp_1144_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3);
v___x_1150_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1149_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(size_t v_sz_1276_, size_t v_i_1277_, lean_object* v_bs_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_lt(v_i_1277_, v_sz_1276_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_bs_1278_);
return v___x_1285_;
}
else
{
lean_object* v_v_1286_; lean_object* v___x_1287_; 
v_v_1286_ = lean_array_uget_borrowed(v_bs_1278_, v_i_1277_);
lean_inc(v_v_1286_);
v___x_1287_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1286_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v_bs_x27_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = lean_unsigned_to_nat(0u);
v_bs_x27_1290_ = lean_array_uset(v_bs_1278_, v_i_1277_, v___x_1289_);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_add(v_i_1277_, v___x_1291_);
v___x_1293_ = lean_array_uset(v_bs_x27_1290_, v_i_1277_, v_a_1288_);
v_i_1277_ = v___x_1292_;
v_bs_1278_ = v___x_1293_;
goto _start;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_bs_1278_);
v_a_1295_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1287_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1287_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object* v_sz_1303_, lean_object* v_i_1304_, lean_object* v_bs_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1303_);
lean_dec(v_sz_1303_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_boxed_1311_, v_i_boxed_1312_, v_bs_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(lean_object* v_v_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_v_1321_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec(v_v_1321_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; 
v___x_1330_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1331_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1330_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1330_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral___boxed(lean_object* v_v_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_v_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
return v_res_1354_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(lean_object* v_a_1355_, lean_object* v_b_1356_){
_start:
{
lean_object* v_fst_1357_; lean_object* v_fst_1358_; uint8_t v___x_1359_; 
v_fst_1357_ = lean_ctor_get(v_a_1355_, 0);
v_fst_1358_ = lean_ctor_get(v_b_1356_, 0);
v___x_1359_ = l_Lean_Name_quickLt(v_fst_1357_, v_fst_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed(lean_object* v_a_1360_, lean_object* v_b_1361_){
_start:
{
uint8_t v_res_1362_; lean_object* v_r_1363_; 
v_res_1362_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(v_a_1360_, v_b_1361_);
lean_dec_ref(v_b_1361_);
lean_dec_ref(v_a_1360_);
v_r_1363_ = lean_box(v_res_1362_);
return v_r_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(lean_object* v_entries_1366_, lean_object* v_fid_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_array_get_size(v_entries_1366_);
v___x_1370_ = lean_nat_dec_lt(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v_fid_1367_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_sub(v___x_1369_, v___x_1372_);
v___x_1374_ = lean_nat_dec_le(v___x_1368_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec(v___x_1373_);
lean_dec(v_fid_1367_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_fid_1367_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0));
v___x_1379_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1));
v___x_1380_ = l_Array_binSearchAux___redArg(v___x_1378_, v___x_1379_, v_entries_1366_, v___x_1377_, v___x_1368_, v___x_1373_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
else
{
lean_object* v_val_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1390_; 
v_val_1382_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1384_ = v___x_1380_;
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_val_1382_);
lean_dec(v___x_1380_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_snd_1386_; lean_object* v___x_1388_; 
v_snd_1386_ = lean_ctor_get(v_val_1382_, 1);
lean_inc(v_snd_1386_);
lean_dec(v_val_1382_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v_snd_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_snd_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___boxed(lean_object* v_entries_1391_, lean_object* v_fid_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(v_entries_1391_, v_fid_1392_);
lean_dec_ref(v_entries_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_es_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_array_mk(v_es_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1396_, lean_object* v_i_1397_, lean_object* v_k_1398_){
_start:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_array_get_size(v_keys_1396_);
v___x_1400_ = lean_nat_dec_lt(v_i_1397_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_dec(v_i_1397_);
return v___x_1400_;
}
else
{
lean_object* v_k_x27_1401_; uint8_t v___x_1402_; 
v_k_x27_1401_ = lean_array_fget_borrowed(v_keys_1396_, v_i_1397_);
v___x_1402_ = lean_name_eq(v_k_1398_, v_k_x27_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_nat_add(v_i_1397_, v___x_1403_);
lean_dec(v_i_1397_);
v_i_1397_ = v___x_1404_;
goto _start;
}
else
{
lean_dec(v_i_1397_);
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1406_, lean_object* v_i_1407_, lean_object* v_k_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1406_, v_i_1407_, v_k_1408_);
lean_dec(v_k_1408_);
lean_dec_ref(v_keys_1406_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1411_, size_t v_x_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v_es_1414_; lean_object* v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; lean_object* v_j_1418_; lean_object* v___x_1419_; 
v_es_1414_ = lean_ctor_get(v_x_1411_, 0);
v___x_1415_ = lean_box(2);
v___x_1416_ = ((size_t)31ULL);
v___x_1417_ = lean_usize_land(v_x_1412_, v___x_1416_);
v_j_1418_ = lean_usize_to_nat(v___x_1417_);
v___x_1419_ = lean_array_get_borrowed(v___x_1415_, v_es_1414_, v_j_1418_);
lean_dec(v_j_1418_);
switch(lean_obj_tag(v___x_1419_))
{
case 0:
{
lean_object* v_key_1420_; uint8_t v___x_1421_; 
v_key_1420_ = lean_ctor_get(v___x_1419_, 0);
v___x_1421_ = lean_name_eq(v_x_1413_, v_key_1420_);
return v___x_1421_;
}
case 1:
{
lean_object* v_node_1422_; size_t v___x_1423_; size_t v___x_1424_; 
v_node_1422_ = lean_ctor_get(v___x_1419_, 0);
v___x_1423_ = ((size_t)5ULL);
v___x_1424_ = lean_usize_shift_right(v_x_1412_, v___x_1423_);
v_x_1411_ = v_node_1422_;
v_x_1412_ = v___x_1424_;
goto _start;
}
default: 
{
uint8_t v___x_1426_; 
v___x_1426_ = 0;
return v___x_1426_;
}
}
}
else
{
lean_object* v_ks_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_ks_1427_ = lean_ctor_get(v_x_1411_, 0);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1427_, v___x_1428_, v_x_1413_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
size_t v_x_1160__boxed_1433_; uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_x_1160__boxed_1433_ = lean_unbox_usize(v_x_1431_);
lean_dec(v_x_1431_);
v_res_1434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1430_, v_x_1160__boxed_1433_, v_x_1432_);
lean_dec(v_x_1432_);
lean_dec_ref(v_x_1430_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1436_; uint64_t v___x_1437_; 
v___x_1436_ = lean_unsigned_to_nat(1723u);
v___x_1437_ = lean_uint64_of_nat(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1438_, lean_object* v_x_1439_){
_start:
{
uint64_t v___y_1441_; 
if (lean_obj_tag(v_x_1439_) == 0)
{
uint64_t v___x_1444_; 
v___x_1444_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1441_ = v___x_1444_;
goto v___jp_1440_;
}
else
{
uint64_t v_hash_1445_; 
v_hash_1445_ = lean_ctor_get_uint64(v_x_1439_, sizeof(void*)*2);
v___y_1441_ = v_hash_1445_;
goto v___jp_1440_;
}
v___jp_1440_:
{
size_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = lean_uint64_to_usize(v___y_1441_);
v___x_1443_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1438_, v___x_1442_, v_x_1439_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1446_, v_x_1447_);
lean_dec(v_x_1447_);
lean_dec_ref(v_x_1446_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x1_1450_, lean_object* v_x2_1451_){
_start:
{
lean_object* v_fst_1452_; uint8_t v___x_1453_; uint8_t v___x_1454_; 
v_fst_1452_ = lean_ctor_get(v_x2_1451_, 0);
v___x_1453_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x1_1450_, v_fst_1452_);
v___x_1454_ = lean_bool_not(v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x1_1455_, lean_object* v_x2_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x1_1455_, v_x2_1456_);
lean_dec_ref(v_x2_1456_);
lean_dec_ref(v_x1_1455_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_f_1459_, lean_object* v_keys_1460_, lean_object* v_vals_1461_, lean_object* v_i_1462_, lean_object* v_acc_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = lean_array_get_size(v_keys_1460_);
v___x_1465_ = lean_nat_dec_lt(v_i_1462_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_dec(v_i_1462_);
lean_dec(v_f_1459_);
return v_acc_1463_;
}
else
{
lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_k_1466_ = lean_array_fget_borrowed(v_keys_1460_, v_i_1462_);
v_v_1467_ = lean_array_fget_borrowed(v_vals_1461_, v_i_1462_);
lean_inc(v_f_1459_);
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
v___x_1468_ = lean_apply_3(v_f_1459_, v_acc_1463_, v_k_1466_, v_v_1467_);
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = lean_nat_add(v_i_1462_, v___x_1469_);
lean_dec(v_i_1462_);
v_i_1462_ = v___x_1470_;
v_acc_1463_ = v___x_1468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_f_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_i_1475_, lean_object* v_acc_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1472_, v_keys_1473_, v_vals_1474_, v_i_1475_, v_acc_1476_);
lean_dec_ref(v_vals_1474_);
lean_dec_ref(v_keys_1473_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
if (lean_obj_tag(v_x_1479_) == 0)
{
lean_object* v_es_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_es_1481_ = lean_ctor_get(v_x_1479_, 0);
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = lean_array_get_size(v_es_1481_);
v___x_1484_ = lean_nat_dec_lt(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_dec(v_f_1478_);
return v_x_1480_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_nat_dec_le(v___x_1483_, v___x_1483_);
if (v___x_1485_ == 0)
{
if (v___x_1484_ == 0)
{
lean_dec(v_f_1478_);
return v_x_1480_;
}
else
{
size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = lean_usize_of_nat(v___x_1483_);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1478_, v_es_1481_, v___x_1486_, v___x_1487_, v_x_1480_);
return v___x_1488_;
}
}
else
{
size_t v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = ((size_t)0ULL);
v___x_1490_ = lean_usize_of_nat(v___x_1483_);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1478_, v_es_1481_, v___x_1489_, v___x_1490_, v_x_1480_);
return v___x_1491_;
}
}
}
else
{
lean_object* v_ks_1492_; lean_object* v_vs_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_ks_1492_ = lean_ctor_get(v_x_1479_, 0);
v_vs_1493_ = lean_ctor_get(v_x_1479_, 1);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1478_, v_ks_1492_, v_vs_1493_, v___x_1494_, v_x_1480_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1496_, lean_object* v_as_1497_, size_t v_i_1498_, size_t v_stop_1499_, lean_object* v_b_1500_){
_start:
{
lean_object* v___y_1502_; uint8_t v___x_1506_; 
v___x_1506_ = lean_usize_dec_eq(v_i_1498_, v_stop_1499_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_array_uget_borrowed(v_as_1497_, v_i_1498_);
switch(lean_obj_tag(v___x_1507_))
{
case 0:
{
lean_object* v_key_1508_; lean_object* v_val_1509_; lean_object* v___x_1510_; 
v_key_1508_ = lean_ctor_get(v___x_1507_, 0);
v_val_1509_ = lean_ctor_get(v___x_1507_, 1);
lean_inc(v_f_1496_);
lean_inc(v_val_1509_);
lean_inc(v_key_1508_);
v___x_1510_ = lean_apply_3(v_f_1496_, v_b_1500_, v_key_1508_, v_val_1509_);
v___y_1502_ = v___x_1510_;
goto v___jp_1501_;
}
case 1:
{
lean_object* v_node_1511_; lean_object* v___x_1512_; 
v_node_1511_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_f_1496_);
v___x_1512_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1496_, v_node_1511_, v_b_1500_);
v___y_1502_ = v___x_1512_;
goto v___jp_1501_;
}
default: 
{
v___y_1502_ = v_b_1500_;
goto v___jp_1501_;
}
}
}
else
{
lean_dec(v_f_1496_);
return v_b_1500_;
}
v___jp_1501_:
{
size_t v___x_1503_; size_t v___x_1504_; 
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1498_, v___x_1503_);
v_i_1498_ = v___x_1504_;
v_b_1500_ = v___y_1502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1513_, lean_object* v_as_1514_, lean_object* v_i_1515_, lean_object* v_stop_1516_, lean_object* v_b_1517_){
_start:
{
size_t v_i_boxed_1518_; size_t v_stop_boxed_1519_; lean_object* v_res_1520_; 
v_i_boxed_1518_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_stop_boxed_1519_ = lean_unbox_usize(v_stop_1516_);
lean_dec(v_stop_1516_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1513_, v_as_1514_, v_i_boxed_1518_, v_stop_boxed_1519_, v_b_1517_);
lean_dec_ref(v_as_1514_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1521_, v_x_1522_, v_x_1523_);
lean_dec_ref(v_x_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1525_, lean_object* v_x1_1526_, lean_object* v_x2_1527_, lean_object* v_x3_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_apply_3(v_f_1525_, v_x1_1526_, v_x2_1527_, v_x3_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1530_, lean_object* v_f_1531_, lean_object* v_init_1532_){
_start:
{
lean_object* v___f_1533_; lean_object* v___x_1534_; 
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1533_, 0, v_f_1531_);
v___x_1534_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1533_, v_map_1530_, v_init_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1535_, lean_object* v_f_1536_, lean_object* v_init_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1535_, v_f_1536_, v_init_1537_);
lean_dec_ref(v_map_1535_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1539_, lean_object* v_k_1540_, lean_object* v_v_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_k_1540_);
lean_ctor_set(v___x_1542_, 1, v_v_1541_);
v___x_1543_ = lean_array_push(v_ps_1539_, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1547_){
_start:
{
lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___f_1548_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1549_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1550_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1547_, v___f_1548_, v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1551_);
lean_dec_ref(v_m_1551_);
return v_res_1552_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_fst_1555_; lean_object* v_fst_1556_; uint8_t v___x_1557_; 
v_fst_1555_ = lean_ctor_get(v___y_1553_, 0);
v_fst_1556_ = lean_ctor_get(v___y_1554_, 0);
v___x_1557_ = l_Lean_Name_quickLt(v_fst_1555_, v_fst_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_res_1560_; lean_object* v_r_1561_; 
v_res_1560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1558_, v___y_1559_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v___y_1558_);
v_r_1561_ = lean_box(v_res_1560_);
return v_r_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_hi_1562_, lean_object* v_pivot_1563_, lean_object* v_as_1564_, lean_object* v_i_1565_, lean_object* v_k_1566_){
_start:
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_nat_dec_lt(v_k_1566_, v_hi_1562_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec(v_k_1566_);
v___x_1568_ = lean_array_fswap(v_as_1564_, v_i_1565_, v_hi_1562_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_i_1565_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
return v___x_1569_;
}
else
{
lean_object* v___x_1570_; lean_object* v_fst_1571_; lean_object* v_fst_1572_; uint8_t v___x_1573_; 
v___x_1570_ = lean_array_fget_borrowed(v_as_1564_, v_k_1566_);
v_fst_1571_ = lean_ctor_get(v___x_1570_, 0);
v_fst_1572_ = lean_ctor_get(v_pivot_1563_, 0);
v___x_1573_ = l_Lean_Name_quickLt(v_fst_1571_, v_fst_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = lean_nat_add(v_k_1566_, v___x_1574_);
lean_dec(v_k_1566_);
v_k_1566_ = v___x_1575_;
goto _start;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1577_ = lean_array_fswap(v_as_1564_, v_i_1565_, v_k_1566_);
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_i_1565_, v___x_1578_);
lean_dec(v_i_1565_);
v___x_1580_ = lean_nat_add(v_k_1566_, v___x_1578_);
lean_dec(v_k_1566_);
v_as_1564_ = v___x_1577_;
v_i_1565_ = v___x_1579_;
v_k_1566_ = v___x_1580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_hi_1582_, lean_object* v_pivot_1583_, lean_object* v_as_1584_, lean_object* v_i_1585_, lean_object* v_k_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1582_, v_pivot_1583_, v_as_1584_, v_i_1585_, v_k_1586_);
lean_dec_ref(v_pivot_1583_);
lean_dec(v_hi_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_1588_, lean_object* v_as_1589_, lean_object* v_lo_1590_, lean_object* v_hi_1591_){
_start:
{
lean_object* v___y_1593_; uint8_t v___x_1603_; 
v___x_1603_ = lean_nat_dec_lt(v_lo_1590_, v_hi_1591_);
if (v___x_1603_ == 0)
{
lean_dec(v_lo_1590_);
return v_as_1589_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v_mid_1606_; lean_object* v___y_1608_; lean_object* v___y_1614_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1604_ = lean_nat_add(v_lo_1590_, v_hi_1591_);
v___x_1605_ = lean_unsigned_to_nat(1u);
v_mid_1606_ = lean_nat_shiftr(v___x_1604_, v___x_1605_);
lean_dec(v___x_1604_);
v___x_1619_ = lean_array_fget_borrowed(v_as_1589_, v_mid_1606_);
v___x_1620_ = lean_array_fget_borrowed(v_as_1589_, v_lo_1590_);
v___x_1621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
v___y_1614_ = v_as_1589_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_array_fswap(v_as_1589_, v_lo_1590_, v_mid_1606_);
v___y_1614_ = v___x_1622_;
goto v___jp_1613_;
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = lean_array_fget_borrowed(v___y_1608_, v_mid_1606_);
v___x_1610_ = lean_array_fget_borrowed(v___y_1608_, v_hi_1591_);
v___x_1611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_dec(v_mid_1606_);
v___y_1593_ = v___y_1608_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_array_fswap(v___y_1608_, v_mid_1606_, v_hi_1591_);
lean_dec(v_mid_1606_);
v___y_1593_ = v___x_1612_;
goto v___jp_1592_;
}
}
v___jp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = lean_array_fget_borrowed(v___y_1614_, v_hi_1591_);
v___x_1616_ = lean_array_fget_borrowed(v___y_1614_, v_lo_1590_);
v___x_1617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
v___y_1608_ = v___y_1614_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_array_fswap(v___y_1614_, v_lo_1590_, v_hi_1591_);
v___y_1608_ = v___x_1618_;
goto v___jp_1607_;
}
}
}
v___jp_1592_:
{
lean_object* v_pivot_1594_; lean_object* v___x_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; uint8_t v___x_1598_; 
v_pivot_1594_ = lean_array_fget(v___y_1593_, v_hi_1591_);
lean_inc_n(v_lo_1590_, 2);
v___x_1595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1591_, v_pivot_1594_, v___y_1593_, v_lo_1590_, v_lo_1590_);
lean_dec(v_pivot_1594_);
v_fst_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_fst_1596_);
v_snd_1597_ = lean_ctor_get(v___x_1595_, 1);
lean_inc(v_snd_1597_);
lean_dec_ref(v___x_1595_);
v___x_1598_ = lean_nat_dec_le(v_hi_1591_, v_fst_1596_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1588_, v_snd_1597_, v_lo_1590_, v_fst_1596_);
v___x_1600_ = lean_unsigned_to_nat(1u);
v___x_1601_ = lean_nat_add(v_fst_1596_, v___x_1600_);
lean_dec(v_fst_1596_);
v_as_1589_ = v___x_1599_;
v_lo_1590_ = v___x_1601_;
goto _start;
}
else
{
lean_dec(v_fst_1596_);
lean_dec(v_lo_1590_);
return v_snd_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_1623_, lean_object* v_as_1624_, lean_object* v_lo_1625_, lean_object* v_hi_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1623_, v_as_1624_, v_lo_1625_, v_hi_1626_);
lean_dec(v_hi_1626_);
lean_dec(v_n_1623_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1630_, lean_object* v_s_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___y_1638_; lean_object* v___y_1639_; uint8_t v___x_1642_; 
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1635_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1631_);
v___x_1636_ = lean_array_get_size(v___x_1635_);
v___x_1642_ = lean_nat_dec_eq(v___x_1636_, v___x_1633_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___y_1646_; uint8_t v___x_1648_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_sub(v___x_1636_, v___x_1643_);
v___x_1648_ = lean_nat_dec_le(v___x_1633_, v___x_1644_);
if (v___x_1648_ == 0)
{
lean_inc(v___x_1644_);
v___y_1646_ = v___x_1644_;
goto v___jp_1645_;
}
else
{
v___y_1646_ = v___x_1633_;
goto v___jp_1645_;
}
v___jp_1645_:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v___y_1646_, v___x_1644_);
if (v___x_1647_ == 0)
{
lean_dec(v___x_1644_);
lean_inc(v___y_1646_);
v___y_1638_ = v___y_1646_;
v___y_1639_ = v___y_1646_;
goto v___jp_1637_;
}
else
{
v___y_1638_ = v___y_1646_;
v___y_1639_ = v___x_1644_;
goto v___jp_1637_;
}
}
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1634_);
lean_ctor_set(v___x_1649_, 1, v___x_1634_);
lean_ctor_set(v___x_1649_, 2, v___x_1635_);
return v___x_1649_;
}
v___jp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1636_, v___x_1635_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
v___x_1641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1634_);
lean_ctor_set(v___x_1641_, 1, v___x_1634_);
lean_ctor_set(v___x_1641_, 2, v___x_1640_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1650_, lean_object* v_s_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1650_, v_s_1651_, v_x_1652_);
lean_dec(v_x_1652_);
lean_dec_ref(v_s_1651_);
lean_dec_ref(v_x_1650_);
return v_res_1653_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1654_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1659_);
lean_dec_ref(v_x_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v_ks_1665_; lean_object* v_vs_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1690_; 
v_ks_1665_ = lean_ctor_get(v_x_1661_, 0);
v_vs_1666_ = lean_ctor_get(v_x_1661_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_x_1661_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1668_ = v_x_1661_;
v_isShared_1669_ = v_isSharedCheck_1690_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_vs_1666_);
lean_inc(v_ks_1665_);
lean_dec(v_x_1661_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1690_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = lean_array_get_size(v_ks_1665_);
v___x_1671_ = lean_nat_dec_lt(v_x_1662_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_dec(v_x_1662_);
v___x_1672_ = lean_array_push(v_ks_1665_, v_x_1663_);
v___x_1673_ = lean_array_push(v_vs_1666_, v_x_1664_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v___x_1673_);
lean_ctor_set(v___x_1668_, 0, v___x_1672_);
v___x_1675_ = v___x_1668_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
lean_object* v_k_x27_1677_; uint8_t v___x_1678_; 
v_k_x27_1677_ = lean_array_fget_borrowed(v_ks_1665_, v_x_1662_);
v___x_1678_ = lean_name_eq(v_x_1663_, v_k_x27_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1680_; 
if (v_isShared_1669_ == 0)
{
v___x_1680_ = v___x_1668_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_ks_1665_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_vs_1666_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_add(v_x_1662_, v___x_1681_);
lean_dec(v_x_1662_);
v_x_1661_ = v___x_1680_;
v_x_1662_ = v___x_1682_;
goto _start;
}
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1685_ = lean_array_fset(v_ks_1665_, v_x_1662_, v_x_1663_);
v___x_1686_ = lean_array_fset(v_vs_1666_, v_x_1662_, v_x_1664_);
lean_dec(v_x_1662_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v___x_1686_);
lean_ctor_set(v___x_1668_, 0, v___x_1685_);
v___x_1688_ = v___x_1668_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_n_1691_, lean_object* v_k_1692_, lean_object* v_v_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_unsigned_to_nat(0u);
v___x_1695_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_n_1691_, v___x_1694_, v_k_1692_, v_v_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_x_1697_, size_t v_x_1698_, size_t v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 0)
{
lean_object* v_es_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v_j_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_es_1702_ = lean_ctor_get(v_x_1697_, 0);
v___x_1703_ = ((size_t)31ULL);
v___x_1704_ = lean_usize_land(v_x_1698_, v___x_1703_);
v_j_1705_ = lean_usize_to_nat(v___x_1704_);
v___x_1706_ = lean_array_get_size(v_es_1702_);
v___x_1707_ = lean_nat_dec_lt(v_j_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_dec(v_j_1705_);
lean_dec(v_x_1701_);
lean_dec(v_x_1700_);
return v_x_1697_;
}
else
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1746_; 
lean_inc_ref(v_es_1702_);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v_x_1697_, 0);
lean_dec(v_unused_1747_);
v___x_1709_ = v_x_1697_;
v_isShared_1710_ = v_isSharedCheck_1746_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v_x_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1746_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_v_1711_; lean_object* v___x_1712_; lean_object* v_xs_x27_1713_; lean_object* v___y_1715_; 
v_v_1711_ = lean_array_fget(v_es_1702_, v_j_1705_);
v___x_1712_ = lean_box(0);
v_xs_x27_1713_ = lean_array_fset(v_es_1702_, v_j_1705_, v___x_1712_);
switch(lean_obj_tag(v_v_1711_))
{
case 0:
{
lean_object* v_key_1720_; lean_object* v_val_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1731_; 
v_key_1720_ = lean_ctor_get(v_v_1711_, 0);
v_val_1721_ = lean_ctor_get(v_v_1711_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_v_1711_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1723_ = v_v_1711_;
v_isShared_1724_ = v_isSharedCheck_1731_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_val_1721_);
lean_inc(v_key_1720_);
lean_dec(v_v_1711_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1731_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_name_eq(v_x_1700_, v_key_1720_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_del_object(v___x_1723_);
v___x_1726_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1720_, v_val_1721_, v_x_1700_, v_x_1701_);
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
v___y_1715_ = v___x_1727_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1729_; 
lean_dec(v_val_1721_);
lean_dec(v_key_1720_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v_x_1701_);
lean_ctor_set(v___x_1723_, 0, v_x_1700_);
v___x_1729_ = v___x_1723_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_x_1700_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_x_1701_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v___y_1715_ = v___x_1729_;
goto v___jp_1714_;
}
}
}
}
case 1:
{
lean_object* v_node_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1744_; 
v_node_1732_ = lean_ctor_get(v_v_1711_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_v_1711_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1734_ = v_v_1711_;
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_node_1732_);
lean_dec(v_v_1711_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
size_t v___x_1736_; size_t v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1736_ = ((size_t)5ULL);
v___x_1737_ = lean_usize_shift_right(v_x_1698_, v___x_1736_);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_x_1699_, v___x_1738_);
v___x_1740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_node_1732_, v___x_1737_, v___x_1739_, v_x_1700_, v_x_1701_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1740_);
v___x_1742_ = v___x_1734_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
v___y_1715_ = v___x_1742_;
goto v___jp_1714_;
}
}
}
default: 
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_x_1700_);
lean_ctor_set(v___x_1745_, 1, v_x_1701_);
v___y_1715_ = v___x_1745_;
goto v___jp_1714_;
}
}
v___jp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_array_fset(v_xs_x27_1713_, v_j_1705_, v___y_1715_);
lean_dec(v_j_1705_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1716_);
v___x_1718_ = v___x_1709_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
else
{
lean_object* v_ks_1748_; lean_object* v_vs_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1769_; 
v_ks_1748_ = lean_ctor_get(v_x_1697_, 0);
v_vs_1749_ = lean_ctor_get(v_x_1697_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1751_ = v_x_1697_;
v_isShared_1752_ = v_isSharedCheck_1769_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_vs_1749_);
lean_inc(v_ks_1748_);
lean_dec(v_x_1697_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1769_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_ks_1748_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_vs_1749_);
v___x_1754_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v_newNode_1755_; uint8_t v___y_1757_; size_t v___x_1763_; uint8_t v___x_1764_; 
v_newNode_1755_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v___x_1754_, v_x_1700_, v_x_1701_);
v___x_1763_ = ((size_t)7ULL);
v___x_1764_ = lean_usize_dec_le(v___x_1763_, v_x_1699_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1765_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1755_);
v___x_1766_ = lean_unsigned_to_nat(4u);
v___x_1767_ = lean_nat_dec_lt(v___x_1765_, v___x_1766_);
lean_dec(v___x_1765_);
v___y_1757_ = v___x_1767_;
goto v___jp_1756_;
}
else
{
v___y_1757_ = v___x_1764_;
goto v___jp_1756_;
}
v___jp_1756_:
{
if (v___y_1757_ == 0)
{
lean_object* v_ks_1758_; lean_object* v_vs_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_ks_1758_ = lean_ctor_get(v_newNode_1755_, 0);
lean_inc_ref(v_ks_1758_);
v_vs_1759_ = lean_ctor_get(v_newNode_1755_, 1);
lean_inc_ref(v_vs_1759_);
lean_dec_ref(v_newNode_1755_);
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0);
v___x_1762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_x_1699_, v_ks_1758_, v_vs_1759_, v___x_1760_, v___x_1761_);
lean_dec_ref(v_vs_1759_);
lean_dec_ref(v_ks_1758_);
return v___x_1762_;
}
else
{
return v_newNode_1755_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t v_depth_1770_, lean_object* v_keys_1771_, lean_object* v_vals_1772_, lean_object* v_i_1773_, lean_object* v_entries_1774_){
_start:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_array_get_size(v_keys_1771_);
v___x_1776_ = lean_nat_dec_lt(v_i_1773_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec(v_i_1773_);
return v_entries_1774_;
}
else
{
lean_object* v_k_1777_; lean_object* v_v_1778_; uint64_t v___y_1780_; 
v_k_1777_ = lean_array_fget_borrowed(v_keys_1771_, v_i_1773_);
v_v_1778_ = lean_array_fget_borrowed(v_vals_1772_, v_i_1773_);
if (lean_obj_tag(v_k_1777_) == 0)
{
uint64_t v___x_1791_; 
v___x_1791_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1780_ = v___x_1791_;
goto v___jp_1779_;
}
else
{
uint64_t v_hash_1792_; 
v_hash_1792_ = lean_ctor_get_uint64(v_k_1777_, sizeof(void*)*2);
v___y_1780_ = v_hash_1792_;
goto v___jp_1779_;
}
v___jp_1779_:
{
size_t v_h_1781_; size_t v___x_1782_; lean_object* v___x_1783_; size_t v___x_1784_; size_t v___x_1785_; size_t v___x_1786_; size_t v_h_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_h_1781_ = lean_uint64_to_usize(v___y_1780_);
v___x_1782_ = ((size_t)5ULL);
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = ((size_t)1ULL);
v___x_1785_ = lean_usize_sub(v_depth_1770_, v___x_1784_);
v___x_1786_ = lean_usize_mul(v___x_1782_, v___x_1785_);
v_h_1787_ = lean_usize_shift_right(v_h_1781_, v___x_1786_);
v___x_1788_ = lean_nat_add(v_i_1773_, v___x_1783_);
lean_dec(v_i_1773_);
lean_inc(v_v_1778_);
lean_inc(v_k_1777_);
v___x_1789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_entries_1774_, v_h_1787_, v_depth_1770_, v_k_1777_, v_v_1778_);
v_i_1773_ = v___x_1788_;
v_entries_1774_ = v___x_1789_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_1793_, lean_object* v_keys_1794_, lean_object* v_vals_1795_, lean_object* v_i_1796_, lean_object* v_entries_1797_){
_start:
{
size_t v_depth_boxed_1798_; lean_object* v_res_1799_; 
v_depth_boxed_1798_ = lean_unbox_usize(v_depth_1793_);
lean_dec(v_depth_1793_);
v_res_1799_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_boxed_1798_, v_keys_1794_, v_vals_1795_, v_i_1796_, v_entries_1797_);
lean_dec_ref(v_vals_1795_);
lean_dec_ref(v_keys_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_x_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
size_t v_x_1569__boxed_1805_; size_t v_x_1570__boxed_1806_; lean_object* v_res_1807_; 
v_x_1569__boxed_1805_ = lean_unbox_usize(v_x_1801_);
lean_dec(v_x_1801_);
v_x_1570__boxed_1806_ = lean_unbox_usize(v_x_1802_);
lean_dec(v_x_1802_);
v_res_1807_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1800_, v_x_1569__boxed_1805_, v_x_1570__boxed_1806_, v_x_1803_, v_x_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_){
_start:
{
uint64_t v___y_1812_; 
if (lean_obj_tag(v_x_1809_) == 0)
{
uint64_t v___x_1816_; 
v___x_1816_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1812_ = v___x_1816_;
goto v___jp_1811_;
}
else
{
uint64_t v_hash_1817_; 
v_hash_1817_ = lean_ctor_get_uint64(v_x_1809_, sizeof(void*)*2);
v___y_1812_ = v_hash_1817_;
goto v___jp_1811_;
}
v___jp_1811_:
{
size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_uint64_to_usize(v___y_1812_);
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1808_, v___x_1813_, v___x_1814_, v_x_1809_, v_x_1810_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v_fst_1820_; lean_object* v_snd_1821_; lean_object* v___x_1822_; 
v_fst_1820_ = lean_ctor_get(v_x_1819_, 0);
lean_inc(v_fst_1820_);
v_snd_1821_ = lean_ctor_get(v_x_1819_, 1);
lean_inc(v_snd_1821_);
lean_dec_ref(v_x_1819_);
v___x_1822_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1818_, v_fst_1820_, v_snd_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1856_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1858_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
uint8_t v___x_1862_; 
v___x_1862_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1860_, v_x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
uint8_t v_res_1866_; lean_object* v_r_1867_; 
v_res_1866_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1863_, v_x_1864_, v_x_1865_);
lean_dec(v_x_1865_);
lean_dec_ref(v_x_1864_);
v_r_1867_ = lean_box(v_res_1866_);
return v_r_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1868_, lean_object* v_m_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1871_, lean_object* v_m_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1871_, v_m_1872_);
lean_dec_ref(v_m_1872_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1874_, lean_object* v_as_1875_, lean_object* v_lo_1876_, lean_object* v_hi_1877_, lean_object* v_w_1878_, lean_object* v_hlo_1879_, lean_object* v_hhi_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1874_, v_as_1875_, v_lo_1876_, v_hi_1877_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1882_, lean_object* v_as_1883_, lean_object* v_lo_1884_, lean_object* v_hi_1885_, lean_object* v_w_1886_, lean_object* v_hlo_1887_, lean_object* v_hhi_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1882_, v_as_1883_, v_lo_1884_, v_hi_1885_, v_w_1886_, v_hlo_1887_, v_hhi_1888_);
lean_dec(v_hi_1885_);
lean_dec(v_n_1882_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1891_, v_x_1892_, v_x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1895_, lean_object* v_x_1896_, size_t v_x_1897_, lean_object* v_x_1898_){
_start:
{
uint8_t v___x_1899_; 
v___x_1899_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1896_, v_x_1897_, v_x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1900_, lean_object* v_x_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
size_t v_x_1876__boxed_1904_; uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_x_1876__boxed_1904_ = lean_unbox_usize(v_x_1902_);
lean_dec(v_x_1902_);
v_res_1905_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1900_, v_x_1901_, v_x_1876__boxed_1904_, v_x_1903_);
lean_dec(v_x_1903_);
lean_dec_ref(v_x_1901_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_map_1909_, lean_object* v_f_1910_, lean_object* v_init_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1909_, v_f_1910_, v_init_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_map_1915_, lean_object* v_f_1916_, lean_object* v_init_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1913_, v_00_u03b2_1914_, v_map_1915_, v_f_1916_, v_init_1917_);
lean_dec_ref(v_map_1915_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_n_1919_, lean_object* v_lo_1920_, lean_object* v_hi_1921_, lean_object* v_hhi_1922_, lean_object* v_pivot_1923_, lean_object* v_as_1924_, lean_object* v_i_1925_, lean_object* v_k_1926_, lean_object* v_ilo_1927_, lean_object* v_ik_1928_, lean_object* v_w_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1921_, v_pivot_1923_, v_as_1924_, v_i_1925_, v_k_1926_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_n_1931_, lean_object* v_lo_1932_, lean_object* v_hi_1933_, lean_object* v_hhi_1934_, lean_object* v_pivot_1935_, lean_object* v_as_1936_, lean_object* v_i_1937_, lean_object* v_k_1938_, lean_object* v_ilo_1939_, lean_object* v_ik_1940_, lean_object* v_w_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(v_n_1931_, v_lo_1932_, v_hi_1933_, v_hhi_1934_, v_pivot_1935_, v_as_1936_, v_i_1937_, v_k_1938_, v_ilo_1939_, v_ik_1940_, v_w_1941_);
lean_dec_ref(v_pivot_1935_);
lean_dec(v_hi_1933_);
lean_dec(v_lo_1932_);
lean_dec(v_n_1931_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1943_, lean_object* v_x_1944_, size_t v_x_1945_, size_t v_x_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1944_, v_x_1945_, v_x_1946_, v_x_1947_, v_x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
size_t v_x_1891__boxed_1956_; size_t v_x_1892__boxed_1957_; lean_object* v_res_1958_; 
v_x_1891__boxed_1956_ = lean_unbox_usize(v_x_1952_);
lean_dec(v_x_1952_);
v_x_1892__boxed_1957_ = lean_unbox_usize(v_x_1953_);
lean_dec(v_x_1953_);
v_res_1958_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1950_, v_x_1951_, v_x_1891__boxed_1956_, v_x_1892__boxed_1957_, v_x_1954_, v_x_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1959_, lean_object* v_keys_1960_, lean_object* v_vals_1961_, lean_object* v_heq_1962_, lean_object* v_i_1963_, lean_object* v_k_1964_){
_start:
{
uint8_t v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1960_, v_i_1963_, v_k_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1966_, lean_object* v_keys_1967_, lean_object* v_vals_1968_, lean_object* v_heq_1969_, lean_object* v_i_1970_, lean_object* v_k_1971_){
_start:
{
uint8_t v_res_1972_; lean_object* v_r_1973_; 
v_res_1972_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1966_, v_keys_1967_, v_vals_1968_, v_heq_1969_, v_i_1970_, v_k_1971_);
lean_dec(v_k_1971_);
lean_dec_ref(v_vals_1968_);
lean_dec_ref(v_keys_1967_);
v_r_1973_ = lean_box(v_res_1972_);
return v_r_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1974_, lean_object* v_f_1975_, lean_object* v_init_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1975_, v_map_1974_, v_init_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1978_, lean_object* v_f_1979_, lean_object* v_init_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1978_, v_f_1979_, v_init_1980_);
lean_dec_ref(v_map_1978_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1982_, lean_object* v_00_u03b2_1983_, lean_object* v_map_1984_, lean_object* v_f_1985_, lean_object* v_init_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1985_, v_map_1984_, v_init_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1988_, lean_object* v_00_u03b2_1989_, lean_object* v_map_1990_, lean_object* v_f_1991_, lean_object* v_init_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1988_, v_00_u03b2_1989_, v_map_1990_, v_f_1991_, v_init_1992_);
lean_dec_ref(v_map_1990_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1994_, lean_object* v_n_1995_, lean_object* v_k_1996_, lean_object* v_v_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_n_1995_, v_k_1996_, v_v_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1999_, size_t v_depth_2000_, lean_object* v_keys_2001_, lean_object* v_vals_2002_, lean_object* v_heq_2003_, lean_object* v_i_2004_, lean_object* v_entries_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_2000_, v_keys_2001_, v_vals_2002_, v_i_2004_, v_entries_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2007_, lean_object* v_depth_2008_, lean_object* v_keys_2009_, lean_object* v_vals_2010_, lean_object* v_heq_2011_, lean_object* v_i_2012_, lean_object* v_entries_2013_){
_start:
{
size_t v_depth_boxed_2014_; lean_object* v_res_2015_; 
v_depth_boxed_2014_ = lean_unbox_usize(v_depth_2008_);
lean_dec(v_depth_2008_);
v_res_2015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(v_00_u03b2_2007_, v_depth_boxed_2014_, v_keys_2009_, v_vals_2010_, v_heq_2011_, v_i_2012_, v_entries_2013_);
lean_dec_ref(v_vals_2010_);
lean_dec_ref(v_keys_2009_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2016_, lean_object* v_00_u03b1_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_f_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2019_, v_x_2020_, v_x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2023_, lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_f_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_2023_, v_00_u03b1_2024_, v_00_u03b2_2025_, v_f_2026_, v_x_2027_, v_x_2028_);
lean_dec_ref(v_x_2027_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_x_2031_, v_x_2032_, v_x_2033_, v_x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_2036_, lean_object* v_00_u03b2_2037_, lean_object* v_00_u03c3_2038_, lean_object* v_f_2039_, lean_object* v_as_2040_, size_t v_i_2041_, size_t v_stop_2042_, lean_object* v_b_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_2039_, v_as_2040_, v_i_2041_, v_stop_2042_, v_b_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2045_, lean_object* v_00_u03b2_2046_, lean_object* v_00_u03c3_2047_, lean_object* v_f_2048_, lean_object* v_as_2049_, lean_object* v_i_2050_, lean_object* v_stop_2051_, lean_object* v_b_2052_){
_start:
{
size_t v_i_boxed_2053_; size_t v_stop_boxed_2054_; lean_object* v_res_2055_; 
v_i_boxed_2053_ = lean_unbox_usize(v_i_2050_);
lean_dec(v_i_2050_);
v_stop_boxed_2054_ = lean_unbox_usize(v_stop_2051_);
lean_dec(v_stop_2051_);
v_res_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_2045_, v_00_u03b2_2046_, v_00_u03c3_2047_, v_f_2048_, v_as_2049_, v_i_boxed_2053_, v_stop_boxed_2054_, v_b_2052_);
lean_dec_ref(v_as_2049_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03c3_2056_, lean_object* v_00_u03b1_2057_, lean_object* v_00_u03b2_2058_, lean_object* v_f_2059_, lean_object* v_keys_2060_, lean_object* v_vals_2061_, lean_object* v_heq_2062_, lean_object* v_i_2063_, lean_object* v_acc_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_2059_, v_keys_2060_, v_vals_2061_, v_i_2063_, v_acc_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03c3_2066_, lean_object* v_00_u03b1_2067_, lean_object* v_00_u03b2_2068_, lean_object* v_f_2069_, lean_object* v_keys_2070_, lean_object* v_vals_2071_, lean_object* v_heq_2072_, lean_object* v_i_2073_, lean_object* v_acc_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(v_00_u03c3_2066_, v_00_u03b1_2067_, v_00_u03b2_2068_, v_f_2069_, v_keys_2070_, v_vals_2071_, v_heq_2072_, v_i_2073_, v_acc_2074_);
lean_dec_ref(v_vals_2071_);
lean_dec_ref(v_keys_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2076_, lean_object* v_fid_2077_, lean_object* v_v_2078_){
_start:
{
lean_object* v___x_2079_; lean_object* v_toEnvExtension_2080_; lean_object* v_asyncMode_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2079_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2080_ = lean_ctor_get(v___x_2079_, 0);
v_asyncMode_2081_ = lean_ctor_get(v_toEnvExtension_2080_, 2);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v_fid_2077_);
lean_ctor_set(v___x_2082_, 1, v_v_2078_);
v___x_2083_ = lean_box(0);
v___x_2084_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2079_, v_env_2076_, v___x_2082_, v_asyncMode_2081_, v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2085_, lean_object* v_vals_2086_, lean_object* v_i_2087_, lean_object* v_k_2088_){
_start:
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = lean_array_get_size(v_keys_2085_);
v___x_2090_ = lean_nat_dec_lt(v_i_2087_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec(v_i_2087_);
v___x_2091_ = lean_box(0);
return v___x_2091_;
}
else
{
lean_object* v_k_x27_2092_; uint8_t v___x_2093_; 
v_k_x27_2092_ = lean_array_fget_borrowed(v_keys_2085_, v_i_2087_);
v___x_2093_ = lean_name_eq(v_k_2088_, v_k_x27_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = lean_nat_add(v_i_2087_, v___x_2094_);
lean_dec(v_i_2087_);
v_i_2087_ = v___x_2095_;
goto _start;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_array_fget_borrowed(v_vals_2086_, v_i_2087_);
lean_dec(v_i_2087_);
lean_inc(v___x_2097_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2099_, lean_object* v_vals_2100_, lean_object* v_i_2101_, lean_object* v_k_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2099_, v_vals_2100_, v_i_2101_, v_k_2102_);
lean_dec(v_k_2102_);
lean_dec_ref(v_vals_2100_);
lean_dec_ref(v_keys_2099_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2104_, size_t v_x_2105_, lean_object* v_x_2106_){
_start:
{
if (lean_obj_tag(v_x_2104_) == 0)
{
lean_object* v_es_2107_; lean_object* v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; lean_object* v_j_2111_; lean_object* v___x_2112_; 
v_es_2107_ = lean_ctor_get(v_x_2104_, 0);
v___x_2108_ = lean_box(2);
v___x_2109_ = ((size_t)31ULL);
v___x_2110_ = lean_usize_land(v_x_2105_, v___x_2109_);
v_j_2111_ = lean_usize_to_nat(v___x_2110_);
v___x_2112_ = lean_array_get_borrowed(v___x_2108_, v_es_2107_, v_j_2111_);
lean_dec(v_j_2111_);
switch(lean_obj_tag(v___x_2112_))
{
case 0:
{
lean_object* v_key_2113_; lean_object* v_val_2114_; uint8_t v___x_2115_; 
v_key_2113_ = lean_ctor_get(v___x_2112_, 0);
v_val_2114_ = lean_ctor_get(v___x_2112_, 1);
v___x_2115_ = lean_name_eq(v_x_2106_, v_key_2113_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_box(0);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; 
lean_inc(v_val_2114_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_val_2114_);
return v___x_2117_;
}
}
case 1:
{
lean_object* v_node_2118_; size_t v___x_2119_; size_t v___x_2120_; 
v_node_2118_ = lean_ctor_get(v___x_2112_, 0);
v___x_2119_ = ((size_t)5ULL);
v___x_2120_ = lean_usize_shift_right(v_x_2105_, v___x_2119_);
v_x_2104_ = v_node_2118_;
v_x_2105_ = v___x_2120_;
goto _start;
}
default: 
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_box(0);
return v___x_2122_;
}
}
}
else
{
lean_object* v_ks_2123_; lean_object* v_vs_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_ks_2123_ = lean_ctor_get(v_x_2104_, 0);
v_vs_2124_ = lean_ctor_get(v_x_2104_, 1);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2123_, v_vs_2124_, v___x_2125_, v_x_2106_);
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_){
_start:
{
size_t v_x_386__boxed_2130_; lean_object* v_res_2131_; 
v_x_386__boxed_2130_ = lean_unbox_usize(v_x_2128_);
lean_dec(v_x_2128_);
v_res_2131_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2127_, v_x_386__boxed_2130_, v_x_2129_);
lean_dec(v_x_2129_);
lean_dec_ref(v_x_2127_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2132_, lean_object* v_x_2133_){
_start:
{
uint64_t v___y_2135_; 
if (lean_obj_tag(v_x_2133_) == 0)
{
uint64_t v___x_2138_; 
v___x_2138_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_2135_ = v___x_2138_;
goto v___jp_2134_;
}
else
{
uint64_t v_hash_2139_; 
v_hash_2139_ = lean_ctor_get_uint64(v_x_2133_, sizeof(void*)*2);
v___y_2135_ = v_hash_2139_;
goto v___jp_2134_;
}
v___jp_2134_:
{
size_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_uint64_to_usize(v___y_2135_);
v___x_2137_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2132_, v___x_2136_, v_x_2133_);
return v___x_2137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2140_, v_x_2141_);
lean_dec(v_x_2141_);
lean_dec_ref(v_x_2140_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2143_, lean_object* v_k_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v_m_2149_; lean_object* v_a_2150_; uint8_t v___x_2151_; 
v___x_2147_ = lean_nat_add(v_x_2145_, v_x_2146_);
v___x_2148_ = lean_unsigned_to_nat(1u);
v_m_2149_ = lean_nat_shiftr(v___x_2147_, v___x_2148_);
lean_dec(v___x_2147_);
v_a_2150_ = lean_array_fget_borrowed(v_as_2143_, v_m_2149_);
v___x_2151_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2150_, v_k_2144_);
if (v___x_2151_ == 0)
{
uint8_t v___x_2152_; 
lean_dec(v_x_2146_);
v___x_2152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2144_, v_a_2150_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_dec(v_m_2149_);
lean_dec(v_x_2145_);
lean_inc(v_a_2150_);
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_a_2150_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = lean_nat_dec_eq(v_m_2149_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = lean_nat_sub(v_m_2149_, v___x_2148_);
lean_dec(v_m_2149_);
v___x_2157_ = lean_nat_dec_lt(v___x_2156_, v_x_2145_);
if (v___x_2157_ == 0)
{
v_x_2146_ = v___x_2156_;
goto _start;
}
else
{
lean_object* v___x_2159_; 
lean_dec(v___x_2156_);
lean_dec(v_x_2145_);
v___x_2159_ = lean_box(0);
return v___x_2159_;
}
}
else
{
lean_object* v___x_2160_; 
lean_dec(v_m_2149_);
lean_dec(v_x_2145_);
v___x_2160_ = lean_box(0);
return v___x_2160_;
}
}
}
else
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
lean_dec(v_x_2145_);
v___x_2161_ = lean_nat_add(v_m_2149_, v___x_2148_);
lean_dec(v_m_2149_);
v___x_2162_ = lean_nat_dec_le(v___x_2161_, v_x_2146_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_dec(v___x_2161_);
lean_dec(v_x_2146_);
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
else
{
v_x_2145_ = v___x_2161_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2165_, lean_object* v_k_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2165_, v_k_2166_, v_x_2167_, v_x_2168_);
lean_dec_ref(v_k_2166_);
lean_dec_ref(v_as_2165_);
return v_res_2169_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2173_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2174_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2176_ = lean_box(0);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2178_, lean_object* v_fid_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2189_; 
v___x_2180_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2181_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2189_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2178_, v_fid_2179_);
if (lean_obj_tag(v___x_2189_) == 0)
{
goto v___jp_2182_;
}
else
{
lean_object* v_val_2190_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v_val_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_val_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2212_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_2180_, v___x_2181_, v_env_2178_, v_val_2190_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_array_get_size(v___x_2212_);
v___x_2215_ = lean_nat_dec_lt(v___x_2213_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_dec_ref(v___x_2212_);
goto v___jp_2191_;
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_sub(v___x_2214_, v___x_2216_);
v___x_2218_ = lean_nat_dec_le(v___x_2213_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_dec(v___x_2217_);
lean_dec_ref(v___x_2212_);
goto v___jp_2191_;
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_box(0);
lean_inc(v_fid_2179_);
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v_fid_2179_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2212_, v___x_2220_, v___x_2213_, v___x_2217_);
lean_dec_ref_known(v___x_2220_, 2);
lean_dec_ref(v___x_2212_);
if (lean_obj_tag(v___x_2221_) == 0)
{
goto v___jp_2191_;
}
else
{
lean_object* v_val_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_val_2190_);
lean_dec(v_fid_2179_);
lean_dec_ref(v_env_2178_);
v_val_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_val_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v_snd_2226_; lean_object* v___x_2228_; 
v_snd_2226_ = lean_ctor_get(v_val_2222_, 1);
lean_inc(v_snd_2226_);
lean_dec(v_val_2222_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v_snd_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_snd_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
v___jp_2191_:
{
uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2192_ = 0;
v___x_2193_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2180_, v___x_2181_, v_env_2178_, v_val_2190_, v___x_2192_);
lean_dec(v_val_2190_);
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_array_get_size(v___x_2193_);
v___x_2196_ = lean_nat_dec_lt(v___x_2194_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_dec_ref(v___x_2193_);
goto v___jp_2182_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2197_ = lean_unsigned_to_nat(1u);
v___x_2198_ = lean_nat_sub(v___x_2195_, v___x_2197_);
v___x_2199_ = lean_nat_dec_le(v___x_2194_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_dec(v___x_2198_);
lean_dec_ref(v___x_2193_);
goto v___jp_2182_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_box(0);
lean_inc(v_fid_2179_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_fid_2179_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2193_, v___x_2201_, v___x_2194_, v___x_2198_);
lean_dec_ref_known(v___x_2201_, 2);
lean_dec_ref(v___x_2193_);
if (lean_obj_tag(v___x_2202_) == 0)
{
goto v___jp_2182_;
}
else
{
lean_object* v_val_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_fid_2179_);
lean_dec_ref(v_env_2178_);
v_val_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_val_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_snd_2207_; lean_object* v___x_2209_; 
v_snd_2207_ = lean_ctor_get(v_val_2203_, 1);
lean_inc(v_snd_2207_);
lean_dec(v_val_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_snd_2207_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_snd_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
}
v___jp_2182_:
{
lean_object* v_toEnvExtension_2183_; lean_object* v_asyncMode_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v_snd_2187_; lean_object* v___x_2188_; 
v_toEnvExtension_2183_ = lean_ctor_get(v___x_2181_, 0);
v_asyncMode_2184_ = lean_ctor_get(v_toEnvExtension_2183_, 2);
v___x_2185_ = lean_box(0);
v___x_2186_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2180_, v___x_2181_, v_env_2178_, v_asyncMode_2184_, v___x_2185_);
v_snd_2187_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_snd_2187_);
lean_dec(v___x_2186_);
v___x_2188_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2187_, v_fid_2179_);
lean_dec(v_fid_2179_);
lean_dec(v_snd_2187_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2232_, v_x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2235_, v_x_2236_, v_x_2237_);
lean_dec(v_x_2237_);
lean_dec_ref(v_x_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2239_, lean_object* v_k_2240_, lean_object* v_x_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2239_, v_k_2240_, v_x_2241_, v_x_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2245_, lean_object* v_k_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_, lean_object* v_x_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2245_, v_k_2246_, v_x_2247_, v_x_2248_, v_x_2249_);
lean_dec_ref(v_k_2246_);
lean_dec_ref(v_as_2245_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2251_, lean_object* v_x_2252_, size_t v_x_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2252_, v_x_2253_, v_x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_, lean_object* v_x_2259_){
_start:
{
size_t v_x_625__boxed_2260_; lean_object* v_res_2261_; 
v_x_625__boxed_2260_ = lean_unbox_usize(v_x_2258_);
lean_dec(v_x_2258_);
v_res_2261_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2256_, v_x_2257_, v_x_625__boxed_2260_, v_x_2259_);
lean_dec(v_x_2259_);
lean_dec_ref(v_x_2257_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2262_, lean_object* v_keys_2263_, lean_object* v_vals_2264_, lean_object* v_heq_2265_, lean_object* v_i_2266_, lean_object* v_k_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2263_, v_vals_2264_, v_i_2266_, v_k_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2269_, lean_object* v_keys_2270_, lean_object* v_vals_2271_, lean_object* v_heq_2272_, lean_object* v_i_2273_, lean_object* v_k_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2269_, v_keys_2270_, v_vals_2271_, v_heq_2272_, v_i_2273_, v_k_2274_);
lean_dec(v_k_2274_);
lean_dec_ref(v_vals_2271_);
lean_dec_ref(v_keys_2270_);
return v_res_2275_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2279_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2280_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2279_, v___x_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v_assignments_2285_; lean_object* v_currFnIdx_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2284_ = lean_st_ref_get(v_a_2282_);
v_assignments_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_ref(v_assignments_2285_);
lean_dec(v___x_2284_);
v_currFnIdx_2286_ = lean_ctor_get(v_a_2281_, 1);
v___x_2287_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2288_ = lean_array_get(v___x_2287_, v_assignments_2285_, v_currFnIdx_2286_);
lean_dec_ref(v_assignments_2285_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2294_, v_a_2295_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v_funVals_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2313_ = lean_st_ref_get(v_a_2311_);
v_funVals_2314_ = lean_ctor_get(v___x_2313_, 1);
lean_inc_ref(v_funVals_2314_);
lean_dec(v___x_2313_);
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_array_get(v___x_2315_, v_funVals_2314_, v_funIdx_2310_);
lean_dec_ref(v_funVals_2314_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2318_, v_a_2319_);
lean_dec(v_a_2319_);
lean_dec(v_funIdx_2318_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2322_, v_a_2324_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_funIdx_2331_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2340_, lean_object* v_as_2341_, lean_object* v_j_2342_){
_start:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_array_get_size(v_as_2341_);
v___x_2344_ = lean_nat_dec_lt(v_j_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec(v_j_2342_);
v___x_2345_ = lean_box(0);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v_toSignature_2347_; lean_object* v_name_2348_; uint8_t v___x_2349_; 
v___x_2346_ = lean_array_fget_borrowed(v_as_2341_, v_j_2342_);
v_toSignature_2347_ = lean_ctor_get(v___x_2346_, 0);
v_name_2348_ = lean_ctor_get(v_toSignature_2347_, 0);
v___x_2349_ = lean_name_eq(v_name_2348_, v_declName_2340_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = lean_nat_add(v_j_2342_, v___x_2350_);
lean_dec(v_j_2342_);
v_j_2342_ = v___x_2351_;
goto _start;
}
else
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_j_2342_);
return v___x_2353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2354_, lean_object* v_as_2355_, lean_object* v_j_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2354_, v_as_2355_, v_j_2356_);
lean_dec_ref(v_as_2355_);
lean_dec(v_declName_2354_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_decls_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_decls_2362_ = lean_ctor_get(v_a_2359_, 0);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2358_, v_decls_2362_, v___x_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
else
{
lean_object* v_val_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2383_; 
v_val_2367_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2369_ = v___x_2364_;
v_isShared_2370_ = v_isSharedCheck_2383_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_val_2367_);
lean_dec(v___x_2364_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2383_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2382_; 
v___x_2371_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2367_, v_a_2360_);
lean_dec(v_val_2367_);
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v_a_2372_);
v___x_2377_ = v___x_2369_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2377_);
v___x_2379_ = v___x_2374_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_declName_2384_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2389_, v_a_2390_, v_a_2391_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_declName_2398_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v_currFnIdx_2412_; lean_object* v_assignments_2413_; lean_object* v_funVals_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2432_; 
v___x_2411_ = lean_st_ref_take(v_a_2409_);
v_currFnIdx_2412_ = lean_ctor_get(v_a_2408_, 1);
v_assignments_2413_ = lean_ctor_get(v___x_2411_, 0);
v_funVals_2414_ = lean_ctor_get(v___x_2411_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2416_ = v___x_2411_;
v_isShared_2417_ = v_isSharedCheck_2432_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_funVals_2414_);
lean_inc(v_assignments_2413_);
lean_dec(v___x_2411_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2432_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___y_2420_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2418_ = lean_box(0);
v___x_2426_ = lean_array_get_size(v_assignments_2413_);
v___x_2427_ = lean_nat_dec_lt(v_currFnIdx_2412_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_dec_ref(v_f_2407_);
v___y_2420_ = v_assignments_2413_;
goto v___jp_2419_;
}
else
{
lean_object* v_v_2428_; lean_object* v_xs_x27_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_v_2428_ = lean_array_fget(v_assignments_2413_, v_currFnIdx_2412_);
v_xs_x27_2429_ = lean_array_fset(v_assignments_2413_, v_currFnIdx_2412_, v___x_2418_);
v___x_2430_ = lean_apply_1(v_f_2407_, v_v_2428_);
v___x_2431_ = lean_array_fset(v_xs_x27_2429_, v_currFnIdx_2412_, v___x_2430_);
v___y_2420_ = v___x_2431_;
goto v___jp_2419_;
}
v___jp_2419_:
{
lean_object* v___x_2422_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___y_2420_);
v___x_2422_ = v___x_2416_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___y_2420_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_funVals_2414_);
v___x_2422_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_st_ref_set(v_a_2409_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2418_);
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2438_, v_a_2439_, v_a_2440_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2456_, lean_object* v_fallback_2457_, lean_object* v_x_2458_){
_start:
{
if (lean_obj_tag(v_x_2458_) == 0)
{
lean_inc(v_fallback_2457_);
return v_fallback_2457_;
}
else
{
lean_object* v_key_2459_; lean_object* v_value_2460_; lean_object* v_tail_2461_; uint8_t v___x_2462_; 
v_key_2459_ = lean_ctor_get(v_x_2458_, 0);
v_value_2460_ = lean_ctor_get(v_x_2458_, 1);
v_tail_2461_ = lean_ctor_get(v_x_2458_, 2);
v___x_2462_ = l_Lean_instBEqFVarId_beq(v_key_2459_, v_a_2456_);
if (v___x_2462_ == 0)
{
v_x_2458_ = v_tail_2461_;
goto _start;
}
else
{
lean_inc(v_value_2460_);
return v_value_2460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2464_, lean_object* v_fallback_2465_, lean_object* v_x_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2464_, v_fallback_2465_, v_x_2466_);
lean_dec(v_x_2466_);
lean_dec(v_fallback_2465_);
lean_dec(v_a_2464_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2468_, lean_object* v_a_2469_, lean_object* v_fallback_2470_){
_start:
{
lean_object* v_buckets_2471_; lean_object* v___x_2472_; uint64_t v___x_2473_; uint64_t v___x_2474_; uint64_t v___x_2475_; uint64_t v_fold_2476_; uint64_t v___x_2477_; uint64_t v___x_2478_; uint64_t v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; size_t v___x_2482_; size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_buckets_2471_ = lean_ctor_get(v_m_2468_, 1);
v___x_2472_ = lean_array_get_size(v_buckets_2471_);
v___x_2473_ = l_Lean_instHashableFVarId_hash(v_a_2469_);
v___x_2474_ = 32ULL;
v___x_2475_ = lean_uint64_shift_right(v___x_2473_, v___x_2474_);
v_fold_2476_ = lean_uint64_xor(v___x_2473_, v___x_2475_);
v___x_2477_ = 16ULL;
v___x_2478_ = lean_uint64_shift_right(v_fold_2476_, v___x_2477_);
v___x_2479_ = lean_uint64_xor(v_fold_2476_, v___x_2478_);
v___x_2480_ = lean_uint64_to_usize(v___x_2479_);
v___x_2481_ = lean_usize_of_nat(v___x_2472_);
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_sub(v___x_2481_, v___x_2482_);
v___x_2484_ = lean_usize_land(v___x_2480_, v___x_2483_);
v___x_2485_ = lean_array_uget_borrowed(v_buckets_2471_, v___x_2484_);
v___x_2486_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2469_, v_fallback_2470_, v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2487_, lean_object* v_a_2488_, lean_object* v_fallback_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2487_, v_a_2488_, v_fallback_2489_);
lean_dec(v_fallback_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_m_2487_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2505_; 
v___x_2495_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2492_, v_a_2493_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2500_ = lean_box(0);
v___x_2501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2496_, v_var_2491_, v___x_2500_);
lean_dec(v_a_2496_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2501_);
v___x_2503_ = v___x_2498_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_var_2506_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2511_, v_a_2512_, v_a_2513_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_var_2520_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2529_, lean_object* v_m_2530_, lean_object* v_a_2531_, lean_object* v_fallback_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2530_, v_a_2531_, v_fallback_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2534_, lean_object* v_m_2535_, lean_object* v_a_2536_, lean_object* v_fallback_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2534_, v_m_2535_, v_a_2536_, v_fallback_2537_);
lean_dec(v_fallback_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_m_2535_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2539_, lean_object* v_a_2540_, lean_object* v_fallback_2541_, lean_object* v_x_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2540_, v_fallback_2541_, v_x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2544_, lean_object* v_a_2545_, lean_object* v_fallback_2546_, lean_object* v_x_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2544_, v_a_2545_, v_fallback_2546_, v_x_2547_);
lean_dec(v_x_2547_);
lean_dec(v_fallback_2546_);
lean_dec(v_a_2545_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
if (lean_obj_tag(v_arg_2549_) == 1)
{
lean_object* v_fvarId_2553_; lean_object* v___x_2554_; 
v_fvarId_2553_ = lean_ctor_get(v_arg_2549_, 0);
v___x_2554_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2553_, v_a_2550_, v_a_2551_);
return v___x_2554_;
}
else
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_box(1);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_arg_2557_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2562_, v_a_2563_, v_a_2564_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_arg_2571_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2580_, lean_object* v_b_2581_, lean_object* v_x_2582_){
_start:
{
if (lean_obj_tag(v_x_2582_) == 0)
{
lean_dec(v_b_2581_);
lean_dec(v_a_2580_);
return v_x_2582_;
}
else
{
lean_object* v_key_2583_; lean_object* v_value_2584_; lean_object* v_tail_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2597_; 
v_key_2583_ = lean_ctor_get(v_x_2582_, 0);
v_value_2584_ = lean_ctor_get(v_x_2582_, 1);
v_tail_2585_ = lean_ctor_get(v_x_2582_, 2);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_x_2582_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2587_ = v_x_2582_;
v_isShared_2588_ = v_isSharedCheck_2597_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_tail_2585_);
lean_inc(v_value_2584_);
lean_inc(v_key_2583_);
lean_dec(v_x_2582_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2597_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
uint8_t v___x_2589_; 
v___x_2589_ = l_Lean_instBEqFVarId_beq(v_key_2583_, v_a_2580_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2580_, v_b_2581_, v_tail_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 2, v___x_2590_);
v___x_2592_ = v___x_2587_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_key_2583_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_value_2584_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
else
{
lean_object* v___x_2595_; 
lean_dec(v_value_2584_);
lean_dec(v_key_2583_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v_b_2581_);
lean_ctor_set(v___x_2587_, 0, v_a_2580_);
v___x_2595_ = v___x_2587_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2580_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_b_2581_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_tail_2585_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2598_, lean_object* v_x_2599_){
_start:
{
if (lean_obj_tag(v_x_2599_) == 0)
{
return v_x_2598_;
}
else
{
lean_object* v_key_2600_; lean_object* v_value_2601_; lean_object* v_tail_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2625_; 
v_key_2600_ = lean_ctor_get(v_x_2599_, 0);
v_value_2601_ = lean_ctor_get(v_x_2599_, 1);
v_tail_2602_ = lean_ctor_get(v_x_2599_, 2);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_x_2599_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2604_ = v_x_2599_;
v_isShared_2605_ = v_isSharedCheck_2625_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_tail_2602_);
lean_inc(v_value_2601_);
lean_inc(v_key_2600_);
lean_dec(v_x_2599_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2625_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; uint64_t v___x_2607_; uint64_t v___x_2608_; uint64_t v___x_2609_; uint64_t v_fold_2610_; uint64_t v___x_2611_; uint64_t v___x_2612_; uint64_t v___x_2613_; size_t v___x_2614_; size_t v___x_2615_; size_t v___x_2616_; size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2606_ = lean_array_get_size(v_x_2598_);
v___x_2607_ = l_Lean_instHashableFVarId_hash(v_key_2600_);
v___x_2608_ = 32ULL;
v___x_2609_ = lean_uint64_shift_right(v___x_2607_, v___x_2608_);
v_fold_2610_ = lean_uint64_xor(v___x_2607_, v___x_2609_);
v___x_2611_ = 16ULL;
v___x_2612_ = lean_uint64_shift_right(v_fold_2610_, v___x_2611_);
v___x_2613_ = lean_uint64_xor(v_fold_2610_, v___x_2612_);
v___x_2614_ = lean_uint64_to_usize(v___x_2613_);
v___x_2615_ = lean_usize_of_nat(v___x_2606_);
v___x_2616_ = ((size_t)1ULL);
v___x_2617_ = lean_usize_sub(v___x_2615_, v___x_2616_);
v___x_2618_ = lean_usize_land(v___x_2614_, v___x_2617_);
v___x_2619_ = lean_array_uget_borrowed(v_x_2598_, v___x_2618_);
lean_inc(v___x_2619_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 2, v___x_2619_);
v___x_2621_ = v___x_2604_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_key_2600_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_value_2601_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_array_uset(v_x_2598_, v___x_2618_, v___x_2621_);
v_x_2598_ = v___x_2622_;
v_x_2599_ = v_tail_2602_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2626_, lean_object* v_source_2627_, lean_object* v_target_2628_){
_start:
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = lean_array_get_size(v_source_2627_);
v___x_2630_ = lean_nat_dec_lt(v_i_2626_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_dec_ref(v_source_2627_);
lean_dec(v_i_2626_);
return v_target_2628_;
}
else
{
lean_object* v_es_2631_; lean_object* v___x_2632_; lean_object* v_source_2633_; lean_object* v_target_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_es_2631_ = lean_array_fget(v_source_2627_, v_i_2626_);
v___x_2632_ = lean_box(0);
v_source_2633_ = lean_array_fset(v_source_2627_, v_i_2626_, v___x_2632_);
v_target_2634_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2628_, v_es_2631_);
v___x_2635_ = lean_unsigned_to_nat(1u);
v___x_2636_ = lean_nat_add(v_i_2626_, v___x_2635_);
lean_dec(v_i_2626_);
v_i_2626_ = v___x_2636_;
v_source_2627_ = v_source_2633_;
v_target_2628_ = v_target_2634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2638_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v_nbuckets_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2639_ = lean_array_get_size(v_data_2638_);
v___x_2640_ = lean_unsigned_to_nat(2u);
v_nbuckets_2641_ = lean_nat_mul(v___x_2639_, v___x_2640_);
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_mk_array(v_nbuckets_2641_, v___x_2643_);
v___x_2645_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2642_, v_data_2638_, v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2646_, lean_object* v_x_2647_){
_start:
{
if (lean_obj_tag(v_x_2647_) == 0)
{
uint8_t v___x_2648_; 
v___x_2648_ = 0;
return v___x_2648_;
}
else
{
lean_object* v_key_2649_; lean_object* v_tail_2650_; uint8_t v___x_2651_; 
v_key_2649_ = lean_ctor_get(v_x_2647_, 0);
v_tail_2650_ = lean_ctor_get(v_x_2647_, 2);
v___x_2651_ = l_Lean_instBEqFVarId_beq(v_key_2649_, v_a_2646_);
if (v___x_2651_ == 0)
{
v_x_2647_ = v_tail_2650_;
goto _start;
}
else
{
return v___x_2651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2653_, lean_object* v_x_2654_){
_start:
{
uint8_t v_res_2655_; lean_object* v_r_2656_; 
v_res_2655_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2653_, v_x_2654_);
lean_dec(v_x_2654_);
lean_dec(v_a_2653_);
v_r_2656_ = lean_box(v_res_2655_);
return v_r_2656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2657_, lean_object* v_a_2658_, lean_object* v_b_2659_){
_start:
{
lean_object* v_size_2660_; lean_object* v_buckets_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2704_; 
v_size_2660_ = lean_ctor_get(v_m_2657_, 0);
v_buckets_2661_ = lean_ctor_get(v_m_2657_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_m_2657_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2663_ = v_m_2657_;
v_isShared_2664_ = v_isSharedCheck_2704_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_buckets_2661_);
lean_inc(v_size_2660_);
lean_dec(v_m_2657_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2704_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; uint64_t v___x_2666_; uint64_t v___x_2667_; uint64_t v___x_2668_; uint64_t v_fold_2669_; uint64_t v___x_2670_; uint64_t v___x_2671_; uint64_t v___x_2672_; size_t v___x_2673_; size_t v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; size_t v___x_2677_; lean_object* v_bkt_2678_; uint8_t v___x_2679_; 
v___x_2665_ = lean_array_get_size(v_buckets_2661_);
v___x_2666_ = l_Lean_instHashableFVarId_hash(v_a_2658_);
v___x_2667_ = 32ULL;
v___x_2668_ = lean_uint64_shift_right(v___x_2666_, v___x_2667_);
v_fold_2669_ = lean_uint64_xor(v___x_2666_, v___x_2668_);
v___x_2670_ = 16ULL;
v___x_2671_ = lean_uint64_shift_right(v_fold_2669_, v___x_2670_);
v___x_2672_ = lean_uint64_xor(v_fold_2669_, v___x_2671_);
v___x_2673_ = lean_uint64_to_usize(v___x_2672_);
v___x_2674_ = lean_usize_of_nat(v___x_2665_);
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = lean_usize_sub(v___x_2674_, v___x_2675_);
v___x_2677_ = lean_usize_land(v___x_2673_, v___x_2676_);
v_bkt_2678_ = lean_array_uget_borrowed(v_buckets_2661_, v___x_2677_);
v___x_2679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2658_, v_bkt_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v_size_x27_2681_; lean_object* v___x_2682_; lean_object* v_buckets_x27_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2680_ = lean_unsigned_to_nat(1u);
v_size_x27_2681_ = lean_nat_add(v_size_2660_, v___x_2680_);
lean_dec(v_size_2660_);
lean_inc(v_bkt_2678_);
v___x_2682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2682_, 0, v_a_2658_);
lean_ctor_set(v___x_2682_, 1, v_b_2659_);
lean_ctor_set(v___x_2682_, 2, v_bkt_2678_);
v_buckets_x27_2683_ = lean_array_uset(v_buckets_2661_, v___x_2677_, v___x_2682_);
v___x_2684_ = lean_unsigned_to_nat(4u);
v___x_2685_ = lean_nat_mul(v_size_x27_2681_, v___x_2684_);
v___x_2686_ = lean_unsigned_to_nat(3u);
v___x_2687_ = lean_nat_div(v___x_2685_, v___x_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_array_get_size(v_buckets_x27_2683_);
v___x_2689_ = lean_nat_dec_le(v___x_2687_, v___x_2688_);
lean_dec(v___x_2687_);
if (v___x_2689_ == 0)
{
lean_object* v_val_2690_; lean_object* v___x_2692_; 
v_val_2690_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2683_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v_val_2690_);
lean_ctor_set(v___x_2663_, 0, v_size_x27_2681_);
v___x_2692_ = v___x_2663_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_size_x27_2681_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_val_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
else
{
lean_object* v___x_2695_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v_buckets_x27_2683_);
lean_ctor_set(v___x_2663_, 0, v_size_x27_2681_);
v___x_2695_ = v___x_2663_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_size_x27_2681_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_buckets_x27_2683_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
else
{
lean_object* v___x_2697_; lean_object* v_buckets_x27_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_inc(v_bkt_2678_);
v___x_2697_ = lean_box(0);
v_buckets_x27_2698_ = lean_array_uset(v_buckets_2661_, v___x_2677_, v___x_2697_);
v___x_2699_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2658_, v_b_2659_, v_bkt_2678_);
v___x_2700_ = lean_array_uset(v_buckets_x27_2698_, v___x_2677_, v___x_2699_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___x_2700_);
v___x_2702_ = v___x_2663_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_size_2660_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2705_, lean_object* v___x_2706_, lean_object* v_x_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2707_, v_var_2705_, v___x_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2709_, lean_object* v_newVal_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = lean_st_ref_get(v_a_2713_);
v___x_2716_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2709_, v_a_2711_, v_a_2712_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v_env_2718_; lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v_env_2718_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_ref(v_env_2718_);
lean_dec(v___x_2715_);
v___x_2719_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2718_, v_a_2717_, v_newVal_2710_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2720_, 0, v_var_2709_);
lean_closure_set(v___f_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2720_, v_a_2711_, v_a_2712_);
return v___x_2721_;
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___x_2715_);
lean_dec(v_newVal_2710_);
lean_dec(v_var_2709_);
v_a_2722_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2716_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2716_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2730_, lean_object* v_newVal_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2730_, v_newVal_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2737_, lean_object* v_newVal_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2737_, v_newVal_2738_, v_a_2739_, v_a_2740_, v_a_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2747_, lean_object* v_newVal_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2747_, v_newVal_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2757_, lean_object* v_m_2758_, lean_object* v_a_2759_, lean_object* v_b_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2758_, v_a_2759_, v_b_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2762_, lean_object* v_a_2763_, lean_object* v_x_2764_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2763_, v_x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2766_, lean_object* v_a_2767_, lean_object* v_x_2768_){
_start:
{
uint8_t v_res_2769_; lean_object* v_r_2770_; 
v_res_2769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2766_, v_a_2767_, v_x_2768_);
lean_dec(v_x_2768_);
lean_dec(v_a_2767_);
v_r_2770_ = lean_box(v_res_2769_);
return v_r_2770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2771_, lean_object* v_data_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2774_, lean_object* v_a_2775_, lean_object* v_b_2776_, lean_object* v_x_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2775_, v_b_2776_, v_x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2779_, lean_object* v_i_2780_, lean_object* v_source_2781_, lean_object* v_target_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2780_, v_source_2781_, v_target_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2785_, v_x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_box(0);
v___x_2791_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2789_, v_var_2788_, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___f_2796_; lean_object* v___x_2797_; 
v___f_2796_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2796_, 0, v_var_2792_);
v___x_2797_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2796_, v_a_2793_, v_a_2794_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2803_, v_a_2804_, v_a_2805_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v_fst_2829_; lean_object* v_snd_2830_; lean_object* v_currFnIdx_2833_; lean_object* v_assignments_2834_; lean_object* v_funVals_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2826_ = lean_st_ref_get(v_a_2824_);
v___x_2827_ = lean_st_ref_take(v_a_2823_);
v_currFnIdx_2833_ = lean_ctor_get(v_a_2822_, 1);
v_assignments_2834_ = lean_ctor_get(v___x_2827_, 0);
lean_inc_ref(v_assignments_2834_);
v_funVals_2835_ = lean_ctor_get(v___x_2827_, 1);
lean_inc_ref(v_funVals_2835_);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_array_get_size(v_funVals_2835_);
v___x_2838_ = lean_nat_dec_lt(v_currFnIdx_2833_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_dec_ref(v_funVals_2835_);
lean_dec_ref(v_assignments_2834_);
lean_dec(v___x_2826_);
lean_dec(v_v_2821_);
v_fst_2829_ = v___x_2836_;
v_snd_2830_ = v___x_2827_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2850_; 
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2850_ == 0)
{
lean_object* v_unused_2851_; lean_object* v_unused_2852_; 
v_unused_2851_ = lean_ctor_get(v___x_2827_, 1);
lean_dec(v_unused_2851_);
v_unused_2852_ = lean_ctor_get(v___x_2827_, 0);
lean_dec(v_unused_2852_);
v___x_2840_ = v___x_2827_;
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2827_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_env_2842_; lean_object* v_v_2843_; lean_object* v_xs_x27_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v_env_2842_ = lean_ctor_get(v___x_2826_, 0);
lean_inc_ref(v_env_2842_);
lean_dec(v___x_2826_);
v_v_2843_ = lean_array_fget(v_funVals_2835_, v_currFnIdx_2833_);
v_xs_x27_2844_ = lean_array_fset(v_funVals_2835_, v_currFnIdx_2833_, v___x_2836_);
v___x_2845_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2842_, v_v_2821_, v_v_2843_);
v___x_2846_ = lean_array_fset(v_xs_x27_2844_, v_currFnIdx_2833_, v___x_2845_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v___x_2846_);
v___x_2848_ = v___x_2840_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_assignments_2834_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
v_fst_2829_ = v___x_2836_;
v_snd_2830_ = v___x_2848_;
goto v___jp_2828_;
}
}
}
v___jp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_st_ref_set(v_a_2823_, v_snd_2830_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v_fst_2829_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
lean_dec(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2859_, v_a_2860_, v_a_2861_, v_a_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2877_, uint8_t v_b_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_array_2883_; lean_object* v_start_2884_; lean_object* v_stop_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2922_; 
v_array_2883_ = lean_ctor_get(v_a_2877_, 0);
v_start_2884_ = lean_ctor_get(v_a_2877_, 1);
v_stop_2885_ = lean_ctor_get(v_a_2877_, 2);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_a_2877_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2887_ = v_a_2877_;
v_isShared_2888_ = v_isSharedCheck_2922_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_stop_2885_);
lean_inc(v_start_2884_);
lean_inc(v_array_2883_);
lean_dec(v_a_2877_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2922_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_nat_dec_lt(v_start_2884_, v_stop_2885_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_del_object(v___x_2887_);
lean_dec(v_stop_2885_);
lean_dec(v_start_2884_);
lean_dec_ref(v_array_2883_);
v___x_2890_ = lean_box(v_b_2878_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; lean_object* v_fvarId_2893_; lean_object* v___x_2894_; 
v___x_2892_ = lean_array_fget_borrowed(v_array_2883_, v_start_2884_);
v_fvarId_2893_ = lean_ctor_get(v___x_2892_, 0);
v___x_2894_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2893_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = lean_box(1);
lean_inc(v_fvarId_2893_);
v___x_2897_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2893_, v___x_2896_, v___y_2879_, v___y_2880_, v___y_2881_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
lean_dec_ref_known(v___x_2897_, 1);
v___x_2898_ = lean_unsigned_to_nat(1u);
v___x_2899_ = lean_nat_add(v_start_2884_, v___x_2898_);
lean_dec(v_start_2884_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v___x_2899_);
v___x_2901_ = v___x_2887_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_array_2883_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2905_, 2, v_stop_2885_);
v___x_2901_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = lean_box(0);
v___x_2903_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2895_, v___x_2902_);
lean_dec(v_a_2895_);
v_a_2877_ = v___x_2901_;
v_b_2878_ = v___x_2903_;
goto _start;
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2895_);
lean_del_object(v___x_2887_);
lean_dec(v_stop_2885_);
lean_dec(v_start_2884_);
lean_dec_ref(v_array_2883_);
v_a_2906_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2897_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2897_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_del_object(v___x_2887_);
lean_dec(v_stop_2885_);
lean_dec(v_start_2884_);
lean_dec_ref(v_array_2883_);
v_a_2914_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2894_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2894_);
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
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2923_, lean_object* v_b_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
uint8_t v_b_boxed_2929_; lean_object* v_res_2930_; 
v_b_boxed_2929_ = lean_unbox(v_b_2924_);
v_res_2930_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2923_, v_b_boxed_2929_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2931_, lean_object* v___x_2932_, lean_object* v_x_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2933_, v_fvarId_2931_, v___x_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2935_, lean_object* v_as_2936_, size_t v_sz_2937_, size_t v_i_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_a_2944_; uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_lt(v_i_2938_, v_sz_2937_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref(v___x_2935_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_b_2939_);
return v___x_2949_;
}
else
{
lean_object* v_snd_2950_; lean_object* v_fst_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3018_; 
v_snd_2950_ = lean_ctor_get(v_b_2939_, 1);
v_fst_2951_ = lean_ctor_get(v_b_2939_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_b_2939_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2953_ = v_b_2939_;
v_isShared_2954_ = v_isSharedCheck_3018_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_snd_2950_);
lean_inc(v_fst_2951_);
lean_dec(v_b_2939_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3018_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_array_2955_; lean_object* v_start_2956_; lean_object* v_stop_2957_; uint8_t v___x_2958_; 
v_array_2955_ = lean_ctor_get(v_snd_2950_, 0);
v_start_2956_ = lean_ctor_get(v_snd_2950_, 1);
v_stop_2957_ = lean_ctor_get(v_snd_2950_, 2);
v___x_2958_ = lean_nat_dec_lt(v_start_2956_, v_stop_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2960_; 
lean_dec_ref(v___x_2935_);
if (v_isShared_2954_ == 0)
{
v___x_2960_ = v___x_2953_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_fst_2951_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_snd_2950_);
v___x_2960_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
return v___x_2961_;
}
}
else
{
lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_3014_; 
lean_inc(v_stop_2957_);
lean_inc(v_start_2956_);
lean_inc_ref(v_array_2955_);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_snd_2950_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; lean_object* v_unused_3016_; lean_object* v_unused_3017_; 
v_unused_3015_ = lean_ctor_get(v_snd_2950_, 2);
lean_dec(v_unused_3015_);
v_unused_3016_ = lean_ctor_get(v_snd_2950_, 1);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v_snd_2950_, 0);
lean_dec(v_unused_3017_);
v___x_2964_ = v_snd_2950_;
v_isShared_2965_ = v_isSharedCheck_3014_;
goto v_resetjp_2963_;
}
else
{
lean_dec(v_snd_2950_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_3014_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_a_2966_; lean_object* v_fvarId_2967_; lean_object* v___x_2968_; 
v_a_2966_ = lean_array_uget_borrowed(v_as_2936_, v_i_2938_);
v_fvarId_2967_ = lean_ctor_get(v_a_2966_, 0);
v___x_2968_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2967_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = lean_array_fget_borrowed(v_array_2955_, v_start_2956_);
v___x_2971_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2970_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2973_ = lean_unsigned_to_nat(1u);
v___x_2974_ = lean_nat_add(v_start_2956_, v___x_2973_);
lean_dec(v_start_2956_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v___x_2974_);
v___x_2976_ = v___x_2964_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_array_2955_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_stop_2957_);
v___x_2976_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; uint8_t v___x_2978_; uint8_t v___x_2979_; 
lean_inc(v_a_2969_);
lean_inc_ref(v___x_2935_);
v___x_2977_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2935_, v_a_2969_, v_a_2972_);
v___x_2978_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2977_, v_a_2969_);
lean_dec(v_a_2969_);
v___x_2979_ = lean_bool_not(v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2981_; 
lean_dec(v___x_2977_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2976_);
v___x_2981_ = v___x_2953_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_fst_2951_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
v_a_2944_ = v___x_2981_;
goto v___jp_2943_;
}
}
else
{
lean_object* v___f_2983_; lean_object* v___x_2984_; 
lean_dec(v_fst_2951_);
lean_inc(v_fvarId_2967_);
v___f_2983_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2983_, 0, v_fvarId_2967_);
lean_closure_set(v___f_2983_, 1, v___x_2977_);
v___x_2984_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2983_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_dec_ref_known(v___x_2984_, 1);
v___x_2985_ = lean_box(v___x_2979_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2976_);
lean_ctor_set(v___x_2953_, 0, v___x_2985_);
v___x_2987_ = v___x_2953_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2976_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
v_a_2944_ = v___x_2987_;
goto v___jp_2943_;
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v___x_2976_);
lean_del_object(v___x_2953_);
lean_dec_ref(v___x_2935_);
v_a_2989_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2984_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2984_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_a_2969_);
lean_del_object(v___x_2964_);
lean_dec(v_stop_2957_);
lean_dec(v_start_2956_);
lean_dec_ref(v_array_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_fst_2951_);
lean_dec_ref(v___x_2935_);
v_a_2998_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2971_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2971_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_del_object(v___x_2964_);
lean_dec(v_stop_2957_);
lean_dec(v_start_2956_);
lean_dec_ref(v_array_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_fst_2951_);
lean_dec_ref(v___x_2935_);
v_a_3006_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2968_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2968_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
}
v___jp_2943_:
{
size_t v___x_2945_; size_t v___x_2946_; 
v___x_2945_ = ((size_t)1ULL);
v___x_2946_ = lean_usize_add(v_i_2938_, v___x_2945_);
v_i_2938_ = v___x_2946_;
v_b_2939_ = v_a_2944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3019_, lean_object* v_as_3020_, lean_object* v_sz_3021_, lean_object* v_i_3022_, lean_object* v_b_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
size_t v_sz_boxed_3027_; size_t v_i_boxed_3028_; lean_object* v_res_3029_; 
v_sz_boxed_3027_ = lean_unbox_usize(v_sz_3021_);
lean_dec(v_sz_3021_);
v_i_boxed_3028_ = lean_unbox_usize(v_i_3022_);
lean_dec(v_i_3022_);
v_res_3029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3019_, v_as_3020_, v_sz_boxed_3027_, v_i_boxed_3028_, v_b_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec_ref(v_as_3020_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3030_, lean_object* v_args_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v_env_3040_; uint8_t v_ret_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; size_t v_sz_3047_; size_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3039_ = lean_st_ref_get(v_a_3037_);
v_env_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc_ref(v_env_3040_);
lean_dec(v___x_3039_);
v_ret_3041_ = 0;
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = lean_array_get_size(v_args_3031_);
v___x_3044_ = l_Array_toSubarray___redArg(v_args_3031_, v___x_3042_, v___x_3043_);
v___x_3045_ = lean_box(v_ret_3041_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3044_);
v_sz_3047_ = lean_array_size(v_params_3030_);
v___x_3048_ = ((size_t)0ULL);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3040_, v_params_3030_, v_sz_3047_, v___x_3048_, v___x_3046_, v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3068_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3068_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3068_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v_fst_3054_; lean_object* v_lower_3056_; lean_object* v_upper_3057_; lean_object* v___x_3061_; uint8_t v___x_3062_; uint8_t v___x_3063_; 
v_fst_3054_ = lean_ctor_get(v_a_3050_, 0);
lean_inc(v_fst_3054_);
lean_dec(v_a_3050_);
v___x_3061_ = lean_array_get_size(v_params_3030_);
v___x_3062_ = lean_nat_dec_eq(v___x_3061_, v___x_3043_);
v___x_3063_ = lean_bool_not(v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3065_; 
lean_dec_ref(v_params_3030_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v_fst_3054_);
v___x_3065_ = v___x_3052_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_fst_3054_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
else
{
uint8_t v___x_3067_; 
lean_del_object(v___x_3052_);
v___x_3067_ = lean_nat_dec_le(v___x_3043_, v___x_3042_);
if (v___x_3067_ == 0)
{
v_lower_3056_ = v___x_3043_;
v_upper_3057_ = v___x_3061_;
goto v___jp_3055_;
}
else
{
v_lower_3056_ = v___x_3042_;
v_upper_3057_ = v___x_3061_;
goto v___jp_3055_;
}
}
v___jp_3055_:
{
lean_object* v___x_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = l_Array_toSubarray___redArg(v_params_3030_, v_lower_3056_, v_upper_3057_);
v___x_3059_ = lean_unbox(v_fst_3054_);
lean_dec(v_fst_3054_);
v___x_3060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3058_, v___x_3059_, v_a_3032_, v_a_3033_, v_a_3037_);
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec_ref(v_params_3030_);
v_a_3069_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3049_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3049_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3077_, lean_object* v_args_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3077_, v_args_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3087_, lean_object* v_as_3088_, size_t v_sz_3089_, size_t v_i_3090_, lean_object* v_b_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3087_, v_as_3088_, v_sz_3089_, v_i_3090_, v_b_3091_, v___y_3092_, v___y_3093_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3100_, lean_object* v_as_3101_, lean_object* v_sz_3102_, lean_object* v_i_3103_, lean_object* v_b_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
size_t v_sz_boxed_3112_; size_t v_i_boxed_3113_; lean_object* v_res_3114_; 
v_sz_boxed_3112_ = lean_unbox_usize(v_sz_3102_);
lean_dec(v_sz_3102_);
v_i_boxed_3113_ = lean_unbox_usize(v_i_3103_);
lean_dec(v_i_3103_);
v_res_3114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3100_, v_as_3101_, v_sz_boxed_3112_, v_i_boxed_3113_, v_b_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec_ref(v_as_3101_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3115_, lean_object* v_R_3116_, lean_object* v_a_3117_, uint8_t v_b_3118_, lean_object* v_c_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3117_, v_b_3118_, v___y_3120_, v___y_3121_, v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3128_, lean_object* v_R_3129_, lean_object* v_a_3130_, lean_object* v_b_3131_, lean_object* v_c_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
uint8_t v_b_boxed_3140_; lean_object* v_res_3141_; 
v_b_boxed_3140_ = lean_unbox(v_b_3131_);
v_res_3141_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3128_, v_R_3129_, v_a_3130_, v_b_boxed_3140_, v_c_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3142_, size_t v_sz_3143_, size_t v_i_3144_, uint8_t v_b_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
uint8_t v_a_3150_; uint8_t v___x_3154_; 
v___x_3154_ = lean_usize_dec_lt(v_i_3144_, v_sz_3143_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_box(v_b_3145_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
else
{
lean_object* v_a_3157_; lean_object* v_fvarId_3158_; lean_object* v___x_3159_; 
v_a_3157_ = lean_array_uget_borrowed(v_as_3142_, v_i_3144_);
v_fvarId_3158_ = lean_ctor_get(v_a_3157_, 0);
v___x_3159_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3158_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; uint8_t v___x_3163_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_box(1);
v___x_3162_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3161_, v_a_3160_);
lean_dec(v_a_3160_);
v___x_3163_ = lean_bool_not(v___x_3162_);
if (v___x_3163_ == 0)
{
v_a_3150_ = v_b_3145_;
goto v___jp_3149_;
}
else
{
lean_object* v___f_3164_; lean_object* v___x_3165_; 
lean_inc(v_fvarId_3158_);
v___f_3164_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3164_, 0, v_fvarId_3158_);
lean_closure_set(v___f_3164_, 1, v___x_3161_);
v___x_3165_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3164_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_dec_ref_known(v___x_3165_, 1);
v_a_3150_ = v___x_3163_;
goto v___jp_3149_;
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3165_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3165_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
v_a_3174_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3159_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3159_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
v___jp_3149_:
{
size_t v___x_3151_; size_t v___x_3152_; 
v___x_3151_ = ((size_t)1ULL);
v___x_3152_ = lean_usize_add(v_i_3144_, v___x_3151_);
v_i_3144_ = v___x_3152_;
v_b_3145_ = v_a_3150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3182_, lean_object* v_sz_3183_, lean_object* v_i_3184_, lean_object* v_b_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
size_t v_sz_boxed_3189_; size_t v_i_boxed_3190_; uint8_t v_b_boxed_3191_; lean_object* v_res_3192_; 
v_sz_boxed_3189_ = lean_unbox_usize(v_sz_3183_);
lean_dec(v_sz_3183_);
v_i_boxed_3190_ = lean_unbox_usize(v_i_3184_);
lean_dec(v_i_3184_);
v_b_boxed_3191_ = lean_unbox(v_b_3185_);
v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3182_, v_sz_boxed_3189_, v_i_boxed_3190_, v_b_boxed_3191_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec_ref(v_as_3182_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
uint8_t v_ret_3201_; size_t v_sz_3202_; size_t v___x_3203_; lean_object* v___x_3204_; 
v_ret_3201_ = 0;
v_sz_3202_ = lean_array_size(v_params_3193_);
v___x_3203_ = ((size_t)0ULL);
v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3193_, v_sz_3202_, v___x_3203_, v_ret_3201_, v_a_3194_, v_a_3195_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec_ref(v_params_3205_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3214_, size_t v_sz_3215_, size_t v_i_3216_, uint8_t v_b_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3214_, v_sz_3215_, v_i_3216_, v_b_3217_, v___y_3218_, v___y_3219_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3226_, lean_object* v_sz_3227_, lean_object* v_i_3228_, lean_object* v_b_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
size_t v_sz_boxed_3237_; size_t v_i_boxed_3238_; uint8_t v_b_boxed_3239_; lean_object* v_res_3240_; 
v_sz_boxed_3237_ = lean_unbox_usize(v_sz_3227_);
lean_dec(v_sz_3227_);
v_i_boxed_3238_ = lean_unbox_usize(v_i_3228_);
lean_dec(v_i_3228_);
v_b_boxed_3239_ = lean_unbox(v_b_3229_);
v_res_3240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3226_, v_sz_boxed_3237_, v_i_boxed_3238_, v_b_boxed_3239_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec_ref(v_as_3226_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3241_, size_t v_i_3242_, size_t v_stop_3243_, lean_object* v_b_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
uint8_t v___x_3248_; 
v___x_3248_ = lean_usize_dec_eq(v_i_3242_, v_stop_3243_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v_fvarId_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_array_uget_borrowed(v_as_3241_, v_i_3242_);
v_fvarId_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_fvarId_3250_);
v___x_3251_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3250_, v___y_3245_, v___y_3246_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; size_t v___x_3253_; size_t v___x_3254_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
v___x_3253_ = ((size_t)1ULL);
v___x_3254_ = lean_usize_add(v_i_3242_, v___x_3253_);
v_i_3242_ = v___x_3254_;
v_b_3244_ = v_a_3252_;
goto _start;
}
else
{
return v___x_3251_;
}
}
else
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_b_3244_);
return v___x_3256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3257_, lean_object* v_i_3258_, lean_object* v_stop_3259_, lean_object* v_b_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
size_t v_i_boxed_3264_; size_t v_stop_boxed_3265_; lean_object* v_res_3266_; 
v_i_boxed_3264_ = lean_unbox_usize(v_i_3258_);
lean_dec(v_i_3258_);
v_stop_boxed_3265_ = lean_unbox_usize(v_stop_3259_);
lean_dec(v_stop_3259_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3257_, v_i_boxed_3264_, v_stop_boxed_3265_, v_b_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec_ref(v_as_3257_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v_decl_3286_; lean_object* v_k_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; 
switch(lean_obj_tag(v_x_3267_))
{
case 0:
{
lean_object* v_k_3308_; 
v_k_3308_ = lean_ctor_get(v_x_3267_, 1);
lean_inc_ref(v_k_3308_);
lean_dec_ref_known(v_x_3267_, 2);
v_x_3267_ = v_k_3308_;
goto _start;
}
case 3:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec_ref_known(v_x_3267_, 2);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
case 4:
{
lean_object* v_cases_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3334_; 
v_cases_3312_ = lean_ctor_get(v_x_3267_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_x_3267_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3314_ = v_x_3267_;
v_isShared_3315_ = v_isSharedCheck_3334_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_cases_3312_);
lean_dec(v_x_3267_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3334_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_alts_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v_alts_3316_ = lean_ctor_get(v_cases_3312_, 3);
lean_inc_ref(v_alts_3316_);
lean_dec_ref(v_cases_3312_);
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = lean_array_get_size(v_alts_3316_);
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_nat_dec_lt(v___x_3317_, v___x_3318_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v_alts_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3319_);
v___x_3322_ = v___x_3314_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3319_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
else
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_nat_dec_le(v___x_3318_, v___x_3318_);
if (v___x_3324_ == 0)
{
if (v___x_3320_ == 0)
{
lean_object* v___x_3326_; 
lean_dec_ref(v_alts_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3319_);
v___x_3326_ = v___x_3314_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3319_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
else
{
size_t v___x_3328_; size_t v___x_3329_; lean_object* v___x_3330_; 
lean_del_object(v___x_3314_);
v___x_3328_ = ((size_t)0ULL);
v___x_3329_ = lean_usize_of_nat(v___x_3318_);
v___x_3330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3316_, v___x_3328_, v___x_3329_, v___x_3319_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
lean_dec_ref(v_alts_3316_);
return v___x_3330_;
}
}
else
{
size_t v___x_3331_; size_t v___x_3332_; lean_object* v___x_3333_; 
lean_del_object(v___x_3314_);
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = lean_usize_of_nat(v___x_3318_);
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3316_, v___x_3331_, v___x_3332_, v___x_3319_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
lean_dec_ref(v_alts_3316_);
return v___x_3333_;
}
}
}
}
case 5:
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3342_; 
v_isSharedCheck_3342_ = !lean_is_exclusive(v_x_3267_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v_x_3267_, 0);
lean_dec(v_unused_3343_);
v___x_3336_ = v_x_3267_;
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v_x_3267_);
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
case 6:
{
lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3351_; 
v_isSharedCheck_3351_ = !lean_is_exclusive(v_x_3267_);
if (v_isSharedCheck_3351_ == 0)
{
lean_object* v_unused_3352_; 
v_unused_3352_ = lean_ctor_get(v_x_3267_, 0);
lean_dec(v_unused_3352_);
v___x_3345_ = v_x_3267_;
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
else
{
lean_dec(v_x_3267_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_box(0);
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3347_);
v___x_3349_ = v___x_3345_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
default: 
{
lean_object* v_decl_3353_; lean_object* v_k_3354_; 
v_decl_3353_ = lean_ctor_get(v_x_3267_, 0);
lean_inc_ref(v_decl_3353_);
v_k_3354_ = lean_ctor_get(v_x_3267_, 1);
lean_inc_ref(v_k_3354_);
lean_dec_ref(v_x_3267_);
v_decl_3286_ = v_decl_3353_;
v_k_3287_ = v_k_3354_;
v___y_3288_ = v_a_3268_;
v___y_3289_ = v_a_3269_;
v___y_3290_ = v_a_3270_;
v___y_3291_ = v_a_3271_;
v___y_3292_ = v_a_3272_;
v___y_3293_ = v_a_3273_;
goto v___jp_3285_;
}
}
v___jp_3275_:
{
if (lean_obj_tag(v___y_3283_) == 0)
{
lean_dec_ref_known(v___y_3283_, 1);
v_x_3267_ = v___y_3277_;
v_a_3268_ = v___y_3276_;
v_a_3269_ = v___y_3279_;
v_a_3270_ = v___y_3282_;
v_a_3271_ = v___y_3280_;
v_a_3272_ = v___y_3278_;
v_a_3273_ = v___y_3281_;
goto _start;
}
else
{
lean_dec_ref(v___y_3277_);
return v___y_3283_;
}
}
v___jp_3285_:
{
lean_object* v_params_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v_params_3294_ = lean_ctor_get(v_decl_3286_, 2);
lean_inc_ref(v_params_3294_);
lean_dec_ref(v_decl_3286_);
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = lean_array_get_size(v_params_3294_);
v___x_3297_ = lean_nat_dec_lt(v___x_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
lean_dec_ref(v_params_3294_);
v_x_3267_ = v_k_3287_;
v_a_3268_ = v___y_3288_;
v_a_3269_ = v___y_3289_;
v_a_3270_ = v___y_3290_;
v_a_3271_ = v___y_3291_;
v_a_3272_ = v___y_3292_;
v_a_3273_ = v___y_3293_;
goto _start;
}
else
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_nat_dec_le(v___x_3296_, v___x_3296_);
if (v___x_3300_ == 0)
{
if (v___x_3297_ == 0)
{
lean_dec_ref(v_params_3294_);
v_x_3267_ = v_k_3287_;
v_a_3268_ = v___y_3288_;
v_a_3269_ = v___y_3289_;
v_a_3270_ = v___y_3290_;
v_a_3271_ = v___y_3291_;
v_a_3272_ = v___y_3292_;
v_a_3273_ = v___y_3293_;
goto _start;
}
else
{
size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = ((size_t)0ULL);
v___x_3303_ = lean_usize_of_nat(v___x_3296_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3294_, v___x_3302_, v___x_3303_, v___x_3299_, v___y_3288_, v___y_3289_);
lean_dec_ref(v_params_3294_);
v___y_3276_ = v___y_3288_;
v___y_3277_ = v_k_3287_;
v___y_3278_ = v___y_3292_;
v___y_3279_ = v___y_3289_;
v___y_3280_ = v___y_3291_;
v___y_3281_ = v___y_3293_;
v___y_3282_ = v___y_3290_;
v___y_3283_ = v___x_3304_;
goto v___jp_3275_;
}
}
else
{
size_t v___x_3305_; size_t v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = lean_usize_of_nat(v___x_3296_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3294_, v___x_3305_, v___x_3306_, v___x_3299_, v___y_3288_, v___y_3289_);
lean_dec_ref(v_params_3294_);
v___y_3276_ = v___y_3288_;
v___y_3277_ = v_k_3287_;
v___y_3278_ = v___y_3292_;
v___y_3279_ = v___y_3289_;
v___y_3280_ = v___y_3291_;
v___y_3281_ = v___y_3293_;
v___y_3282_ = v___y_3290_;
v___y_3283_ = v___x_3307_;
goto v___jp_3275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3355_, size_t v_i_3356_, size_t v_stop_3357_, lean_object* v_b_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___y_3367_; uint8_t v___x_3373_; 
v___x_3373_ = lean_usize_dec_eq(v_i_3356_, v_stop_3357_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_array_uget_borrowed(v_as_3355_, v_i_3356_);
switch(lean_obj_tag(v___x_3374_))
{
case 0:
{
lean_object* v_code_3375_; 
v_code_3375_ = lean_ctor_get(v___x_3374_, 2);
lean_inc_ref(v_code_3375_);
v___y_3367_ = v_code_3375_;
goto v___jp_3366_;
}
case 1:
{
lean_object* v_code_3376_; 
v_code_3376_ = lean_ctor_get(v___x_3374_, 1);
lean_inc_ref(v_code_3376_);
v___y_3367_ = v_code_3376_;
goto v___jp_3366_;
}
default: 
{
lean_object* v_code_3377_; 
v_code_3377_ = lean_ctor_get(v___x_3374_, 0);
lean_inc_ref(v_code_3377_);
v___y_3367_ = v_code_3377_;
goto v___jp_3366_;
}
}
}
else
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v_b_3358_);
return v___x_3378_;
}
v___jp_3366_:
{
lean_object* v___x_3368_; 
v___x_3368_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3367_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; size_t v___x_3370_; size_t v___x_3371_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3368_, 1);
v___x_3370_ = ((size_t)1ULL);
v___x_3371_ = lean_usize_add(v_i_3356_, v___x_3370_);
v_i_3356_ = v___x_3371_;
v_b_3358_ = v_a_3369_;
goto _start;
}
else
{
return v___x_3368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3379_, lean_object* v_i_3380_, lean_object* v_stop_3381_, lean_object* v_b_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
size_t v_i_boxed_3390_; size_t v_stop_boxed_3391_; lean_object* v_res_3392_; 
v_i_boxed_3390_ = lean_unbox_usize(v_i_3380_);
lean_dec(v_i_3380_);
v_stop_boxed_3391_ = lean_unbox_usize(v_stop_3381_);
lean_dec(v_stop_3381_);
v_res_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3379_, v_i_boxed_3390_, v_stop_boxed_3391_, v_b_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec_ref(v_as_3379_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3402_, size_t v_i_3403_, size_t v_stop_3404_, lean_object* v_b_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3402_, v_i_3403_, v_stop_3404_, v_b_3405_, v___y_3406_, v___y_3407_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3414_, lean_object* v_i_3415_, lean_object* v_stop_3416_, lean_object* v_b_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
size_t v_i_boxed_3425_; size_t v_stop_boxed_3426_; lean_object* v_res_3427_; 
v_i_boxed_3425_ = lean_unbox_usize(v_i_3415_);
lean_dec(v_i_3415_);
v_stop_boxed_3426_ = lean_unbox_usize(v_stop_3416_);
lean_dec(v_stop_3416_);
v_res_3427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3414_, v_i_boxed_3425_, v_stop_boxed_3426_, v_b_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v_as_3414_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3428_, lean_object* v_b_3429_){
_start:
{
lean_object* v_array_3430_; lean_object* v_start_3431_; lean_object* v_stop_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3445_; 
v_array_3430_ = lean_ctor_get(v_a_3428_, 0);
v_start_3431_ = lean_ctor_get(v_a_3428_, 1);
v_stop_3432_ = lean_ctor_get(v_a_3428_, 2);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_a_3428_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3434_ = v_a_3428_;
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_stop_3432_);
lean_inc(v_start_3431_);
lean_inc(v_array_3430_);
lean_dec(v_a_3428_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_nat_dec_lt(v_start_3431_, v_stop_3432_);
if (v___x_3436_ == 0)
{
lean_del_object(v___x_3434_);
lean_dec(v_stop_3432_);
lean_dec(v_start_3431_);
lean_dec_ref(v_array_3430_);
return v_b_3429_;
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3437_ = lean_unsigned_to_nat(1u);
v___x_3438_ = lean_nat_add(v_start_3431_, v___x_3437_);
lean_inc_ref(v_array_3430_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3438_);
v___x_3440_ = v___x_3434_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_array_3430_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_stop_3432_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = lean_array_fget(v_array_3430_, v_start_3431_);
lean_dec(v_start_3431_);
lean_dec_ref(v_array_3430_);
v___x_3442_ = lean_array_push(v_b_3429_, v___x_3441_);
v_a_3428_ = v___x_3440_;
v_b_3429_ = v___x_3442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3446_, size_t v_i_3447_, lean_object* v_bs_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
uint8_t v___x_3452_; 
v___x_3452_ = lean_usize_dec_lt(v_i_3447_, v_sz_3446_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v_bs_3448_);
return v___x_3453_;
}
else
{
lean_object* v_v_3454_; lean_object* v___x_3455_; 
v_v_3454_ = lean_array_uget_borrowed(v_bs_3448_, v_i_3447_);
v___x_3455_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3454_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; lean_object* v_bs_x27_3458_; size_t v___x_3459_; size_t v___x_3460_; lean_object* v___x_3461_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = lean_unsigned_to_nat(0u);
v_bs_x27_3458_ = lean_array_uset(v_bs_3448_, v_i_3447_, v___x_3457_);
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3447_, v___x_3459_);
v___x_3461_ = lean_array_uset(v_bs_x27_3458_, v_i_3447_, v_a_3456_);
v_i_3447_ = v___x_3460_;
v_bs_3448_ = v___x_3461_;
goto _start;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v_bs_3448_);
v_a_3463_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3455_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3455_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3471_, lean_object* v_i_3472_, lean_object* v_bs_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
size_t v_sz_boxed_3477_; size_t v_i_boxed_3478_; lean_object* v_res_3479_; 
v_sz_boxed_3477_ = lean_unbox_usize(v_sz_3471_);
lean_dec(v_sz_3471_);
v_i_boxed_3478_ = lean_unbox_usize(v_i_3472_);
lean_dec(v_i_3472_);
v_res_3479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3477_, v_i_boxed_3478_, v_bs_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3480_, size_t v_i_3481_, size_t v_stop_3482_, lean_object* v_b_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
uint8_t v___x_3488_; 
v___x_3488_ = lean_usize_dec_eq(v_i_3481_, v_stop_3482_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v_fvarId_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3489_ = lean_array_uget_borrowed(v_as_3480_, v_i_3481_);
v_fvarId_3490_ = lean_ctor_get(v___x_3489_, 0);
v___x_3491_ = lean_box(1);
lean_inc(v_fvarId_3490_);
v___x_3492_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3490_, v___x_3491_, v___y_3484_, v___y_3485_, v___y_3486_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; size_t v___x_3494_; size_t v___x_3495_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = ((size_t)1ULL);
v___x_3495_ = lean_usize_add(v_i_3481_, v___x_3494_);
v_i_3481_ = v___x_3495_;
v_b_3483_ = v_a_3493_;
goto _start;
}
else
{
return v___x_3492_;
}
}
else
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v_b_3483_);
return v___x_3497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3498_, lean_object* v_i_3499_, lean_object* v_stop_3500_, lean_object* v_b_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
size_t v_i_boxed_3506_; size_t v_stop_boxed_3507_; lean_object* v_res_3508_; 
v_i_boxed_3506_ = lean_unbox_usize(v_i_3499_);
lean_dec(v_i_3499_);
v_stop_boxed_3507_ = lean_unbox_usize(v_stop_3500_);
lean_dec(v_stop_3500_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3498_, v_i_boxed_3506_, v_stop_boxed_3507_, v_b_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v_as_3498_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3509_, size_t v_i_3510_, size_t v_stop_3511_, lean_object* v_b_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
uint8_t v___x_3517_; 
v___x_3517_ = lean_usize_dec_eq(v_i_3510_, v_stop_3511_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v_fst_3519_; lean_object* v_snd_3520_; lean_object* v_fvarId_3521_; lean_object* v___x_3522_; 
v___x_3518_ = lean_array_uget_borrowed(v_as_3509_, v_i_3510_);
v_fst_3519_ = lean_ctor_get(v___x_3518_, 0);
v_snd_3520_ = lean_ctor_get(v___x_3518_, 1);
v_fvarId_3521_ = lean_ctor_get(v_fst_3519_, 0);
lean_inc(v_snd_3520_);
lean_inc(v_fvarId_3521_);
v___x_3522_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3521_, v_snd_3520_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; size_t v___x_3524_; size_t v___x_3525_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
v___x_3524_ = ((size_t)1ULL);
v___x_3525_ = lean_usize_add(v_i_3510_, v___x_3524_);
v_i_3510_ = v___x_3525_;
v_b_3512_ = v_a_3523_;
goto _start;
}
else
{
return v___x_3522_;
}
}
else
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v_b_3512_);
return v___x_3527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3528_, lean_object* v_i_3529_, lean_object* v_stop_3530_, lean_object* v_b_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
size_t v_i_boxed_3536_; size_t v_stop_boxed_3537_; lean_object* v_res_3538_; 
v_i_boxed_3536_ = lean_unbox_usize(v_i_3529_);
lean_dec(v_i_3529_);
v_stop_boxed_3537_ = lean_unbox_usize(v_stop_3530_);
lean_dec(v_stop_3530_);
v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3528_, v_i_boxed_3536_, v_stop_boxed_3537_, v_b_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec_ref(v_as_3528_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3541_, size_t v_i_3542_, size_t v_stop_3543_, lean_object* v_b_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
uint8_t v___x_3552_; 
v___x_3552_ = lean_usize_dec_eq(v_i_3542_, v_stop_3543_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_array_uget_borrowed(v_as_3541_, v_i_3542_);
v___x_3554_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3553_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; size_t v___x_3556_; size_t v___x_3557_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
v___x_3556_ = ((size_t)1ULL);
v___x_3557_ = lean_usize_add(v_i_3542_, v___x_3556_);
v_i_3542_ = v___x_3557_;
v_b_3544_ = v_a_3555_;
goto _start;
}
else
{
return v___x_3554_;
}
}
else
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_b_3544_);
return v___x_3559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v___y_3575_; 
switch(lean_obj_tag(v_letVal_3560_))
{
case 0:
{
lean_object* v_value_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3592_; 
v_value_3584_ = lean_ctor_get(v_letVal_3560_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_letVal_3560_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3586_ = v_letVal_3560_;
v_isShared_3587_ = v_isSharedCheck_3592_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_value_3584_);
lean_dec(v_letVal_3560_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3592_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3588_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3584_);
lean_dec_ref(v_value_3584_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3588_);
v___x_3590_ = v___x_3586_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
case 1:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = lean_box(1);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
return v___x_3594_;
}
case 2:
{
lean_object* v_idx_3595_; lean_object* v_struct_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_idx_3595_ = lean_ctor_get(v_letVal_3560_, 1);
lean_inc(v_idx_3595_);
v_struct_3596_ = lean_ctor_get(v_letVal_3560_, 2);
lean_inc(v_struct_3596_);
lean_dec_ref_known(v_letVal_3560_, 3);
v___x_3597_ = lean_st_ref_get(v_a_3566_);
v___x_3598_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3596_, v_a_3561_, v_a_3562_);
lean_dec(v_struct_3596_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3608_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3608_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3608_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v_env_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v_env_3603_ = lean_ctor_get(v___x_3597_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3597_);
v___x_3604_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3603_, v_a_3599_, v_idx_3595_);
lean_dec(v_idx_3595_);
lean_dec(v_a_3599_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3604_);
v___x_3606_ = v___x_3601_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
else
{
lean_dec(v___x_3597_);
lean_dec(v_idx_3595_);
return v___x_3598_;
}
}
case 3:
{
lean_object* v_declName_3609_; lean_object* v_args_3610_; lean_object* v___x_3611_; lean_object* v_env_3612_; lean_object* v___x_3613_; lean_object* v_numFields_3615_; lean_object* v_lower_3616_; lean_object* v_upper_3617_; lean_object* v___x_3645_; lean_object* v___y_3714_; uint8_t v___x_3723_; 
v_declName_3609_ = lean_ctor_get(v_letVal_3560_, 0);
lean_inc(v_declName_3609_);
v_args_3610_ = lean_ctor_get(v_letVal_3560_, 2);
lean_inc_ref(v_args_3610_);
lean_dec_ref_known(v_letVal_3560_, 3);
v___x_3611_ = lean_st_ref_get(v_a_3566_);
v_env_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc_ref(v_env_3612_);
lean_dec(v___x_3611_);
v___x_3613_ = lean_unsigned_to_nat(0u);
v___x_3645_ = lean_array_get_size(v_args_3610_);
v___x_3723_ = lean_nat_dec_lt(v___x_3613_, v___x_3645_);
if (v___x_3723_ == 0)
{
goto v___jp_3646_;
}
else
{
lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = lean_box(0);
v___x_3725_ = lean_nat_dec_le(v___x_3645_, v___x_3645_);
if (v___x_3725_ == 0)
{
if (v___x_3723_ == 0)
{
goto v___jp_3646_;
}
else
{
size_t v___x_3726_; size_t v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = ((size_t)0ULL);
v___x_3727_ = lean_usize_of_nat(v___x_3645_);
v___x_3728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3610_, v___x_3726_, v___x_3727_, v___x_3724_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
v___y_3714_ = v___x_3728_;
goto v___jp_3713_;
}
}
else
{
size_t v___x_3729_; size_t v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = lean_usize_of_nat(v___x_3645_);
v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3610_, v___x_3729_, v___x_3730_, v___x_3724_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
v___y_3714_ = v___x_3731_;
goto v___jp_3713_;
}
}
v___jp_3614_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3618_ = l_Array_toSubarray___redArg(v_args_3610_, v_lower_3616_, v_upper_3617_);
v___x_3619_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3620_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3618_, v___x_3619_);
v___x_3621_ = lean_array_get_size(v___x_3620_);
v___x_3622_ = lean_nat_dec_eq(v_numFields_3615_, v___x_3621_);
lean_dec(v_numFields_3615_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
lean_dec_ref(v___x_3620_);
lean_dec(v_declName_3609_);
v___x_3623_ = lean_box(1);
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
return v___x_3624_;
}
else
{
size_t v_sz_3625_; size_t v___x_3626_; lean_object* v___x_3627_; 
v_sz_3625_ = lean_array_size(v___x_3620_);
v___x_3626_ = ((size_t)0ULL);
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3625_, v___x_3626_, v___x_3620_, v_a_3561_, v_a_3562_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3636_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3632_, 0, v_declName_3609_);
lean_ctor_set(v___x_3632_, 1, v_a_3628_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3632_);
v___x_3634_ = v___x_3630_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_declName_3609_);
v_a_3637_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3627_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3627_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
v___jp_3646_:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3563_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; uint8_t v___x_3649_; lean_object* v___x_3650_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___x_3647_, 1);
v___x_3649_ = lean_unbox(v_a_3648_);
lean_dec(v_a_3648_);
lean_inc(v_declName_3609_);
v___x_3650_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3609_, v___x_3649_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3696_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3696_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3696_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
if (lean_obj_tag(v_a_3651_) == 1)
{
lean_object* v_val_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
lean_dec_ref(v_args_3610_);
v_val_3655_ = lean_ctor_get(v_a_3651_, 0);
lean_inc(v_val_3655_);
lean_dec_ref_known(v_a_3651_, 1);
v___x_3656_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3655_);
lean_dec(v_val_3655_);
v___x_3657_ = lean_nat_dec_eq(v___x_3656_, v___x_3645_);
lean_dec(v___x_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_dec_ref(v_env_3612_);
lean_dec(v_declName_3609_);
v___x_3658_ = lean_box(1);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3658_);
v___x_3660_ = v___x_3653_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
else
{
lean_object* v___x_3662_; 
lean_inc(v_declName_3609_);
v___x_3662_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3612_, v_declName_3609_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v___x_3663_; 
lean_del_object(v___x_3653_);
v___x_3663_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3609_, v_a_3561_, v_a_3562_);
lean_dec(v_declName_3609_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3676_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3676_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3676_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
if (lean_obj_tag(v_a_3664_) == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3668_ = lean_box(1);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3668_);
v___x_3670_ = v___x_3666_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
else
{
lean_object* v_val_3672_; lean_object* v___x_3674_; 
v_val_3672_ = lean_ctor_get(v_a_3664_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v_a_3664_, 1);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v_val_3672_);
v___x_3674_ = v___x_3666_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_val_3672_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3663_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3663_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_val_3685_; lean_object* v___x_3687_; 
lean_dec(v_declName_3609_);
v_val_3685_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_val_3685_);
lean_dec_ref_known(v___x_3662_, 1);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v_val_3685_);
v___x_3687_ = v___x_3653_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_val_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
uint8_t v___x_3689_; lean_object* v___x_3690_; 
lean_del_object(v___x_3653_);
lean_dec(v_a_3651_);
v___x_3689_ = 0;
lean_inc(v_declName_3609_);
v___x_3690_ = l_Lean_Environment_find_x3f(v_env_3612_, v_declName_3609_, v___x_3689_);
if (lean_obj_tag(v___x_3690_) == 1)
{
lean_object* v_val_3691_; 
v_val_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v___x_3690_, 1);
if (lean_obj_tag(v_val_3691_) == 6)
{
lean_object* v_val_3692_; lean_object* v_numParams_3693_; lean_object* v_numFields_3694_; uint8_t v___x_3695_; 
v_val_3692_ = lean_ctor_get(v_val_3691_, 0);
lean_inc_ref(v_val_3692_);
lean_dec_ref_known(v_val_3691_, 1);
v_numParams_3693_ = lean_ctor_get(v_val_3692_, 3);
lean_inc(v_numParams_3693_);
v_numFields_3694_ = lean_ctor_get(v_val_3692_, 4);
lean_inc(v_numFields_3694_);
lean_dec_ref(v_val_3692_);
v___x_3695_ = lean_nat_dec_le(v_numParams_3693_, v___x_3613_);
if (v___x_3695_ == 0)
{
v_numFields_3615_ = v_numFields_3694_;
v_lower_3616_ = v_numParams_3693_;
v_upper_3617_ = v___x_3645_;
goto v___jp_3614_;
}
else
{
lean_dec(v_numParams_3693_);
v_numFields_3615_ = v_numFields_3694_;
v_lower_3616_ = v___x_3613_;
v_upper_3617_ = v___x_3645_;
goto v___jp_3614_;
}
}
else
{
lean_dec(v_val_3691_);
lean_dec_ref(v_args_3610_);
lean_dec(v_declName_3609_);
goto v___jp_3568_;
}
}
else
{
lean_dec(v___x_3690_);
lean_dec_ref(v_args_3610_);
lean_dec(v_declName_3609_);
goto v___jp_3568_;
}
}
}
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec_ref(v_env_3612_);
lean_dec_ref(v_args_3610_);
lean_dec(v_declName_3609_);
v_a_3697_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3650_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3650_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec_ref(v_env_3612_);
lean_dec_ref(v_args_3610_);
lean_dec(v_declName_3609_);
v_a_3705_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3647_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3647_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
v___jp_3713_:
{
if (lean_obj_tag(v___y_3714_) == 0)
{
lean_dec_ref_known(v___y_3714_, 1);
goto v___jp_3646_;
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec_ref(v_env_3612_);
lean_dec_ref(v_args_3610_);
lean_dec(v_declName_3609_);
v_a_3715_ = lean_ctor_get(v___y_3714_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___y_3714_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___y_3714_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___y_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
default: 
{
lean_object* v_args_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v_args_3732_ = lean_ctor_get(v_letVal_3560_, 1);
lean_inc_ref(v_args_3732_);
lean_dec_ref_known(v_letVal_3560_, 2);
v___x_3733_ = lean_unsigned_to_nat(0u);
v___x_3734_ = lean_array_get_size(v_args_3732_);
v___x_3735_ = lean_nat_dec_lt(v___x_3733_, v___x_3734_);
if (v___x_3735_ == 0)
{
lean_dec_ref(v_args_3732_);
goto v___jp_3571_;
}
else
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_nat_dec_le(v___x_3734_, v___x_3734_);
if (v___x_3737_ == 0)
{
if (v___x_3735_ == 0)
{
lean_dec_ref(v_args_3732_);
goto v___jp_3571_;
}
else
{
size_t v___x_3738_; size_t v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = ((size_t)0ULL);
v___x_3739_ = lean_usize_of_nat(v___x_3734_);
v___x_3740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3732_, v___x_3738_, v___x_3739_, v___x_3736_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
lean_dec_ref(v_args_3732_);
v___y_3575_ = v___x_3740_;
goto v___jp_3574_;
}
}
else
{
size_t v___x_3741_; size_t v___x_3742_; lean_object* v___x_3743_; 
v___x_3741_ = ((size_t)0ULL);
v___x_3742_ = lean_usize_of_nat(v___x_3734_);
v___x_3743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3732_, v___x_3741_, v___x_3742_, v___x_3736_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
lean_dec_ref(v_args_3732_);
v___y_3575_ = v___x_3743_;
goto v___jp_3574_;
}
}
}
}
v___jp_3568_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = lean_box(1);
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
v___jp_3571_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = lean_box(1);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
v___jp_3574_:
{
if (lean_obj_tag(v___y_3575_) == 0)
{
lean_dec_ref_known(v___y_3575_, 1);
goto v___jp_3571_;
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
v_a_3576_ = lean_ctor_get(v___y_3575_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___y_3575_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___y_3575_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___y_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3744_, lean_object* v_args_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v_params_3753_; lean_object* v_value_3754_; lean_object* v___x_3755_; 
v_params_3753_ = lean_ctor_get(v_funDecl_3744_, 2);
lean_inc_ref(v_params_3753_);
v_value_3754_ = lean_ctor_get(v_funDecl_3744_, 4);
lean_inc_ref(v_value_3754_);
lean_dec_ref(v_funDecl_3744_);
v___x_3755_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3753_, v_args_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3767_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3767_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3767_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_unbox(v_a_3756_);
lean_dec(v_a_3756_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
lean_dec_ref(v_value_3754_);
v___x_3761_ = lean_box(0);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3761_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
else
{
lean_object* v___x_3765_; 
lean_del_object(v___x_3758_);
lean_inc_ref(v_value_3754_);
v___x_3765_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3754_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v___x_3766_; 
lean_dec_ref_known(v___x_3765_, 1);
v___x_3766_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3754_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
return v___x_3766_;
}
else
{
lean_dec_ref(v_value_3754_);
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_value_3754_);
v_a_3768_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3755_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3755_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3776_, lean_object* v_as_3777_, size_t v_sz_3778_, size_t v_i_3779_, lean_object* v_b_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_a_3789_; uint8_t v___x_3793_; 
v___x_3793_ = lean_usize_dec_lt(v_i_3779_, v_sz_3778_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v_b_3780_);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v_a_3796_; 
v___x_3795_ = lean_box(0);
v_a_3796_ = lean_array_uget_borrowed(v_as_3777_, v_i_3779_);
if (lean_obj_tag(v_a_3796_) == 0)
{
lean_object* v_ctorName_3797_; lean_object* v_params_3798_; lean_object* v_code_3799_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3809_; lean_object* v___y_3811_; lean_object* v___x_3812_; 
v_ctorName_3797_ = lean_ctor_get(v_a_3796_, 0);
v_params_3798_ = lean_ctor_get(v_a_3796_, 1);
v_code_3799_ = lean_ctor_get(v_a_3796_, 2);
v___x_3812_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3776_, v_ctorName_3797_);
if (lean_obj_tag(v___x_3812_) == 1)
{
lean_object* v_val_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_val_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_val_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v___x_3814_ = l_Array_zip___redArg(v_params_3798_, v_val_3813_);
lean_dec(v_val_3813_);
v___x_3815_ = lean_unsigned_to_nat(0u);
v___x_3816_ = lean_array_get_size(v___x_3814_);
v___x_3817_ = lean_nat_dec_lt(v___x_3815_, v___x_3816_);
if (v___x_3817_ == 0)
{
lean_dec_ref(v___x_3814_);
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
v___y_3806_ = v___y_3786_;
goto v___jp_3800_;
}
else
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_nat_dec_le(v___x_3816_, v___x_3816_);
if (v___x_3818_ == 0)
{
if (v___x_3817_ == 0)
{
lean_dec_ref(v___x_3814_);
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
v___y_3806_ = v___y_3786_;
goto v___jp_3800_;
}
else
{
size_t v___x_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = ((size_t)0ULL);
v___x_3820_ = lean_usize_of_nat(v___x_3816_);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3814_, v___x_3819_, v___x_3820_, v___x_3795_, v___y_3781_, v___y_3782_, v___y_3786_);
lean_dec_ref(v___x_3814_);
v___y_3809_ = v___x_3821_;
goto v___jp_3808_;
}
}
else
{
size_t v___x_3822_; size_t v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = ((size_t)0ULL);
v___x_3823_ = lean_usize_of_nat(v___x_3816_);
v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3814_, v___x_3822_, v___x_3823_, v___x_3795_, v___y_3781_, v___y_3782_, v___y_3786_);
lean_dec_ref(v___x_3814_);
v___y_3809_ = v___x_3824_;
goto v___jp_3808_;
}
}
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
lean_dec(v___x_3812_);
v___x_3825_ = lean_unsigned_to_nat(0u);
v___x_3826_ = lean_array_get_size(v_params_3798_);
v___x_3827_ = lean_nat_dec_lt(v___x_3825_, v___x_3826_);
if (v___x_3827_ == 0)
{
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
v___y_3806_ = v___y_3786_;
goto v___jp_3800_;
}
else
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_nat_dec_le(v___x_3826_, v___x_3826_);
if (v___x_3828_ == 0)
{
if (v___x_3827_ == 0)
{
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
v___y_3806_ = v___y_3786_;
goto v___jp_3800_;
}
else
{
size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = ((size_t)0ULL);
v___x_3830_ = lean_usize_of_nat(v___x_3826_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3798_, v___x_3829_, v___x_3830_, v___x_3795_, v___y_3781_, v___y_3782_, v___y_3786_);
v___y_3811_ = v___x_3831_;
goto v___jp_3810_;
}
}
else
{
size_t v___x_3832_; size_t v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = ((size_t)0ULL);
v___x_3833_ = lean_usize_of_nat(v___x_3826_);
v___x_3834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3798_, v___x_3832_, v___x_3833_, v___x_3795_, v___y_3781_, v___y_3782_, v___y_3786_);
v___y_3811_ = v___x_3834_;
goto v___jp_3810_;
}
}
}
v___jp_3800_:
{
lean_object* v___x_3807_; 
lean_inc_ref(v_code_3799_);
v___x_3807_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3799_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_dec_ref_known(v___x_3807_, 1);
v_a_3789_ = v___x_3795_;
goto v___jp_3788_;
}
else
{
return v___x_3807_;
}
}
v___jp_3808_:
{
if (lean_obj_tag(v___y_3809_) == 0)
{
lean_dec_ref_known(v___y_3809_, 1);
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
v___y_3806_ = v___y_3786_;
goto v___jp_3800_;
}
else
{
return v___y_3809_;
}
}
v___jp_3810_:
{
if (lean_obj_tag(v___y_3811_) == 0)
{
lean_dec_ref_known(v___y_3811_, 1);
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
v___y_3806_ = v___y_3786_;
goto v___jp_3800_;
}
else
{
return v___y_3811_;
}
}
}
else
{
lean_object* v_code_3835_; lean_object* v___x_3836_; 
v_code_3835_ = lean_ctor_get(v_a_3796_, 0);
lean_inc_ref(v_code_3835_);
v___x_3836_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3835_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_dec_ref_known(v___x_3836_, 1);
v_a_3789_ = v___x_3795_;
goto v___jp_3788_;
}
else
{
return v___x_3836_;
}
}
}
v___jp_3788_:
{
size_t v___x_3790_; size_t v___x_3791_; 
v___x_3790_ = ((size_t)1ULL);
v___x_3791_ = lean_usize_add(v_i_3779_, v___x_3790_);
v_i_3779_ = v___x_3791_;
v_b_3780_ = v_a_3789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_decl_3846_; lean_object* v_k_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; 
switch(lean_obj_tag(v_x_3837_))
{
case 0:
{
lean_object* v_decl_3857_; lean_object* v_k_3858_; lean_object* v_fvarId_3859_; lean_object* v_value_3860_; lean_object* v___x_3861_; 
v_decl_3857_ = lean_ctor_get(v_x_3837_, 0);
lean_inc_ref(v_decl_3857_);
v_k_3858_ = lean_ctor_get(v_x_3837_, 1);
lean_inc_ref(v_k_3858_);
lean_dec_ref_known(v_x_3837_, 2);
v_fvarId_3859_ = lean_ctor_get(v_decl_3857_, 0);
lean_inc(v_fvarId_3859_);
v_value_3860_ = lean_ctor_get(v_decl_3857_, 3);
lean_inc_n(v_value_3860_, 2);
lean_dec_ref(v_decl_3857_);
v___x_3861_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3860_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3863_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3861_, 1);
v___x_3863_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3859_, v_a_3862_, v_a_3838_, v_a_3839_, v_a_3843_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_dec_ref_known(v___x_3863_, 1);
if (lean_obj_tag(v_value_3860_) == 4)
{
lean_object* v_fvarId_3864_; lean_object* v_args_3865_; uint8_t v___x_3866_; lean_object* v___x_3867_; 
v_fvarId_3864_ = lean_ctor_get(v_value_3860_, 0);
lean_inc(v_fvarId_3864_);
v_args_3865_ = lean_ctor_get(v_value_3860_, 1);
lean_inc_ref(v_args_3865_);
lean_dec_ref_known(v_value_3860_, 2);
v___x_3866_ = 0;
v___x_3867_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3866_, v_fvarId_3864_, v_a_3841_);
lean_dec(v_fvarId_3864_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
if (lean_obj_tag(v_a_3868_) == 1)
{
lean_object* v_val_3869_; lean_object* v___x_3870_; 
v_val_3869_ = lean_ctor_get(v_a_3868_, 0);
lean_inc(v_val_3869_);
lean_dec_ref_known(v_a_3868_, 1);
v___x_3870_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3869_, v_args_3865_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_dec_ref_known(v___x_3870_, 1);
v_x_3837_ = v_k_3858_;
goto _start;
}
else
{
lean_dec_ref(v_k_3858_);
return v___x_3870_;
}
}
else
{
lean_dec(v_a_3868_);
lean_dec_ref(v_args_3865_);
v_x_3837_ = v_k_3858_;
goto _start;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v_args_3865_);
lean_dec_ref(v_k_3858_);
v_a_3873_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3867_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3867_);
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
else
{
lean_dec(v_value_3860_);
v_x_3837_ = v_k_3858_;
goto _start;
}
}
else
{
lean_dec(v_value_3860_);
lean_dec_ref(v_k_3858_);
return v___x_3863_;
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec(v_value_3860_);
lean_dec(v_fvarId_3859_);
lean_dec_ref(v_k_3858_);
v_a_3882_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3861_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3861_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3890_; lean_object* v_args_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; 
v_fvarId_3890_ = lean_ctor_get(v_x_3837_, 0);
lean_inc(v_fvarId_3890_);
v_args_3891_ = lean_ctor_get(v_x_3837_, 1);
lean_inc_ref(v_args_3891_);
lean_dec_ref_known(v_x_3837_, 2);
v___x_3892_ = 0;
v___x_3893_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3892_, v_fvarId_3890_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___y_3896_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = lean_array_get_size(v_args_3891_);
v___x_3900_ = lean_nat_dec_lt(v___x_3898_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
v___x_3901_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3894_, v_args_3891_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
return v___x_3901_;
}
else
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = lean_box(0);
v___x_3903_ = lean_nat_dec_le(v___x_3899_, v___x_3899_);
if (v___x_3903_ == 0)
{
if (v___x_3900_ == 0)
{
lean_object* v___x_3904_; 
v___x_3904_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3894_, v_args_3891_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
return v___x_3904_;
}
else
{
size_t v___x_3905_; size_t v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = ((size_t)0ULL);
v___x_3906_ = lean_usize_of_nat(v___x_3899_);
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3891_, v___x_3905_, v___x_3906_, v___x_3902_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
v___y_3896_ = v___x_3907_;
goto v___jp_3895_;
}
}
else
{
size_t v___x_3908_; size_t v___x_3909_; lean_object* v___x_3910_; 
v___x_3908_ = ((size_t)0ULL);
v___x_3909_ = lean_usize_of_nat(v___x_3899_);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3891_, v___x_3908_, v___x_3909_, v___x_3902_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
v___y_3896_ = v___x_3910_;
goto v___jp_3895_;
}
}
v___jp_3895_:
{
if (lean_obj_tag(v___y_3896_) == 0)
{
lean_object* v___x_3897_; 
lean_dec_ref_known(v___y_3896_, 1);
v___x_3897_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3894_, v_args_3891_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
return v___x_3897_;
}
else
{
lean_dec(v_a_3894_);
lean_dec_ref(v_args_3891_);
return v___y_3896_;
}
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_dec_ref(v_args_3891_);
v_a_3911_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3893_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3893_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
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
case 4:
{
lean_object* v_cases_3919_; lean_object* v_discr_3920_; lean_object* v_alts_3921_; lean_object* v___x_3922_; 
v_cases_3919_ = lean_ctor_get(v_x_3837_, 0);
lean_inc_ref(v_cases_3919_);
lean_dec_ref_known(v_x_3837_, 1);
v_discr_3920_ = lean_ctor_get(v_cases_3919_, 2);
lean_inc(v_discr_3920_);
v_alts_3921_ = lean_ctor_get(v_cases_3919_, 3);
lean_inc_ref(v_alts_3921_);
lean_dec_ref(v_cases_3919_);
v___x_3922_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3920_, v_a_3838_, v_a_3839_);
lean_dec(v_discr_3920_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3924_; size_t v_sz_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v___x_3922_, 1);
v___x_3924_ = lean_box(0);
v_sz_3925_ = lean_array_size(v_alts_3921_);
v___x_3926_ = ((size_t)0ULL);
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3923_, v_alts_3921_, v_sz_3925_, v___x_3926_, v___x_3924_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
lean_dec_ref(v_alts_3921_);
lean_dec(v_a_3923_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3934_ == 0)
{
lean_object* v_unused_3935_; 
v_unused_3935_ = lean_ctor_get(v___x_3927_, 0);
lean_dec(v_unused_3935_);
v___x_3929_ = v___x_3927_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_dec(v___x_3927_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v___x_3924_);
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3924_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
else
{
return v___x_3927_;
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec_ref(v_alts_3921_);
v_a_3936_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3922_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3922_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3944_; lean_object* v___x_3945_; 
v_fvarId_3944_ = lean_ctor_get(v_x_3837_, 0);
lean_inc(v_fvarId_3944_);
lean_dec_ref_known(v_x_3837_, 1);
v___x_3945_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3944_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v___x_3946_; 
lean_dec_ref_known(v___x_3945_, 1);
v___x_3946_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3944_, v_a_3838_, v_a_3839_);
lean_dec(v_fvarId_3944_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3948_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3946_, 1);
v___x_3948_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3947_, v_a_3838_, v_a_3839_, v_a_3843_);
return v___x_3948_;
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
v_a_3949_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3946_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3946_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_dec(v_fvarId_3944_);
return v___x_3945_;
}
}
case 6:
{
lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3964_; 
v_isSharedCheck_3964_ = !lean_is_exclusive(v_x_3837_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v_x_3837_, 0);
lean_dec(v_unused_3965_);
v___x_3958_ = v_x_3837_;
v_isShared_3959_ = v_isSharedCheck_3964_;
goto v_resetjp_3957_;
}
else
{
lean_dec(v_x_3837_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3964_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = lean_box(0);
if (v_isShared_3959_ == 0)
{
lean_ctor_set_tag(v___x_3958_, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3960_);
v___x_3962_ = v___x_3958_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
default: 
{
lean_object* v_decl_3966_; lean_object* v_k_3967_; 
v_decl_3966_ = lean_ctor_get(v_x_3837_, 0);
lean_inc_ref(v_decl_3966_);
v_k_3967_ = lean_ctor_get(v_x_3837_, 1);
lean_inc_ref(v_k_3967_);
lean_dec_ref(v_x_3837_);
v_decl_3846_ = v_decl_3966_;
v_k_3847_ = v_k_3967_;
v___y_3848_ = v_a_3838_;
v___y_3849_ = v_a_3839_;
v___y_3850_ = v_a_3840_;
v___y_3851_ = v_a_3841_;
v___y_3852_ = v_a_3842_;
v___y_3853_ = v_a_3843_;
goto v___jp_3845_;
}
}
v___jp_3845_:
{
lean_object* v_value_3854_; lean_object* v___x_3855_; 
v_value_3854_ = lean_ctor_get(v_decl_3846_, 4);
lean_inc_ref(v_value_3854_);
lean_dec_ref(v_decl_3846_);
v___x_3855_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3854_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_dec_ref_known(v___x_3855_, 1);
v_x_3837_ = v_k_3847_;
v_a_3838_ = v___y_3848_;
v_a_3839_ = v___y_3849_;
v_a_3840_ = v___y_3850_;
v_a_3841_ = v___y_3851_;
v_a_3842_ = v___y_3852_;
v_a_3843_ = v___y_3853_;
goto _start;
}
else
{
lean_dec_ref(v_k_3847_);
return v___x_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
uint8_t v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = 0;
v___x_3977_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3976_, v_var_3968_, v_a_3972_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4010_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_4010_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3977_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4010_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
if (lean_obj_tag(v_a_3978_) == 1)
{
lean_object* v_val_3982_; lean_object* v_params_3983_; lean_object* v_value_3984_; lean_object* v___x_3985_; 
lean_del_object(v___x_3980_);
v_val_3982_ = lean_ctor_get(v_a_3978_, 0);
lean_inc(v_val_3982_);
lean_dec_ref_known(v_a_3978_, 1);
v_params_3983_ = lean_ctor_get(v_val_3982_, 2);
lean_inc_ref(v_params_3983_);
v_value_3984_ = lean_ctor_get(v_val_3982_, 4);
lean_inc_ref(v_value_3984_);
lean_dec(v_val_3982_);
v___x_3985_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3983_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec_ref(v_params_3983_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3997_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_3997_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3997_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
uint8_t v___x_3990_; 
v___x_3990_ = lean_unbox(v_a_3986_);
lean_dec(v_a_3986_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; lean_object* v___x_3993_; 
lean_dec_ref(v_value_3984_);
v___x_3991_ = lean_box(0);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_3991_);
v___x_3993_ = v___x_3988_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
else
{
lean_object* v___x_3995_; 
lean_del_object(v___x_3988_);
lean_inc_ref(v_value_3984_);
v___x_3995_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3984_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v___x_3996_; 
lean_dec_ref_known(v___x_3995_, 1);
v___x_3996_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3984_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
return v___x_3996_;
}
else
{
lean_dec_ref(v_value_3984_);
return v___x_3995_;
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec_ref(v_value_3984_);
v_a_3998_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3985_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3985_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4008_; 
lean_dec(v_a_3978_);
v___x_4006_ = lean_box(0);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_4006_);
v___x_4008_ = v___x_3980_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
v_a_4011_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3977_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3977_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
if (lean_obj_tag(v_arg_4019_) == 1)
{
lean_object* v_fvarId_4027_; lean_object* v___x_4028_; 
v_fvarId_4027_ = lean_ctor_get(v_arg_4019_, 0);
v___x_4028_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4027_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
return v___x_4028_;
}
else
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_box(0);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_arg_4031_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_4040_, lean_object* v_i_4041_, lean_object* v_stop_4042_, lean_object* v_b_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
size_t v_i_boxed_4051_; size_t v_stop_boxed_4052_; lean_object* v_res_4053_; 
v_i_boxed_4051_ = lean_unbox_usize(v_i_4041_);
lean_dec(v_i_4041_);
v_stop_boxed_4052_ = lean_unbox_usize(v_stop_4042_);
lean_dec(v_stop_4042_);
v_res_4053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_4040_, v_i_boxed_4051_, v_stop_boxed_4052_, v_b_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v_as_4040_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_4054_, lean_object* v_args_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_4054_, v_args_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_var_4064_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4073_, lean_object* v_as_4074_, lean_object* v_sz_4075_, lean_object* v_i_4076_, lean_object* v_b_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
size_t v_sz_boxed_4085_; size_t v_i_boxed_4086_; lean_object* v_res_4087_; 
v_sz_boxed_4085_ = lean_unbox_usize(v_sz_4075_);
lean_dec(v_sz_4075_);
v_i_boxed_4086_ = lean_unbox_usize(v_i_4076_);
lean_dec(v_i_4076_);
v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4073_, v_as_4074_, v_sz_boxed_4085_, v_i_boxed_4086_, v_b_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec_ref(v_as_4074_);
lean_dec(v_a_4073_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4106_, lean_object* v_R_4107_, lean_object* v_a_4108_, lean_object* v_b_4109_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4108_, v_b_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4111_, size_t v_i_4112_, lean_object* v_bs_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4111_, v_i_4112_, v_bs_4113_, v___y_4114_, v___y_4115_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4122_, lean_object* v_i_4123_, lean_object* v_bs_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
size_t v_sz_boxed_4132_; size_t v_i_boxed_4133_; lean_object* v_res_4134_; 
v_sz_boxed_4132_ = lean_unbox_usize(v_sz_4122_);
lean_dec(v_sz_4122_);
v_i_boxed_4133_ = lean_unbox_usize(v_i_4123_);
lean_dec(v_i_4123_);
v_res_4134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4132_, v_i_boxed_4133_, v_bs_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4135_, size_t v_i_4136_, size_t v_stop_4137_, lean_object* v_b_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4135_, v_i_4136_, v_stop_4137_, v_b_4138_, v___y_4139_, v___y_4140_, v___y_4144_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4147_, lean_object* v_i_4148_, lean_object* v_stop_4149_, lean_object* v_b_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
size_t v_i_boxed_4158_; size_t v_stop_boxed_4159_; lean_object* v_res_4160_; 
v_i_boxed_4158_ = lean_unbox_usize(v_i_4148_);
lean_dec(v_i_4148_);
v_stop_boxed_4159_ = lean_unbox_usize(v_stop_4149_);
lean_dec(v_stop_4149_);
v_res_4160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4147_, v_i_boxed_4158_, v_stop_boxed_4159_, v_b_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec_ref(v_as_4147_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4161_, size_t v_i_4162_, size_t v_stop_4163_, lean_object* v_b_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4161_, v_i_4162_, v_stop_4163_, v_b_4164_, v___y_4165_, v___y_4166_, v___y_4170_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4173_, lean_object* v_i_4174_, lean_object* v_stop_4175_, lean_object* v_b_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
size_t v_i_boxed_4184_; size_t v_stop_boxed_4185_; lean_object* v_res_4186_; 
v_i_boxed_4184_ = lean_unbox_usize(v_i_4174_);
lean_dec(v_i_4174_);
v_stop_boxed_4185_ = lean_unbox_usize(v_stop_4175_);
lean_dec(v_stop_4175_);
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4173_, v_i_boxed_4184_, v_stop_boxed_4185_, v_b_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec_ref(v_as_4173_);
return v_res_4186_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4187_ = lean_unsigned_to_nat(32u);
v___x_4188_ = lean_mk_empty_array_with_capacity(v___x_4187_);
v___x_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
return v___x_4189_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4190_ = ((size_t)5ULL);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = lean_unsigned_to_nat(32u);
v___x_4193_ = lean_mk_empty_array_with_capacity(v___x_4192_);
v___x_4194_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4195_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
lean_ctor_set(v___x_4195_, 1, v___x_4193_);
lean_ctor_set(v___x_4195_, 2, v___x_4191_);
lean_ctor_set(v___x_4195_, 3, v___x_4191_);
lean_ctor_set_usize(v___x_4195_, 4, v___x_4190_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4196_){
_start:
{
lean_object* v___x_4198_; lean_object* v_traceState_4199_; lean_object* v_traces_4200_; lean_object* v___x_4201_; lean_object* v_traceState_4202_; lean_object* v_env_4203_; lean_object* v_nextMacroScope_4204_; lean_object* v_ngen_4205_; lean_object* v_auxDeclNGen_4206_; lean_object* v_cache_4207_; lean_object* v_messages_4208_; lean_object* v_infoState_4209_; lean_object* v_snapshotTasks_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4229_; 
v___x_4198_ = lean_st_ref_get(v___y_4196_);
v_traceState_4199_ = lean_ctor_get(v___x_4198_, 4);
lean_inc_ref(v_traceState_4199_);
lean_dec(v___x_4198_);
v_traces_4200_ = lean_ctor_get(v_traceState_4199_, 0);
lean_inc_ref(v_traces_4200_);
lean_dec_ref(v_traceState_4199_);
v___x_4201_ = lean_st_ref_take(v___y_4196_);
v_traceState_4202_ = lean_ctor_get(v___x_4201_, 4);
v_env_4203_ = lean_ctor_get(v___x_4201_, 0);
v_nextMacroScope_4204_ = lean_ctor_get(v___x_4201_, 1);
v_ngen_4205_ = lean_ctor_get(v___x_4201_, 2);
v_auxDeclNGen_4206_ = lean_ctor_get(v___x_4201_, 3);
v_cache_4207_ = lean_ctor_get(v___x_4201_, 5);
v_messages_4208_ = lean_ctor_get(v___x_4201_, 6);
v_infoState_4209_ = lean_ctor_get(v___x_4201_, 7);
v_snapshotTasks_4210_ = lean_ctor_get(v___x_4201_, 8);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4212_ = v___x_4201_;
v_isShared_4213_ = v_isSharedCheck_4229_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_snapshotTasks_4210_);
lean_inc(v_infoState_4209_);
lean_inc(v_messages_4208_);
lean_inc(v_cache_4207_);
lean_inc(v_traceState_4202_);
lean_inc(v_auxDeclNGen_4206_);
lean_inc(v_ngen_4205_);
lean_inc(v_nextMacroScope_4204_);
lean_inc(v_env_4203_);
lean_dec(v___x_4201_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4229_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
uint64_t v_tid_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4227_; 
v_tid_4214_ = lean_ctor_get_uint64(v_traceState_4202_, sizeof(void*)*1);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_traceState_4202_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; 
v_unused_4228_ = lean_ctor_get(v_traceState_4202_, 0);
lean_dec(v_unused_4228_);
v___x_4216_ = v_traceState_4202_;
v_isShared_4217_ = v_isSharedCheck_4227_;
goto v_resetjp_4215_;
}
else
{
lean_dec(v_traceState_4202_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4227_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4218_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 0, v___x_4218_);
v___x_4220_ = v___x_4216_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4218_);
lean_ctor_set_uint64(v_reuseFailAlloc_4226_, sizeof(void*)*1, v_tid_4214_);
v___x_4220_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
lean_object* v___x_4222_; 
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 4, v___x_4220_);
v___x_4222_ = v___x_4212_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_env_4203_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_nextMacroScope_4204_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v_ngen_4205_);
lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_auxDeclNGen_4206_);
lean_ctor_set(v_reuseFailAlloc_4225_, 4, v___x_4220_);
lean_ctor_set(v_reuseFailAlloc_4225_, 5, v_cache_4207_);
lean_ctor_set(v_reuseFailAlloc_4225_, 6, v_messages_4208_);
lean_ctor_set(v_reuseFailAlloc_4225_, 7, v_infoState_4209_);
lean_ctor_set(v_reuseFailAlloc_4225_, 8, v_snapshotTasks_4210_);
v___x_4222_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = lean_st_ref_set(v___y_4196_, v___x_4222_);
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v_traces_4200_);
return v___x_4224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4230_);
lean_dec(v___y_4230_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4238_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
return v_res_4248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4249_, lean_object* v_opt_4250_){
_start:
{
lean_object* v_name_4251_; lean_object* v_defValue_4252_; lean_object* v_map_4253_; lean_object* v___x_4254_; 
v_name_4251_ = lean_ctor_get(v_opt_4250_, 0);
v_defValue_4252_ = lean_ctor_get(v_opt_4250_, 1);
v_map_4253_ = lean_ctor_get(v_opts_4249_, 0);
v___x_4254_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4253_, v_name_4251_);
if (lean_obj_tag(v___x_4254_) == 0)
{
uint8_t v___x_4255_; 
v___x_4255_ = lean_unbox(v_defValue_4252_);
return v___x_4255_;
}
else
{
lean_object* v_val_4256_; 
v_val_4256_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_val_4256_);
lean_dec_ref_known(v___x_4254_, 1);
if (lean_obj_tag(v_val_4256_) == 1)
{
uint8_t v_v_4257_; 
v_v_4257_ = lean_ctor_get_uint8(v_val_4256_, 0);
lean_dec_ref_known(v_val_4256_, 0);
return v_v_4257_;
}
else
{
uint8_t v___x_4258_; 
lean_dec(v_val_4256_);
v___x_4258_ = lean_unbox(v_defValue_4252_);
return v___x_4258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4259_, lean_object* v_opt_4260_){
_start:
{
uint8_t v_res_4261_; lean_object* v_r_4262_; 
v_res_4261_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4259_, v_opt_4260_);
lean_dec_ref(v_opt_4260_);
lean_dec_ref(v_opts_4259_);
v_r_4262_ = lean_box(v_res_4261_);
return v_r_4262_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4264_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4265_ = l_Lean_stringToMessageData(v___x_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4266_, lean_object* v_x_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4275_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4276_ = l_Lean_MessageData_ofName(v_name_4266_);
v___x_4277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4275_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4279_, lean_object* v_x_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4279_, v_x_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_x_4280_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4289_, lean_object* v_opt_4290_){
_start:
{
lean_object* v_name_4291_; lean_object* v_defValue_4292_; lean_object* v_map_4293_; lean_object* v___x_4294_; 
v_name_4291_ = lean_ctor_get(v_opt_4290_, 0);
v_defValue_4292_ = lean_ctor_get(v_opt_4290_, 1);
v_map_4293_ = lean_ctor_get(v_opts_4289_, 0);
v___x_4294_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4293_, v_name_4291_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_inc(v_defValue_4292_);
return v_defValue_4292_;
}
else
{
lean_object* v_val_4295_; 
v_val_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_val_4295_);
lean_dec_ref_known(v___x_4294_, 1);
if (lean_obj_tag(v_val_4295_) == 3)
{
lean_object* v_v_4296_; 
v_v_4296_ = lean_ctor_get(v_val_4295_, 0);
lean_inc(v_v_4296_);
lean_dec_ref_known(v_val_4295_, 1);
return v_v_4296_;
}
else
{
lean_dec(v_val_4295_);
lean_inc(v_defValue_4292_);
return v_defValue_4292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4297_, lean_object* v_opt_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4297_, v_opt_4298_);
lean_dec_ref(v_opt_4298_);
lean_dec_ref(v_opts_4297_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4300_){
_start:
{
if (lean_obj_tag(v_x_4300_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_a_4302_ = lean_ctor_get(v_x_4300_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v_x_4300_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v_x_4300_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v_x_4300_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set_tag(v___x_4304_, 1);
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_a_4310_ = lean_ctor_get(v_x_4300_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_x_4300_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v_x_4300_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v_x_4300_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
lean_ctor_set_tag(v___x_4312_, 0);
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4318_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4321_, size_t v_i_4322_, lean_object* v_bs_4323_){
_start:
{
uint8_t v___x_4324_; 
v___x_4324_ = lean_usize_dec_lt(v_i_4322_, v_sz_4321_);
if (v___x_4324_ == 0)
{
return v_bs_4323_;
}
else
{
lean_object* v_v_4325_; lean_object* v_msg_4326_; lean_object* v___x_4327_; lean_object* v_bs_x27_4328_; size_t v___x_4329_; size_t v___x_4330_; lean_object* v___x_4331_; 
v_v_4325_ = lean_array_uget_borrowed(v_bs_4323_, v_i_4322_);
v_msg_4326_ = lean_ctor_get(v_v_4325_, 1);
lean_inc_ref(v_msg_4326_);
v___x_4327_ = lean_unsigned_to_nat(0u);
v_bs_x27_4328_ = lean_array_uset(v_bs_4323_, v_i_4322_, v___x_4327_);
v___x_4329_ = ((size_t)1ULL);
v___x_4330_ = lean_usize_add(v_i_4322_, v___x_4329_);
v___x_4331_ = lean_array_uset(v_bs_x27_4328_, v_i_4322_, v_msg_4326_);
v_i_4322_ = v___x_4330_;
v_bs_4323_ = v___x_4331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4333_, lean_object* v_i_4334_, lean_object* v_bs_4335_){
_start:
{
size_t v_sz_boxed_4336_; size_t v_i_boxed_4337_; lean_object* v_res_4338_; 
v_sz_boxed_4336_ = lean_unbox_usize(v_sz_4333_);
lean_dec(v_sz_4333_);
v_i_boxed_4337_ = lean_unbox_usize(v_i_4334_);
lean_dec(v_i_4334_);
v_res_4338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4336_, v_i_boxed_4337_, v_bs_4335_);
return v_res_4338_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4339_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4340_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
return v___x_4341_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4342_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
lean_ctor_set(v___x_4344_, 2, v___x_4343_);
lean_ctor_set(v___x_4344_, 3, v___x_4343_);
lean_ctor_set(v___x_4344_, 4, v___x_4342_);
lean_ctor_set(v___x_4344_, 5, v___x_4342_);
lean_ctor_set(v___x_4344_, 6, v___x_4342_);
lean_ctor_set(v___x_4344_, 7, v___x_4342_);
lean_ctor_set(v___x_4344_, 8, v___x_4342_);
lean_ctor_set(v___x_4344_, 9, v___x_4342_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4345_, lean_object* v_data_4346_, lean_object* v_ref_4347_, lean_object* v_msg_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_options_4354_; lean_object* v___x_4355_; lean_object* v_traceState_4356_; lean_object* v_traces_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_options_4354_ = lean_ctor_get(v___y_4351_, 2);
v___x_4355_ = lean_st_ref_get(v___y_4352_);
v_traceState_4356_ = lean_ctor_get(v___x_4355_, 4);
lean_inc_ref(v_traceState_4356_);
lean_dec(v___x_4355_);
v_traces_4357_ = lean_ctor_get(v_traceState_4356_, 0);
lean_inc_ref(v_traces_4357_);
lean_dec_ref(v_traceState_4356_);
v___x_4358_ = lean_st_ref_get(v___y_4352_);
v___x_4359_ = lean_st_ref_get(v___y_4350_);
v___x_4360_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4349_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4417_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4363_ = v___x_4360_;
v_isShared_4364_ = v_isSharedCheck_4417_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4360_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4417_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v_env_4365_; lean_object* v_lctx_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4415_; 
v_env_4365_ = lean_ctor_get(v___x_4358_, 0);
lean_inc_ref(v_env_4365_);
lean_dec(v___x_4358_);
v_lctx_4366_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4415_ == 0)
{
lean_object* v_unused_4416_; 
v_unused_4416_ = lean_ctor_get(v___x_4359_, 1);
lean_dec(v_unused_4416_);
v___x_4368_ = v___x_4359_;
v_isShared_4369_ = v_isSharedCheck_4415_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_lctx_4366_);
lean_dec(v___x_4359_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4415_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_traceState_4372_; lean_object* v_env_4373_; lean_object* v_nextMacroScope_4374_; lean_object* v_ngen_4375_; lean_object* v_auxDeclNGen_4376_; lean_object* v_cache_4377_; lean_object* v_messages_4378_; lean_object* v_infoState_4379_; lean_object* v_snapshotTasks_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4414_; 
v___x_4370_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4371_ = lean_st_ref_take(v___y_4352_);
v_traceState_4372_ = lean_ctor_get(v___x_4371_, 4);
v_env_4373_ = lean_ctor_get(v___x_4371_, 0);
v_nextMacroScope_4374_ = lean_ctor_get(v___x_4371_, 1);
v_ngen_4375_ = lean_ctor_get(v___x_4371_, 2);
v_auxDeclNGen_4376_ = lean_ctor_get(v___x_4371_, 3);
v_cache_4377_ = lean_ctor_get(v___x_4371_, 5);
v_messages_4378_ = lean_ctor_get(v___x_4371_, 6);
v_infoState_4379_ = lean_ctor_get(v___x_4371_, 7);
v_snapshotTasks_4380_ = lean_ctor_get(v___x_4371_, 8);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4382_ = v___x_4371_;
v_isShared_4383_ = v_isSharedCheck_4414_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_snapshotTasks_4380_);
lean_inc(v_infoState_4379_);
lean_inc(v_messages_4378_);
lean_inc(v_cache_4377_);
lean_inc(v_traceState_4372_);
lean_inc(v_auxDeclNGen_4376_);
lean_inc(v_ngen_4375_);
lean_inc(v_nextMacroScope_4374_);
lean_inc(v_env_4373_);
lean_dec(v___x_4371_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4414_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
uint64_t v_tid_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4412_; 
v_tid_4384_ = lean_ctor_get_uint64(v_traceState_4372_, sizeof(void*)*1);
v_isSharedCheck_4412_ = !lean_is_exclusive(v_traceState_4372_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; 
v_unused_4413_ = lean_ctor_get(v_traceState_4372_, 0);
lean_dec(v_unused_4413_);
v___x_4386_ = v_traceState_4372_;
v_isShared_4387_ = v_isSharedCheck_4412_;
goto v_resetjp_4385_;
}
else
{
lean_dec(v_traceState_4372_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4412_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4388_; size_t v_sz_4389_; size_t v___x_4390_; lean_object* v___x_4391_; lean_object* v_msg_4392_; uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4388_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4357_);
lean_dec_ref(v_traces_4357_);
v_sz_4389_ = lean_array_size(v___x_4388_);
v___x_4390_ = ((size_t)0ULL);
v___x_4391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4389_, v___x_4390_, v___x_4388_);
v_msg_4392_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4392_, 0, v_data_4346_);
lean_ctor_set(v_msg_4392_, 1, v_msg_4348_);
lean_ctor_set(v_msg_4392_, 2, v___x_4391_);
v___x_4393_ = lean_unbox(v_a_4361_);
lean_dec(v_a_4361_);
v___x_4394_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4366_, v___x_4393_);
lean_dec_ref(v_lctx_4366_);
lean_inc_ref(v_options_4354_);
v___x_4395_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4395_, 0, v_env_4365_);
lean_ctor_set(v___x_4395_, 1, v___x_4370_);
lean_ctor_set(v___x_4395_, 2, v___x_4394_);
lean_ctor_set(v___x_4395_, 3, v_options_4354_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set_tag(v___x_4368_, 3);
lean_ctor_set(v___x_4368_, 1, v_msg_4392_);
lean_ctor_set(v___x_4368_, 0, v___x_4395_);
v___x_4397_ = v___x_4368_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_msg_4392_);
v___x_4397_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; 
v___x_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4398_, 0, v_ref_4347_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4345_, v___x_4398_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 0, v___x_4399_);
v___x_4401_ = v___x_4386_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4399_);
lean_ctor_set_uint64(v_reuseFailAlloc_4410_, sizeof(void*)*1, v_tid_4384_);
v___x_4401_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
lean_object* v___x_4403_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 4, v___x_4401_);
v___x_4403_ = v___x_4382_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_env_4373_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_nextMacroScope_4374_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v_ngen_4375_);
lean_ctor_set(v_reuseFailAlloc_4409_, 3, v_auxDeclNGen_4376_);
lean_ctor_set(v_reuseFailAlloc_4409_, 4, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4409_, 5, v_cache_4377_);
lean_ctor_set(v_reuseFailAlloc_4409_, 6, v_messages_4378_);
lean_ctor_set(v_reuseFailAlloc_4409_, 7, v_infoState_4379_);
lean_ctor_set(v_reuseFailAlloc_4409_, 8, v_snapshotTasks_4380_);
v___x_4403_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4404_ = lean_st_ref_set(v___y_4352_, v___x_4403_);
v___x_4405_ = lean_box(0);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 0, v___x_4405_);
v___x_4407_ = v___x_4363_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
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
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v___x_4359_);
lean_dec(v___x_4358_);
lean_dec_ref(v_traces_4357_);
lean_dec_ref(v_msg_4348_);
lean_dec(v_ref_4347_);
lean_dec_ref(v_data_4346_);
lean_dec_ref(v_oldTraces_4345_);
v_a_4418_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4360_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4360_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4426_, lean_object* v_data_4427_, lean_object* v_ref_4428_, lean_object* v_msg_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4426_, v_data_4427_, v_ref_4428_, v_msg_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
return v_res_4435_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4436_){
_start:
{
if (lean_obj_tag(v_e_4436_) == 0)
{
uint8_t v___x_4437_; 
v___x_4437_ = 2;
return v___x_4437_;
}
else
{
uint8_t v___x_4438_; 
v___x_4438_ = 0;
return v___x_4438_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4439_){
_start:
{
uint8_t v_res_4440_; lean_object* v_r_4441_; 
v_res_4440_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4439_);
lean_dec_ref(v_e_4439_);
v_r_4441_ = lean_box(v_res_4440_);
return v_r_4441_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4442_; double v___x_4443_; 
v___x_4442_ = lean_unsigned_to_nat(0u);
v___x_4443_ = lean_float_of_nat(v___x_4442_);
return v___x_4443_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4446_ = l_Lean_stringToMessageData(v___x_4445_);
return v___x_4446_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4447_; double v___x_4448_; 
v___x_4447_ = lean_unsigned_to_nat(1000u);
v___x_4448_ = lean_float_of_nat(v___x_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4449_, uint8_t v_collapsed_4450_, lean_object* v_tag_4451_, lean_object* v_opts_4452_, uint8_t v_clsEnabled_4453_, lean_object* v_oldTraces_4454_, lean_object* v_msg_4455_, lean_object* v_resStartStop_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_fst_4464_; lean_object* v_snd_4465_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v_data_4469_; lean_object* v_fst_4472_; lean_object* v_snd_4473_; lean_object* v___x_4474_; uint8_t v___x_4475_; lean_object* v___y_4477_; lean_object* v_a_4478_; uint8_t v___y_4493_; double v___y_4524_; 
v_fst_4464_ = lean_ctor_get(v_resStartStop_4456_, 0);
lean_inc(v_fst_4464_);
v_snd_4465_ = lean_ctor_get(v_resStartStop_4456_, 1);
lean_inc(v_snd_4465_);
lean_dec_ref(v_resStartStop_4456_);
v_fst_4472_ = lean_ctor_get(v_snd_4465_, 0);
lean_inc(v_fst_4472_);
v_snd_4473_ = lean_ctor_get(v_snd_4465_, 1);
lean_inc(v_snd_4473_);
lean_dec(v_snd_4465_);
v___x_4474_ = l_Lean_trace_profiler;
v___x_4475_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4452_, v___x_4474_);
if (v___x_4475_ == 0)
{
v___y_4493_ = v___x_4475_;
goto v___jp_4492_;
}
else
{
lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4529_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4530_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4452_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; double v___x_4533_; double v___x_4534_; double v___x_4535_; 
v___x_4531_ = l_Lean_trace_profiler_threshold;
v___x_4532_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4452_, v___x_4531_);
v___x_4533_ = lean_float_of_nat(v___x_4532_);
v___x_4534_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4535_ = lean_float_div(v___x_4533_, v___x_4534_);
v___y_4524_ = v___x_4535_;
goto v___jp_4523_;
}
else
{
lean_object* v___x_4536_; lean_object* v___x_4537_; double v___x_4538_; 
v___x_4536_ = l_Lean_trace_profiler_threshold;
v___x_4537_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4452_, v___x_4536_);
v___x_4538_ = lean_float_of_nat(v___x_4537_);
v___y_4524_ = v___x_4538_;
goto v___jp_4523_;
}
}
v___jp_4466_:
{
lean_object* v___x_4470_; 
lean_inc(v___y_4468_);
v___x_4470_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4454_, v_data_4469_, v___y_4468_, v___y_4467_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v___x_4471_; 
lean_dec_ref_known(v___x_4470_, 1);
v___x_4471_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4464_);
return v___x_4471_;
}
else
{
lean_dec(v_fst_4464_);
return v___x_4470_;
}
}
v___jp_4476_:
{
uint8_t v_result_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; double v___x_4482_; lean_object* v_data_4483_; 
v_result_4479_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4464_);
v___x_4480_ = lean_box(v_result_4479_);
v___x_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
v___x_4482_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4451_);
lean_inc_ref(v___x_4481_);
lean_inc(v_cls_4449_);
v_data_4483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4483_, 0, v_cls_4449_);
lean_ctor_set(v_data_4483_, 1, v___x_4481_);
lean_ctor_set(v_data_4483_, 2, v_tag_4451_);
lean_ctor_set_float(v_data_4483_, sizeof(void*)*3, v___x_4482_);
lean_ctor_set_float(v_data_4483_, sizeof(void*)*3 + 8, v___x_4482_);
lean_ctor_set_uint8(v_data_4483_, sizeof(void*)*3 + 16, v_collapsed_4450_);
if (v___x_4475_ == 0)
{
lean_dec_ref_known(v___x_4481_, 1);
lean_dec(v_snd_4473_);
lean_dec(v_fst_4472_);
lean_dec_ref(v_tag_4451_);
lean_dec(v_cls_4449_);
v___y_4467_ = v_a_4478_;
v___y_4468_ = v___y_4477_;
v_data_4469_ = v_data_4483_;
goto v___jp_4466_;
}
else
{
lean_object* v_data_4484_; double v___x_4485_; double v___x_4486_; 
lean_dec_ref_known(v_data_4483_, 3);
v_data_4484_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4484_, 0, v_cls_4449_);
lean_ctor_set(v_data_4484_, 1, v___x_4481_);
lean_ctor_set(v_data_4484_, 2, v_tag_4451_);
v___x_4485_ = lean_unbox_float(v_fst_4472_);
lean_dec(v_fst_4472_);
lean_ctor_set_float(v_data_4484_, sizeof(void*)*3, v___x_4485_);
v___x_4486_ = lean_unbox_float(v_snd_4473_);
lean_dec(v_snd_4473_);
lean_ctor_set_float(v_data_4484_, sizeof(void*)*3 + 8, v___x_4486_);
lean_ctor_set_uint8(v_data_4484_, sizeof(void*)*3 + 16, v_collapsed_4450_);
v___y_4467_ = v_a_4478_;
v___y_4468_ = v___y_4477_;
v_data_4469_ = v_data_4484_;
goto v___jp_4466_;
}
}
v___jp_4487_:
{
lean_object* v_ref_4488_; lean_object* v___x_4489_; 
v_ref_4488_ = lean_ctor_get(v___y_4461_, 5);
lean_inc(v___y_4462_);
lean_inc_ref(v___y_4461_);
lean_inc(v___y_4460_);
lean_inc_ref(v___y_4459_);
lean_inc(v___y_4458_);
lean_inc_ref(v___y_4457_);
lean_inc(v_fst_4464_);
v___x_4489_ = lean_apply_8(v_msg_4455_, v_fst_4464_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, lean_box(0));
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___y_4477_ = v_ref_4488_;
v_a_4478_ = v_a_4490_;
goto v___jp_4476_;
}
else
{
lean_object* v___x_4491_; 
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4477_ = v_ref_4488_;
v_a_4478_ = v___x_4491_;
goto v___jp_4476_;
}
}
v___jp_4492_:
{
if (v_clsEnabled_4453_ == 0)
{
if (v___y_4493_ == 0)
{
lean_object* v___x_4494_; lean_object* v_traceState_4495_; lean_object* v_env_4496_; lean_object* v_nextMacroScope_4497_; lean_object* v_ngen_4498_; lean_object* v_auxDeclNGen_4499_; lean_object* v_cache_4500_; lean_object* v_messages_4501_; lean_object* v_infoState_4502_; lean_object* v_snapshotTasks_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4522_; 
lean_dec(v_snd_4473_);
lean_dec(v_fst_4472_);
lean_dec_ref(v_msg_4455_);
lean_dec_ref(v_tag_4451_);
lean_dec(v_cls_4449_);
v___x_4494_ = lean_st_ref_take(v___y_4462_);
v_traceState_4495_ = lean_ctor_get(v___x_4494_, 4);
v_env_4496_ = lean_ctor_get(v___x_4494_, 0);
v_nextMacroScope_4497_ = lean_ctor_get(v___x_4494_, 1);
v_ngen_4498_ = lean_ctor_get(v___x_4494_, 2);
v_auxDeclNGen_4499_ = lean_ctor_get(v___x_4494_, 3);
v_cache_4500_ = lean_ctor_get(v___x_4494_, 5);
v_messages_4501_ = lean_ctor_get(v___x_4494_, 6);
v_infoState_4502_ = lean_ctor_get(v___x_4494_, 7);
v_snapshotTasks_4503_ = lean_ctor_get(v___x_4494_, 8);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4505_ = v___x_4494_;
v_isShared_4506_ = v_isSharedCheck_4522_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_snapshotTasks_4503_);
lean_inc(v_infoState_4502_);
lean_inc(v_messages_4501_);
lean_inc(v_cache_4500_);
lean_inc(v_traceState_4495_);
lean_inc(v_auxDeclNGen_4499_);
lean_inc(v_ngen_4498_);
lean_inc(v_nextMacroScope_4497_);
lean_inc(v_env_4496_);
lean_dec(v___x_4494_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4522_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
uint64_t v_tid_4507_; lean_object* v_traces_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4521_; 
v_tid_4507_ = lean_ctor_get_uint64(v_traceState_4495_, sizeof(void*)*1);
v_traces_4508_ = lean_ctor_get(v_traceState_4495_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_traceState_4495_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4510_ = v_traceState_4495_;
v_isShared_4511_ = v_isSharedCheck_4521_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_traces_4508_);
lean_dec(v_traceState_4495_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4521_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4512_; lean_object* v___x_4514_; 
v___x_4512_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4454_, v_traces_4508_);
lean_dec_ref(v_traces_4508_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4512_);
v___x_4514_ = v___x_4510_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4512_);
lean_ctor_set_uint64(v_reuseFailAlloc_4520_, sizeof(void*)*1, v_tid_4507_);
v___x_4514_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4516_; 
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 4, v___x_4514_);
v___x_4516_ = v___x_4505_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_env_4496_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_nextMacroScope_4497_);
lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_ngen_4498_);
lean_ctor_set(v_reuseFailAlloc_4519_, 3, v_auxDeclNGen_4499_);
lean_ctor_set(v_reuseFailAlloc_4519_, 4, v___x_4514_);
lean_ctor_set(v_reuseFailAlloc_4519_, 5, v_cache_4500_);
lean_ctor_set(v_reuseFailAlloc_4519_, 6, v_messages_4501_);
lean_ctor_set(v_reuseFailAlloc_4519_, 7, v_infoState_4502_);
lean_ctor_set(v_reuseFailAlloc_4519_, 8, v_snapshotTasks_4503_);
v___x_4516_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_st_ref_set(v___y_4462_, v___x_4516_);
v___x_4518_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4464_);
return v___x_4518_;
}
}
}
}
}
else
{
goto v___jp_4487_;
}
}
else
{
goto v___jp_4487_;
}
}
v___jp_4523_:
{
double v___x_4525_; double v___x_4526_; double v___x_4527_; uint8_t v___x_4528_; 
v___x_4525_ = lean_unbox_float(v_snd_4473_);
v___x_4526_ = lean_unbox_float(v_fst_4472_);
v___x_4527_ = lean_float_sub(v___x_4525_, v___x_4526_);
v___x_4528_ = lean_float_decLt(v___y_4524_, v___x_4527_);
v___y_4493_ = v___x_4528_;
goto v___jp_4492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4539_, lean_object* v_collapsed_4540_, lean_object* v_tag_4541_, lean_object* v_opts_4542_, lean_object* v_clsEnabled_4543_, lean_object* v_oldTraces_4544_, lean_object* v_msg_4545_, lean_object* v_resStartStop_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
uint8_t v_collapsed_boxed_4554_; uint8_t v_clsEnabled_boxed_4555_; lean_object* v_res_4556_; 
v_collapsed_boxed_4554_ = lean_unbox(v_collapsed_4540_);
v_clsEnabled_boxed_4555_ = lean_unbox(v_clsEnabled_4543_);
v_res_4556_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4539_, v_collapsed_boxed_4554_, v_tag_4541_, v_opts_4542_, v_clsEnabled_boxed_4555_, v_oldTraces_4544_, v_msg_4545_, v_resStartStop_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec_ref(v_opts_4542_);
return v_res_4556_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4560_; double v___x_4561_; 
v___x_4560_ = lean_unsigned_to_nat(1000000000u);
v___x_4561_ = lean_float_of_nat(v___x_4560_);
return v___x_4561_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4572_ = l_Lean_Name_append(v___x_4571_, v___x_4570_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4573_, lean_object* v___x_4574_, lean_object* v_a_4575_, lean_object* v_b_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v_a_4585_; uint8_t v___x_4589_; 
v___x_4589_ = lean_nat_dec_lt(v_a_4575_, v_upperBound_4573_);
if (v___x_4589_ == 0)
{
lean_object* v___x_4590_; 
lean_dec(v_a_4575_);
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v_b_4576_);
return v___x_4590_;
}
else
{
lean_object* v___x_4591_; lean_object* v_toSignature_4592_; lean_object* v_value_4593_; lean_object* v_name_4594_; lean_object* v_params_4595_; uint8_t v_safe_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; 
lean_dec_ref(v_b_4576_);
v___x_4591_ = lean_array_fget_borrowed(v___x_4574_, v_a_4575_);
v_toSignature_4592_ = lean_ctor_get(v___x_4591_, 0);
v_value_4593_ = lean_ctor_get(v___x_4591_, 1);
v_name_4594_ = lean_ctor_get(v_toSignature_4592_, 0);
v_params_4595_ = lean_ctor_get(v_toSignature_4592_, 3);
v_safe_4596_ = lean_ctor_get_uint8(v_toSignature_4592_, sizeof(void*)*4);
v___x_4597_ = lean_box(0);
v___x_4598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4599_ = lean_bool_not(v_safe_4596_);
if (v___x_4599_ == 0)
{
lean_object* v___x_4600_; 
v___x_4600_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4575_, v___y_4578_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v_a_4601_; lean_object* v___y_4603_; lean_object* v_decls_4634_; lean_object* v___f_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___y_4640_; lean_object* v___y_4641_; uint8_t v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v_a_4646_; lean_object* v___y_4659_; lean_object* v___y_4660_; uint8_t v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v_a_4665_; lean_object* v___y_4675_; lean_object* v___y_4676_; uint8_t v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; lean_object* v___y_4732_; uint8_t v_a_4733_; lean_object* v___y_4751_; uint8_t v___x_4760_; 
v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_a_4601_);
lean_dec_ref_known(v___x_4600_, 1);
v_decls_4634_ = lean_ctor_get(v___y_4577_, 0);
lean_inc(v_name_4594_);
v___f_4635_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4635_, 0, v_name_4594_);
v___x_4636_ = lean_unsigned_to_nat(0u);
v___x_4637_ = lean_array_get_size(v_params_4595_);
lean_inc(v_a_4575_);
lean_inc_ref(v_decls_4634_);
v___x_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4638_, 0, v_decls_4634_);
lean_ctor_set(v___x_4638_, 1, v_a_4575_);
v___x_4760_ = lean_nat_dec_lt(v___x_4636_, v___x_4637_);
if (v___x_4760_ == 0)
{
goto v___jp_4737_;
}
else
{
uint8_t v___x_4761_; 
v___x_4761_ = lean_nat_dec_le(v___x_4637_, v___x_4637_);
if (v___x_4761_ == 0)
{
if (v___x_4760_ == 0)
{
goto v___jp_4737_;
}
else
{
size_t v___x_4762_; size_t v___x_4763_; lean_object* v___x_4764_; 
v___x_4762_ = ((size_t)0ULL);
v___x_4763_ = lean_usize_of_nat(v___x_4637_);
v___x_4764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4595_, v___x_4762_, v___x_4763_, v___x_4597_, v___x_4638_, v___y_4578_, v___y_4582_);
v___y_4751_ = v___x_4764_;
goto v___jp_4750_;
}
}
else
{
size_t v___x_4765_; size_t v___x_4766_; lean_object* v___x_4767_; 
v___x_4765_ = ((size_t)0ULL);
v___x_4766_ = lean_usize_of_nat(v___x_4637_);
v___x_4767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4595_, v___x_4765_, v___x_4766_, v___x_4597_, v___x_4638_, v___y_4578_, v___y_4582_);
v___y_4751_ = v___x_4767_;
goto v___jp_4750_;
}
}
v___jp_4602_:
{
if (lean_obj_tag(v___y_4603_) == 0)
{
lean_object* v___x_4604_; 
lean_dec_ref_known(v___y_4603_, 1);
v___x_4604_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4575_, v___y_4578_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4617_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4617_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4617_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
uint8_t v___x_4609_; uint8_t v___x_4610_; 
v___x_4609_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4601_, v_a_4605_);
lean_dec(v_a_4605_);
lean_dec(v_a_4601_);
v___x_4610_ = lean_bool_not(v___x_4609_);
if (v___x_4610_ == 0)
{
lean_del_object(v___x_4607_);
v_a_4585_ = v___x_4598_;
goto v___jp_4584_;
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4615_; 
lean_dec(v_a_4575_);
v___x_4611_ = lean_box(v___x_4589_);
v___x_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
v___x_4613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4612_);
lean_ctor_set(v___x_4613_, 1, v___x_4597_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4613_);
v___x_4615_ = v___x_4607_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4613_);
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
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_dec(v_a_4601_);
lean_dec(v_a_4575_);
v_a_4618_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4604_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4604_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_dec(v_a_4601_);
lean_dec(v_a_4575_);
v_a_4626_ = lean_ctor_get(v___y_4603_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___y_4603_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___y_4603_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___y_4603_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
v___jp_4639_:
{
lean_object* v___x_4647_; double v___x_4648_; double v___x_4649_; double v___x_4650_; double v___x_4651_; double v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4647_ = lean_io_mono_nanos_now();
v___x_4648_ = lean_float_of_nat(v___y_4640_);
v___x_4649_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4650_ = lean_float_div(v___x_4648_, v___x_4649_);
v___x_4651_ = lean_float_of_nat(v___x_4647_);
v___x_4652_ = lean_float_div(v___x_4651_, v___x_4649_);
v___x_4653_ = lean_box_float(v___x_4650_);
v___x_4654_ = lean_box_float(v___x_4652_);
v___x_4655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4653_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v_a_4646_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
lean_inc_ref(v___y_4645_);
lean_inc(v___y_4643_);
v___x_4657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4643_, v___x_4589_, v___y_4645_, v___y_4644_, v___y_4642_, v___y_4641_, v___f_4635_, v___x_4656_, v___x_4638_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec_ref_known(v___x_4638_, 2);
v___y_4603_ = v___x_4657_;
goto v___jp_4602_;
}
v___jp_4658_:
{
lean_object* v___x_4666_; double v___x_4667_; double v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4666_ = lean_io_get_num_heartbeats();
v___x_4667_ = lean_float_of_nat(v___y_4659_);
v___x_4668_ = lean_float_of_nat(v___x_4666_);
v___x_4669_ = lean_box_float(v___x_4667_);
v___x_4670_ = lean_box_float(v___x_4668_);
v___x_4671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4669_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
v___x_4672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4672_, 0, v_a_4665_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
lean_inc_ref(v___y_4664_);
lean_inc(v___y_4662_);
v___x_4673_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4662_, v___x_4589_, v___y_4664_, v___y_4663_, v___y_4661_, v___y_4660_, v___f_4635_, v___x_4672_, v___x_4638_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec_ref_known(v___x_4638_, 2);
v___y_4603_ = v___x_4673_;
goto v___jp_4602_;
}
v___jp_4674_:
{
lean_object* v___x_4680_; 
v___x_4680_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4582_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v___x_4680_, 1);
v___x_4682_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4683_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4678_, v___x_4682_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4684_ = lean_io_mono_nanos_now();
v___x_4685_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4675_, v___x_4638_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4685_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4685_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
lean_ctor_set_tag(v___x_4688_, 1);
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
v___y_4640_ = v___x_4684_;
v___y_4641_ = v_a_4681_;
v___y_4642_ = v___y_4677_;
v___y_4643_ = v___y_4676_;
v___y_4644_ = v___y_4678_;
v___y_4645_ = v___y_4679_;
v_a_4646_ = v___x_4691_;
goto v___jp_4639_;
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
v_a_4694_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4685_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4685_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
lean_ctor_set_tag(v___x_4696_, 0);
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
v___y_4640_ = v___x_4684_;
v___y_4641_ = v_a_4681_;
v___y_4642_ = v___y_4677_;
v___y_4643_ = v___y_4676_;
v___y_4644_ = v___y_4678_;
v___y_4645_ = v___y_4679_;
v_a_4646_ = v___x_4699_;
goto v___jp_4639_;
}
}
}
}
else
{
lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4702_ = lean_io_get_num_heartbeats();
v___x_4703_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4675_, v___x_4638_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
lean_ctor_set_tag(v___x_4706_, 1);
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
v___y_4659_ = v___x_4702_;
v___y_4660_ = v_a_4681_;
v___y_4661_ = v___y_4677_;
v___y_4662_ = v___y_4676_;
v___y_4663_ = v___y_4678_;
v___y_4664_ = v___y_4679_;
v_a_4665_ = v___x_4709_;
goto v___jp_4658_;
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
v_a_4712_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4703_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4703_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
lean_ctor_set_tag(v___x_4714_, 0);
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
v___y_4659_ = v___x_4702_;
v___y_4660_ = v_a_4681_;
v___y_4661_ = v___y_4677_;
v___y_4662_ = v___y_4676_;
v___y_4663_ = v___y_4678_;
v___y_4664_ = v___y_4679_;
v_a_4665_ = v___x_4717_;
goto v___jp_4658_;
}
}
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_dec_ref(v___y_4675_);
lean_dec_ref_known(v___x_4638_, 2);
lean_dec_ref(v___f_4635_);
lean_dec(v_a_4601_);
lean_dec(v_a_4575_);
v_a_4720_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4680_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4680_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
v___jp_4728_:
{
lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4734_ = l_Lean_trace_profiler;
v___x_4735_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4731_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; 
lean_dec_ref(v___f_4635_);
v___x_4736_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4730_, v___x_4638_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec_ref_known(v___x_4638_, 2);
v___y_4603_ = v___x_4736_;
goto v___jp_4602_;
}
else
{
v___y_4675_ = v___y_4730_;
v___y_4676_ = v___y_4729_;
v___y_4677_ = v_a_4733_;
v___y_4678_ = v___y_4731_;
v___y_4679_ = v___y_4732_;
goto v___jp_4674_;
}
}
v___jp_4737_:
{
if (lean_obj_tag(v_value_4593_) == 0)
{
lean_object* v_options_4738_; lean_object* v_code_4739_; lean_object* v_inheritedTraceOptions_4740_; uint8_t v_hasTrace_4741_; uint8_t v___x_4742_; 
v_options_4738_ = lean_ctor_get(v___y_4581_, 2);
v_code_4739_ = lean_ctor_get(v_value_4593_, 0);
v_inheritedTraceOptions_4740_ = lean_ctor_get(v___y_4581_, 13);
v_hasTrace_4741_ = lean_ctor_get_uint8(v_options_4738_, sizeof(void*)*1);
v___x_4742_ = lean_bool_not(v_hasTrace_4741_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4744_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
if (v_hasTrace_4741_ == 0)
{
lean_inc_ref(v_code_4739_);
v___y_4729_ = v___x_4743_;
v___y_4730_ = v_code_4739_;
v___y_4731_ = v_options_4738_;
v___y_4732_ = v___x_4744_;
v_a_4733_ = v_hasTrace_4741_;
goto v___jp_4728_;
}
else
{
lean_object* v___x_4745_; uint8_t v___x_4746_; 
v___x_4745_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4740_, v_options_4738_, v___x_4745_);
if (v___x_4746_ == 0)
{
lean_inc_ref(v_code_4739_);
v___y_4729_ = v___x_4743_;
v___y_4730_ = v_code_4739_;
v___y_4731_ = v_options_4738_;
v___y_4732_ = v___x_4744_;
v_a_4733_ = v___x_4746_;
goto v___jp_4728_;
}
else
{
lean_inc_ref(v_code_4739_);
v___y_4675_ = v_code_4739_;
v___y_4676_ = v___x_4743_;
v___y_4677_ = v___x_4746_;
v___y_4678_ = v_options_4738_;
v___y_4679_ = v___x_4744_;
goto v___jp_4674_;
}
}
}
else
{
lean_object* v___x_4747_; 
lean_dec_ref(v___f_4635_);
lean_inc_ref(v_code_4739_);
v___x_4747_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4739_, v___x_4638_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec_ref_known(v___x_4638_, 2);
v___y_4603_ = v___x_4747_;
goto v___jp_4602_;
}
}
else
{
lean_object* v___x_4748_; lean_object* v___x_4749_; 
lean_dec_ref(v___f_4635_);
v___x_4748_ = lean_box(1);
v___x_4749_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4748_, v___x_4638_, v___y_4578_, v___y_4582_);
lean_dec_ref_known(v___x_4638_, 2);
v___y_4603_ = v___x_4749_;
goto v___jp_4602_;
}
}
v___jp_4750_:
{
if (lean_obj_tag(v___y_4751_) == 0)
{
lean_dec_ref_known(v___y_4751_, 1);
goto v___jp_4737_;
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec_ref_known(v___x_4638_, 2);
lean_dec_ref(v___f_4635_);
lean_dec(v_a_4601_);
lean_dec(v_a_4575_);
v_a_4752_ = lean_ctor_get(v___y_4751_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___y_4751_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___y_4751_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___y_4751_);
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
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
lean_dec(v_a_4575_);
v_a_4768_ = lean_ctor_get(v___x_4600_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4600_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4600_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
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
v_a_4585_ = v___x_4598_;
goto v___jp_4584_;
}
}
v___jp_4584_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = lean_unsigned_to_nat(1u);
v___x_4587_ = lean_nat_add(v_a_4575_, v___x_4586_);
lean_dec(v_a_4575_);
lean_inc_ref(v_a_4585_);
v_a_4575_ = v___x_4587_;
v_b_4576_ = v_a_4585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4776_, lean_object* v___x_4777_, lean_object* v_a_4778_, lean_object* v_b_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4776_, v___x_4777_, v_a_4778_, v_b_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec_ref(v___x_4777_);
lean_dec(v_upperBound_4776_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_){
_start:
{
lean_object* v_decls_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v_decls_4795_ = lean_ctor_get(v_a_4788_, 0);
v___x_4796_ = lean_array_get_size(v_decls_4795_);
v___x_4797_ = lean_unsigned_to_nat(0u);
v___x_4798_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4799_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4796_, v_decls_4795_, v___x_4797_, v___x_4798_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4814_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4814_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4814_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v_fst_4804_; 
v_fst_4804_ = lean_ctor_get(v_a_4800_, 0);
lean_inc(v_fst_4804_);
lean_dec(v_a_4800_);
if (lean_obj_tag(v_fst_4804_) == 0)
{
uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___x_4805_ = 0;
v___x_4806_ = lean_box(v___x_4805_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4806_);
v___x_4808_ = v___x_4802_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
else
{
lean_object* v_val_4810_; lean_object* v___x_4812_; 
v_val_4810_ = lean_ctor_get(v_fst_4804_, 0);
lean_inc(v_val_4810_);
lean_dec_ref_known(v_fst_4804_, 1);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_val_4810_);
v___x_4812_ = v___x_4802_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_val_4810_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
v_a_4815_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4799_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4799_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4831_, lean_object* v_x_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4832_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4841_, lean_object* v_x_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4841_, v_x_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4851_, lean_object* v___x_4852_, lean_object* v_inst_4853_, lean_object* v_R_4854_, lean_object* v_a_4855_, lean_object* v_b_4856_, lean_object* v_c_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4851_, v___x_4852_, v_a_4855_, v_b_4856_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4866_, lean_object* v___x_4867_, lean_object* v_inst_4868_, lean_object* v_R_4869_, lean_object* v_a_4870_, lean_object* v_b_4871_, lean_object* v_c_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4866_, v___x_4867_, v_inst_4868_, v_R_4869_, v_a_4870_, v_b_4871_, v_c_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec_ref(v___x_4867_);
lean_dec(v_upperBound_4866_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4881_, lean_object* v_data_4882_, lean_object* v_ref_4883_, lean_object* v_msg_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4881_, v_data_4882_, v_ref_4883_, v_msg_4884_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4893_, lean_object* v_data_4894_, lean_object* v_ref_4895_, lean_object* v_msg_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4893_, v_data_4894_, v_ref_4895_, v_msg_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
lean_dec(v___y_4902_);
lean_dec_ref(v___y_4901_);
lean_dec(v___y_4900_);
lean_dec_ref(v___y_4899_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4907_, lean_object* v_msg_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v_options_4914_; lean_object* v_ref_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v_options_4914_ = lean_ctor_get(v___y_4911_, 2);
v_ref_4915_ = lean_ctor_get(v___y_4911_, 5);
v___x_4916_ = lean_st_ref_get(v___y_4912_);
v___x_4917_ = lean_st_ref_get(v___y_4910_);
v___x_4918_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4909_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4977_; 
v_a_4919_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4921_ = v___x_4918_;
v_isShared_4922_ = v_isSharedCheck_4977_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4918_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4977_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v_env_4923_; lean_object* v_lctx_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4975_; 
v_env_4923_ = lean_ctor_get(v___x_4916_, 0);
lean_inc_ref(v_env_4923_);
lean_dec(v___x_4916_);
v_lctx_4924_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v___x_4917_, 1);
lean_dec(v_unused_4976_);
v___x_4926_ = v___x_4917_;
v_isShared_4927_ = v_isSharedCheck_4975_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_lctx_4924_);
lean_dec(v___x_4917_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4975_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v_traceState_4930_; lean_object* v_env_4931_; lean_object* v_nextMacroScope_4932_; lean_object* v_ngen_4933_; lean_object* v_auxDeclNGen_4934_; lean_object* v_cache_4935_; lean_object* v_messages_4936_; lean_object* v_infoState_4937_; lean_object* v_snapshotTasks_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4974_; 
v___x_4928_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4929_ = lean_st_ref_take(v___y_4912_);
v_traceState_4930_ = lean_ctor_get(v___x_4929_, 4);
v_env_4931_ = lean_ctor_get(v___x_4929_, 0);
v_nextMacroScope_4932_ = lean_ctor_get(v___x_4929_, 1);
v_ngen_4933_ = lean_ctor_get(v___x_4929_, 2);
v_auxDeclNGen_4934_ = lean_ctor_get(v___x_4929_, 3);
v_cache_4935_ = lean_ctor_get(v___x_4929_, 5);
v_messages_4936_ = lean_ctor_get(v___x_4929_, 6);
v_infoState_4937_ = lean_ctor_get(v___x_4929_, 7);
v_snapshotTasks_4938_ = lean_ctor_get(v___x_4929_, 8);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4940_ = v___x_4929_;
v_isShared_4941_ = v_isSharedCheck_4974_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_snapshotTasks_4938_);
lean_inc(v_infoState_4937_);
lean_inc(v_messages_4936_);
lean_inc(v_cache_4935_);
lean_inc(v_traceState_4930_);
lean_inc(v_auxDeclNGen_4934_);
lean_inc(v_ngen_4933_);
lean_inc(v_nextMacroScope_4932_);
lean_inc(v_env_4931_);
lean_dec(v___x_4929_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4974_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
uint64_t v_tid_4942_; lean_object* v_traces_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4973_; 
v_tid_4942_ = lean_ctor_get_uint64(v_traceState_4930_, sizeof(void*)*1);
v_traces_4943_ = lean_ctor_get(v_traceState_4930_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v_traceState_4930_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4945_ = v_traceState_4930_;
v_isShared_4946_ = v_isSharedCheck_4973_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_traces_4943_);
lean_dec(v_traceState_4930_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4973_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
uint8_t v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4951_; 
v___x_4947_ = lean_unbox(v_a_4919_);
lean_dec(v_a_4919_);
v___x_4948_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4924_, v___x_4947_);
lean_dec_ref(v_lctx_4924_);
lean_inc_ref(v_options_4914_);
v___x_4949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4949_, 0, v_env_4923_);
lean_ctor_set(v___x_4949_, 1, v___x_4928_);
lean_ctor_set(v___x_4949_, 2, v___x_4948_);
lean_ctor_set(v___x_4949_, 3, v_options_4914_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set_tag(v___x_4926_, 3);
lean_ctor_set(v___x_4926_, 1, v_msg_4908_);
lean_ctor_set(v___x_4926_, 0, v___x_4949_);
v___x_4951_ = v___x_4926_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v___x_4949_);
lean_ctor_set(v_reuseFailAlloc_4972_, 1, v_msg_4908_);
v___x_4951_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
lean_object* v___x_4952_; double v___x_4953_; uint8_t v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4962_; 
v___x_4952_ = lean_box(0);
v___x_4953_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4954_ = 0;
v___x_4955_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4956_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4956_, 0, v_cls_4907_);
lean_ctor_set(v___x_4956_, 1, v___x_4952_);
lean_ctor_set(v___x_4956_, 2, v___x_4955_);
lean_ctor_set_float(v___x_4956_, sizeof(void*)*3, v___x_4953_);
lean_ctor_set_float(v___x_4956_, sizeof(void*)*3 + 8, v___x_4953_);
lean_ctor_set_uint8(v___x_4956_, sizeof(void*)*3 + 16, v___x_4954_);
v___x_4957_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4958_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4951_);
lean_ctor_set(v___x_4958_, 2, v___x_4957_);
lean_inc(v_ref_4915_);
v___x_4959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4959_, 0, v_ref_4915_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = l_Lean_PersistentArray_push___redArg(v_traces_4943_, v___x_4959_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 0, v___x_4960_);
v___x_4962_ = v___x_4945_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4960_);
lean_ctor_set_uint64(v_reuseFailAlloc_4971_, sizeof(void*)*1, v_tid_4942_);
v___x_4962_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
lean_object* v___x_4964_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 4, v___x_4962_);
v___x_4964_ = v___x_4940_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_env_4931_);
lean_ctor_set(v_reuseFailAlloc_4970_, 1, v_nextMacroScope_4932_);
lean_ctor_set(v_reuseFailAlloc_4970_, 2, v_ngen_4933_);
lean_ctor_set(v_reuseFailAlloc_4970_, 3, v_auxDeclNGen_4934_);
lean_ctor_set(v_reuseFailAlloc_4970_, 4, v___x_4962_);
lean_ctor_set(v_reuseFailAlloc_4970_, 5, v_cache_4935_);
lean_ctor_set(v_reuseFailAlloc_4970_, 6, v_messages_4936_);
lean_ctor_set(v_reuseFailAlloc_4970_, 7, v_infoState_4937_);
lean_ctor_set(v_reuseFailAlloc_4970_, 8, v_snapshotTasks_4938_);
v___x_4964_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4968_; 
v___x_4965_ = lean_st_ref_set(v___y_4912_, v___x_4964_);
v___x_4966_ = lean_box(0);
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 0, v___x_4966_);
v___x_4968_ = v___x_4921_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v___x_4966_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
return v___x_4968_;
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
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
lean_dec(v___x_4917_);
lean_dec(v___x_4916_);
lean_dec_ref(v_msg_4908_);
lean_dec(v_cls_4907_);
v_a_4978_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4918_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4918_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4986_, lean_object* v_msg_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4986_, v_msg_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
lean_dec(v___y_4989_);
lean_dec_ref(v___y_4988_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4994_, lean_object* v_msg_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4994_, v_msg_4995_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_5004_, lean_object* v_msg_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_5004_, v_msg_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
return v_res_5013_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5014_ = lean_box(0);
v___x_5015_ = lean_unsigned_to_nat(16u);
v___x_5016_ = lean_mk_array(v___x_5015_, v___x_5014_);
return v___x_5016_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_5018_ = lean_unsigned_to_nat(0u);
v___x_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
lean_ctor_set(v___x_5019_, 1, v___x_5017_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_5020_, size_t v_i_5021_, lean_object* v_bs_5022_){
_start:
{
uint8_t v___x_5023_; 
v___x_5023_ = lean_usize_dec_lt(v_i_5021_, v_sz_5020_);
if (v___x_5023_ == 0)
{
return v_bs_5022_;
}
else
{
lean_object* v___x_5024_; lean_object* v_bs_x27_5025_; lean_object* v___x_5026_; size_t v___x_5027_; size_t v___x_5028_; lean_object* v___x_5029_; 
v___x_5024_ = lean_unsigned_to_nat(0u);
v_bs_x27_5025_ = lean_array_uset(v_bs_5022_, v_i_5021_, v___x_5024_);
v___x_5026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5027_ = ((size_t)1ULL);
v___x_5028_ = lean_usize_add(v_i_5021_, v___x_5027_);
v___x_5029_ = lean_array_uset(v_bs_x27_5025_, v_i_5021_, v___x_5026_);
v_i_5021_ = v___x_5028_;
v_bs_5022_ = v___x_5029_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_5031_, lean_object* v_i_5032_, lean_object* v_bs_5033_){
_start:
{
size_t v_sz_boxed_5034_; size_t v_i_boxed_5035_; lean_object* v_res_5036_; 
v_sz_boxed_5034_ = lean_unbox_usize(v_sz_5031_);
lean_dec(v_sz_5031_);
v_i_boxed_5035_ = lean_unbox_usize(v_i_5032_);
lean_dec(v_i_5032_);
v_res_5036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_5034_, v_i_boxed_5035_, v_bs_5033_);
return v_res_5036_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5038_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5039_ = l_Lean_stringToMessageData(v___x_5038_);
return v___x_5039_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5041_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5042_ = l_Lean_stringToMessageData(v___x_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v___x_5054_; lean_object* v_decls_5055_; lean_object* v_funVals_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5095_; 
v___x_5054_ = lean_st_ref_take(v_a_5045_);
v_decls_5055_ = lean_ctor_get(v_a_5044_, 0);
v_funVals_5056_ = lean_ctor_get(v___x_5054_, 1);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5095_ == 0)
{
lean_object* v_unused_5096_; 
v_unused_5096_ = lean_ctor_get(v___x_5054_, 0);
lean_dec(v_unused_5096_);
v___x_5058_ = v___x_5054_;
v_isShared_5059_ = v_isSharedCheck_5095_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_funVals_5056_);
lean_dec(v___x_5054_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5095_;
goto v_resetjp_5057_;
}
v___jp_5051_:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5052_ = lean_box(0);
v___x_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
return v___x_5053_;
}
v_resetjp_5057_:
{
size_t v_sz_5060_; size_t v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5064_; 
v_sz_5060_ = lean_array_size(v_decls_5055_);
v___x_5061_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5055_);
v___x_5062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5060_, v___x_5061_, v_decls_5055_);
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5062_);
v___x_5064_ = v___x_5058_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5062_);
lean_ctor_set(v_reuseFailAlloc_5094_, 1, v_funVals_5056_);
v___x_5064_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = lean_st_ref_set(v_a_5045_, v___x_5064_);
v___x_5066_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; uint8_t v___x_5068_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5068_ = lean_unbox(v_a_5067_);
lean_dec(v_a_5067_);
if (v___x_5068_ == 0)
{
lean_object* v_options_5069_; uint8_t v_hasTrace_5070_; 
v_options_5069_ = lean_ctor_get(v_a_5048_, 2);
v_hasTrace_5070_ = lean_ctor_get_uint8(v_options_5069_, sizeof(void*)*1);
if (v_hasTrace_5070_ == 0)
{
lean_dec(v_n_5043_);
goto v___jp_5051_;
}
else
{
lean_object* v_inheritedTraceOptions_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; uint8_t v___x_5074_; 
v_inheritedTraceOptions_5071_ = lean_ctor_get(v_a_5048_, 13);
v___x_5072_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5073_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5071_, v_options_5069_, v___x_5073_);
if (v___x_5074_ == 0)
{
lean_dec(v_n_5043_);
goto v___jp_5051_;
}
else
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5075_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5076_ = l_Nat_reprFast(v_n_5043_);
v___x_5077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
v___x_5078_ = l_Lean_MessageData_ofFormat(v___x_5077_);
v___x_5079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___x_5075_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
v___x_5080_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5079_);
lean_ctor_set(v___x_5081_, 1, v___x_5080_);
v___x_5082_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5072_, v___x_5081_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_dec_ref_known(v___x_5082_, 1);
goto v___jp_5051_;
}
else
{
return v___x_5082_;
}
}
}
}
else
{
lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5083_ = lean_unsigned_to_nat(1u);
v___x_5084_ = lean_nat_add(v_n_5043_, v___x_5083_);
lean_dec(v_n_5043_);
v_n_5043_ = v___x_5084_;
goto _start;
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_dec(v_n_5043_);
v_a_5086_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5066_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5066_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_);
lean_dec(v_a_5103_);
lean_dec_ref(v_a_5102_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
return v_res_5105_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = 0;
v___x_5107_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5106_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5108_){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5110_ = lean_panic_fn_borrowed(v___x_5109_, v_msg_5108_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5111_, lean_object* v_msg_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_options_5118_; lean_object* v_ref_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_options_5118_ = lean_ctor_get(v___y_5115_, 2);
v_ref_5119_ = lean_ctor_get(v___y_5115_, 5);
v___x_5120_ = lean_st_ref_get(v___y_5116_);
v___x_5121_ = lean_st_ref_get(v___y_5114_);
v___x_5122_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5113_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5181_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5125_ = v___x_5122_;
v_isShared_5126_ = v_isSharedCheck_5181_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5122_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5181_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v_env_5127_; lean_object* v_lctx_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5179_; 
v_env_5127_ = lean_ctor_get(v___x_5120_, 0);
lean_inc_ref(v_env_5127_);
lean_dec(v___x_5120_);
v_lctx_5128_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5179_ == 0)
{
lean_object* v_unused_5180_; 
v_unused_5180_ = lean_ctor_get(v___x_5121_, 1);
lean_dec(v_unused_5180_);
v___x_5130_ = v___x_5121_;
v_isShared_5131_ = v_isSharedCheck_5179_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_lctx_5128_);
lean_dec(v___x_5121_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5179_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v_traceState_5134_; lean_object* v_env_5135_; lean_object* v_nextMacroScope_5136_; lean_object* v_ngen_5137_; lean_object* v_auxDeclNGen_5138_; lean_object* v_cache_5139_; lean_object* v_messages_5140_; lean_object* v_infoState_5141_; lean_object* v_snapshotTasks_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5178_; 
v___x_5132_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_5133_ = lean_st_ref_take(v___y_5116_);
v_traceState_5134_ = lean_ctor_get(v___x_5133_, 4);
v_env_5135_ = lean_ctor_get(v___x_5133_, 0);
v_nextMacroScope_5136_ = lean_ctor_get(v___x_5133_, 1);
v_ngen_5137_ = lean_ctor_get(v___x_5133_, 2);
v_auxDeclNGen_5138_ = lean_ctor_get(v___x_5133_, 3);
v_cache_5139_ = lean_ctor_get(v___x_5133_, 5);
v_messages_5140_ = lean_ctor_get(v___x_5133_, 6);
v_infoState_5141_ = lean_ctor_get(v___x_5133_, 7);
v_snapshotTasks_5142_ = lean_ctor_get(v___x_5133_, 8);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5144_ = v___x_5133_;
v_isShared_5145_ = v_isSharedCheck_5178_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_snapshotTasks_5142_);
lean_inc(v_infoState_5141_);
lean_inc(v_messages_5140_);
lean_inc(v_cache_5139_);
lean_inc(v_traceState_5134_);
lean_inc(v_auxDeclNGen_5138_);
lean_inc(v_ngen_5137_);
lean_inc(v_nextMacroScope_5136_);
lean_inc(v_env_5135_);
lean_dec(v___x_5133_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5178_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
uint64_t v_tid_5146_; lean_object* v_traces_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5177_; 
v_tid_5146_ = lean_ctor_get_uint64(v_traceState_5134_, sizeof(void*)*1);
v_traces_5147_ = lean_ctor_get(v_traceState_5134_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_traceState_5134_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5149_ = v_traceState_5134_;
v_isShared_5150_ = v_isSharedCheck_5177_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_traces_5147_);
lean_dec(v_traceState_5134_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5177_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
uint8_t v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5155_; 
v___x_5151_ = lean_unbox(v_a_5123_);
lean_dec(v_a_5123_);
v___x_5152_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5128_, v___x_5151_);
lean_dec_ref(v_lctx_5128_);
lean_inc_ref(v_options_5118_);
v___x_5153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5153_, 0, v_env_5127_);
lean_ctor_set(v___x_5153_, 1, v___x_5132_);
lean_ctor_set(v___x_5153_, 2, v___x_5152_);
lean_ctor_set(v___x_5153_, 3, v_options_5118_);
if (v_isShared_5131_ == 0)
{
lean_ctor_set_tag(v___x_5130_, 3);
lean_ctor_set(v___x_5130_, 1, v_msg_5112_);
lean_ctor_set(v___x_5130_, 0, v___x_5153_);
v___x_5155_ = v___x_5130_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5153_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v_msg_5112_);
v___x_5155_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
lean_object* v___x_5156_; double v___x_5157_; uint8_t v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5166_; 
v___x_5156_ = lean_box(0);
v___x_5157_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5158_ = 0;
v___x_5159_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5160_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5160_, 0, v_cls_5111_);
lean_ctor_set(v___x_5160_, 1, v___x_5156_);
lean_ctor_set(v___x_5160_, 2, v___x_5159_);
lean_ctor_set_float(v___x_5160_, sizeof(void*)*3, v___x_5157_);
lean_ctor_set_float(v___x_5160_, sizeof(void*)*3 + 8, v___x_5157_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*3 + 16, v___x_5158_);
v___x_5161_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5162_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5160_);
lean_ctor_set(v___x_5162_, 1, v___x_5155_);
lean_ctor_set(v___x_5162_, 2, v___x_5161_);
lean_inc(v_ref_5119_);
v___x_5163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5163_, 0, v_ref_5119_);
lean_ctor_set(v___x_5163_, 1, v___x_5162_);
v___x_5164_ = l_Lean_PersistentArray_push___redArg(v_traces_5147_, v___x_5163_);
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v___x_5164_);
v___x_5166_ = v___x_5149_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5164_);
lean_ctor_set_uint64(v_reuseFailAlloc_5175_, sizeof(void*)*1, v_tid_5146_);
v___x_5166_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
lean_object* v___x_5168_; 
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 4, v___x_5166_);
v___x_5168_ = v___x_5144_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_env_5135_);
lean_ctor_set(v_reuseFailAlloc_5174_, 1, v_nextMacroScope_5136_);
lean_ctor_set(v_reuseFailAlloc_5174_, 2, v_ngen_5137_);
lean_ctor_set(v_reuseFailAlloc_5174_, 3, v_auxDeclNGen_5138_);
lean_ctor_set(v_reuseFailAlloc_5174_, 4, v___x_5166_);
lean_ctor_set(v_reuseFailAlloc_5174_, 5, v_cache_5139_);
lean_ctor_set(v_reuseFailAlloc_5174_, 6, v_messages_5140_);
lean_ctor_set(v_reuseFailAlloc_5174_, 7, v_infoState_5141_);
lean_ctor_set(v_reuseFailAlloc_5174_, 8, v_snapshotTasks_5142_);
v___x_5168_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5172_; 
v___x_5169_ = lean_st_ref_set(v___y_5116_, v___x_5168_);
v___x_5170_ = lean_box(0);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v___x_5170_);
v___x_5172_ = v___x_5125_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5170_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
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
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec(v___x_5121_);
lean_dec(v___x_5120_);
lean_dec_ref(v_msg_5112_);
lean_dec(v_cls_5111_);
v_a_5182_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5122_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5122_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5190_, lean_object* v_msg_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5190_, v_msg_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_);
lean_dec(v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5198_, size_t v_i_5199_, size_t v_stop_5200_, lean_object* v_b_5201_){
_start:
{
uint8_t v___x_5203_; 
v___x_5203_ = lean_usize_dec_eq(v_i_5199_, v_stop_5200_);
if (v___x_5203_ == 0)
{
lean_object* v_fst_5204_; lean_object* v_snd_5205_; lean_object* v___x_5206_; lean_object* v_snd_5207_; lean_object* v_fst_5208_; lean_object* v_fst_5209_; lean_object* v_snd_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5225_; 
v_fst_5204_ = lean_ctor_get(v_b_5201_, 0);
lean_inc(v_fst_5204_);
v_snd_5205_ = lean_ctor_get(v_b_5201_, 1);
lean_inc(v_snd_5205_);
lean_dec_ref(v_b_5201_);
v___x_5206_ = lean_array_uget_borrowed(v_as_5198_, v_i_5199_);
v_snd_5207_ = lean_ctor_get(v___x_5206_, 1);
lean_inc(v_snd_5207_);
v_fst_5208_ = lean_ctor_get(v___x_5206_, 0);
v_fst_5209_ = lean_ctor_get(v_snd_5207_, 0);
v_snd_5210_ = lean_ctor_get(v_snd_5207_, 1);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_snd_5207_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5212_ = v_snd_5207_;
v_isShared_5213_ = v_isSharedCheck_5225_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_snd_5210_);
lean_inc(v_fst_5209_);
lean_dec(v_snd_5207_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5225_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v_fvarId_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5220_; 
v_fvarId_5214_ = lean_ctor_get(v_fst_5208_, 0);
v___x_5215_ = 0;
v___x_5216_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5215_, v_fst_5209_, v_fst_5204_);
lean_dec(v_fst_5209_);
v___x_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5217_, 0, v_snd_5210_);
lean_inc(v_fvarId_5214_);
v___x_5218_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5205_, v_fvarId_5214_, v___x_5217_);
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 1, v___x_5218_);
lean_ctor_set(v___x_5212_, 0, v___x_5216_);
v___x_5220_ = v___x_5212_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5216_);
lean_ctor_set(v_reuseFailAlloc_5224_, 1, v___x_5218_);
v___x_5220_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
size_t v___x_5221_; size_t v___x_5222_; 
v___x_5221_ = ((size_t)1ULL);
v___x_5222_ = lean_usize_add(v_i_5199_, v___x_5221_);
v_i_5199_ = v___x_5222_;
v_b_5201_ = v___x_5220_;
goto _start;
}
}
}
else
{
lean_object* v___x_5226_; 
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v_b_5201_);
return v___x_5226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5227_, lean_object* v_i_5228_, lean_object* v_stop_5229_, lean_object* v_b_5230_, lean_object* v___y_5231_){
_start:
{
size_t v_i_boxed_5232_; size_t v_stop_boxed_5233_; lean_object* v_res_5234_; 
v_i_boxed_5232_ = lean_unbox_usize(v_i_5228_);
lean_dec(v_i_5228_);
v_stop_boxed_5233_ = lean_unbox_usize(v_stop_5229_);
lean_dec(v_stop_5229_);
v_res_5234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5227_, v_i_boxed_5232_, v_stop_boxed_5233_, v_b_5230_);
lean_dec_ref(v_as_5227_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5235_, lean_object* v_x_5236_){
_start:
{
if (lean_obj_tag(v_x_5236_) == 0)
{
lean_object* v___x_5237_; 
v___x_5237_ = lean_box(0);
return v___x_5237_;
}
else
{
lean_object* v_key_5238_; lean_object* v_value_5239_; lean_object* v_tail_5240_; uint8_t v___x_5241_; 
v_key_5238_ = lean_ctor_get(v_x_5236_, 0);
v_value_5239_ = lean_ctor_get(v_x_5236_, 1);
v_tail_5240_ = lean_ctor_get(v_x_5236_, 2);
v___x_5241_ = l_Lean_instBEqFVarId_beq(v_key_5238_, v_a_5235_);
if (v___x_5241_ == 0)
{
v_x_5236_ = v_tail_5240_;
goto _start;
}
else
{
lean_object* v___x_5243_; 
lean_inc(v_value_5239_);
v___x_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5243_, 0, v_value_5239_);
return v___x_5243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5244_, lean_object* v_x_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5244_, v_x_5245_);
lean_dec(v_x_5245_);
lean_dec(v_a_5244_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5247_, lean_object* v_a_5248_){
_start:
{
lean_object* v_buckets_5249_; lean_object* v___x_5250_; uint64_t v___x_5251_; uint64_t v___x_5252_; uint64_t v___x_5253_; uint64_t v_fold_5254_; uint64_t v___x_5255_; uint64_t v___x_5256_; uint64_t v___x_5257_; size_t v___x_5258_; size_t v___x_5259_; size_t v___x_5260_; size_t v___x_5261_; size_t v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; 
v_buckets_5249_ = lean_ctor_get(v_m_5247_, 1);
v___x_5250_ = lean_array_get_size(v_buckets_5249_);
v___x_5251_ = l_Lean_instHashableFVarId_hash(v_a_5248_);
v___x_5252_ = 32ULL;
v___x_5253_ = lean_uint64_shift_right(v___x_5251_, v___x_5252_);
v_fold_5254_ = lean_uint64_xor(v___x_5251_, v___x_5253_);
v___x_5255_ = 16ULL;
v___x_5256_ = lean_uint64_shift_right(v_fold_5254_, v___x_5255_);
v___x_5257_ = lean_uint64_xor(v_fold_5254_, v___x_5256_);
v___x_5258_ = lean_uint64_to_usize(v___x_5257_);
v___x_5259_ = lean_usize_of_nat(v___x_5250_);
v___x_5260_ = ((size_t)1ULL);
v___x_5261_ = lean_usize_sub(v___x_5259_, v___x_5260_);
v___x_5262_ = lean_usize_land(v___x_5258_, v___x_5261_);
v___x_5263_ = lean_array_uget_borrowed(v_buckets_5249_, v___x_5262_);
v___x_5264_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5248_, v___x_5263_);
return v___x_5264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5265_, v_a_5266_);
lean_dec(v_a_5266_);
lean_dec_ref(v_m_5265_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5268_, lean_object* v_as_5269_, size_t v_i_5270_, size_t v_stop_5271_, lean_object* v_b_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v_a_5279_; uint8_t v___x_5283_; 
v___x_5283_ = lean_usize_dec_eq(v_i_5270_, v_stop_5271_);
if (v___x_5283_ == 0)
{
lean_object* v___x_5284_; lean_object* v_fvarId_5285_; lean_object* v___x_5286_; 
v___x_5284_ = lean_array_uget_borrowed(v_as_5269_, v_i_5270_);
v_fvarId_5285_ = lean_ctor_get(v___x_5284_, 0);
v___x_5286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5268_, v_fvarId_5285_);
if (lean_obj_tag(v___x_5286_) == 1)
{
lean_object* v_val_5287_; lean_object* v___x_5288_; 
v_val_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc(v_val_5287_);
lean_dec_ref_known(v___x_5286_, 1);
v___x_5288_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5287_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
lean_inc(v_a_5289_);
lean_dec_ref_known(v___x_5288_, 1);
if (lean_obj_tag(v_a_5289_) == 1)
{
lean_object* v_val_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
v_val_5290_ = lean_ctor_get(v_a_5289_, 0);
lean_inc(v_val_5290_);
lean_dec_ref_known(v_a_5289_, 1);
lean_inc(v___x_5284_);
v___x_5291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5284_);
lean_ctor_set(v___x_5291_, 1, v_val_5290_);
v___x_5292_ = lean_array_push(v_b_5272_, v___x_5291_);
v_a_5279_ = v___x_5292_;
goto v___jp_5278_;
}
else
{
lean_dec(v_a_5289_);
v_a_5279_ = v_b_5272_;
goto v___jp_5278_;
}
}
else
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5300_; 
lean_dec_ref(v_b_5272_);
v_a_5293_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5295_ = v___x_5288_;
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5288_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
else
{
lean_dec(v___x_5286_);
v_a_5279_ = v_b_5272_;
goto v___jp_5278_;
}
}
else
{
lean_object* v___x_5301_; 
v___x_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5301_, 0, v_b_5272_);
return v___x_5301_;
}
v___jp_5278_:
{
size_t v___x_5280_; size_t v___x_5281_; 
v___x_5280_ = ((size_t)1ULL);
v___x_5281_ = lean_usize_add(v_i_5270_, v___x_5280_);
v_i_5270_ = v___x_5281_;
v_b_5272_ = v_a_5279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5302_, lean_object* v_as_5303_, lean_object* v_i_5304_, lean_object* v_stop_5305_, lean_object* v_b_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
size_t v_i_boxed_5312_; size_t v_stop_boxed_5313_; lean_object* v_res_5314_; 
v_i_boxed_5312_ = lean_unbox_usize(v_i_5304_);
lean_dec(v_i_5304_);
v_stop_boxed_5313_ = lean_unbox_usize(v_stop_5305_);
lean_dec(v_stop_5305_);
v_res_5314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5302_, v_as_5303_, v_i_boxed_5312_, v_stop_boxed_5313_, v_b_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec_ref(v_as_5303_);
lean_dec_ref(v_assignment_5302_);
return v_res_5314_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5317_, lean_object* v_as_5318_, lean_object* v_start_5319_, lean_object* v_stop_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v___x_5326_; uint8_t v___x_5327_; 
v___x_5326_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5327_ = lean_nat_dec_lt(v_start_5319_, v_stop_5320_);
if (v___x_5327_ == 0)
{
lean_object* v___x_5328_; 
v___x_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5326_);
return v___x_5328_;
}
else
{
lean_object* v___x_5329_; uint8_t v___x_5330_; 
v___x_5329_ = lean_array_get_size(v_as_5318_);
v___x_5330_ = lean_nat_dec_le(v_stop_5320_, v___x_5329_);
if (v___x_5330_ == 0)
{
uint8_t v___x_5331_; 
v___x_5331_ = lean_nat_dec_lt(v_start_5319_, v___x_5329_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5332_; 
v___x_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5326_);
return v___x_5332_;
}
else
{
size_t v___x_5333_; size_t v___x_5334_; lean_object* v___x_5335_; 
v___x_5333_ = lean_usize_of_nat(v_start_5319_);
v___x_5334_ = lean_usize_of_nat(v___x_5329_);
v___x_5335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5317_, v_as_5318_, v___x_5333_, v___x_5334_, v___x_5326_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
return v___x_5335_;
}
}
else
{
size_t v___x_5336_; size_t v___x_5337_; lean_object* v___x_5338_; 
v___x_5336_ = lean_usize_of_nat(v_start_5319_);
v___x_5337_ = lean_usize_of_nat(v_stop_5320_);
v___x_5338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5317_, v_as_5318_, v___x_5336_, v___x_5337_, v___x_5326_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
return v___x_5338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5339_, lean_object* v_as_5340_, lean_object* v_start_5341_, lean_object* v_stop_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v_res_5348_; 
v_res_5348_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5339_, v_as_5340_, v_start_5341_, v_stop_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v_stop_5342_);
lean_dec(v_start_5341_);
lean_dec_ref(v_as_5340_);
lean_dec_ref(v_assignment_5339_);
return v_res_5348_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5351_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5352_ = lean_unsigned_to_nat(9u);
v___x_5353_ = lean_unsigned_to_nat(641u);
v___x_5354_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5355_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5356_ = l_mkPanicMessageWithDecl(v___x_5355_, v___x_5354_, v___x_5353_, v___x_5352_, v___x_5351_);
return v___x_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5359_, lean_object* v_discrVal_5360_, lean_object* v_discr_5361_, lean_object* v_assignment_5362_, lean_object* v_i_5363_, lean_object* v_as_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_){
_start:
{
lean_object* v___x_5370_; uint8_t v___x_5371_; 
v___x_5370_ = lean_array_get_size(v_as_5364_);
v___x_5371_ = lean_nat_dec_lt(v_i_5363_, v___x_5370_);
if (v___x_5371_ == 0)
{
lean_object* v___x_5372_; 
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v___x_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5372_, 0, v_as_5364_);
return v___x_5372_;
}
else
{
lean_object* v_a_5373_; lean_object* v_a_5375_; 
v_a_5373_ = lean_array_fget_borrowed(v_as_5364_, v_i_5363_);
if (lean_obj_tag(v_a_5373_) == 0)
{
lean_object* v_ctorName_5386_; lean_object* v_params_5387_; lean_object* v_code_5388_; uint8_t v___x_5389_; lean_object* v_fst_5391_; lean_object* v_snd_5392_; lean_object* v___y_5406_; lean_object* v___y_5419_; lean_object* v___y_5420_; lean_object* v___y_5433_; uint8_t v___x_5437_; 
v_ctorName_5386_ = lean_ctor_get(v_a_5373_, 0);
v_params_5387_ = lean_ctor_get(v_a_5373_, 1);
v_code_5388_ = lean_ctor_get(v_a_5373_, 2);
v___x_5389_ = 0;
v___x_5437_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5360_, v_ctorName_5386_);
if (v___x_5437_ == 0)
{
lean_object* v_options_5438_; uint8_t v_hasTrace_5439_; 
v_options_5438_ = lean_ctor_get(v___y_5367_, 2);
v_hasTrace_5439_ = lean_ctor_get_uint8(v_options_5438_, sizeof(void*)*1);
if (v_hasTrace_5439_ == 0)
{
v___y_5433_ = v___y_5366_;
goto v___jp_5432_;
}
else
{
lean_object* v_inheritedTraceOptions_5440_; lean_object* v_cls_5441_; lean_object* v___x_5442_; uint8_t v___x_5443_; 
v_inheritedTraceOptions_5440_ = lean_ctor_get(v___y_5367_, 13);
v_cls_5441_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5442_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5443_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5440_, v_options_5438_, v___x_5442_);
if (v___x_5443_ == 0)
{
v___y_5433_ = v___y_5366_;
goto v___jp_5432_;
}
else
{
lean_object* v___x_5444_; 
lean_inc(v_discr_5361_);
v___x_5444_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5361_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref_known(v___x_5444_, 1);
v___x_5446_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5447_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5445_, v___x_5443_);
v___x_5448_ = lean_string_append(v___x_5446_, v___x_5447_);
lean_dec_ref(v___x_5447_);
v___x_5449_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5450_ = lean_string_append(v___x_5448_, v___x_5449_);
lean_inc(v_ctorName_5386_);
v___x_5451_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5386_, v___x_5443_);
v___x_5452_ = lean_string_append(v___x_5450_, v___x_5451_);
lean_dec_ref(v___x_5451_);
v___x_5453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5453_, 0, v___x_5452_);
v___x_5454_ = l_Lean_MessageData_ofFormat(v___x_5453_);
v___x_5455_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5441_, v___x_5454_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_dec_ref_known(v___x_5455_, 1);
v___y_5433_ = v___y_5366_;
goto v___jp_5432_;
}
else
{
lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5463_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5456_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5458_ = v___x_5455_;
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v___x_5455_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5459_ == 0)
{
v___x_5461_ = v___x_5458_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
}
else
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5464_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___x_5444_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5444_);
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
}
else
{
lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5472_ = lean_unsigned_to_nat(0u);
v___x_5473_ = lean_array_get_size(v_params_5387_);
v___x_5474_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5362_, v_params_5387_, v___x_5472_, v___x_5473_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v_a_5475_; lean_object* v___x_5476_; uint8_t v___x_5477_; uint8_t v___x_5478_; 
v_a_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_a_5475_);
lean_dec_ref_known(v___x_5474_, 1);
v___x_5476_ = lean_array_get_size(v_a_5475_);
v___x_5477_ = lean_nat_dec_eq(v___x_5476_, v___x_5472_);
v___x_5478_ = lean_bool_not(v___x_5477_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; 
lean_dec(v_a_5475_);
lean_inc_ref(v_code_5388_);
v___x_5479_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5362_, v_code_5388_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5479_) == 0)
{
lean_object* v_a_5480_; lean_object* v___x_5481_; 
v_a_5480_ = lean_ctor_get(v___x_5479_, 0);
lean_inc(v_a_5480_);
lean_dec_ref_known(v___x_5479_, 1);
lean_inc_ref(v_a_5373_);
v___x_5481_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5373_, v_a_5480_);
v_a_5375_ = v___x_5481_;
goto v___jp_5374_;
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
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
else
{
lean_object* v___x_5490_; 
lean_inc_ref(v_code_5388_);
v___x_5490_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5362_, v_code_5388_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5492_; uint8_t v___x_5493_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v___x_5490_, 1);
v___x_5492_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5493_ = lean_nat_dec_lt(v___x_5472_, v___x_5476_);
if (v___x_5493_ == 0)
{
lean_dec(v_a_5475_);
v_fst_5391_ = v_a_5491_;
v_snd_5392_ = v___x_5492_;
goto v___jp_5390_;
}
else
{
lean_object* v___x_5494_; uint8_t v___x_5495_; 
lean_inc(v_a_5491_);
v___x_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5494_, 0, v_a_5491_);
lean_ctor_set(v___x_5494_, 1, v___x_5492_);
v___x_5495_ = lean_nat_dec_le(v___x_5476_, v___x_5476_);
if (v___x_5495_ == 0)
{
if (v___x_5493_ == 0)
{
lean_dec_ref_known(v___x_5494_, 2);
lean_dec(v_a_5475_);
v_fst_5391_ = v_a_5491_;
v_snd_5392_ = v___x_5492_;
goto v___jp_5390_;
}
else
{
size_t v___x_5496_; size_t v___x_5497_; lean_object* v___x_5498_; 
lean_dec(v_a_5491_);
v___x_5496_ = ((size_t)0ULL);
v___x_5497_ = lean_usize_of_nat(v___x_5476_);
v___x_5498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5475_, v___x_5496_, v___x_5497_, v___x_5494_);
lean_dec(v_a_5475_);
v___y_5406_ = v___x_5498_;
goto v___jp_5405_;
}
}
else
{
size_t v___x_5499_; size_t v___x_5500_; lean_object* v___x_5501_; 
lean_dec(v_a_5491_);
v___x_5499_ = ((size_t)0ULL);
v___x_5500_ = lean_usize_of_nat(v___x_5476_);
v___x_5501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5475_, v___x_5499_, v___x_5500_, v___x_5494_);
lean_dec(v_a_5475_);
v___y_5406_ = v___x_5501_;
goto v___jp_5405_;
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_a_5475_);
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5502_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5490_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5490_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5510_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5474_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5474_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
v___jp_5390_:
{
uint8_t v___x_5393_; lean_object* v___x_5394_; 
v___x_5393_ = 0;
v___x_5394_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5389_, v_fst_5391_, v_snd_5392_, v___x_5393_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
lean_dec_ref(v_snd_5392_);
if (lean_obj_tag(v___x_5394_) == 0)
{
lean_object* v_a_5395_; lean_object* v___x_5396_; 
v_a_5395_ = lean_ctor_get(v___x_5394_, 0);
lean_inc(v_a_5395_);
lean_dec_ref_known(v___x_5394_, 1);
lean_inc_ref(v_a_5373_);
v___x_5396_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5373_, v_a_5395_);
v_a_5375_ = v___x_5396_;
goto v___jp_5374_;
}
else
{
lean_object* v_a_5397_; lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5404_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5397_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5399_ = v___x_5394_;
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
else
{
lean_inc(v_a_5397_);
lean_dec(v___x_5394_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v___x_5402_; 
if (v_isShared_5400_ == 0)
{
v___x_5402_ = v___x_5399_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5397_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
return v___x_5402_;
}
}
}
}
v___jp_5405_:
{
if (lean_obj_tag(v___y_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v_fst_5408_; lean_object* v_snd_5409_; 
v_a_5407_ = lean_ctor_get(v___y_5406_, 0);
lean_inc(v_a_5407_);
lean_dec_ref_known(v___y_5406_, 1);
v_fst_5408_ = lean_ctor_get(v_a_5407_, 0);
lean_inc(v_fst_5408_);
v_snd_5409_ = lean_ctor_get(v_a_5407_, 1);
lean_inc(v_snd_5409_);
lean_dec(v_a_5407_);
v_fst_5391_ = v_fst_5408_;
v_snd_5392_ = v_snd_5409_;
goto v___jp_5390_;
}
else
{
lean_object* v_a_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5417_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5410_ = lean_ctor_get(v___y_5406_, 0);
v_isSharedCheck_5417_ = !lean_is_exclusive(v___y_5406_);
if (v_isSharedCheck_5417_ == 0)
{
v___x_5412_ = v___y_5406_;
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_a_5410_);
lean_dec(v___y_5406_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5415_; 
if (v_isShared_5413_ == 0)
{
v___x_5415_ = v___x_5412_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
return v___x_5415_;
}
}
}
}
v___jp_5418_:
{
lean_object* v___x_5421_; 
v___x_5421_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5389_, v___y_5420_, v___y_5419_);
lean_dec_ref(v___y_5420_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v___x_5422_; lean_object* v___x_5423_; 
lean_dec_ref_known(v___x_5421_, 1);
lean_inc_ref(v_resultType_5359_);
v___x_5422_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5422_, 0, v_resultType_5359_);
lean_inc_ref(v_a_5373_);
v___x_5423_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5373_, v___x_5422_);
v_a_5375_ = v___x_5423_;
goto v___jp_5374_;
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5424_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5421_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5421_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
v___jp_5432_:
{
switch(lean_obj_tag(v_a_5373_))
{
case 0:
{
lean_object* v_code_5434_; 
v_code_5434_ = lean_ctor_get(v_a_5373_, 2);
lean_inc_ref(v_code_5434_);
v___y_5419_ = v___y_5433_;
v___y_5420_ = v_code_5434_;
goto v___jp_5418_;
}
case 1:
{
lean_object* v_code_5435_; 
v_code_5435_ = lean_ctor_get(v_a_5373_, 1);
lean_inc_ref(v_code_5435_);
v___y_5419_ = v___y_5433_;
v___y_5420_ = v_code_5435_;
goto v___jp_5418_;
}
default: 
{
lean_object* v_code_5436_; 
v_code_5436_ = lean_ctor_get(v_a_5373_, 0);
lean_inc_ref(v_code_5436_);
v___y_5419_ = v___y_5433_;
v___y_5420_ = v_code_5436_;
goto v___jp_5418_;
}
}
}
}
else
{
lean_object* v_code_5518_; lean_object* v___x_5519_; 
v_code_5518_ = lean_ctor_get(v_a_5373_, 0);
lean_inc_ref(v_code_5518_);
v___x_5519_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5362_, v_code_5518_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5519_) == 0)
{
lean_object* v_a_5520_; lean_object* v___x_5521_; 
v_a_5520_ = lean_ctor_get(v___x_5519_, 0);
lean_inc(v_a_5520_);
lean_dec_ref_known(v___x_5519_, 1);
lean_inc_ref(v_a_5373_);
v___x_5521_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5373_, v_a_5520_);
v_a_5375_ = v___x_5521_;
goto v___jp_5374_;
}
else
{
lean_object* v_a_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5529_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5522_ = lean_ctor_get(v___x_5519_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5524_ = v___x_5519_;
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5519_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5527_; 
if (v_isShared_5525_ == 0)
{
v___x_5527_ = v___x_5524_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_a_5522_);
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
v___jp_5374_:
{
size_t v___x_5376_; size_t v___x_5377_; uint8_t v___x_5378_; 
v___x_5376_ = lean_ptr_addr(v_a_5373_);
v___x_5377_ = lean_ptr_addr(v_a_5375_);
v___x_5378_ = lean_usize_dec_eq(v___x_5376_, v___x_5377_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5379_ = lean_unsigned_to_nat(1u);
v___x_5380_ = lean_nat_add(v_i_5363_, v___x_5379_);
v___x_5381_ = lean_array_fset(v_as_5364_, v_i_5363_, v_a_5375_);
lean_dec(v_i_5363_);
v_i_5363_ = v___x_5380_;
v_as_5364_ = v___x_5381_;
goto _start;
}
else
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
lean_dec_ref(v_a_5375_);
v___x_5383_ = lean_unsigned_to_nat(1u);
v___x_5384_ = lean_nat_add(v_i_5363_, v___x_5383_);
lean_dec(v_i_5363_);
v_i_5363_ = v___x_5384_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5530_, lean_object* v_code_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v___y_5538_; lean_object* v___y_5539_; uint8_t v___y_5540_; lean_object* v___y_5545_; lean_object* v___y_5546_; uint8_t v___y_5547_; lean_object* v_decl_5552_; lean_object* v_k_5553_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v___y_5556_; lean_object* v___y_5557_; 
switch(lean_obj_tag(v_code_5531_))
{
case 0:
{
lean_object* v_decl_5603_; lean_object* v_k_5604_; lean_object* v___x_5605_; 
v_decl_5603_ = lean_ctor_get(v_code_5531_, 0);
v_k_5604_ = lean_ctor_get(v_code_5531_, 1);
lean_inc_ref(v_k_5604_);
v___x_5605_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5530_, v_k_5604_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5605_) == 0)
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5632_; 
v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5605_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5608_ = v___x_5605_;
v_isShared_5609_ = v_isSharedCheck_5632_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5605_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5632_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
uint8_t v___y_5611_; size_t v___x_5627_; size_t v___x_5628_; uint8_t v___x_5629_; 
v___x_5627_ = lean_ptr_addr(v_k_5604_);
v___x_5628_ = lean_ptr_addr(v_a_5606_);
v___x_5629_ = lean_usize_dec_eq(v___x_5627_, v___x_5628_);
if (v___x_5629_ == 0)
{
v___y_5611_ = v___x_5629_;
goto v___jp_5610_;
}
else
{
size_t v___x_5630_; uint8_t v___x_5631_; 
v___x_5630_ = lean_ptr_addr(v_decl_5603_);
v___x_5631_ = lean_usize_dec_eq(v___x_5630_, v___x_5630_);
v___y_5611_ = v___x_5631_;
goto v___jp_5610_;
}
v___jp_5610_:
{
if (v___y_5611_ == 0)
{
lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5621_; 
lean_inc_ref(v_decl_5603_);
v_isSharedCheck_5621_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5621_ == 0)
{
lean_object* v_unused_5622_; lean_object* v_unused_5623_; 
v_unused_5622_ = lean_ctor_get(v_code_5531_, 1);
lean_dec(v_unused_5622_);
v_unused_5623_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5623_);
v___x_5613_ = v_code_5531_;
v_isShared_5614_ = v_isSharedCheck_5621_;
goto v_resetjp_5612_;
}
else
{
lean_dec(v_code_5531_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5621_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5616_; 
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 1, v_a_5606_);
v___x_5616_ = v___x_5613_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_decl_5603_);
lean_ctor_set(v_reuseFailAlloc_5620_, 1, v_a_5606_);
v___x_5616_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
lean_object* v___x_5618_; 
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 0, v___x_5616_);
v___x_5618_ = v___x_5608_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5616_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
}
else
{
lean_object* v___x_5625_; 
lean_dec(v_a_5606_);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 0, v_code_5531_);
v___x_5625_ = v___x_5608_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_code_5531_);
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
}
else
{
lean_dec_ref_known(v_code_5531_, 2);
return v___x_5605_;
}
}
case 1:
{
lean_object* v_decl_5633_; lean_object* v_k_5634_; 
v_decl_5633_ = lean_ctor_get(v_code_5531_, 0);
v_k_5634_ = lean_ctor_get(v_code_5531_, 1);
lean_inc_ref(v_k_5634_);
lean_inc_ref(v_decl_5633_);
v_decl_5552_ = v_decl_5633_;
v_k_5553_ = v_k_5634_;
v___y_5554_ = v_a_5532_;
v___y_5555_ = v_a_5533_;
v___y_5556_ = v_a_5534_;
v___y_5557_ = v_a_5535_;
goto v___jp_5551_;
}
case 2:
{
lean_object* v_decl_5635_; lean_object* v_k_5636_; 
v_decl_5635_ = lean_ctor_get(v_code_5531_, 0);
v_k_5636_ = lean_ctor_get(v_code_5531_, 1);
lean_inc_ref(v_k_5636_);
lean_inc_ref(v_decl_5635_);
v_decl_5552_ = v_decl_5635_;
v_k_5553_ = v_k_5636_;
v___y_5554_ = v_a_5532_;
v___y_5555_ = v_a_5533_;
v___y_5556_ = v_a_5534_;
v___y_5557_ = v_a_5535_;
goto v___jp_5551_;
}
case 4:
{
lean_object* v_cases_5637_; lean_object* v_typeName_5638_; lean_object* v_resultType_5639_; lean_object* v_discr_5640_; lean_object* v_alts_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5682_; 
v_cases_5637_ = lean_ctor_get(v_code_5531_, 0);
lean_inc_ref(v_cases_5637_);
v_typeName_5638_ = lean_ctor_get(v_cases_5637_, 0);
v_resultType_5639_ = lean_ctor_get(v_cases_5637_, 1);
v_discr_5640_ = lean_ctor_get(v_cases_5637_, 2);
v_alts_5641_ = lean_ctor_get(v_cases_5637_, 3);
v_isSharedCheck_5682_ = !lean_is_exclusive(v_cases_5637_);
if (v_isSharedCheck_5682_ == 0)
{
v___x_5643_ = v_cases_5637_;
v_isShared_5644_ = v_isSharedCheck_5682_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_alts_5641_);
lean_inc(v_discr_5640_);
lean_inc(v_resultType_5639_);
lean_inc(v_typeName_5638_);
lean_dec(v_cases_5637_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5682_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5645_; lean_object* v_discrVal_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5645_ = lean_box(0);
v_discrVal_5646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5530_, v_discr_5640_, v___x_5645_);
v___x_5647_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5641_);
lean_inc(v_discr_5640_);
lean_inc_ref(v_resultType_5639_);
v___x_5648_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5639_, v_discrVal_5646_, v_discr_5640_, v_assignment_5530_, v___x_5647_, v_alts_5641_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
lean_dec(v_discrVal_5646_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5673_; 
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5651_ = v___x_5648_;
v_isShared_5652_ = v_isSharedCheck_5673_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5648_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5673_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
size_t v___x_5653_; size_t v___x_5654_; uint8_t v___x_5655_; 
v___x_5653_ = lean_ptr_addr(v_alts_5641_);
lean_dec_ref(v_alts_5641_);
v___x_5654_ = lean_ptr_addr(v_a_5649_);
v___x_5655_ = lean_usize_dec_eq(v___x_5653_, v___x_5654_);
if (v___x_5655_ == 0)
{
lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5668_; 
v_isSharedCheck_5668_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5668_ == 0)
{
lean_object* v_unused_5669_; 
v_unused_5669_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5669_);
v___x_5657_ = v_code_5531_;
v_isShared_5658_ = v_isSharedCheck_5668_;
goto v_resetjp_5656_;
}
else
{
lean_dec(v_code_5531_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5668_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v___x_5660_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 3, v_a_5649_);
v___x_5660_ = v___x_5643_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_typeName_5638_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v_resultType_5639_);
lean_ctor_set(v_reuseFailAlloc_5667_, 2, v_discr_5640_);
lean_ctor_set(v_reuseFailAlloc_5667_, 3, v_a_5649_);
v___x_5660_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
lean_object* v___x_5662_; 
if (v_isShared_5658_ == 0)
{
lean_ctor_set(v___x_5657_, 0, v___x_5660_);
v___x_5662_ = v___x_5657_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v___x_5660_);
v___x_5662_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5664_; 
if (v_isShared_5652_ == 0)
{
lean_ctor_set(v___x_5651_, 0, v___x_5662_);
v___x_5664_ = v___x_5651_;
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
}
else
{
lean_object* v___x_5671_; 
lean_dec(v_a_5649_);
lean_del_object(v___x_5643_);
lean_dec(v_discr_5640_);
lean_dec_ref(v_resultType_5639_);
lean_dec(v_typeName_5638_);
if (v_isShared_5652_ == 0)
{
lean_ctor_set(v___x_5651_, 0, v_code_5531_);
v___x_5671_ = v___x_5651_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_code_5531_);
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
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_del_object(v___x_5643_);
lean_dec_ref(v_alts_5641_);
lean_dec(v_discr_5640_);
lean_dec_ref(v_resultType_5639_);
lean_dec(v_typeName_5638_);
lean_dec_ref_known(v_code_5531_, 1);
v_a_5674_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5648_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5648_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
}
default: 
{
lean_object* v___x_5683_; 
v___x_5683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5683_, 0, v_code_5531_);
return v___x_5683_;
}
}
v___jp_5537_:
{
if (v___y_5540_ == 0)
{
lean_object* v___x_5541_; lean_object* v___x_5542_; 
lean_dec_ref(v_code_5531_);
v___x_5541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5541_, 0, v___y_5539_);
lean_ctor_set(v___x_5541_, 1, v___y_5538_);
v___x_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5541_);
return v___x_5542_;
}
else
{
lean_object* v___x_5543_; 
lean_dec_ref(v___y_5539_);
lean_dec_ref(v___y_5538_);
v___x_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5543_, 0, v_code_5531_);
return v___x_5543_;
}
}
v___jp_5544_:
{
if (v___y_5547_ == 0)
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
lean_dec_ref(v_code_5531_);
v___x_5548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5548_, 0, v___y_5546_);
lean_ctor_set(v___x_5548_, 1, v___y_5545_);
v___x_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
return v___x_5549_;
}
else
{
lean_object* v___x_5550_; 
lean_dec_ref(v___y_5546_);
lean_dec_ref(v___y_5545_);
v___x_5550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5550_, 0, v_code_5531_);
return v___x_5550_;
}
}
v___jp_5551_:
{
lean_object* v_params_5558_; lean_object* v_type_5559_; lean_object* v_value_5560_; lean_object* v___x_5561_; 
v_params_5558_ = lean_ctor_get(v_decl_5552_, 2);
lean_inc_ref(v_params_5558_);
v_type_5559_ = lean_ctor_get(v_decl_5552_, 3);
lean_inc_ref(v_type_5559_);
v_value_5560_ = lean_ctor_get(v_decl_5552_, 4);
lean_inc_ref(v_value_5560_);
v___x_5561_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5530_, v_value_5560_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
if (lean_obj_tag(v___x_5561_) == 0)
{
lean_object* v_a_5562_; uint8_t v___x_5563_; lean_object* v___x_5564_; 
v_a_5562_ = lean_ctor_get(v___x_5561_, 0);
lean_inc(v_a_5562_);
lean_dec_ref_known(v___x_5561_, 1);
v___x_5563_ = 0;
v___x_5564_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5563_, v_decl_5552_, v_type_5559_, v_params_5558_, v_a_5562_, v___y_5555_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_a_5565_; lean_object* v___x_5566_; 
v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_a_5565_);
lean_dec_ref_known(v___x_5564_, 1);
v___x_5566_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5530_, v_k_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
if (lean_obj_tag(v___x_5566_) == 0)
{
switch(lean_obj_tag(v_code_5531_))
{
case 1:
{
lean_object* v_a_5567_; lean_object* v_decl_5568_; lean_object* v_k_5569_; size_t v___x_5570_; size_t v___x_5571_; uint8_t v___x_5572_; 
v_a_5567_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_a_5567_);
lean_dec_ref_known(v___x_5566_, 1);
v_decl_5568_ = lean_ctor_get(v_code_5531_, 0);
v_k_5569_ = lean_ctor_get(v_code_5531_, 1);
v___x_5570_ = lean_ptr_addr(v_k_5569_);
v___x_5571_ = lean_ptr_addr(v_a_5567_);
v___x_5572_ = lean_usize_dec_eq(v___x_5570_, v___x_5571_);
if (v___x_5572_ == 0)
{
v___y_5538_ = v_a_5567_;
v___y_5539_ = v_a_5565_;
v___y_5540_ = v___x_5572_;
goto v___jp_5537_;
}
else
{
size_t v___x_5573_; size_t v___x_5574_; uint8_t v___x_5575_; 
v___x_5573_ = lean_ptr_addr(v_decl_5568_);
v___x_5574_ = lean_ptr_addr(v_a_5565_);
v___x_5575_ = lean_usize_dec_eq(v___x_5573_, v___x_5574_);
v___y_5538_ = v_a_5567_;
v___y_5539_ = v_a_5565_;
v___y_5540_ = v___x_5575_;
goto v___jp_5537_;
}
}
case 2:
{
lean_object* v_a_5576_; lean_object* v_decl_5577_; lean_object* v_k_5578_; size_t v___x_5579_; size_t v___x_5580_; uint8_t v___x_5581_; 
v_a_5576_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_a_5576_);
lean_dec_ref_known(v___x_5566_, 1);
v_decl_5577_ = lean_ctor_get(v_code_5531_, 0);
v_k_5578_ = lean_ctor_get(v_code_5531_, 1);
v___x_5579_ = lean_ptr_addr(v_k_5578_);
v___x_5580_ = lean_ptr_addr(v_a_5576_);
v___x_5581_ = lean_usize_dec_eq(v___x_5579_, v___x_5580_);
if (v___x_5581_ == 0)
{
v___y_5545_ = v_a_5576_;
v___y_5546_ = v_a_5565_;
v___y_5547_ = v___x_5581_;
goto v___jp_5544_;
}
else
{
size_t v___x_5582_; size_t v___x_5583_; uint8_t v___x_5584_; 
v___x_5582_ = lean_ptr_addr(v_decl_5577_);
v___x_5583_ = lean_ptr_addr(v_a_5565_);
v___x_5584_ = lean_usize_dec_eq(v___x_5582_, v___x_5583_);
v___y_5545_ = v_a_5576_;
v___y_5546_ = v_a_5565_;
v___y_5547_ = v___x_5584_;
goto v___jp_5544_;
}
}
default: 
{
lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5593_; 
lean_dec(v_a_5565_);
lean_dec_ref(v_code_5531_);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5566_);
if (v_isSharedCheck_5593_ == 0)
{
lean_object* v_unused_5594_; 
v_unused_5594_ = lean_ctor_get(v___x_5566_, 0);
lean_dec(v_unused_5594_);
v___x_5586_ = v___x_5566_;
v_isShared_5587_ = v_isSharedCheck_5593_;
goto v_resetjp_5585_;
}
else
{
lean_dec(v___x_5566_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5593_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5591_; 
v___x_5588_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5589_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5588_);
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 0, v___x_5589_);
v___x_5591_ = v___x_5586_;
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
}
else
{
lean_dec(v_a_5565_);
lean_dec_ref(v_code_5531_);
return v___x_5566_;
}
}
else
{
lean_object* v_a_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5602_; 
lean_dec_ref(v_k_5553_);
lean_dec_ref(v_code_5531_);
v_a_5595_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5597_ = v___x_5564_;
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_a_5595_);
lean_dec(v___x_5564_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v___x_5600_; 
if (v_isShared_5598_ == 0)
{
v___x_5600_ = v___x_5597_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
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
lean_dec_ref(v_type_5559_);
lean_dec_ref(v_params_5558_);
lean_dec_ref(v_k_5553_);
lean_dec_ref(v_decl_5552_);
lean_dec_ref(v_code_5531_);
return v___x_5561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5684_, lean_object* v_code_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_){
_start:
{
lean_object* v_res_5691_; 
v_res_5691_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5684_, v_code_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_);
lean_dec(v_a_5689_);
lean_dec_ref(v_a_5688_);
lean_dec(v_a_5687_);
lean_dec_ref(v_a_5686_);
lean_dec_ref(v_assignment_5684_);
return v_res_5691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5692_, lean_object* v_discrVal_5693_, lean_object* v_discr_5694_, lean_object* v_assignment_5695_, lean_object* v_i_5696_, lean_object* v_as_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_){
_start:
{
lean_object* v_res_5703_; 
v_res_5703_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5692_, v_discrVal_5693_, v_discr_5694_, v_assignment_5695_, v_i_5696_, v_as_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
lean_dec_ref(v_assignment_5695_);
lean_dec(v_discrVal_5693_);
return v_res_5703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5704_, lean_object* v_m_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v___x_5707_; 
v___x_5707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5705_, v_a_5706_);
return v___x_5707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5708_, lean_object* v_m_5709_, lean_object* v_a_5710_){
_start:
{
lean_object* v_res_5711_; 
v_res_5711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5708_, v_m_5709_, v_a_5710_);
lean_dec(v_a_5710_);
lean_dec_ref(v_m_5709_);
return v_res_5711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5712_, size_t v_i_5713_, size_t v_stop_5714_, lean_object* v_b_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_){
_start:
{
lean_object* v___x_5721_; 
v___x_5721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5712_, v_i_5713_, v_stop_5714_, v_b_5715_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5722_, lean_object* v_i_5723_, lean_object* v_stop_5724_, lean_object* v_b_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_){
_start:
{
size_t v_i_boxed_5731_; size_t v_stop_boxed_5732_; lean_object* v_res_5733_; 
v_i_boxed_5731_ = lean_unbox_usize(v_i_5723_);
lean_dec(v_i_5723_);
v_stop_boxed_5732_ = lean_unbox_usize(v_stop_5724_);
lean_dec(v_stop_5724_);
v_res_5733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5722_, v_i_boxed_5731_, v_stop_boxed_5732_, v_b_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
lean_dec_ref(v_as_5722_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5734_, lean_object* v_a_5735_, lean_object* v_x_5736_){
_start:
{
lean_object* v___x_5737_; 
v___x_5737_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5735_, v_x_5736_);
return v___x_5737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5738_, lean_object* v_a_5739_, lean_object* v_x_5740_){
_start:
{
lean_object* v_res_5741_; 
v_res_5741_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5738_, v_a_5739_, v_x_5740_);
lean_dec(v_x_5740_);
lean_dec(v_a_5739_);
return v_res_5741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5742_, lean_object* v_v_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_){
_start:
{
if (lean_obj_tag(v_v_5743_) == 0)
{
lean_object* v_code_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5773_; 
v_code_5749_ = lean_ctor_get(v_v_5743_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v_v_5743_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5751_ = v_v_5743_;
v_isShared_5752_ = v_isSharedCheck_5773_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_code_5749_);
lean_dec(v_v_5743_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5773_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v___x_5753_; 
lean_inc(v___y_5747_);
lean_inc_ref(v___y_5746_);
lean_inc(v___y_5745_);
lean_inc_ref(v___y_5744_);
v___x_5753_ = lean_apply_6(v_f_5742_, v_code_5749_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, lean_box(0));
if (lean_obj_tag(v___x_5753_) == 0)
{
lean_object* v_a_5754_; lean_object* v___x_5756_; uint8_t v_isShared_5757_; uint8_t v_isSharedCheck_5764_; 
v_a_5754_ = lean_ctor_get(v___x_5753_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5753_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5756_ = v___x_5753_;
v_isShared_5757_ = v_isSharedCheck_5764_;
goto v_resetjp_5755_;
}
else
{
lean_inc(v_a_5754_);
lean_dec(v___x_5753_);
v___x_5756_ = lean_box(0);
v_isShared_5757_ = v_isSharedCheck_5764_;
goto v_resetjp_5755_;
}
v_resetjp_5755_:
{
lean_object* v___x_5759_; 
if (v_isShared_5752_ == 0)
{
lean_ctor_set(v___x_5751_, 0, v_a_5754_);
v___x_5759_ = v___x_5751_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5754_);
v___x_5759_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
lean_object* v___x_5761_; 
if (v_isShared_5757_ == 0)
{
lean_ctor_set(v___x_5756_, 0, v___x_5759_);
v___x_5761_ = v___x_5756_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v___x_5759_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
}
else
{
lean_object* v_a_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5772_; 
lean_del_object(v___x_5751_);
v_a_5765_ = lean_ctor_get(v___x_5753_, 0);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5753_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5767_ = v___x_5753_;
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_a_5765_);
lean_dec(v___x_5753_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5770_; 
if (v_isShared_5768_ == 0)
{
v___x_5770_ = v___x_5767_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_a_5765_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
}
}
else
{
lean_object* v___x_5774_; 
lean_dec_ref(v_f_5742_);
v___x_5774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5774_, 0, v_v_5743_);
return v___x_5774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5775_, lean_object* v_v_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_){
_start:
{
lean_object* v_res_5782_; 
v_res_5782_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5775_, v_v_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v___y_5778_);
lean_dec_ref(v___y_5777_);
return v_res_5782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5783_, lean_object* v_f_5784_, lean_object* v_v_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_){
_start:
{
lean_object* v___x_5791_; 
v___x_5791_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5784_, v_v_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
return v___x_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5792_, lean_object* v_f_5793_, lean_object* v_v_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_){
_start:
{
uint8_t v_pu_boxed_5800_; lean_object* v_res_5801_; 
v_pu_boxed_5800_ = lean_unbox(v_pu_5792_);
v_res_5801_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5800_, v_f_5793_, v_v_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
return v_res_5801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5802_, lean_object* v_x_5803_){
_start:
{
if (lean_obj_tag(v_x_5803_) == 0)
{
return v_x_5802_;
}
else
{
lean_object* v_key_5804_; lean_object* v_value_5805_; lean_object* v_tail_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; 
v_key_5804_ = lean_ctor_get(v_x_5803_, 0);
v_value_5805_ = lean_ctor_get(v_x_5803_, 1);
v_tail_5806_ = lean_ctor_get(v_x_5803_, 2);
lean_inc(v_value_5805_);
lean_inc(v_key_5804_);
v___x_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5807_, 0, v_key_5804_);
lean_ctor_set(v___x_5807_, 1, v_value_5805_);
v___x_5808_ = lean_array_push(v_x_5802_, v___x_5807_);
v_x_5802_ = v___x_5808_;
v_x_5803_ = v_tail_5806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5810_, lean_object* v_x_5811_){
_start:
{
lean_object* v_res_5812_; 
v_res_5812_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5810_, v_x_5811_);
lean_dec(v_x_5811_);
return v_res_5812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5813_, size_t v_i_5814_, size_t v_stop_5815_, lean_object* v_b_5816_){
_start:
{
uint8_t v___x_5817_; 
v___x_5817_ = lean_usize_dec_eq(v_i_5814_, v_stop_5815_);
if (v___x_5817_ == 0)
{
lean_object* v___x_5818_; lean_object* v___x_5819_; size_t v___x_5820_; size_t v___x_5821_; 
v___x_5818_ = lean_array_uget_borrowed(v_as_5813_, v_i_5814_);
v___x_5819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5816_, v___x_5818_);
v___x_5820_ = ((size_t)1ULL);
v___x_5821_ = lean_usize_add(v_i_5814_, v___x_5820_);
v_i_5814_ = v___x_5821_;
v_b_5816_ = v___x_5819_;
goto _start;
}
else
{
return v_b_5816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5823_, lean_object* v_i_5824_, lean_object* v_stop_5825_, lean_object* v_b_5826_){
_start:
{
size_t v_i_boxed_5827_; size_t v_stop_boxed_5828_; lean_object* v_res_5829_; 
v_i_boxed_5827_ = lean_unbox_usize(v_i_5824_);
lean_dec(v_i_5824_);
v_stop_boxed_5828_ = lean_unbox_usize(v_stop_5825_);
lean_dec(v_stop_5825_);
v_res_5829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5823_, v_i_boxed_5827_, v_stop_boxed_5828_, v_b_5826_);
lean_dec_ref(v_as_5823_);
return v_res_5829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5830_, size_t v_sz_5831_, size_t v_i_5832_, lean_object* v_bs_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
uint8_t v___x_5839_; 
v___x_5839_ = lean_usize_dec_lt(v_i_5832_, v_sz_5831_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; 
v___x_5840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5840_, 0, v_bs_5833_);
return v___x_5840_;
}
else
{
lean_object* v_v_5841_; lean_object* v_fst_5842_; lean_object* v_snd_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5867_; 
v_v_5841_ = lean_array_uget(v_bs_5833_, v_i_5832_);
v_fst_5842_ = lean_ctor_get(v_v_5841_, 0);
v_snd_5843_ = lean_ctor_get(v_v_5841_, 1);
v_isSharedCheck_5867_ = !lean_is_exclusive(v_v_5841_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5845_ = v_v_5841_;
v_isShared_5846_ = v_isSharedCheck_5867_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_snd_5843_);
lean_inc(v_fst_5842_);
lean_dec(v_v_5841_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5867_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5847_; 
v___x_5847_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5842_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; lean_object* v___x_5849_; lean_object* v_bs_x27_5850_; lean_object* v___x_5851_; lean_object* v___x_5853_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5847_, 1);
v___x_5849_ = lean_unsigned_to_nat(0u);
v_bs_x27_5850_ = lean_array_uset(v_bs_5833_, v_i_5832_, v___x_5849_);
v___x_5851_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5848_, v_a_5830_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 0, v___x_5851_);
v___x_5853_ = v___x_5845_;
goto v_reusejp_5852_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v___x_5851_);
lean_ctor_set(v_reuseFailAlloc_5858_, 1, v_snd_5843_);
v___x_5853_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5852_;
}
v_reusejp_5852_:
{
size_t v___x_5854_; size_t v___x_5855_; lean_object* v___x_5856_; 
v___x_5854_ = ((size_t)1ULL);
v___x_5855_ = lean_usize_add(v_i_5832_, v___x_5854_);
v___x_5856_ = lean_array_uset(v_bs_x27_5850_, v_i_5832_, v___x_5853_);
v_i_5832_ = v___x_5855_;
v_bs_5833_ = v___x_5856_;
goto _start;
}
}
else
{
lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5866_; 
lean_del_object(v___x_5845_);
lean_dec(v_snd_5843_);
lean_dec_ref(v_bs_5833_);
v_a_5859_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5861_ = v___x_5847_;
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5847_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5864_; 
if (v_isShared_5862_ == 0)
{
v___x_5864_ = v___x_5861_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_a_5859_);
v___x_5864_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
return v___x_5864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5868_, lean_object* v_sz_5869_, lean_object* v_i_5870_, lean_object* v_bs_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_){
_start:
{
uint8_t v_a_2702__boxed_5877_; size_t v_sz_boxed_5878_; size_t v_i_boxed_5879_; lean_object* v_res_5880_; 
v_a_2702__boxed_5877_ = lean_unbox(v_a_5868_);
v_sz_boxed_5878_ = lean_unbox_usize(v_sz_5869_);
lean_dec(v_sz_5869_);
v_i_boxed_5879_ = lean_unbox_usize(v_i_5870_);
lean_dec(v_i_5870_);
v_res_5880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2702__boxed_5877_, v_sz_boxed_5878_, v_i_boxed_5879_, v_bs_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
return v_res_5880_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5881_){
_start:
{
lean_object* v_fst_5882_; lean_object* v_snd_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5906_; 
v_fst_5882_ = lean_ctor_get(v_x_5881_, 0);
v_snd_5883_ = lean_ctor_get(v_x_5881_, 1);
v_isSharedCheck_5906_ = !lean_is_exclusive(v_x_5881_);
if (v_isSharedCheck_5906_ == 0)
{
v___x_5885_ = v_x_5881_;
v_isShared_5886_ = v_isSharedCheck_5906_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_snd_5883_);
lean_inc(v_fst_5882_);
lean_dec(v_x_5881_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5906_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5891_; 
v___x_5887_ = l_String_quote(v_fst_5882_);
v___x_5888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5887_);
v___x_5889_ = lean_box(0);
if (v_isShared_5886_ == 0)
{
lean_ctor_set_tag(v___x_5885_, 1);
lean_ctor_set(v___x_5885_, 1, v___x_5889_);
lean_ctor_set(v___x_5885_, 0, v___x_5888_);
v___x_5891_ = v___x_5885_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5905_; 
v_reuseFailAlloc_5905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5905_, 0, v___x_5888_);
lean_ctor_set(v_reuseFailAlloc_5905_, 1, v___x_5889_);
v___x_5891_ = v_reuseFailAlloc_5905_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; uint8_t v___x_5903_; lean_object* v___x_5904_; 
v___x_5892_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5883_);
v___x_5893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5892_);
lean_ctor_set(v___x_5893_, 1, v___x_5891_);
v___x_5894_ = l_List_reverse___redArg(v___x_5893_);
v___x_5895_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5896_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5894_, v___x_5895_);
v___x_5897_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5898_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5898_);
lean_ctor_set(v___x_5899_, 1, v___x_5896_);
v___x_5900_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5899_);
lean_ctor_set(v___x_5901_, 1, v___x_5900_);
v___x_5902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5897_);
lean_ctor_set(v___x_5902_, 1, v___x_5901_);
v___x_5903_ = 0;
v___x_5904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5904_, 0, v___x_5902_);
lean_ctor_set_uint8(v___x_5904_, sizeof(void*)*1, v___x_5903_);
return v___x_5904_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5907_, lean_object* v_x_5908_, lean_object* v_x_5909_){
_start:
{
if (lean_obj_tag(v_x_5909_) == 0)
{
lean_dec(v_x_5907_);
return v_x_5908_;
}
else
{
lean_object* v_head_5910_; lean_object* v_tail_5911_; lean_object* v___x_5913_; uint8_t v_isShared_5914_; uint8_t v_isSharedCheck_5921_; 
v_head_5910_ = lean_ctor_get(v_x_5909_, 0);
v_tail_5911_ = lean_ctor_get(v_x_5909_, 1);
v_isSharedCheck_5921_ = !lean_is_exclusive(v_x_5909_);
if (v_isSharedCheck_5921_ == 0)
{
v___x_5913_ = v_x_5909_;
v_isShared_5914_ = v_isSharedCheck_5921_;
goto v_resetjp_5912_;
}
else
{
lean_inc(v_tail_5911_);
lean_inc(v_head_5910_);
lean_dec(v_x_5909_);
v___x_5913_ = lean_box(0);
v_isShared_5914_ = v_isSharedCheck_5921_;
goto v_resetjp_5912_;
}
v_resetjp_5912_:
{
lean_object* v___x_5916_; 
lean_inc(v_x_5907_);
if (v_isShared_5914_ == 0)
{
lean_ctor_set_tag(v___x_5913_, 5);
lean_ctor_set(v___x_5913_, 1, v_x_5907_);
lean_ctor_set(v___x_5913_, 0, v_x_5908_);
v___x_5916_ = v___x_5913_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_x_5908_);
lean_ctor_set(v_reuseFailAlloc_5920_, 1, v_x_5907_);
v___x_5916_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
lean_object* v___x_5917_; lean_object* v___x_5918_; 
v___x_5917_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5910_);
v___x_5918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5916_);
lean_ctor_set(v___x_5918_, 1, v___x_5917_);
v_x_5908_ = v___x_5918_;
v_x_5909_ = v_tail_5911_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5922_, lean_object* v_x_5923_, lean_object* v_x_5924_){
_start:
{
if (lean_obj_tag(v_x_5924_) == 0)
{
lean_dec(v_x_5922_);
return v_x_5923_;
}
else
{
lean_object* v_head_5925_; lean_object* v_tail_5926_; lean_object* v___x_5928_; uint8_t v_isShared_5929_; uint8_t v_isSharedCheck_5936_; 
v_head_5925_ = lean_ctor_get(v_x_5924_, 0);
v_tail_5926_ = lean_ctor_get(v_x_5924_, 1);
v_isSharedCheck_5936_ = !lean_is_exclusive(v_x_5924_);
if (v_isSharedCheck_5936_ == 0)
{
v___x_5928_ = v_x_5924_;
v_isShared_5929_ = v_isSharedCheck_5936_;
goto v_resetjp_5927_;
}
else
{
lean_inc(v_tail_5926_);
lean_inc(v_head_5925_);
lean_dec(v_x_5924_);
v___x_5928_ = lean_box(0);
v_isShared_5929_ = v_isSharedCheck_5936_;
goto v_resetjp_5927_;
}
v_resetjp_5927_:
{
lean_object* v___x_5931_; 
lean_inc(v_x_5922_);
if (v_isShared_5929_ == 0)
{
lean_ctor_set_tag(v___x_5928_, 5);
lean_ctor_set(v___x_5928_, 1, v_x_5922_);
lean_ctor_set(v___x_5928_, 0, v_x_5923_);
v___x_5931_ = v___x_5928_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_x_5923_);
lean_ctor_set(v_reuseFailAlloc_5935_, 1, v_x_5922_);
v___x_5931_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5932_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5925_);
v___x_5933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5931_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5922_, v___x_5933_, v_tail_5926_);
return v___x_5934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5937_, lean_object* v_x_5938_){
_start:
{
if (lean_obj_tag(v_x_5937_) == 0)
{
lean_object* v___x_5939_; 
lean_dec(v_x_5938_);
v___x_5939_ = lean_box(0);
return v___x_5939_;
}
else
{
lean_object* v_tail_5940_; 
v_tail_5940_ = lean_ctor_get(v_x_5937_, 1);
if (lean_obj_tag(v_tail_5940_) == 0)
{
lean_object* v_head_5941_; lean_object* v___x_5942_; 
lean_dec(v_x_5938_);
v_head_5941_ = lean_ctor_get(v_x_5937_, 0);
lean_inc(v_head_5941_);
lean_dec_ref_known(v_x_5937_, 2);
v___x_5942_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5941_);
return v___x_5942_;
}
else
{
lean_object* v_head_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; 
lean_inc(v_tail_5940_);
v_head_5943_ = lean_ctor_get(v_x_5937_, 0);
lean_inc(v_head_5943_);
lean_dec_ref_known(v_x_5937_, 2);
v___x_5944_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5943_);
v___x_5945_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5938_, v___x_5944_, v_tail_5940_);
return v___x_5945_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; 
v___x_5947_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5948_ = lean_string_length(v___x_5947_);
return v___x_5948_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; 
v___x_5949_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5950_ = lean_nat_to_int(v___x_5949_);
return v___x_5950_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5956_){
_start:
{
lean_object* v___x_5957_; lean_object* v___x_5958_; uint8_t v___x_5959_; 
v___x_5957_ = lean_array_get_size(v_xs_5956_);
v___x_5958_ = lean_unsigned_to_nat(0u);
v___x_5959_ = lean_nat_dec_eq(v___x_5957_, v___x_5958_);
if (v___x_5959_ == 0)
{
lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; 
v___x_5960_ = lean_array_to_list(v_xs_5956_);
v___x_5961_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5962_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5960_, v___x_5961_);
v___x_5963_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5964_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
lean_ctor_set(v___x_5965_, 1, v___x_5962_);
v___x_5966_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5965_);
lean_ctor_set(v___x_5967_, 1, v___x_5966_);
v___x_5968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5963_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = l_Std_Format_fill(v___x_5968_);
return v___x_5969_;
}
else
{
lean_object* v___x_5970_; 
lean_dec_ref(v_xs_5956_);
v___x_5970_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_5970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_5973_, lean_object* v_decl_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_){
_start:
{
lean_object* v___y_5981_; lean_object* v___y_5982_; lean_object* v___y_5983_; lean_object* v___y_5984_; lean_object* v_options_6014_; uint8_t v_hasTrace_6015_; 
v_options_6014_ = lean_ctor_get(v_a_5977_, 2);
v_hasTrace_6015_ = lean_ctor_get_uint8(v_options_6014_, sizeof(void*)*1);
if (v_hasTrace_6015_ == 0)
{
v___y_5981_ = v_a_5975_;
v___y_5982_ = v_a_5976_;
v___y_5983_ = v_a_5977_;
v___y_5984_ = v_a_5978_;
goto v___jp_5980_;
}
else
{
lean_object* v_inheritedTraceOptions_6016_; lean_object* v_cls_6017_; uint8_t v___y_6019_; lean_object* v___y_6020_; lean_object* v___x_6056_; uint8_t v___x_6057_; 
v_inheritedTraceOptions_6016_ = lean_ctor_get(v_a_5977_, 13);
v_cls_6017_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6056_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6016_, v_options_6014_, v___x_6056_);
if (v___x_6057_ == 0)
{
v___y_5981_ = v_a_5975_;
v___y_5982_ = v_a_5976_;
v___y_5983_ = v_a_5977_;
v___y_5984_ = v_a_5978_;
goto v___jp_5980_;
}
else
{
lean_object* v_size_6058_; lean_object* v_buckets_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; uint8_t v___x_6063_; 
v_size_6058_ = lean_ctor_get(v_assignment_5973_, 0);
v_buckets_6059_ = lean_ctor_get(v_assignment_5973_, 1);
v___x_6060_ = lean_mk_empty_array_with_capacity(v_size_6058_);
v___x_6061_ = lean_unsigned_to_nat(0u);
v___x_6062_ = lean_array_get_size(v_buckets_6059_);
v___x_6063_ = lean_nat_dec_lt(v___x_6061_, v___x_6062_);
if (v___x_6063_ == 0)
{
v___y_6019_ = v___x_6057_;
v___y_6020_ = v___x_6060_;
goto v___jp_6018_;
}
else
{
uint8_t v___x_6064_; 
v___x_6064_ = lean_nat_dec_le(v___x_6062_, v___x_6062_);
if (v___x_6064_ == 0)
{
if (v___x_6063_ == 0)
{
v___y_6019_ = v___x_6057_;
v___y_6020_ = v___x_6060_;
goto v___jp_6018_;
}
else
{
size_t v___x_6065_; size_t v___x_6066_; lean_object* v___x_6067_; 
v___x_6065_ = ((size_t)0ULL);
v___x_6066_ = lean_usize_of_nat(v___x_6062_);
v___x_6067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6059_, v___x_6065_, v___x_6066_, v___x_6060_);
v___y_6019_ = v___x_6057_;
v___y_6020_ = v___x_6067_;
goto v___jp_6018_;
}
}
else
{
size_t v___x_6068_; size_t v___x_6069_; lean_object* v___x_6070_; 
v___x_6068_ = ((size_t)0ULL);
v___x_6069_ = lean_usize_of_nat(v___x_6062_);
v___x_6070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6059_, v___x_6068_, v___x_6069_, v___x_6060_);
v___y_6019_ = v___x_6057_;
v___y_6020_ = v___x_6070_;
goto v___jp_6018_;
}
}
}
v___jp_6018_:
{
size_t v_sz_6021_; size_t v___x_6022_; lean_object* v___x_6023_; 
v_sz_6021_ = lean_array_size(v___y_6020_);
v___x_6022_ = ((size_t)0ULL);
v___x_6023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6019_, v_sz_6021_, v___x_6022_, v___y_6020_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_);
if (lean_obj_tag(v___x_6023_) == 0)
{
lean_object* v_toSignature_6024_; lean_object* v_a_6025_; lean_object* v_name_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v_toSignature_6024_ = lean_ctor_get(v_decl_5974_, 0);
v_a_6025_ = lean_ctor_get(v___x_6023_, 0);
lean_inc(v_a_6025_);
lean_dec_ref_known(v___x_6023_, 1);
v_name_6026_ = lean_ctor_get(v_toSignature_6024_, 0);
v___x_6027_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6026_);
v___x_6028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6026_, v___y_6019_);
v___x_6029_ = lean_string_append(v___x_6027_, v___x_6028_);
lean_dec_ref(v___x_6028_);
v___x_6030_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6031_ = lean_string_append(v___x_6029_, v___x_6030_);
v___x_6032_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6025_);
v___x_6033_ = l_Std_Format_defWidth;
v___x_6034_ = lean_unsigned_to_nat(0u);
v___x_6035_ = l_Std_Format_pretty(v___x_6032_, v___x_6033_, v___x_6034_, v___x_6034_);
v___x_6036_ = lean_string_append(v___x_6031_, v___x_6035_);
lean_dec_ref(v___x_6035_);
v___x_6037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6036_);
v___x_6038_ = l_Lean_MessageData_ofFormat(v___x_6037_);
v___x_6039_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_6017_, v___x_6038_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_);
if (lean_obj_tag(v___x_6039_) == 0)
{
lean_dec_ref_known(v___x_6039_, 1);
v___y_5981_ = v_a_5975_;
v___y_5982_ = v_a_5976_;
v___y_5983_ = v_a_5977_;
v___y_5984_ = v_a_5978_;
goto v___jp_5980_;
}
else
{
lean_object* v_a_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6047_; 
lean_dec_ref(v_decl_5974_);
lean_dec_ref(v_assignment_5973_);
v_a_6040_ = lean_ctor_get(v___x_6039_, 0);
v_isSharedCheck_6047_ = !lean_is_exclusive(v___x_6039_);
if (v_isSharedCheck_6047_ == 0)
{
v___x_6042_ = v___x_6039_;
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_a_6040_);
lean_dec(v___x_6039_);
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
else
{
lean_object* v_a_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6055_; 
lean_dec_ref(v_decl_5974_);
lean_dec_ref(v_assignment_5973_);
v_a_6048_ = lean_ctor_get(v___x_6023_, 0);
v_isSharedCheck_6055_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6055_ == 0)
{
v___x_6050_ = v___x_6023_;
v_isShared_6051_ = v_isSharedCheck_6055_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_a_6048_);
lean_dec(v___x_6023_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6055_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
lean_object* v___x_6053_; 
if (v_isShared_6051_ == 0)
{
v___x_6053_ = v___x_6050_;
goto v_reusejp_6052_;
}
else
{
lean_object* v_reuseFailAlloc_6054_; 
v_reuseFailAlloc_6054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6054_, 0, v_a_6048_);
v___x_6053_ = v_reuseFailAlloc_6054_;
goto v_reusejp_6052_;
}
v_reusejp_6052_:
{
return v___x_6053_;
}
}
}
}
}
v___jp_5980_:
{
lean_object* v_toSignature_5985_; lean_object* v_value_5986_; uint8_t v_recursive_5987_; lean_object* v_inlineAttr_x3f_5988_; lean_object* v___x_5990_; uint8_t v_isShared_5991_; uint8_t v_isSharedCheck_6013_; 
v_toSignature_5985_ = lean_ctor_get(v_decl_5974_, 0);
v_value_5986_ = lean_ctor_get(v_decl_5974_, 1);
v_recursive_5987_ = lean_ctor_get_uint8(v_decl_5974_, sizeof(void*)*3);
v_inlineAttr_x3f_5988_ = lean_ctor_get(v_decl_5974_, 2);
v_isSharedCheck_6013_ = !lean_is_exclusive(v_decl_5974_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_5990_ = v_decl_5974_;
v_isShared_5991_ = v_isSharedCheck_6013_;
goto v_resetjp_5989_;
}
else
{
lean_inc(v_inlineAttr_x3f_5988_);
lean_inc(v_value_5986_);
lean_inc(v_toSignature_5985_);
lean_dec(v_decl_5974_);
v___x_5990_ = lean_box(0);
v_isShared_5991_ = v_isSharedCheck_6013_;
goto v_resetjp_5989_;
}
v_resetjp_5989_:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; 
v___x_5992_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_5992_, 0, v_assignment_5973_);
v___x_5993_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_5992_, v_value_5986_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
if (lean_obj_tag(v___x_5993_) == 0)
{
lean_object* v_a_5994_; lean_object* v___x_5996_; uint8_t v_isShared_5997_; uint8_t v_isSharedCheck_6004_; 
v_a_5994_ = lean_ctor_get(v___x_5993_, 0);
v_isSharedCheck_6004_ = !lean_is_exclusive(v___x_5993_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5996_ = v___x_5993_;
v_isShared_5997_ = v_isSharedCheck_6004_;
goto v_resetjp_5995_;
}
else
{
lean_inc(v_a_5994_);
lean_dec(v___x_5993_);
v___x_5996_ = lean_box(0);
v_isShared_5997_ = v_isSharedCheck_6004_;
goto v_resetjp_5995_;
}
v_resetjp_5995_:
{
lean_object* v___x_5999_; 
if (v_isShared_5991_ == 0)
{
lean_ctor_set(v___x_5990_, 1, v_a_5994_);
v___x_5999_ = v___x_5990_;
goto v_reusejp_5998_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_toSignature_5985_);
lean_ctor_set(v_reuseFailAlloc_6003_, 1, v_a_5994_);
lean_ctor_set(v_reuseFailAlloc_6003_, 2, v_inlineAttr_x3f_5988_);
lean_ctor_set_uint8(v_reuseFailAlloc_6003_, sizeof(void*)*3, v_recursive_5987_);
v___x_5999_ = v_reuseFailAlloc_6003_;
goto v_reusejp_5998_;
}
v_reusejp_5998_:
{
lean_object* v___x_6001_; 
if (v_isShared_5997_ == 0)
{
lean_ctor_set(v___x_5996_, 0, v___x_5999_);
v___x_6001_ = v___x_5996_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v___x_5999_);
v___x_6001_ = v_reuseFailAlloc_6002_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
return v___x_6001_;
}
}
}
}
else
{
lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6012_; 
lean_del_object(v___x_5990_);
lean_dec(v_inlineAttr_x3f_5988_);
lean_dec_ref(v_toSignature_5985_);
v_a_6005_ = lean_ctor_get(v___x_5993_, 0);
v_isSharedCheck_6012_ = !lean_is_exclusive(v___x_5993_);
if (v_isSharedCheck_6012_ == 0)
{
v___x_6007_ = v___x_5993_;
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___x_5993_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6010_; 
if (v_isShared_6008_ == 0)
{
v___x_6010_ = v___x_6007_;
goto v_reusejp_6009_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_a_6005_);
v___x_6010_ = v_reuseFailAlloc_6011_;
goto v_reusejp_6009_;
}
v_reusejp_6009_:
{
return v___x_6010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6071_, lean_object* v_decl_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_, lean_object* v_a_6077_){
_start:
{
lean_object* v_res_6078_; 
v_res_6078_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6071_, v_decl_6072_, v_a_6073_, v_a_6074_, v_a_6075_, v_a_6076_);
lean_dec(v_a_6076_);
lean_dec_ref(v_a_6075_);
lean_dec(v_a_6074_);
lean_dec_ref(v_a_6073_);
return v_res_6078_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6079_, lean_object* v_x_6080_){
_start:
{
lean_object* v___x_6081_; 
v___x_6081_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6079_);
return v___x_6081_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6082_, lean_object* v_x_6083_){
_start:
{
lean_object* v_res_6084_; 
v_res_6084_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6082_, v_x_6083_);
lean_dec(v_x_6083_);
return v_res_6084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6085_, size_t v_i_6086_, lean_object* v_bs_6087_){
_start:
{
uint8_t v___x_6088_; 
v___x_6088_ = lean_usize_dec_lt(v_i_6086_, v_sz_6085_);
if (v___x_6088_ == 0)
{
return v_bs_6087_;
}
else
{
lean_object* v_v_6089_; lean_object* v_toSignature_6090_; lean_object* v_name_6091_; lean_object* v___x_6092_; lean_object* v_bs_x27_6093_; size_t v___x_6094_; size_t v___x_6095_; lean_object* v___x_6096_; 
v_v_6089_ = lean_array_uget_borrowed(v_bs_6087_, v_i_6086_);
v_toSignature_6090_ = lean_ctor_get(v_v_6089_, 0);
v_name_6091_ = lean_ctor_get(v_toSignature_6090_, 0);
lean_inc(v_name_6091_);
v___x_6092_ = lean_unsigned_to_nat(0u);
v_bs_x27_6093_ = lean_array_uset(v_bs_6087_, v_i_6086_, v___x_6092_);
v___x_6094_ = ((size_t)1ULL);
v___x_6095_ = lean_usize_add(v_i_6086_, v___x_6094_);
v___x_6096_ = lean_array_uset(v_bs_x27_6093_, v_i_6086_, v_name_6091_);
v_i_6086_ = v___x_6095_;
v_bs_6087_ = v___x_6096_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6098_, lean_object* v_i_6099_, lean_object* v_bs_6100_){
_start:
{
size_t v_sz_boxed_6101_; size_t v_i_boxed_6102_; lean_object* v_res_6103_; 
v_sz_boxed_6101_ = lean_unbox_usize(v_sz_6098_);
lean_dec(v_sz_6098_);
v_i_boxed_6102_ = lean_unbox_usize(v_i_6099_);
lean_dec(v_i_6099_);
v_res_6103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6101_, v_i_boxed_6102_, v_bs_6100_);
return v_res_6103_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6104_, lean_object* v_a_6105_){
_start:
{
if (lean_obj_tag(v_a_6104_) == 0)
{
lean_object* v___x_6106_; 
v___x_6106_ = l_List_reverse___redArg(v_a_6105_);
return v___x_6106_;
}
else
{
lean_object* v_head_6107_; lean_object* v_tail_6108_; lean_object* v___x_6110_; uint8_t v_isShared_6111_; uint8_t v_isSharedCheck_6117_; 
v_head_6107_ = lean_ctor_get(v_a_6104_, 0);
v_tail_6108_ = lean_ctor_get(v_a_6104_, 1);
v_isSharedCheck_6117_ = !lean_is_exclusive(v_a_6104_);
if (v_isSharedCheck_6117_ == 0)
{
v___x_6110_ = v_a_6104_;
v_isShared_6111_ = v_isSharedCheck_6117_;
goto v_resetjp_6109_;
}
else
{
lean_inc(v_tail_6108_);
lean_inc(v_head_6107_);
lean_dec(v_a_6104_);
v___x_6110_ = lean_box(0);
v_isShared_6111_ = v_isSharedCheck_6117_;
goto v_resetjp_6109_;
}
v_resetjp_6109_:
{
lean_object* v___x_6112_; lean_object* v___x_6114_; 
v___x_6112_ = l_Lean_MessageData_ofName(v_head_6107_);
if (v_isShared_6111_ == 0)
{
lean_ctor_set(v___x_6110_, 1, v_a_6105_);
lean_ctor_set(v___x_6110_, 0, v___x_6112_);
v___x_6114_ = v___x_6110_;
goto v_reusejp_6113_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v___x_6112_);
lean_ctor_set(v_reuseFailAlloc_6116_, 1, v_a_6105_);
v___x_6114_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6113_;
}
v_reusejp_6113_:
{
v_a_6104_ = v_tail_6108_;
v_a_6105_ = v___x_6114_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6119_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6120_ = l_Lean_stringToMessageData(v___x_6119_);
return v___x_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6121_, lean_object* v_x_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v___x_6130_; size_t v_sz_6131_; size_t v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; 
v___x_6130_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6131_ = lean_array_size(v___y_6121_);
v___x_6132_ = ((size_t)0ULL);
v___x_6133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6131_, v___x_6132_, v___y_6121_);
v___x_6134_ = lean_array_to_list(v___x_6133_);
v___x_6135_ = lean_box(0);
v___x_6136_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6134_, v___x_6135_);
v___x_6137_ = l_Lean_MessageData_ofList(v___x_6136_);
v___x_6138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6130_);
lean_ctor_set(v___x_6138_, 1, v___x_6137_);
v___x_6139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
return v___x_6139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6140_, lean_object* v_x_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_){
_start:
{
lean_object* v_res_6149_; 
v_res_6149_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6140_, v_x_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
lean_dec(v___y_6143_);
lean_dec_ref(v___y_6142_);
lean_dec_ref(v_x_6141_);
return v_res_6149_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6150_; lean_object* v___x_6151_; 
v___x_6150_ = 0;
v___x_6151_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6150_);
return v___x_6151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6152_, lean_object* v_n_6153_, lean_object* v_j_6154_, lean_object* v_a_6155_){
_start:
{
lean_object* v_zero_6156_; uint8_t v_isZero_6157_; 
v_zero_6156_ = lean_unsigned_to_nat(0u);
v_isZero_6157_ = lean_nat_dec_eq(v_j_6154_, v_zero_6156_);
if (v_isZero_6157_ == 1)
{
lean_dec(v_j_6154_);
return v_a_6155_;
}
else
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v_toSignature_6161_; uint8_t v_safe_6162_; lean_object* v_one_6163_; lean_object* v_n_6164_; 
v___x_6158_ = lean_nat_sub(v_n_6153_, v_j_6154_);
v___x_6159_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6160_ = lean_array_get_borrowed(v___x_6159_, v___y_6152_, v___x_6158_);
lean_dec(v___x_6158_);
v_toSignature_6161_ = lean_ctor_get(v___x_6160_, 0);
v_safe_6162_ = lean_ctor_get_uint8(v_toSignature_6161_, sizeof(void*)*4);
v_one_6163_ = lean_unsigned_to_nat(1u);
v_n_6164_ = lean_nat_sub(v_j_6154_, v_one_6163_);
lean_dec(v_j_6154_);
if (v_safe_6162_ == 0)
{
lean_object* v___x_6165_; lean_object* v___x_6166_; 
v___x_6165_ = lean_box(1);
v___x_6166_ = lean_array_push(v_a_6155_, v___x_6165_);
v_j_6154_ = v_n_6164_;
v_a_6155_ = v___x_6166_;
goto _start;
}
else
{
lean_object* v___x_6168_; lean_object* v___x_6169_; 
v___x_6168_ = lean_box(0);
v___x_6169_ = lean_array_push(v_a_6155_, v___x_6168_);
v_j_6154_ = v_n_6164_;
v_a_6155_ = v___x_6169_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6171_, lean_object* v_n_6172_, lean_object* v_j_6173_, lean_object* v_a_6174_){
_start:
{
lean_object* v_res_6175_; 
v_res_6175_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6171_, v_n_6172_, v_j_6173_, v_a_6174_);
lean_dec(v_n_6172_);
lean_dec_ref(v___y_6171_);
return v_res_6175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6176_, size_t v_sz_6177_, size_t v_i_6178_, lean_object* v_bs_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_){
_start:
{
uint8_t v___x_6185_; 
v___x_6185_ = lean_usize_dec_lt(v_i_6178_, v_sz_6177_);
if (v___x_6185_ == 0)
{
lean_object* v___x_6186_; 
v___x_6186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6186_, 0, v_bs_6179_);
return v___x_6186_;
}
else
{
lean_object* v_v_6187_; lean_object* v_toSignature_6188_; uint8_t v_safe_6189_; lean_object* v___x_6190_; lean_object* v_bs_x27_6191_; lean_object* v_a_6193_; 
v_v_6187_ = lean_array_uget(v_bs_6179_, v_i_6178_);
v_toSignature_6188_ = lean_ctor_get(v_v_6187_, 0);
v_safe_6189_ = lean_ctor_get_uint8(v_toSignature_6188_, sizeof(void*)*4);
v___x_6190_ = lean_unsigned_to_nat(0u);
v_bs_x27_6191_ = lean_array_uset(v_bs_6179_, v_i_6178_, v___x_6190_);
if (v_safe_6189_ == 0)
{
v_a_6193_ = v_v_6187_;
goto v___jp_6192_;
}
else
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; 
v___x_6198_ = lean_usize_to_nat(v_i_6178_);
v___x_6199_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6200_ = lean_array_get_borrowed(v___x_6199_, v___x_6176_, v___x_6198_);
lean_dec(v___x_6198_);
lean_inc(v___x_6200_);
v___x_6201_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6200_, v_v_6187_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_);
if (lean_obj_tag(v___x_6201_) == 0)
{
lean_object* v_a_6202_; 
v_a_6202_ = lean_ctor_get(v___x_6201_, 0);
lean_inc(v_a_6202_);
lean_dec_ref_known(v___x_6201_, 1);
v_a_6193_ = v_a_6202_;
goto v___jp_6192_;
}
else
{
lean_object* v_a_6203_; lean_object* v___x_6205_; uint8_t v_isShared_6206_; uint8_t v_isSharedCheck_6210_; 
lean_dec_ref(v_bs_x27_6191_);
v_a_6203_ = lean_ctor_get(v___x_6201_, 0);
v_isSharedCheck_6210_ = !lean_is_exclusive(v___x_6201_);
if (v_isSharedCheck_6210_ == 0)
{
v___x_6205_ = v___x_6201_;
v_isShared_6206_ = v_isSharedCheck_6210_;
goto v_resetjp_6204_;
}
else
{
lean_inc(v_a_6203_);
lean_dec(v___x_6201_);
v___x_6205_ = lean_box(0);
v_isShared_6206_ = v_isSharedCheck_6210_;
goto v_resetjp_6204_;
}
v_resetjp_6204_:
{
lean_object* v___x_6208_; 
if (v_isShared_6206_ == 0)
{
v___x_6208_ = v___x_6205_;
goto v_reusejp_6207_;
}
else
{
lean_object* v_reuseFailAlloc_6209_; 
v_reuseFailAlloc_6209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
v___x_6208_ = v_reuseFailAlloc_6209_;
goto v_reusejp_6207_;
}
v_reusejp_6207_:
{
return v___x_6208_;
}
}
}
}
v___jp_6192_:
{
size_t v___x_6194_; size_t v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = ((size_t)1ULL);
v___x_6195_ = lean_usize_add(v_i_6178_, v___x_6194_);
v___x_6196_ = lean_array_uset(v_bs_x27_6191_, v_i_6178_, v_a_6193_);
v_i_6178_ = v___x_6195_;
v_bs_6179_ = v___x_6196_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6211_, lean_object* v_sz_6212_, lean_object* v_i_6213_, lean_object* v_bs_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_){
_start:
{
size_t v_sz_boxed_6220_; size_t v_i_boxed_6221_; lean_object* v_res_6222_; 
v_sz_boxed_6220_ = lean_unbox_usize(v_sz_6212_);
lean_dec(v_sz_6212_);
v_i_boxed_6221_ = lean_unbox_usize(v_i_6213_);
lean_dec(v_i_6213_);
v_res_6222_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6211_, v_sz_boxed_6220_, v_i_boxed_6221_, v_bs_6214_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_);
lean_dec(v___y_6218_);
lean_dec_ref(v___y_6217_);
lean_dec(v___y_6216_);
lean_dec_ref(v___y_6215_);
lean_dec_ref(v___x_6211_);
return v_res_6222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6225_, lean_object* v_pivot_6226_, lean_object* v_as_6227_, lean_object* v_i_6228_, lean_object* v_k_6229_){
_start:
{
uint8_t v___x_6230_; 
v___x_6230_ = lean_nat_dec_lt(v_k_6229_, v_hi_6225_);
if (v___x_6230_ == 0)
{
lean_object* v___x_6231_; lean_object* v___x_6232_; 
lean_dec(v_k_6229_);
lean_dec_ref(v_pivot_6226_);
v___x_6231_ = lean_array_fswap(v_as_6227_, v_i_6228_, v_hi_6225_);
v___x_6232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6232_, 0, v_i_6228_);
lean_ctor_set(v___x_6232_, 1, v___x_6231_);
return v___x_6232_;
}
else
{
lean_object* v___x_6233_; lean_object* v_toSignature_6234_; lean_object* v_toSignature_6235_; lean_object* v_name_6236_; lean_object* v_name_6237_; uint8_t v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; uint8_t v___x_6248_; 
v___x_6233_ = lean_array_fget_borrowed(v_as_6227_, v_k_6229_);
v_toSignature_6234_ = lean_ctor_get(v___x_6233_, 0);
v_toSignature_6235_ = lean_ctor_get(v_pivot_6226_, 0);
v_name_6236_ = lean_ctor_get(v_toSignature_6234_, 0);
v_name_6237_ = lean_ctor_get(v_toSignature_6235_, 0);
v___x_6238_ = 0;
v___x_6239_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6238_, v___x_6233_);
v___x_6240_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6241_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6242_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6236_);
v___x_6243_ = l_Lean_Name_toString(v_name_6236_, v___x_6230_);
v___x_6244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6244_, 0, v___x_6239_);
lean_ctor_set(v___x_6244_, 1, v___x_6243_);
v___x_6245_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6238_, v_pivot_6226_);
lean_inc(v_name_6237_);
v___x_6246_ = l_Lean_Name_toString(v_name_6237_, v___x_6230_);
v___x_6247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6247_, 0, v___x_6245_);
lean_ctor_set(v___x_6247_, 1, v___x_6246_);
v___x_6248_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6240_, v___x_6241_, v___x_6242_, v___x_6244_, v___x_6247_);
if (v___x_6248_ == 0)
{
lean_object* v___x_6249_; lean_object* v___x_6250_; 
v___x_6249_ = lean_unsigned_to_nat(1u);
v___x_6250_ = lean_nat_add(v_k_6229_, v___x_6249_);
lean_dec(v_k_6229_);
v_k_6229_ = v___x_6250_;
goto _start;
}
else
{
lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6252_ = lean_array_fswap(v_as_6227_, v_i_6228_, v_k_6229_);
v___x_6253_ = lean_unsigned_to_nat(1u);
v___x_6254_ = lean_nat_add(v_i_6228_, v___x_6253_);
lean_dec(v_i_6228_);
v___x_6255_ = lean_nat_add(v_k_6229_, v___x_6253_);
lean_dec(v_k_6229_);
v_as_6227_ = v___x_6252_;
v_i_6228_ = v___x_6254_;
v_k_6229_ = v___x_6255_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6257_, lean_object* v_pivot_6258_, lean_object* v_as_6259_, lean_object* v_i_6260_, lean_object* v_k_6261_){
_start:
{
lean_object* v_res_6262_; 
v_res_6262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6257_, v_pivot_6258_, v_as_6259_, v_i_6260_, v_k_6261_);
lean_dec(v_hi_6257_);
return v_res_6262_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6263_, lean_object* v_l_6264_, lean_object* v_r_6265_){
_start:
{
lean_object* v_toSignature_6266_; lean_object* v_toSignature_6267_; lean_object* v_name_6268_; lean_object* v_name_6269_; uint8_t v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; uint8_t v___x_6280_; 
v_toSignature_6266_ = lean_ctor_get(v_l_6264_, 0);
v_toSignature_6267_ = lean_ctor_get(v_r_6265_, 0);
v_name_6268_ = lean_ctor_get(v_toSignature_6266_, 0);
lean_inc(v_name_6268_);
v_name_6269_ = lean_ctor_get(v_toSignature_6267_, 0);
lean_inc(v_name_6269_);
v___x_6270_ = 0;
v___x_6271_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6270_, v_l_6264_);
lean_dec_ref(v_l_6264_);
v___x_6272_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6273_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6274_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6275_ = l_Lean_Name_toString(v_name_6268_, v___x_6263_);
v___x_6276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6276_, 0, v___x_6271_);
lean_ctor_set(v___x_6276_, 1, v___x_6275_);
v___x_6277_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6270_, v_r_6265_);
lean_dec_ref(v_r_6265_);
v___x_6278_ = l_Lean_Name_toString(v_name_6269_, v___x_6263_);
v___x_6279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6279_, 0, v___x_6277_);
lean_ctor_set(v___x_6279_, 1, v___x_6278_);
v___x_6280_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6272_, v___x_6273_, v___x_6274_, v___x_6276_, v___x_6279_);
return v___x_6280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6281_, lean_object* v_l_6282_, lean_object* v_r_6283_){
_start:
{
uint8_t v___x_13112__boxed_6284_; uint8_t v_res_6285_; lean_object* v_r_6286_; 
v___x_13112__boxed_6284_ = lean_unbox(v___x_6281_);
v_res_6285_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13112__boxed_6284_, v_l_6282_, v_r_6283_);
v_r_6286_ = lean_box(v_res_6285_);
return v_r_6286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6287_, lean_object* v_as_6288_, lean_object* v_lo_6289_, lean_object* v_hi_6290_){
_start:
{
lean_object* v___y_6292_; uint8_t v___x_6302_; 
v___x_6302_ = lean_nat_dec_lt(v_lo_6289_, v_hi_6290_);
if (v___x_6302_ == 0)
{
lean_dec(v_lo_6289_);
return v_as_6288_;
}
else
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v_mid_6305_; lean_object* v___y_6307_; lean_object* v___y_6313_; lean_object* v___x_6318_; lean_object* v___x_6319_; uint8_t v___x_6320_; 
v___x_6303_ = lean_nat_add(v_lo_6289_, v_hi_6290_);
v___x_6304_ = lean_unsigned_to_nat(1u);
v_mid_6305_ = lean_nat_shiftr(v___x_6303_, v___x_6304_);
lean_dec(v___x_6303_);
v___x_6318_ = lean_array_fget_borrowed(v_as_6288_, v_mid_6305_);
v___x_6319_ = lean_array_fget_borrowed(v_as_6288_, v_lo_6289_);
lean_inc(v___x_6319_);
lean_inc(v___x_6318_);
v___x_6320_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6302_, v___x_6318_, v___x_6319_);
if (v___x_6320_ == 0)
{
v___y_6313_ = v_as_6288_;
goto v___jp_6312_;
}
else
{
lean_object* v___x_6321_; 
v___x_6321_ = lean_array_fswap(v_as_6288_, v_lo_6289_, v_mid_6305_);
v___y_6313_ = v___x_6321_;
goto v___jp_6312_;
}
v___jp_6306_:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; uint8_t v___x_6310_; 
v___x_6308_ = lean_array_fget_borrowed(v___y_6307_, v_mid_6305_);
v___x_6309_ = lean_array_fget_borrowed(v___y_6307_, v_hi_6290_);
lean_inc(v___x_6309_);
lean_inc(v___x_6308_);
v___x_6310_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6302_, v___x_6308_, v___x_6309_);
if (v___x_6310_ == 0)
{
lean_dec(v_mid_6305_);
v___y_6292_ = v___y_6307_;
goto v___jp_6291_;
}
else
{
lean_object* v___x_6311_; 
v___x_6311_ = lean_array_fswap(v___y_6307_, v_mid_6305_, v_hi_6290_);
lean_dec(v_mid_6305_);
v___y_6292_ = v___x_6311_;
goto v___jp_6291_;
}
}
v___jp_6312_:
{
lean_object* v___x_6314_; lean_object* v___x_6315_; uint8_t v___x_6316_; 
v___x_6314_ = lean_array_fget_borrowed(v___y_6313_, v_hi_6290_);
v___x_6315_ = lean_array_fget_borrowed(v___y_6313_, v_lo_6289_);
lean_inc(v___x_6315_);
lean_inc(v___x_6314_);
v___x_6316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6302_, v___x_6314_, v___x_6315_);
if (v___x_6316_ == 0)
{
v___y_6307_ = v___y_6313_;
goto v___jp_6306_;
}
else
{
lean_object* v___x_6317_; 
v___x_6317_ = lean_array_fswap(v___y_6313_, v_lo_6289_, v_hi_6290_);
v___y_6307_ = v___x_6317_;
goto v___jp_6306_;
}
}
}
v___jp_6291_:
{
lean_object* v_pivot_6293_; lean_object* v___x_6294_; lean_object* v_fst_6295_; lean_object* v_snd_6296_; uint8_t v___x_6297_; 
v_pivot_6293_ = lean_array_fget(v___y_6292_, v_hi_6290_);
lean_inc_n(v_lo_6289_, 2);
v___x_6294_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6290_, v_pivot_6293_, v___y_6292_, v_lo_6289_, v_lo_6289_);
v_fst_6295_ = lean_ctor_get(v___x_6294_, 0);
lean_inc(v_fst_6295_);
v_snd_6296_ = lean_ctor_get(v___x_6294_, 1);
lean_inc(v_snd_6296_);
lean_dec_ref(v___x_6294_);
v___x_6297_ = lean_nat_dec_le(v_hi_6290_, v_fst_6295_);
if (v___x_6297_ == 0)
{
lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; 
v___x_6298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6287_, v_snd_6296_, v_lo_6289_, v_fst_6295_);
v___x_6299_ = lean_unsigned_to_nat(1u);
v___x_6300_ = lean_nat_add(v_fst_6295_, v___x_6299_);
lean_dec(v_fst_6295_);
v_as_6288_ = v___x_6298_;
v_lo_6289_ = v___x_6300_;
goto _start;
}
else
{
lean_dec(v_fst_6295_);
lean_dec(v_lo_6289_);
return v_snd_6296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6322_, lean_object* v_as_6323_, lean_object* v_lo_6324_, lean_object* v_hi_6325_){
_start:
{
lean_object* v_res_6326_; 
v_res_6326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6322_, v_as_6323_, v_lo_6324_, v_hi_6325_);
lean_dec(v_hi_6325_);
lean_dec(v_n_6322_);
return v_res_6326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6327_, lean_object* v___x_6328_, lean_object* v_n_6329_, lean_object* v_j_6330_, lean_object* v_a_6331_){
_start:
{
lean_object* v_zero_6332_; uint8_t v_isZero_6333_; 
v_zero_6332_ = lean_unsigned_to_nat(0u);
v_isZero_6333_ = lean_nat_dec_eq(v_j_6330_, v_zero_6332_);
if (v_isZero_6333_ == 1)
{
lean_dec(v_j_6330_);
return v_a_6331_;
}
else
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v_toSignature_6336_; lean_object* v_name_6337_; lean_object* v___x_6338_; lean_object* v_one_6339_; lean_object* v_n_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; 
v___x_6334_ = lean_nat_sub(v_n_6329_, v_j_6330_);
v___x_6335_ = lean_array_fget_borrowed(v___y_6327_, v___x_6334_);
v_toSignature_6336_ = lean_ctor_get(v___x_6335_, 0);
v_name_6337_ = lean_ctor_get(v_toSignature_6336_, 0);
v___x_6338_ = lean_box(0);
v_one_6339_ = lean_unsigned_to_nat(1u);
v_n_6340_ = lean_nat_sub(v_j_6330_, v_one_6339_);
lean_dec(v_j_6330_);
v___x_6341_ = lean_array_get_borrowed(v___x_6338_, v___x_6328_, v___x_6334_);
lean_dec(v___x_6334_);
lean_inc(v___x_6341_);
lean_inc(v_name_6337_);
v___x_6342_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6331_, v_name_6337_, v___x_6341_);
v_j_6330_ = v_n_6340_;
v_a_6331_ = v___x_6342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6344_, lean_object* v___x_6345_, lean_object* v_n_6346_, lean_object* v_j_6347_, lean_object* v_a_6348_){
_start:
{
lean_object* v_res_6349_; 
v_res_6349_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6344_, v___x_6345_, v_n_6346_, v_j_6347_, v_a_6348_);
lean_dec(v_n_6346_);
lean_dec_ref(v___x_6345_);
lean_dec_ref(v___y_6344_);
return v_res_6349_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6350_; 
v___x_6350_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6350_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; 
v___x_6351_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6352_, 0, v___x_6351_);
return v___x_6352_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; 
v___x_6353_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6354_, 0, v___x_6353_);
lean_ctor_set(v___x_6354_, 1, v___x_6353_);
return v___x_6354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6357_, lean_object* v_a_6358_, lean_object* v_a_6359_, lean_object* v_a_6360_, lean_object* v_a_6361_){
_start:
{
size_t v___y_6364_; size_t v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; lean_object* v___y_6403_; size_t v___y_6404_; size_t v___y_6405_; lean_object* v___y_6406_; lean_object* v___y_6407_; uint8_t v___y_6408_; lean_object* v___y_6409_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v___y_6412_; uint8_t v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; lean_object* v_a_6417_; lean_object* v___y_6427_; lean_object* v___y_6428_; size_t v___y_6429_; size_t v___y_6430_; lean_object* v___y_6431_; lean_object* v___y_6432_; uint8_t v___y_6433_; lean_object* v___y_6434_; lean_object* v___y_6435_; lean_object* v___y_6436_; lean_object* v___y_6437_; uint8_t v___y_6438_; lean_object* v___y_6439_; lean_object* v___y_6440_; lean_object* v_a_6441_; lean_object* v___x_6453_; lean_object* v___y_6455_; size_t v___y_6456_; size_t v___y_6457_; lean_object* v___y_6458_; lean_object* v___y_6459_; uint8_t v___y_6460_; lean_object* v___y_6461_; lean_object* v___y_6462_; lean_object* v___y_6463_; uint8_t v___y_6464_; lean_object* v___y_6465_; lean_object* v___y_6466_; lean_object* v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6510_; lean_object* v___y_6511_; lean_object* v___y_6512_; uint8_t v___y_6513_; size_t v___y_6514_; lean_object* v___y_6515_; size_t v___y_6516_; lean_object* v___y_6517_; lean_object* v___y_6518_; uint8_t v_a_6519_; lean_object* v___y_6524_; lean_object* v___x_6545_; lean_object* v___y_6547_; lean_object* v___y_6548_; uint8_t v___x_6550_; 
v___x_6453_ = lean_unsigned_to_nat(0u);
v___x_6545_ = lean_array_get_size(v_decls_6357_);
v___x_6550_ = lean_nat_dec_eq(v___x_6545_, v___x_6453_);
if (v___x_6550_ == 0)
{
lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___y_6554_; uint8_t v___x_6556_; 
v___x_6551_ = lean_unsigned_to_nat(1u);
v___x_6552_ = lean_nat_sub(v___x_6545_, v___x_6551_);
v___x_6556_ = lean_nat_dec_le(v___x_6453_, v___x_6552_);
if (v___x_6556_ == 0)
{
lean_inc(v___x_6552_);
v___y_6554_ = v___x_6552_;
goto v___jp_6553_;
}
else
{
v___y_6554_ = v___x_6453_;
goto v___jp_6553_;
}
v___jp_6553_:
{
uint8_t v___x_6555_; 
v___x_6555_ = lean_nat_dec_le(v___y_6554_, v___x_6552_);
if (v___x_6555_ == 0)
{
lean_dec(v___x_6552_);
lean_inc(v___y_6554_);
v___y_6547_ = v___y_6554_;
v___y_6548_ = v___y_6554_;
goto v___jp_6546_;
}
else
{
v___y_6547_ = v___y_6554_;
v___y_6548_ = v___x_6552_;
goto v___jp_6546_;
}
}
}
else
{
v___y_6524_ = v_decls_6357_;
goto v___jp_6523_;
}
v___jp_6363_:
{
if (lean_obj_tag(v___y_6369_) == 0)
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v_assignments_6372_; lean_object* v_funVals_6373_; lean_object* v_env_6374_; lean_object* v_nextMacroScope_6375_; lean_object* v_ngen_6376_; lean_object* v_auxDeclNGen_6377_; lean_object* v_traceState_6378_; lean_object* v_messages_6379_; lean_object* v_infoState_6380_; lean_object* v_snapshotTasks_6381_; lean_object* v___x_6383_; uint8_t v_isShared_6384_; uint8_t v_isSharedCheck_6392_; 
lean_dec_ref_known(v___y_6369_, 1);
v___x_6370_ = lean_st_ref_get(v___y_6368_);
lean_dec(v___y_6368_);
v___x_6371_ = lean_st_ref_take(v_a_6361_);
v_assignments_6372_ = lean_ctor_get(v___x_6370_, 0);
lean_inc_ref(v_assignments_6372_);
v_funVals_6373_ = lean_ctor_get(v___x_6370_, 1);
lean_inc_ref(v_funVals_6373_);
lean_dec(v___x_6370_);
v_env_6374_ = lean_ctor_get(v___x_6371_, 0);
v_nextMacroScope_6375_ = lean_ctor_get(v___x_6371_, 1);
v_ngen_6376_ = lean_ctor_get(v___x_6371_, 2);
v_auxDeclNGen_6377_ = lean_ctor_get(v___x_6371_, 3);
v_traceState_6378_ = lean_ctor_get(v___x_6371_, 4);
v_messages_6379_ = lean_ctor_get(v___x_6371_, 6);
v_infoState_6380_ = lean_ctor_get(v___x_6371_, 7);
v_snapshotTasks_6381_ = lean_ctor_get(v___x_6371_, 8);
v_isSharedCheck_6392_ = !lean_is_exclusive(v___x_6371_);
if (v_isSharedCheck_6392_ == 0)
{
lean_object* v_unused_6393_; 
v_unused_6393_ = lean_ctor_get(v___x_6371_, 5);
lean_dec(v_unused_6393_);
v___x_6383_ = v___x_6371_;
v_isShared_6384_ = v_isSharedCheck_6392_;
goto v_resetjp_6382_;
}
else
{
lean_inc(v_snapshotTasks_6381_);
lean_inc(v_infoState_6380_);
lean_inc(v_messages_6379_);
lean_inc(v_traceState_6378_);
lean_inc(v_auxDeclNGen_6377_);
lean_inc(v_ngen_6376_);
lean_inc(v_nextMacroScope_6375_);
lean_inc(v_env_6374_);
lean_dec(v___x_6371_);
v___x_6383_ = lean_box(0);
v_isShared_6384_ = v_isSharedCheck_6392_;
goto v_resetjp_6382_;
}
v_resetjp_6382_:
{
lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6388_; 
lean_inc(v___y_6366_);
v___x_6385_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6367_, v_funVals_6373_, v___y_6366_, v___y_6366_, v_env_6374_);
lean_dec(v___y_6366_);
lean_dec_ref(v_funVals_6373_);
v___x_6386_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6384_ == 0)
{
lean_ctor_set(v___x_6383_, 5, v___x_6386_);
lean_ctor_set(v___x_6383_, 0, v___x_6385_);
v___x_6388_ = v___x_6383_;
goto v_reusejp_6387_;
}
else
{
lean_object* v_reuseFailAlloc_6391_; 
v_reuseFailAlloc_6391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6391_, 0, v___x_6385_);
lean_ctor_set(v_reuseFailAlloc_6391_, 1, v_nextMacroScope_6375_);
lean_ctor_set(v_reuseFailAlloc_6391_, 2, v_ngen_6376_);
lean_ctor_set(v_reuseFailAlloc_6391_, 3, v_auxDeclNGen_6377_);
lean_ctor_set(v_reuseFailAlloc_6391_, 4, v_traceState_6378_);
lean_ctor_set(v_reuseFailAlloc_6391_, 5, v___x_6386_);
lean_ctor_set(v_reuseFailAlloc_6391_, 6, v_messages_6379_);
lean_ctor_set(v_reuseFailAlloc_6391_, 7, v_infoState_6380_);
lean_ctor_set(v_reuseFailAlloc_6391_, 8, v_snapshotTasks_6381_);
v___x_6388_ = v_reuseFailAlloc_6391_;
goto v_reusejp_6387_;
}
v_reusejp_6387_:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6389_ = lean_st_ref_set(v_a_6361_, v___x_6388_);
v___x_6390_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6372_, v___y_6364_, v___y_6365_, v___y_6367_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
lean_dec_ref(v_assignments_6372_);
return v___x_6390_;
}
}
}
else
{
lean_object* v_a_6394_; lean_object* v___x_6396_; uint8_t v_isShared_6397_; uint8_t v_isSharedCheck_6401_; 
lean_dec(v___y_6368_);
lean_dec_ref(v___y_6367_);
lean_dec(v___y_6366_);
v_a_6394_ = lean_ctor_get(v___y_6369_, 0);
v_isSharedCheck_6401_ = !lean_is_exclusive(v___y_6369_);
if (v_isSharedCheck_6401_ == 0)
{
v___x_6396_ = v___y_6369_;
v_isShared_6397_ = v_isSharedCheck_6401_;
goto v_resetjp_6395_;
}
else
{
lean_inc(v_a_6394_);
lean_dec(v___y_6369_);
v___x_6396_ = lean_box(0);
v_isShared_6397_ = v_isSharedCheck_6401_;
goto v_resetjp_6395_;
}
v_resetjp_6395_:
{
lean_object* v___x_6399_; 
if (v_isShared_6397_ == 0)
{
v___x_6399_ = v___x_6396_;
goto v_reusejp_6398_;
}
else
{
lean_object* v_reuseFailAlloc_6400_; 
v_reuseFailAlloc_6400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6400_, 0, v_a_6394_);
v___x_6399_ = v_reuseFailAlloc_6400_;
goto v_reusejp_6398_;
}
v_reusejp_6398_:
{
return v___x_6399_;
}
}
}
}
v___jp_6402_:
{
lean_object* v___x_6418_; double v___x_6419_; double v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; 
v___x_6418_ = lean_io_get_num_heartbeats();
v___x_6419_ = lean_float_of_nat(v___y_6415_);
v___x_6420_ = lean_float_of_nat(v___x_6418_);
v___x_6421_ = lean_box_float(v___x_6419_);
v___x_6422_ = lean_box_float(v___x_6420_);
v___x_6423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6423_, 0, v___x_6421_);
lean_ctor_set(v___x_6423_, 1, v___x_6422_);
v___x_6424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6424_, 0, v_a_6417_);
lean_ctor_set(v___x_6424_, 1, v___x_6423_);
lean_inc_ref(v___y_6403_);
lean_inc(v___y_6411_);
v___x_6425_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6411_, v___y_6413_, v___y_6403_, v___y_6407_, v___y_6408_, v___y_6410_, v___y_6412_, v___x_6424_, v___y_6409_, v___y_6416_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
lean_dec_ref(v___y_6409_);
v___y_6364_ = v___y_6404_;
v___y_6365_ = v___y_6405_;
v___y_6366_ = v___y_6414_;
v___y_6367_ = v___y_6406_;
v___y_6368_ = v___y_6416_;
v___y_6369_ = v___x_6425_;
goto v___jp_6363_;
}
v___jp_6426_:
{
lean_object* v___x_6442_; double v___x_6443_; double v___x_6444_; double v___x_6445_; double v___x_6446_; double v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6442_ = lean_io_mono_nanos_now();
v___x_6443_ = lean_float_of_nat(v___y_6428_);
v___x_6444_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6445_ = lean_float_div(v___x_6443_, v___x_6444_);
v___x_6446_ = lean_float_of_nat(v___x_6442_);
v___x_6447_ = lean_float_div(v___x_6446_, v___x_6444_);
v___x_6448_ = lean_box_float(v___x_6445_);
v___x_6449_ = lean_box_float(v___x_6447_);
v___x_6450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6450_, 0, v___x_6448_);
lean_ctor_set(v___x_6450_, 1, v___x_6449_);
v___x_6451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6451_, 0, v_a_6441_);
lean_ctor_set(v___x_6451_, 1, v___x_6450_);
lean_inc_ref(v___y_6427_);
lean_inc(v___y_6436_);
v___x_6452_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6436_, v___y_6438_, v___y_6427_, v___y_6432_, v___y_6433_, v___y_6435_, v___y_6437_, v___x_6451_, v___y_6434_, v___y_6440_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
lean_dec_ref(v___y_6434_);
v___y_6364_ = v___y_6429_;
v___y_6365_ = v___y_6430_;
v___y_6366_ = v___y_6439_;
v___y_6367_ = v___y_6431_;
v___y_6368_ = v___y_6440_;
v___y_6369_ = v___x_6452_;
goto v___jp_6363_;
}
v___jp_6454_:
{
lean_object* v___x_6467_; lean_object* v_a_6468_; lean_object* v___x_6469_; uint8_t v___x_6470_; 
v___x_6467_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6361_);
v_a_6468_ = lean_ctor_get(v___x_6467_, 0);
lean_inc(v_a_6468_);
lean_dec_ref(v___x_6467_);
v___x_6469_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6470_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6459_, v___x_6469_);
if (v___x_6470_ == 0)
{
lean_object* v___x_6471_; lean_object* v___x_6472_; 
v___x_6471_ = lean_io_mono_nanos_now();
v___x_6472_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6453_, v___y_6461_, v___y_6466_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
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
v___y_6427_ = v___y_6455_;
v___y_6428_ = v___x_6471_;
v___y_6429_ = v___y_6456_;
v___y_6430_ = v___y_6457_;
v___y_6431_ = v___y_6458_;
v___y_6432_ = v___y_6459_;
v___y_6433_ = v___y_6460_;
v___y_6434_ = v___y_6461_;
v___y_6435_ = v_a_6468_;
v___y_6436_ = v___y_6462_;
v___y_6437_ = v___y_6463_;
v___y_6438_ = v___y_6464_;
v___y_6439_ = v___y_6465_;
v___y_6440_ = v___y_6466_;
v_a_6441_ = v___x_6478_;
goto v___jp_6426_;
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
v___y_6427_ = v___y_6455_;
v___y_6428_ = v___x_6471_;
v___y_6429_ = v___y_6456_;
v___y_6430_ = v___y_6457_;
v___y_6431_ = v___y_6458_;
v___y_6432_ = v___y_6459_;
v___y_6433_ = v___y_6460_;
v___y_6434_ = v___y_6461_;
v___y_6435_ = v_a_6468_;
v___y_6436_ = v___y_6462_;
v___y_6437_ = v___y_6463_;
v___y_6438_ = v___y_6464_;
v___y_6439_ = v___y_6465_;
v___y_6440_ = v___y_6466_;
v_a_6441_ = v___x_6486_;
goto v___jp_6426_;
}
}
}
}
else
{
lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6489_ = lean_io_get_num_heartbeats();
v___x_6490_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6453_, v___y_6461_, v___y_6466_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
if (lean_obj_tag(v___x_6490_) == 0)
{
lean_object* v_a_6491_; lean_object* v___x_6493_; uint8_t v_isShared_6494_; uint8_t v_isSharedCheck_6498_; 
v_a_6491_ = lean_ctor_get(v___x_6490_, 0);
v_isSharedCheck_6498_ = !lean_is_exclusive(v___x_6490_);
if (v_isSharedCheck_6498_ == 0)
{
v___x_6493_ = v___x_6490_;
v_isShared_6494_ = v_isSharedCheck_6498_;
goto v_resetjp_6492_;
}
else
{
lean_inc(v_a_6491_);
lean_dec(v___x_6490_);
v___x_6493_ = lean_box(0);
v_isShared_6494_ = v_isSharedCheck_6498_;
goto v_resetjp_6492_;
}
v_resetjp_6492_:
{
lean_object* v___x_6496_; 
if (v_isShared_6494_ == 0)
{
lean_ctor_set_tag(v___x_6493_, 1);
v___x_6496_ = v___x_6493_;
goto v_reusejp_6495_;
}
else
{
lean_object* v_reuseFailAlloc_6497_; 
v_reuseFailAlloc_6497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6497_, 0, v_a_6491_);
v___x_6496_ = v_reuseFailAlloc_6497_;
goto v_reusejp_6495_;
}
v_reusejp_6495_:
{
v___y_6403_ = v___y_6455_;
v___y_6404_ = v___y_6456_;
v___y_6405_ = v___y_6457_;
v___y_6406_ = v___y_6458_;
v___y_6407_ = v___y_6459_;
v___y_6408_ = v___y_6460_;
v___y_6409_ = v___y_6461_;
v___y_6410_ = v_a_6468_;
v___y_6411_ = v___y_6462_;
v___y_6412_ = v___y_6463_;
v___y_6413_ = v___y_6464_;
v___y_6414_ = v___y_6465_;
v___y_6415_ = v___x_6489_;
v___y_6416_ = v___y_6466_;
v_a_6417_ = v___x_6496_;
goto v___jp_6402_;
}
}
}
else
{
lean_object* v_a_6499_; lean_object* v___x_6501_; uint8_t v_isShared_6502_; uint8_t v_isSharedCheck_6506_; 
v_a_6499_ = lean_ctor_get(v___x_6490_, 0);
v_isSharedCheck_6506_ = !lean_is_exclusive(v___x_6490_);
if (v_isSharedCheck_6506_ == 0)
{
v___x_6501_ = v___x_6490_;
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
else
{
lean_inc(v_a_6499_);
lean_dec(v___x_6490_);
v___x_6501_ = lean_box(0);
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
v_resetjp_6500_:
{
lean_object* v___x_6504_; 
if (v_isShared_6502_ == 0)
{
lean_ctor_set_tag(v___x_6501_, 0);
v___x_6504_ = v___x_6501_;
goto v_reusejp_6503_;
}
else
{
lean_object* v_reuseFailAlloc_6505_; 
v_reuseFailAlloc_6505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6505_, 0, v_a_6499_);
v___x_6504_ = v_reuseFailAlloc_6505_;
goto v_reusejp_6503_;
}
v_reusejp_6503_:
{
v___y_6403_ = v___y_6455_;
v___y_6404_ = v___y_6456_;
v___y_6405_ = v___y_6457_;
v___y_6406_ = v___y_6458_;
v___y_6407_ = v___y_6459_;
v___y_6408_ = v___y_6460_;
v___y_6409_ = v___y_6461_;
v___y_6410_ = v_a_6468_;
v___y_6411_ = v___y_6462_;
v___y_6412_ = v___y_6463_;
v___y_6413_ = v___y_6464_;
v___y_6414_ = v___y_6465_;
v___y_6415_ = v___x_6489_;
v___y_6416_ = v___y_6466_;
v_a_6417_ = v___x_6504_;
goto v___jp_6402_;
}
}
}
}
}
v___jp_6507_:
{
lean_object* v___x_6520_; uint8_t v___x_6521_; 
v___x_6520_ = l_Lean_trace_profiler;
v___x_6521_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6508_, v___x_6520_);
if (v___x_6521_ == 0)
{
lean_object* v___x_6522_; 
lean_dec_ref(v___y_6511_);
v___x_6522_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6453_, v___y_6509_, v___y_6518_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
lean_dec_ref(v___y_6509_);
v___y_6364_ = v___y_6514_;
v___y_6365_ = v___y_6516_;
v___y_6366_ = v___y_6515_;
v___y_6367_ = v___y_6517_;
v___y_6368_ = v___y_6518_;
v___y_6369_ = v___x_6522_;
goto v___jp_6363_;
}
else
{
v___y_6455_ = v___y_6510_;
v___y_6456_ = v___y_6514_;
v___y_6457_ = v___y_6516_;
v___y_6458_ = v___y_6517_;
v___y_6459_ = v___y_6508_;
v___y_6460_ = v_a_6519_;
v___y_6461_ = v___y_6509_;
v___y_6462_ = v___y_6512_;
v___y_6463_ = v___y_6511_;
v___y_6464_ = v___y_6513_;
v___y_6465_ = v___y_6515_;
v___y_6466_ = v___y_6518_;
goto v___jp_6454_;
}
}
v___jp_6523_:
{
size_t v_sz_6525_; size_t v___x_6526_; lean_object* v_assignments_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v_funVals_6530_; lean_object* v_state_6531_; lean_object* v___x_6532_; lean_object* v_options_6533_; lean_object* v_inheritedTraceOptions_6534_; uint8_t v_hasTrace_6535_; lean_object* v_ctx_6536_; uint8_t v___x_6537_; 
v_sz_6525_ = lean_array_size(v___y_6524_);
v___x_6526_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6524_, 2);
v_assignments_6527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6525_, v___x_6526_, v___y_6524_);
v___x_6528_ = lean_array_get_size(v___y_6524_);
v___x_6529_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6530_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6524_, v___x_6528_, v___x_6528_, v___x_6529_);
v_state_6531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6531_, 0, v_assignments_6527_);
lean_ctor_set(v_state_6531_, 1, v_funVals_6530_);
v___x_6532_ = lean_st_mk_ref(v_state_6531_);
v_options_6533_ = lean_ctor_get(v_a_6360_, 2);
v_inheritedTraceOptions_6534_ = lean_ctor_get(v_a_6360_, 13);
v_hasTrace_6535_ = lean_ctor_get_uint8(v_options_6533_, sizeof(void*)*1);
v_ctx_6536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6536_, 0, v___y_6524_);
lean_ctor_set(v_ctx_6536_, 1, v___x_6453_);
v___x_6537_ = lean_bool_not(v_hasTrace_6535_);
if (v___x_6537_ == 0)
{
lean_object* v___f_6538_; lean_object* v___x_6539_; uint8_t v___x_6540_; lean_object* v___x_6541_; 
lean_inc_ref(v___y_6524_);
v___f_6538_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6538_, 0, v___y_6524_);
v___x_6539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6540_ = 1;
v___x_6541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
if (v_hasTrace_6535_ == 0)
{
v___y_6508_ = v_options_6533_;
v___y_6509_ = v_ctx_6536_;
v___y_6510_ = v___x_6541_;
v___y_6511_ = v___f_6538_;
v___y_6512_ = v___x_6539_;
v___y_6513_ = v___x_6540_;
v___y_6514_ = v_sz_6525_;
v___y_6515_ = v___x_6528_;
v___y_6516_ = v___x_6526_;
v___y_6517_ = v___y_6524_;
v___y_6518_ = v___x_6532_;
v_a_6519_ = v_hasTrace_6535_;
goto v___jp_6507_;
}
else
{
lean_object* v___x_6542_; uint8_t v___x_6543_; 
v___x_6542_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6543_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6534_, v_options_6533_, v___x_6542_);
if (v___x_6543_ == 0)
{
v___y_6508_ = v_options_6533_;
v___y_6509_ = v_ctx_6536_;
v___y_6510_ = v___x_6541_;
v___y_6511_ = v___f_6538_;
v___y_6512_ = v___x_6539_;
v___y_6513_ = v___x_6540_;
v___y_6514_ = v_sz_6525_;
v___y_6515_ = v___x_6528_;
v___y_6516_ = v___x_6526_;
v___y_6517_ = v___y_6524_;
v___y_6518_ = v___x_6532_;
v_a_6519_ = v___x_6543_;
goto v___jp_6507_;
}
else
{
v___y_6455_ = v___x_6541_;
v___y_6456_ = v_sz_6525_;
v___y_6457_ = v___x_6526_;
v___y_6458_ = v___y_6524_;
v___y_6459_ = v_options_6533_;
v___y_6460_ = v___x_6543_;
v___y_6461_ = v_ctx_6536_;
v___y_6462_ = v___x_6539_;
v___y_6463_ = v___f_6538_;
v___y_6464_ = v___x_6540_;
v___y_6465_ = v___x_6528_;
v___y_6466_ = v___x_6532_;
goto v___jp_6454_;
}
}
}
else
{
lean_object* v___x_6544_; 
v___x_6544_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6453_, v_ctx_6536_, v___x_6532_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
lean_dec_ref_known(v_ctx_6536_, 2);
v___y_6364_ = v_sz_6525_;
v___y_6365_ = v___x_6526_;
v___y_6366_ = v___x_6528_;
v___y_6367_ = v___y_6524_;
v___y_6368_ = v___x_6532_;
v___y_6369_ = v___x_6544_;
goto v___jp_6363_;
}
}
v___jp_6546_:
{
lean_object* v___x_6549_; 
v___x_6549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6545_, v_decls_6357_, v___y_6547_, v___y_6548_);
lean_dec(v___y_6548_);
v___y_6524_ = v___x_6549_;
goto v___jp_6523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6557_, lean_object* v_a_6558_, lean_object* v_a_6559_, lean_object* v_a_6560_, lean_object* v_a_6561_, lean_object* v_a_6562_){
_start:
{
lean_object* v_res_6563_; 
v_res_6563_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6557_, v_a_6558_, v_a_6559_, v_a_6560_, v_a_6561_);
lean_dec(v_a_6561_);
lean_dec_ref(v_a_6560_);
lean_dec(v_a_6559_);
lean_dec_ref(v_a_6558_);
return v_res_6563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6564_, lean_object* v_n_6565_, lean_object* v_j_6566_, lean_object* v_a_6567_, lean_object* v_a_6568_){
_start:
{
lean_object* v___x_6569_; 
v___x_6569_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6564_, v_n_6565_, v_j_6566_, v_a_6568_);
return v___x_6569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6570_, lean_object* v_n_6571_, lean_object* v_j_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_){
_start:
{
lean_object* v_res_6575_; 
v_res_6575_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6570_, v_n_6571_, v_j_6572_, v_a_6573_, v_a_6574_);
lean_dec(v_n_6571_);
lean_dec_ref(v___y_6570_);
return v_res_6575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6576_, lean_object* v___x_6577_, lean_object* v_n_6578_, lean_object* v_j_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_){
_start:
{
lean_object* v___x_6582_; 
v___x_6582_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6576_, v___x_6577_, v_n_6578_, v_j_6579_, v_a_6581_);
return v___x_6582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6583_, lean_object* v___x_6584_, lean_object* v_n_6585_, lean_object* v_j_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_){
_start:
{
lean_object* v_res_6589_; 
v_res_6589_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6583_, v___x_6584_, v_n_6585_, v_j_6586_, v_a_6587_, v_a_6588_);
lean_dec(v_n_6585_);
lean_dec_ref(v___x_6584_);
lean_dec_ref(v___y_6583_);
return v_res_6589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6590_, lean_object* v_as_6591_, size_t v_sz_6592_, size_t v_i_6593_, lean_object* v_bs_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_){
_start:
{
lean_object* v___x_6600_; 
v___x_6600_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6590_, v_sz_6592_, v_i_6593_, v_bs_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
return v___x_6600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6601_, lean_object* v_as_6602_, lean_object* v_sz_6603_, lean_object* v_i_6604_, lean_object* v_bs_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_){
_start:
{
size_t v_sz_boxed_6611_; size_t v_i_boxed_6612_; lean_object* v_res_6613_; 
v_sz_boxed_6611_ = lean_unbox_usize(v_sz_6603_);
lean_dec(v_sz_6603_);
v_i_boxed_6612_ = lean_unbox_usize(v_i_6604_);
lean_dec(v_i_6604_);
v_res_6613_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6601_, v_as_6602_, v_sz_boxed_6611_, v_i_boxed_6612_, v_bs_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_);
lean_dec(v___y_6609_);
lean_dec_ref(v___y_6608_);
lean_dec(v___y_6607_);
lean_dec_ref(v___y_6606_);
lean_dec_ref(v_as_6602_);
lean_dec_ref(v___x_6601_);
return v_res_6613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6614_, lean_object* v_as_6615_, lean_object* v_lo_6616_, lean_object* v_hi_6617_, lean_object* v_w_6618_, lean_object* v_hlo_6619_, lean_object* v_hhi_6620_){
_start:
{
lean_object* v___x_6621_; 
v___x_6621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6614_, v_as_6615_, v_lo_6616_, v_hi_6617_);
return v___x_6621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6622_, lean_object* v_as_6623_, lean_object* v_lo_6624_, lean_object* v_hi_6625_, lean_object* v_w_6626_, lean_object* v_hlo_6627_, lean_object* v_hhi_6628_){
_start:
{
lean_object* v_res_6629_; 
v_res_6629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6622_, v_as_6623_, v_lo_6624_, v_hi_6625_, v_w_6626_, v_hlo_6627_, v_hhi_6628_);
lean_dec(v_hi_6625_);
lean_dec(v_n_6622_);
return v_res_6629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6630_, lean_object* v_lo_6631_, lean_object* v_hi_6632_, lean_object* v_hhi_6633_, lean_object* v_pivot_6634_, lean_object* v_as_6635_, lean_object* v_i_6636_, lean_object* v_k_6637_, lean_object* v_ilo_6638_, lean_object* v_ik_6639_, lean_object* v_w_6640_){
_start:
{
lean_object* v___x_6641_; 
v___x_6641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6632_, v_pivot_6634_, v_as_6635_, v_i_6636_, v_k_6637_);
return v___x_6641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6642_, lean_object* v_lo_6643_, lean_object* v_hi_6644_, lean_object* v_hhi_6645_, lean_object* v_pivot_6646_, lean_object* v_as_6647_, lean_object* v_i_6648_, lean_object* v_k_6649_, lean_object* v_ilo_6650_, lean_object* v_ik_6651_, lean_object* v_w_6652_){
_start:
{
lean_object* v_res_6653_; 
v_res_6653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6642_, v_lo_6643_, v_hi_6644_, v_hhi_6645_, v_pivot_6646_, v_as_6647_, v_i_6648_, v_k_6649_, v_ilo_6650_, v_ik_6651_, v_w_6652_);
lean_dec(v_hi_6644_);
lean_dec(v_lo_6643_);
lean_dec(v_n_6642_);
return v_res_6653_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; 
v___x_6713_ = lean_unsigned_to_nat(3955956072u);
v___x_6714_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6715_ = l_Lean_Name_num___override(v___x_6714_, v___x_6713_);
return v___x_6715_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; 
v___x_6717_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6718_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6719_ = l_Lean_Name_str___override(v___x_6718_, v___x_6717_);
return v___x_6719_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; 
v___x_6721_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6722_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6723_ = l_Lean_Name_str___override(v___x_6722_, v___x_6721_);
return v___x_6723_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; 
v___x_6724_ = lean_unsigned_to_nat(2u);
v___x_6725_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6726_ = l_Lean_Name_num___override(v___x_6725_, v___x_6724_);
return v___x_6726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6728_; uint8_t v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; 
v___x_6728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6729_ = 1;
v___x_6730_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6731_ = l_Lean_registerTraceClass(v___x_6728_, v___x_6729_, v___x_6730_);
return v___x_6731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6732_){
_start:
{
lean_object* v_res_6733_; 
v_res_6733_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6733_;
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
