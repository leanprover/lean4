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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Compiler_hasInductiveOverride(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInductiveOverride_x3f(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__6_value;
LEAN_EXPORT uint8_t l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.ElimDeadBranches"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 116, .m_capacity = 116, .m_length = 115, .m_data = "_private.Lean.Compiler.LCNF.ElimDeadBranches.0.Lean.Compiler.LCNF.UnreachableBranches.Value.merge.inductHasNumCtors"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__4;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__7_value;
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__6_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__7_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__2_value;
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__1_value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0_value;
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
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__2_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__3;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "_private.Lean.Compiler.LCNF.ElimDeadBranches.0.Lean.Compiler.LCNF.UnreachableBranches.Value.getLiteral.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_value;
static const lean_array_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0(lean_object* v_msg_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___f_276_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__0));
v___f_277_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__1));
v___f_278_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__2));
v___f_279_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__3));
v___f_280_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__4));
v___f_281_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__5));
v___f_282_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__6));
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
v___x_286_ = 0;
v___x_287_ = lean_box(v___x_286_);
v___x_288_ = l_instInhabitedOfMonad___redArg(v___x_285_, v___x_287_);
v___x_289_ = lean_panic_fn_borrowed(v___x_288_, v_msg_275_);
lean_dec(v___x_288_);
v___x_290_ = lean_unbox(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___boxed(lean_object* v_msg_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0(v_msg_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__3(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2));
v___x_298_ = lean_unsigned_to_nat(60u);
v___x_299_ = lean_unsigned_to_nat(129u);
v___x_300_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__1));
v___x_301_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0));
v___x_302_ = l_mkPanicMessageWithDecl(v___x_301_, v___x_300_, v___x_299_, v___x_298_, v___x_297_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__4(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2));
v___x_304_ = lean_unsigned_to_nat(72u);
v___x_305_ = lean_unsigned_to_nat(130u);
v___x_306_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__1));
v___x_307_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0));
v___x_308_ = l_mkPanicMessageWithDecl(v___x_307_, v___x_306_, v___x_305_, v___x_304_, v___x_303_);
return v___x_308_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(lean_object* v_ctorName_312_, lean_object* v_env_313_, lean_object* v_n_314_){
_start:
{
lean_object* v_induct_319_; 
if (lean_obj_tag(v_ctorName_312_) == 1)
{
lean_object* v_pre_339_; 
v_pre_339_ = lean_ctor_get(v_ctorName_312_, 0);
if (lean_obj_tag(v_pre_339_) == 1)
{
lean_object* v_pre_340_; 
v_pre_340_ = lean_ctor_get(v_pre_339_, 0);
if (lean_obj_tag(v_pre_340_) == 0)
{
lean_object* v_str_341_; lean_object* v_str_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_str_341_ = lean_ctor_get(v_ctorName_312_, 1);
v_str_342_ = lean_ctor_get(v_pre_339_, 1);
v___x_343_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5));
v___x_344_ = lean_string_dec_eq(v_str_342_, v___x_343_);
if (v___x_344_ == 0)
{
goto v___jp_334_;
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__6));
v___x_346_ = lean_string_dec_eq(v_str_341_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__7));
v___x_348_ = lean_string_dec_eq(v_str_341_, v___x_347_);
if (v___x_348_ == 0)
{
goto v___jp_334_;
}
else
{
lean_dec_ref_known(v_ctorName_312_, 2);
lean_dec_ref(v_env_313_);
return v___x_346_;
}
}
else
{
uint8_t v___x_349_; 
lean_dec_ref_known(v_ctorName_312_, 2);
lean_dec_ref(v_env_313_);
v___x_349_ = 0;
return v___x_349_;
}
}
}
else
{
goto v___jp_334_;
}
}
else
{
goto v___jp_334_;
}
}
else
{
goto v___jp_334_;
}
v___jp_315_:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__3, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__3);
v___x_317_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0(v___x_316_);
return v___x_317_;
}
v___jp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_313_, v_induct_319_);
if (lean_obj_tag(v___x_320_) == 1)
{
lean_object* v_val_321_; lean_object* v_ctors_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_val_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v___x_320_, 1);
v_ctors_322_ = lean_ctor_get(v_val_321_, 1);
lean_inc(v_ctors_322_);
lean_dec(v_val_321_);
v___x_323_ = l_List_lengthTR___redArg(v_ctors_322_);
lean_dec(v_ctors_322_);
v___x_324_ = lean_nat_dec_eq(v_n_314_, v___x_323_);
lean_dec(v___x_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; uint8_t v___x_326_; 
lean_dec(v___x_320_);
v___x_325_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__4, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__4);
v___x_326_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0(v___x_325_);
return v___x_326_;
}
}
v___jp_327_:
{
uint8_t v___x_328_; lean_object* v___x_329_; 
v___x_328_ = 0;
lean_inc_ref(v_env_313_);
v___x_329_ = l_Lean_Environment_find_x3f(v_env_313_, v_ctorName_312_, v___x_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_dec_ref(v_env_313_);
goto v___jp_315_;
}
else
{
lean_object* v_val_330_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v___x_329_, 1);
if (lean_obj_tag(v_val_330_) == 6)
{
lean_object* v_val_331_; lean_object* v_induct_332_; uint8_t v___x_333_; 
v_val_331_ = lean_ctor_get(v_val_330_, 0);
lean_inc_ref(v_val_331_);
lean_dec_ref_known(v_val_330_, 1);
v_induct_332_ = lean_ctor_get(v_val_331_, 1);
lean_inc_n(v_induct_332_, 2);
lean_dec_ref(v_val_331_);
lean_inc_ref(v_env_313_);
v___x_333_ = l_Lean_Compiler_hasInductiveOverride(v_env_313_, v_induct_332_);
if (v___x_333_ == 0)
{
v_induct_319_ = v_induct_332_;
goto v___jp_318_;
}
else
{
lean_dec(v_induct_332_);
lean_dec_ref(v_env_313_);
goto v___jp_315_;
}
}
else
{
lean_dec(v_val_330_);
lean_dec_ref(v_env_313_);
goto v___jp_315_;
}
}
}
v___jp_334_:
{
lean_object* v___x_335_; 
lean_inc(v_ctorName_312_);
lean_inc_ref(v_env_313_);
v___x_335_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_313_, v_ctorName_312_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; 
v_val_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v___x_335_, 1);
if (lean_obj_tag(v_val_336_) == 2)
{
lean_object* v_info_337_; lean_object* v_induct_338_; 
lean_dec(v_ctorName_312_);
v_info_337_ = lean_ctor_get(v_val_336_, 1);
lean_inc_ref(v_info_337_);
lean_dec_ref_known(v_val_336_, 2);
v_induct_338_ = lean_ctor_get(v_info_337_, 0);
lean_inc(v_induct_338_);
lean_dec_ref(v_info_337_);
v_induct_319_ = v_induct_338_;
goto v___jp_318_;
}
else
{
lean_dec(v_val_336_);
goto v___jp_327_;
}
}
else
{
lean_dec(v___x_335_);
goto v___jp_327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___boxed(lean_object* v_ctorName_350_, lean_object* v_env_351_, lean_object* v_n_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_ctorName_350_, v_env_351_, v_n_352_);
lean_dec(v_n_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(uint8_t v___x_355_, lean_object* v_v_356_){
_start:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_box(1);
v___x_358_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_v_356_, v___x_357_);
if (v___x_358_ == 0)
{
return v___x_355_;
}
else
{
uint8_t v___x_359_; 
v___x_359_ = 0;
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed(lean_object* v___x_360_, lean_object* v_v_361_){
_start:
{
uint8_t v___x_158__boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v___x_158__boxed_362_ = lean_unbox(v___x_360_);
v_res_363_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(v___x_158__boxed_362_, v_v_361_);
lean_dec(v_v_361_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(lean_object* v_value_365_){
_start:
{
if (lean_obj_tag(v_value_365_) == 2)
{
lean_object* v_vs_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_393_; 
v_vs_366_ = lean_ctor_get(v_value_365_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v_value_365_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v_value_365_, 0);
lean_dec(v_unused_394_);
v___x_368_ = v_value_365_;
v_isShared_369_ = v_isSharedCheck_393_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_vs_366_);
lean_dec(v_value_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_393_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___x_380_; 
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_array_get_size(v_vs_366_);
v___f_372_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__0));
v___f_373_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__1));
v___f_374_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__2));
v___f_375_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__3));
v___f_376_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__4));
v___f_377_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__5));
v___f_378_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__6));
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 0);
lean_ctor_set(v___x_368_, 1, v___f_373_);
lean_ctor_set(v___x_368_, 0, v___f_372_);
v___x_380_ = v___x_368_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___f_372_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___f_373_);
v___x_380_ = v_reuseFailAlloc_392_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___f_374_);
lean_ctor_set(v___x_381_, 2, v___f_375_);
lean_ctor_set(v___x_381_, 3, v___f_376_);
lean_ctor_set(v___x_381_, 4, v___f_377_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___f_378_);
v___x_383_ = lean_nat_dec_lt(v___x_370_, v___x_371_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
lean_dec_ref_known(v___x_382_, 2);
lean_dec_ref(v_vs_366_);
v___x_384_ = 1;
return v___x_384_;
}
else
{
if (v___x_383_ == 0)
{
lean_dec_ref_known(v___x_382_, 2);
lean_dec_ref(v_vs_366_);
return v___x_383_;
}
else
{
lean_object* v___x_385_; lean_object* v___f_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_385_ = lean_box(v___x_383_);
v___f_386_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed), 2, 1);
lean_closure_set(v___f_386_, 0, v___x_385_);
v___x_387_ = ((size_t)0ULL);
v___x_388_ = lean_usize_of_nat(v___x_371_);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_382_, v___f_386_, v_vs_366_, v___x_387_, v___x_388_);
v___x_390_ = lean_unbox(v___x_389_);
lean_dec(v___x_389_);
if (v___x_390_ == 0)
{
return v___x_383_;
}
else
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
}
}
}
}
}
else
{
uint8_t v___x_395_; 
lean_dec(v_value_365_);
v___x_395_ = 0;
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___boxed(lean_object* v_value_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(v_value_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(lean_object* v_msg_399_){
_start:
{
lean_object* v___f_400_; lean_object* v___f_401_; lean_object* v___f_402_; lean_object* v___f_403_; lean_object* v___f_404_; lean_object* v___f_405_; lean_object* v___f_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___f_400_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__0));
v___f_401_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__1));
v___f_402_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__2));
v___f_403_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__3));
v___f_404_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__4));
v___f_405_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__5));
v___f_406_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors_spec__0___closed__6));
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___f_400_);
lean_ctor_set(v___x_407_, 1, v___f_401_);
v___x_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___f_402_);
lean_ctor_set(v___x_408_, 2, v___f_403_);
lean_ctor_set(v___x_408_, 3, v___f_404_);
lean_ctor_set(v___x_408_, 4, v___f_405_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___f_406_);
v___x_410_ = lean_box(0);
v___x_411_ = l_instInhabitedOfMonad___redArg(v___x_409_, v___x_410_);
v___x_412_ = lean_panic_fn_borrowed(v___x_411_, v_msg_399_);
lean_dec(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(lean_object* v_as_413_, size_t v_i_414_, size_t v_stop_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_eq(v_i_414_, v_stop_415_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_417_ = 1;
v___x_418_ = lean_array_uget_borrowed(v_as_413_, v_i_414_);
v___x_419_ = lean_box(1);
v___x_420_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
return v___x_417_;
}
else
{
if (v___x_416_ == 0)
{
size_t v___x_421_; size_t v___x_422_; 
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_add(v_i_414_, v___x_421_);
v_i_414_ = v___x_422_;
goto _start;
}
else
{
return v___x_417_;
}
}
}
else
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0___boxed(lean_object* v_as_425_, lean_object* v_i_426_, lean_object* v_stop_427_){
_start:
{
size_t v_i_boxed_428_; size_t v_stop_boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_i_boxed_428_ = lean_unbox_usize(v_i_426_);
lean_dec(v_i_426_);
v_stop_boxed_429_ = lean_unbox_usize(v_stop_427_);
lean_dec(v_stop_427_);
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_as_425_, v_i_boxed_428_, v_stop_boxed_429_);
lean_dec_ref(v_as_425_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
uint8_t v___x_433_; 
v___x_433_ = 1;
return v___x_433_;
}
else
{
lean_object* v_head_434_; 
v_head_434_ = lean_ctor_get(v_x_432_, 0);
if (lean_obj_tag(v_head_434_) == 2)
{
lean_object* v_tail_435_; lean_object* v_vs_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_tail_435_ = lean_ctor_get(v_x_432_, 1);
v_vs_436_ = lean_ctor_get(v_head_434_, 1);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_array_get_size(v_vs_436_);
v___x_439_ = lean_nat_dec_lt(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
v_x_432_ = v_tail_435_;
goto _start;
}
else
{
if (v___x_439_ == 0)
{
v_x_432_ = v_tail_435_;
goto _start;
}
else
{
size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_438_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_436_, v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
v_x_432_ = v_tail_435_;
goto _start;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = 0;
return v___x_446_;
}
}
}
}
else
{
uint8_t v___x_447_; 
v___x_447_ = 0;
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1___boxed(lean_object* v_x_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_x_448_);
lean_dec(v_x_448_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2));
v___x_453_ = lean_unsigned_to_nat(42u);
v___x_454_ = lean_unsigned_to_nat(117u);
v___x_455_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0));
v___x_456_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0));
v___x_457_ = l_mkPanicMessageWithDecl(v___x_456_, v___x_455_, v___x_454_, v___x_453_, v___x_452_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(lean_object* v_env_458_, lean_object* v_vs_459_){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_vs_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec_ref(v_env_458_);
v___x_461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_461_, 0, v_vs_459_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_box(0);
v___x_463_ = l_List_head_x21___redArg(v___x_462_, v_vs_459_);
if (lean_obj_tag(v___x_463_) == 2)
{
lean_object* v_i_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_i_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_i_464_);
lean_dec_ref_known(v___x_463_, 2);
v___x_465_ = l_List_lengthTR___redArg(v_vs_459_);
v___x_466_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_i_464_, v_env_458_, v___x_465_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_467_, 0, v_vs_459_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
lean_dec(v_vs_459_);
v___x_468_ = lean_box(1);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v___x_463_);
lean_dec(v_vs_459_);
lean_dec_ref(v_env_458_);
v___x_469_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1);
v___x_470_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(v___x_469_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(lean_object* v_msg_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_box(0);
v___x_473_ = lean_panic_fn_borrowed(v___x_472_, v_msg_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_dec(v_x_474_);
return v_x_475_;
}
else
{
lean_object* v_head_477_; lean_object* v_tail_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_488_; 
v_head_477_ = lean_ctor_get(v_x_476_, 0);
v_tail_478_ = lean_ctor_get(v_x_476_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_488_ == 0)
{
v___x_480_ = v_x_476_;
v_isShared_481_ = v_isSharedCheck_488_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_tail_478_);
lean_inc(v_head_477_);
lean_dec(v_x_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_488_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
lean_inc(v_x_474_);
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 5);
lean_ctor_set(v___x_480_, 1, v_x_474_);
lean_ctor_set(v___x_480_, 0, v_x_475_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_x_475_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_x_474_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_477_);
v___x_485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v_x_475_ = v___x_485_;
v_x_476_ = v_tail_478_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v___x_491_; 
lean_dec(v_x_490_);
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v_tail_492_; 
v_tail_492_ = lean_ctor_get(v_x_489_, 1);
if (lean_obj_tag(v_tail_492_) == 0)
{
lean_object* v_head_493_; lean_object* v___x_494_; 
lean_dec(v_x_490_);
v_head_493_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_head_493_);
lean_dec_ref_known(v_x_489_, 2);
v___x_494_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_493_);
return v___x_494_;
}
else
{
lean_object* v_head_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_inc(v_tail_492_);
v_head_495_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_head_495_);
lean_dec_ref_known(v_x_489_, 2);
v___x_496_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_495_);
v___x_497_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(v_x_490_, v___x_496_, v_tail_492_);
return v___x_497_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2));
v___x_510_ = lean_string_length(v___x_509_);
return v___x_510_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7);
v___x_512_ = lean_nat_to_int(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(lean_object* v_a_517_){
_start:
{
if (lean_obj_tag(v_a_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1));
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; 
v___x_519_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_520_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(v_a_517_, v___x_519_);
v___x_521_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8);
v___x_522_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9));
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_520_);
v___x_524_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_521_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = 0;
v___x_528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_527_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(lean_object* v_env_534_, lean_object* v_v1_535_, lean_object* v_v2_536_){
_start:
{
lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_544_; lean_object* v_i_545_; lean_object* v_vs_546_; 
switch(lean_obj_tag(v_v1_535_))
{
case 0:
{
switch(lean_obj_tag(v_v2_536_))
{
case 2:
{
lean_object* v_i_553_; lean_object* v_vs_554_; 
v_i_553_ = lean_ctor_get(v_v2_536_, 0);
lean_inc(v_i_553_);
v_vs_554_ = lean_ctor_get(v_v2_536_, 1);
lean_inc_ref(v_vs_554_);
v___y_544_ = v_v2_536_;
v_i_545_ = v_i_553_;
v_vs_546_ = v_vs_554_;
goto v___jp_543_;
}
case 3:
{
lean_object* v_vs_555_; lean_object* v___x_556_; 
v_vs_555_ = lean_ctor_get(v_v2_536_, 0);
lean_inc(v_vs_555_);
lean_dec_ref_known(v_v2_536_, 1);
v___x_556_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_534_, v_vs_555_);
return v___x_556_;
}
default: 
{
lean_dec_ref(v_env_534_);
return v_v2_536_;
}
}
}
case 1:
{
lean_dec_ref(v_env_534_);
switch(lean_obj_tag(v_v2_536_))
{
case 0:
{
return v_v1_535_;
}
case 1:
{
return v_v2_536_;
}
case 3:
{
lean_dec_ref_known(v_v2_536_, 1);
return v_v1_535_;
}
default: 
{
lean_dec(v_v2_536_);
return v_v1_535_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_v2_536_))
{
case 0:
{
lean_object* v_i_557_; lean_object* v_vs_558_; 
v_i_557_ = lean_ctor_get(v_v1_535_, 0);
lean_inc(v_i_557_);
v_vs_558_ = lean_ctor_get(v_v1_535_, 1);
lean_inc_ref(v_vs_558_);
v___y_544_ = v_v1_535_;
v_i_545_ = v_i_557_;
v_vs_546_ = v_vs_558_;
goto v___jp_543_;
}
case 1:
{
lean_dec_ref_known(v_v1_535_, 2);
lean_dec_ref(v_env_534_);
return v_v2_536_;
}
case 2:
{
lean_object* v_i_559_; lean_object* v_vs_560_; lean_object* v_i_561_; lean_object* v_vs_562_; uint8_t v___x_563_; 
v_i_559_ = lean_ctor_get(v_v1_535_, 0);
v_vs_560_ = lean_ctor_get(v_v1_535_, 1);
v_i_561_ = lean_ctor_get(v_v2_536_, 0);
v_vs_562_ = lean_ctor_get(v_v2_536_, 1);
v___x_563_ = lean_name_eq(v_i_559_, v_i_561_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v_v2_536_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v_v1_535_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_534_, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_577_; 
lean_inc_ref(v_vs_562_);
lean_inc_ref(v_vs_560_);
lean_inc(v_i_559_);
lean_dec_ref_known(v_v1_535_, 2);
v_isSharedCheck_577_ = !lean_is_exclusive(v_v2_536_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; lean_object* v_unused_579_; 
v_unused_578_ = lean_ctor_get(v_v2_536_, 1);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_v2_536_, 0);
lean_dec(v_unused_579_);
v___x_569_ = v_v2_536_;
v_isShared_570_ = v_isSharedCheck_577_;
goto v_resetjp_568_;
}
else
{
lean_dec(v_v2_536_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_577_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
lean_inc_ref(v_env_534_);
v___x_573_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_534_, v_vs_560_, v_vs_562_, v___x_571_, v___x_572_);
lean_dec_ref(v_vs_562_);
lean_dec_ref(v_vs_560_);
lean_inc_ref(v___x_573_);
lean_inc(v_i_559_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v___x_573_);
lean_ctor_set(v___x_569_, 0, v_i_559_);
v___x_575_ = v___x_569_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_i_559_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v___y_544_ = v___x_575_;
v_i_545_ = v_i_559_;
v_vs_546_ = v___x_573_;
goto v___jp_543_;
}
}
}
}
default: 
{
lean_object* v_vs_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_vs_580_ = lean_ctor_get(v_v2_536_, 0);
lean_inc(v_vs_580_);
lean_dec_ref_known(v_v2_536_, 1);
lean_inc_ref(v_env_534_);
v___x_581_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_534_, v_vs_580_, v_v1_535_);
v___x_582_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_534_, v___x_581_);
return v___x_582_;
}
}
}
default: 
{
switch(lean_obj_tag(v_v2_536_))
{
case 0:
{
lean_object* v_vs_583_; lean_object* v___x_584_; 
v_vs_583_ = lean_ctor_get(v_v1_535_, 0);
lean_inc(v_vs_583_);
lean_dec_ref_known(v_v1_535_, 1);
v___x_584_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_534_, v_vs_583_);
return v___x_584_;
}
case 1:
{
lean_dec_ref_known(v_v1_535_, 1);
lean_dec_ref(v_env_534_);
return v_v2_536_;
}
case 3:
{
lean_object* v_vs_585_; lean_object* v_vs_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_vs_585_ = lean_ctor_get(v_v1_535_, 0);
lean_inc(v_vs_585_);
lean_dec_ref_known(v_v1_535_, 1);
v_vs_586_ = lean_ctor_get(v_v2_536_, 0);
lean_inc(v_vs_586_);
lean_dec_ref_known(v_v2_536_, 1);
lean_inc_ref(v_env_534_);
v___x_587_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(v_env_534_, v_vs_586_, v_vs_585_);
v___x_588_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_534_, v___x_587_);
return v___x_588_;
}
default: 
{
lean_object* v_vs_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_vs_589_ = lean_ctor_get(v_v1_535_, 0);
lean_inc(v_vs_589_);
lean_dec_ref_known(v_v1_535_, 1);
lean_inc_ref(v_env_534_);
v___x_590_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_534_, v_vs_589_, v_v2_536_);
v___x_591_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_534_, v___x_590_);
return v___x_591_;
}
}
}
}
v___jp_537_:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v___y_539_, v_env_534_, v___x_540_);
if (v___x_541_ == 0)
{
return v___y_538_;
}
else
{
lean_object* v___x_542_; 
lean_dec(v___y_538_);
v___x_542_ = lean_box(1);
return v___x_542_;
}
}
v___jp_543_:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_array_get_size(v_vs_546_);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec_ref(v_vs_546_);
v___y_538_ = v___y_544_;
v___y_539_ = v_i_545_;
goto v___jp_537_;
}
else
{
if (v___x_549_ == 0)
{
lean_dec_ref(v_vs_546_);
v___y_538_ = v___y_544_;
v___y_539_ = v_i_545_;
goto v___jp_537_;
}
else
{
size_t v___x_550_; size_t v___x_551_; uint8_t v___x_552_; 
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_548_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_546_, v___x_550_, v___x_551_);
lean_dec_ref(v_vs_546_);
if (v___x_552_ == 0)
{
v___y_538_ = v___y_544_;
v___y_539_ = v_i_545_;
goto v___jp_537_;
}
else
{
lean_dec(v_i_545_);
lean_dec_ref(v_env_534_);
return v___y_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(lean_object* v_env_592_, lean_object* v_as_593_, lean_object* v_bs_594_, lean_object* v_i_595_, lean_object* v_cs_596_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_get_size(v_as_593_);
v___x_598_ = lean_nat_dec_lt(v_i_595_, v___x_597_);
if (v___x_598_ == 0)
{
lean_dec(v_i_595_);
lean_dec_ref(v_env_592_);
return v_cs_596_;
}
else
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_array_get_size(v_bs_594_);
v___x_600_ = lean_nat_dec_lt(v_i_595_, v___x_599_);
if (v___x_600_ == 0)
{
lean_dec(v_i_595_);
lean_dec_ref(v_env_592_);
return v_cs_596_;
}
else
{
lean_object* v_a_601_; lean_object* v_b_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_a_601_ = lean_array_fget_borrowed(v_as_593_, v_i_595_);
v_b_602_ = lean_array_fget_borrowed(v_bs_594_, v_i_595_);
lean_inc(v_b_602_);
lean_inc(v_a_601_);
lean_inc_ref(v_env_592_);
v___x_603_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_592_, v_a_601_, v_b_602_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_595_, v___x_604_);
lean_dec(v_i_595_);
v___x_606_ = lean_array_push(v_cs_596_, v___x_603_);
v_i_595_ = v___x_605_;
v_cs_596_ = v___x_606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(lean_object* v_env_608_, lean_object* v_vs_609_, lean_object* v_v_610_){
_start:
{
if (lean_obj_tag(v_vs_609_) == 0)
{
lean_object* v___x_629_; 
lean_dec_ref(v_env_608_);
v___x_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_629_, 0, v_v_610_);
lean_ctor_set(v___x_629_, 1, v_vs_609_);
return v___x_629_;
}
else
{
lean_object* v_head_630_; 
v_head_630_ = lean_ctor_get(v_vs_609_, 0);
if (lean_obj_tag(v_head_630_) == 2)
{
if (lean_obj_tag(v_v_610_) == 2)
{
lean_object* v_tail_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_659_; 
lean_inc_ref(v_head_630_);
v_tail_631_ = lean_ctor_get(v_vs_609_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_vs_609_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_vs_609_, 0);
lean_dec(v_unused_660_);
v___x_633_ = v_vs_609_;
v_isShared_634_ = v_isSharedCheck_659_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_tail_631_);
lean_dec(v_vs_609_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_659_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_i_635_; lean_object* v_vs_636_; lean_object* v_i_637_; lean_object* v_vs_638_; uint8_t v___x_639_; 
v_i_635_ = lean_ctor_get(v_head_630_, 0);
v_vs_636_ = lean_ctor_get(v_head_630_, 1);
v_i_637_ = lean_ctor_get(v_v_610_, 0);
v_vs_638_ = lean_ctor_get(v_v_610_, 1);
v___x_639_ = lean_name_eq(v_i_635_, v_i_637_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_608_, v_tail_631_, v_v_610_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_640_);
v___x_642_ = v___x_633_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_head_630_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
else
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_656_; 
lean_inc_ref(v_vs_638_);
lean_inc_ref(v_vs_636_);
lean_inc(v_i_635_);
lean_dec_ref_known(v_head_630_, 2);
v_isSharedCheck_656_ = !lean_is_exclusive(v_v_610_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; lean_object* v_unused_658_; 
v_unused_657_ = lean_ctor_get(v_v_610_, 1);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_v_610_, 0);
lean_dec(v_unused_658_);
v___x_645_ = v_v_610_;
v_isShared_646_ = v_isSharedCheck_656_;
goto v_resetjp_644_;
}
else
{
lean_dec(v_v_610_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_656_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
v___x_649_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_608_, v_vs_636_, v_vs_638_, v___x_647_, v___x_648_);
lean_dec_ref(v_vs_638_);
lean_dec_ref(v_vs_636_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_649_);
lean_ctor_set(v___x_645_, 0, v_i_635_);
v___x_651_ = v___x_645_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_i_635_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_651_);
v___x_653_ = v___x_633_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_tail_631_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_608_);
goto v___jp_611_;
}
}
else
{
lean_dec_ref(v_env_608_);
goto v___jp_611_;
}
}
v___jp_611_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0));
v___x_613_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0));
v___x_614_ = lean_unsigned_to_nat(87u);
v___x_615_ = lean_unsigned_to_nat(12u);
v___x_616_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1));
v___x_617_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_610_);
v___x_618_ = l_Std_Format_defWidth;
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l_Std_Format_pretty(v___x_617_, v___x_618_, v___x_619_, v___x_619_);
v___x_621_ = lean_string_append(v___x_616_, v___x_620_);
lean_dec_ref(v___x_620_);
v___x_622_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2));
v___x_623_ = lean_string_append(v___x_621_, v___x_622_);
v___x_624_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_vs_609_);
v___x_625_ = l_Std_Format_pretty(v___x_624_, v___x_618_, v___x_619_, v___x_619_);
v___x_626_ = lean_string_append(v___x_623_, v___x_625_);
lean_dec_ref(v___x_625_);
v___x_627_ = l_mkPanicMessageWithDecl(v___x_612_, v___x_613_, v___x_614_, v___x_615_, v___x_626_);
lean_dec_ref(v___x_626_);
v___x_628_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(lean_object* v_env_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
lean_dec_ref(v_env_661_);
return v_x_662_;
}
else
{
lean_object* v_head_664_; lean_object* v_tail_665_; lean_object* v___x_666_; 
v_head_664_ = lean_ctor_get(v_x_663_, 0);
lean_inc(v_head_664_);
v_tail_665_ = lean_ctor_get(v_x_663_, 1);
lean_inc(v_tail_665_);
lean_dec_ref_known(v_x_663_, 2);
lean_inc_ref(v_env_661_);
v___x_666_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_661_, v_x_662_, v_head_664_);
v_x_662_ = v___x_666_;
v_x_663_ = v_tail_665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2___boxed(lean_object* v_env_668_, lean_object* v_as_669_, lean_object* v_bs_670_, lean_object* v_i_671_, lean_object* v_cs_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_668_, v_as_669_, v_bs_670_, v_i_671_, v_cs_672_);
lean_dec_ref(v_bs_670_);
lean_dec_ref(v_as_669_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(lean_object* v_a_674_, lean_object* v_n_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_a_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___boxed(lean_object* v_a_677_, lean_object* v_n_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(v_a_677_, v_n_678_);
lean_dec(v_n_678_);
return v_res_679_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(lean_object* v_a_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
uint8_t v___x_682_; 
v___x_682_ = 0;
return v___x_682_;
}
else
{
lean_object* v_head_683_; lean_object* v_tail_684_; uint8_t v___x_685_; 
v_head_683_ = lean_ctor_get(v_x_681_, 0);
v_tail_684_ = lean_ctor_get(v_x_681_, 1);
v___x_685_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_680_, v_head_683_);
if (v___x_685_ == 0)
{
v_x_681_ = v_tail_684_;
goto _start;
}
else
{
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object* v_a_687_, lean_object* v_x_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v_a_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec(v_a_687_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(lean_object* v_env_691_, lean_object* v_forbiddenTypes_x27_692_, lean_object* v_n_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_bs_696_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_697_ == 0)
{
lean_dec(v_forbiddenTypes_x27_692_);
lean_dec_ref(v_env_691_);
return v_bs_696_;
}
else
{
lean_object* v_v_698_; lean_object* v___x_699_; lean_object* v_bs_x27_700_; lean_object* v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v_v_698_ = lean_array_uget(v_bs_696_, v_i_695_);
v___x_699_ = lean_unsigned_to_nat(0u);
v_bs_x27_700_ = lean_array_uset(v_bs_696_, v_i_695_, v___x_699_);
lean_inc(v_forbiddenTypes_x27_692_);
lean_inc_ref(v_env_691_);
v___x_701_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_691_, v_v_698_, v_forbiddenTypes_x27_692_, v_n_693_);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_add(v_i_695_, v___x_702_);
v___x_704_ = lean_array_uset(v_bs_x27_700_, v_i_695_, v___x_701_);
v_i_695_ = v___x_703_;
v_bs_696_ = v___x_704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(lean_object* v_env_714_, lean_object* v_v_715_, lean_object* v_forbiddenTypes_716_, lean_object* v_remainingDepth_717_){
_start:
{
lean_object* v_zero_718_; uint8_t v_isZero_719_; 
v_zero_718_ = lean_unsigned_to_nat(0u);
v_isZero_719_ = lean_nat_dec_eq(v_remainingDepth_717_, v_zero_718_);
if (v_isZero_719_ == 1)
{
lean_object* v___x_720_; 
lean_dec(v_forbiddenTypes_716_);
lean_dec(v_v_715_);
lean_dec_ref(v_env_714_);
v___x_720_ = lean_box(1);
return v___x_720_;
}
else
{
lean_object* v_one_721_; lean_object* v_n_722_; 
v_one_721_ = lean_unsigned_to_nat(1u);
v_n_722_ = lean_nat_sub(v_remainingDepth_717_, v_one_721_);
switch(lean_obj_tag(v_v_715_))
{
case 2:
{
lean_object* v_i_723_; lean_object* v_vs_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_766_; 
v_i_723_ = lean_ctor_get(v_v_715_, 0);
v_vs_724_ = lean_ctor_get(v_v_715_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_v_715_);
if (v_isSharedCheck_766_ == 0)
{
v___x_726_ = v_v_715_;
v_isShared_727_ = v_isSharedCheck_766_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_vs_724_);
lean_inc(v_i_723_);
lean_dec(v_v_715_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_766_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_forbiddenTypes_x27_729_; lean_object* v_inductName_737_; uint8_t v_inductRec_738_; lean_object* v_inductName_742_; lean_object* v_induct_744_; uint8_t v___y_749_; uint8_t v___y_756_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_inductName_742_ = lean_box(0);
v___x_762_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__1));
v___x_763_ = lean_name_eq(v_i_723_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__2));
v___x_765_ = lean_name_eq(v_i_723_, v___x_764_);
v___y_756_ = v___x_765_;
goto v___jp_755_;
}
else
{
v___y_756_ = v___x_763_;
goto v___jp_755_;
}
v___jp_728_:
{
size_t v_sz_730_; size_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v_sz_730_ = lean_array_size(v_vs_724_);
v___x_731_ = ((size_t)0ULL);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_714_, v_forbiddenTypes_x27_729_, v_n_722_, v_sz_730_, v___x_731_, v_vs_724_);
lean_dec(v_n_722_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_732_);
v___x_734_ = v___x_726_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_i_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
v___jp_736_:
{
uint8_t v___x_739_; 
v___x_739_ = l_Lean_NameSet_contains(v_forbiddenTypes_716_, v_inductName_737_);
if (v___x_739_ == 0)
{
if (v_inductRec_738_ == 0)
{
lean_dec(v_inductName_737_);
v_forbiddenTypes_x27_729_ = v_forbiddenTypes_716_;
goto v___jp_728_;
}
else
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_NameSet_insert(v_forbiddenTypes_716_, v_inductName_737_);
v_forbiddenTypes_x27_729_ = v___x_740_;
goto v___jp_728_;
}
}
else
{
lean_object* v___x_741_; 
lean_dec(v_inductName_737_);
lean_del_object(v___x_726_);
lean_dec_ref(v_vs_724_);
lean_dec(v_i_723_);
lean_dec(v_n_722_);
lean_dec(v_forbiddenTypes_716_);
lean_dec_ref(v_env_714_);
v___x_741_ = lean_box(1);
return v___x_741_;
}
}
v___jp_743_:
{
lean_object* v___x_745_; 
lean_inc(v_induct_744_);
lean_inc_ref(v_env_714_);
v___x_745_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_714_, v_induct_744_);
if (lean_obj_tag(v___x_745_) == 1)
{
lean_object* v_val_746_; uint8_t v_isRec_747_; 
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v___x_745_, 1);
v_isRec_747_ = lean_ctor_get_uint8(v_val_746_, sizeof(void*)*2);
lean_dec(v_val_746_);
v_inductName_737_ = v_induct_744_;
v_inductRec_738_ = v_isRec_747_;
goto v___jp_736_;
}
else
{
lean_dec(v___x_745_);
lean_dec(v_induct_744_);
v_inductName_737_ = v_inductName_742_;
v_inductRec_738_ = v_isZero_719_;
goto v___jp_736_;
}
}
v___jp_748_:
{
lean_object* v___x_750_; 
lean_inc(v_i_723_);
lean_inc_ref(v_env_714_);
v___x_750_ = l_Lean_Environment_find_x3f(v_env_714_, v_i_723_, v___y_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
v_inductName_737_ = v_inductName_742_;
v_inductRec_738_ = v_isZero_719_;
goto v___jp_736_;
}
else
{
lean_object* v_val_751_; 
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v___x_750_, 1);
if (lean_obj_tag(v_val_751_) == 6)
{
lean_object* v_val_752_; lean_object* v_induct_753_; uint8_t v___x_754_; 
v_val_752_ = lean_ctor_get(v_val_751_, 0);
lean_inc_ref(v_val_752_);
lean_dec_ref_known(v_val_751_, 1);
v_induct_753_ = lean_ctor_get(v_val_752_, 1);
lean_inc_n(v_induct_753_, 2);
lean_dec_ref(v_val_752_);
lean_inc_ref(v_env_714_);
v___x_754_ = l_Lean_Compiler_hasInductiveOverride(v_env_714_, v_induct_753_);
if (v___x_754_ == 0)
{
v_induct_744_ = v_induct_753_;
goto v___jp_743_;
}
else
{
lean_dec(v_induct_753_);
v_inductName_737_ = v_inductName_742_;
v_inductRec_738_ = v_isZero_719_;
goto v___jp_736_;
}
}
else
{
lean_dec(v_val_751_);
v_inductName_737_ = v_inductName_742_;
v_inductRec_738_ = v_isZero_719_;
goto v___jp_736_;
}
}
}
v___jp_755_:
{
if (v___y_756_ == 0)
{
lean_object* v___x_757_; 
lean_inc(v_i_723_);
lean_inc_ref(v_env_714_);
v___x_757_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_714_, v_i_723_);
if (lean_obj_tag(v___x_757_) == 1)
{
lean_object* v_val_758_; 
v_val_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v___x_757_, 1);
if (lean_obj_tag(v_val_758_) == 2)
{
lean_object* v_info_759_; lean_object* v_induct_760_; 
v_info_759_ = lean_ctor_get(v_val_758_, 1);
lean_inc_ref(v_info_759_);
lean_dec_ref_known(v_val_758_, 2);
v_induct_760_ = lean_ctor_get(v_info_759_, 0);
lean_inc(v_induct_760_);
lean_dec_ref(v_info_759_);
v_induct_744_ = v_induct_760_;
goto v___jp_743_;
}
else
{
lean_dec(v_val_758_);
v___y_749_ = v___y_756_;
goto v___jp_748_;
}
}
else
{
lean_dec(v___x_757_);
v___y_749_ = v___y_756_;
goto v___jp_748_;
}
}
else
{
lean_object* v_inductName_761_; 
v_inductName_761_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__0));
v_inductName_737_ = v_inductName_761_;
v_inductRec_738_ = v___y_756_;
goto v___jp_736_;
}
}
}
}
case 3:
{
lean_object* v_vs_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
v_vs_767_ = lean_ctor_get(v_v_715_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_v_715_);
if (v_isSharedCheck_778_ == 0)
{
v___x_769_ = v_v_715_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_vs_767_);
lean_dec(v_v_715_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v_vs_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_771_ = lean_box(0);
v_vs_772_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_714_, v_forbiddenTypes_716_, v_n_722_, v_vs_767_, v___x_771_);
lean_dec(v_n_722_);
v___x_773_ = lean_box(1);
v___x_774_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v___x_773_, v_vs_772_);
if (v___x_774_ == 0)
{
lean_object* v___x_776_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_vs_772_);
v___x_776_ = v___x_769_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_vs_772_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_dec(v_vs_772_);
lean_del_object(v___x_769_);
return v___x_773_;
}
}
}
default: 
{
lean_dec(v_n_722_);
lean_dec(v_forbiddenTypes_716_);
lean_dec_ref(v_env_714_);
return v_v_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(lean_object* v_env_779_, lean_object* v_forbiddenTypes_780_, lean_object* v_n_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
if (lean_obj_tag(v_a_782_) == 0)
{
lean_object* v___x_784_; 
lean_dec(v_forbiddenTypes_780_);
lean_dec_ref(v_env_779_);
v___x_784_ = l_List_reverse___redArg(v_a_783_);
return v___x_784_;
}
else
{
lean_object* v_head_785_; lean_object* v_tail_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_795_; 
v_head_785_ = lean_ctor_get(v_a_782_, 0);
v_tail_786_ = lean_ctor_get(v_a_782_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_782_);
if (v_isSharedCheck_795_ == 0)
{
v___x_788_ = v_a_782_;
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_tail_786_);
lean_inc(v_head_785_);
lean_dec(v_a_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_forbiddenTypes_780_);
lean_inc_ref(v_env_779_);
v___x_790_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_779_, v_head_785_, v_forbiddenTypes_780_, v_n_781_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_a_783_);
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_a_783_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_a_782_ = v_tail_786_;
v_a_783_ = v___x_792_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object* v_env_796_, lean_object* v_forbiddenTypes_797_, lean_object* v_n_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_796_, v_forbiddenTypes_797_, v_n_798_, v_a_799_, v_a_800_);
lean_dec(v_n_798_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object* v_env_802_, lean_object* v_forbiddenTypes_x27_803_, lean_object* v_n_804_, lean_object* v_sz_805_, lean_object* v_i_806_, lean_object* v_bs_807_){
_start:
{
size_t v_sz_boxed_808_; size_t v_i_boxed_809_; lean_object* v_res_810_; 
v_sz_boxed_808_ = lean_unbox_usize(v_sz_805_);
lean_dec(v_sz_805_);
v_i_boxed_809_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_802_, v_forbiddenTypes_x27_803_, v_n_804_, v_sz_boxed_808_, v_i_boxed_809_, v_bs_807_);
lean_dec(v_n_804_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___boxed(lean_object* v_env_811_, lean_object* v_v_812_, lean_object* v_forbiddenTypes_813_, lean_object* v_remainingDepth_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_811_, v_v_812_, v_forbiddenTypes_813_, v_remainingDepth_814_);
lean_dec(v_remainingDepth_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(lean_object* v_env_816_, lean_object* v_v_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = l_Lean_NameSet_empty;
v___x_819_ = lean_unsigned_to_nat(8u);
v___x_820_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_816_, v_v_817_, v___x_818_, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(lean_object* v_env_821_, lean_object* v_v1_822_, lean_object* v_v2_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_inc_ref(v_env_821_);
v___x_824_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_821_, v_v1_822_, v_v2_823_);
v___x_825_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(v_env_821_, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_827_) == 0)
{
uint8_t v___x_828_; 
v___x_828_ = 0;
return v___x_828_;
}
else
{
lean_object* v_head_829_; lean_object* v_tail_830_; uint8_t v___x_831_; 
v_head_829_ = lean_ctor_get(v_x_827_, 0);
v_tail_830_ = lean_ctor_get(v_x_827_, 1);
v___x_831_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_head_829_, v_x_826_);
if (v___x_831_ == 0)
{
v_x_827_ = v_tail_830_;
goto _start;
}
else
{
return v___x_831_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
switch(lean_obj_tag(v_x_833_))
{
case 2:
{
lean_object* v_i_835_; uint8_t v___x_836_; 
v_i_835_ = lean_ctor_get(v_x_833_, 0);
v___x_836_ = lean_name_eq(v_i_835_, v_x_834_);
return v___x_836_;
}
case 3:
{
lean_object* v_vs_837_; uint8_t v___x_838_; 
v_vs_837_ = lean_ctor_get(v_x_833_, 0);
v___x_838_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_834_, v_vs_837_);
return v___x_838_;
}
default: 
{
uint8_t v___x_839_; 
v___x_839_ = 1;
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_x_840_, v_x_841_);
lean_dec(v_x_841_);
lean_dec(v_x_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0___boxed(lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_844_, v_x_845_);
lean_dec(v_x_845_);
lean_dec(v_x_844_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(lean_object* v_x_851_, lean_object* v_as_x27_852_, lean_object* v_b_853_){
_start:
{
if (lean_obj_tag(v_as_x27_852_) == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v_b_853_);
return v___x_854_;
}
else
{
lean_object* v_head_855_; lean_object* v_tail_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_b_853_);
v_head_855_ = lean_ctor_get(v_as_x27_852_, 0);
v_tail_856_ = lean_ctor_get(v_as_x27_852_, 1);
v___x_857_ = lean_box(0);
v___x_858_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_855_) == 2)
{
lean_object* v_i_859_; lean_object* v_vs_860_; uint8_t v___x_861_; 
v_i_859_ = lean_ctor_get(v_head_855_, 0);
v_vs_860_ = lean_ctor_get(v_head_855_, 1);
v___x_861_ = lean_name_eq(v_i_859_, v_x_851_);
if (v___x_861_ == 0)
{
v_as_x27_852_ = v_tail_856_;
v_b_853_ = v___x_858_;
goto _start;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_inc_ref(v_vs_860_);
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_vs_860_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_857_);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
else
{
v_as_x27_852_ = v_tail_856_;
v_b_853_ = v___x_858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___boxed(lean_object* v_x_867_, lean_object* v_as_x27_868_, lean_object* v_b_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_867_, v_as_x27_868_, v_b_869_);
lean_dec(v_as_x27_868_);
lean_dec(v_x_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
switch(lean_obj_tag(v_x_871_))
{
case 2:
{
lean_object* v_i_873_; lean_object* v_vs_874_; uint8_t v___x_875_; 
v_i_873_ = lean_ctor_get(v_x_871_, 0);
v_vs_874_ = lean_ctor_get(v_x_871_, 1);
v___x_875_ = lean_name_eq(v_i_873_, v_x_872_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
v___x_876_ = lean_box(0);
return v___x_876_;
}
else
{
lean_object* v___x_877_; 
lean_inc_ref(v_vs_874_);
v___x_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_877_, 0, v_vs_874_);
return v___x_877_;
}
}
case 3:
{
lean_object* v_vs_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_val_882_; lean_object* v_fst_883_; 
v_vs_878_ = lean_ctor_get(v_x_871_, 0);
v___x_879_ = lean_box(0);
v___x_880_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
v___x_881_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_872_, v_vs_878_, v___x_880_);
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec(v___x_881_);
v_fst_883_ = lean_ctor_get(v_val_882_, 0);
lean_inc(v_fst_883_);
lean_dec(v_val_882_);
if (lean_obj_tag(v_fst_883_) == 0)
{
return v___x_879_;
}
else
{
return v_fst_883_;
}
}
default: 
{
lean_object* v___x_884_; 
v___x_884_ = lean_box(0);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs___boxed(lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_x_885_, v_x_886_);
lean_dec(v_x_886_);
lean_dec(v_x_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(lean_object* v_x_888_, lean_object* v_as_889_, lean_object* v_as_x27_890_, lean_object* v_b_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_888_, v_as_x27_890_, v_b_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___boxed(lean_object* v_x_894_, lean_object* v_as_895_, lean_object* v_as_x27_896_, lean_object* v_b_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(v_x_894_, v_as_895_, v_as_x27_896_, v_b_897_, v_a_898_);
lean_dec(v_as_x27_896_);
lean_dec(v_as_895_);
lean_dec(v_x_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(lean_object* v_a_903_){
_start:
{
lean_object* v_zero_904_; uint8_t v_isZero_905_; 
v_zero_904_ = lean_unsigned_to_nat(0u);
v_isZero_905_ = lean_nat_dec_eq(v_a_903_, v_zero_904_);
if (v_isZero_905_ == 1)
{
lean_object* v___x_906_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
return v___x_906_;
}
else
{
lean_object* v_one_907_; lean_object* v_n_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_one_907_ = lean_unsigned_to_nat(1u);
v_n_908_ = lean_nat_sub(v_a_903_, v_one_907_);
v___x_909_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___closed__2));
v___x_910_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_908_);
lean_dec(v_n_908_);
v___x_911_ = lean_mk_empty_array_with_capacity(v_one_907_);
v___x_912_ = lean_array_push(v___x_911_, v___x_910_);
v___x_913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_909_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___boxed(lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_a_914_);
lean_dec(v_a_914_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(lean_object* v_n_916_){
_start:
{
lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_917_ = lean_unsigned_to_nat(8u);
v___x_918_ = lean_nat_dec_lt(v___x_917_, v_n_916_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_916_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = lean_box(1);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat___boxed(lean_object* v_n_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_n_921_);
lean_dec(v_n_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(lean_object* v_x_923_){
_start:
{
if (lean_obj_tag(v_x_923_) == 0)
{
lean_object* v_val_924_; lean_object* v___x_925_; 
v_val_924_ = lean_ctor_get(v_x_923_, 0);
v___x_925_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_val_924_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; 
v___x_926_ = lean_box(1);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit___boxed(lean_object* v_x_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_x_927_);
lean_dec_ref(v_x_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(lean_object* v_env_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
switch(lean_obj_tag(v_x_930_))
{
case 2:
{
lean_object* v_vs_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
lean_dec_ref(v_env_929_);
v_vs_932_ = lean_ctor_get(v_x_930_, 1);
v___x_933_ = lean_array_get_size(v_vs_932_);
v___x_934_ = lean_nat_dec_lt(v_x_931_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
v___x_935_ = lean_box(0);
return v___x_935_;
}
else
{
lean_object* v___x_936_; 
v___x_936_ = lean_array_fget_borrowed(v_vs_932_, v_x_931_);
lean_inc(v___x_936_);
return v___x_936_;
}
}
case 3:
{
lean_object* v_vs_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_vs_937_ = lean_ctor_get(v_x_930_, 0);
v___x_938_ = lean_box(0);
v___x_939_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_929_, v_x_931_, v___x_938_, v_vs_937_);
return v___x_939_;
}
default: 
{
lean_dec_ref(v_env_929_);
lean_inc(v_x_930_);
return v_x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(lean_object* v_env_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_dec_ref(v_env_940_);
return v_x_942_;
}
else
{
lean_object* v_head_944_; lean_object* v_tail_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_head_944_ = lean_ctor_get(v_x_943_, 0);
v_tail_945_ = lean_ctor_get(v_x_943_, 1);
lean_inc_ref_n(v_env_940_, 2);
v___x_946_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_940_, v_head_944_, v_x_941_);
v___x_947_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_940_, v_x_942_, v___x_946_);
v_x_942_ = v___x_947_;
v_x_943_ = v_tail_945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0___boxed(lean_object* v_env_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_949_, v_x_950_, v_x_951_, v_x_952_);
lean_dec(v_x_952_);
lean_dec(v_x_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj___boxed(lean_object* v_env_954_, lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_954_, v_x_955_, v_x_956_);
lean_dec(v_x_956_);
lean_dec(v_x_955_);
return v_res_957_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_958_) == 2)
{
lean_object* v_vs_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_vs_959_ = lean_ctor_get(v_x_958_, 1);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_array_get_size(v_vs_959_);
v___x_962_ = lean_nat_dec_lt(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
uint8_t v___x_963_; 
v___x_963_ = 1;
return v___x_963_;
}
else
{
if (v___x_962_ == 0)
{
return v___x_962_;
}
else
{
size_t v___x_964_; size_t v___x_965_; uint8_t v___x_966_; 
v___x_964_ = ((size_t)0ULL);
v___x_965_ = lean_usize_of_nat(v___x_961_);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_vs_959_, v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
return v___x_962_;
}
else
{
uint8_t v___x_967_; 
v___x_967_ = 0;
return v___x_967_;
}
}
}
}
else
{
uint8_t v___x_968_; 
v___x_968_ = 0;
return v___x_968_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(lean_object* v_as_969_, size_t v_i_970_, size_t v_stop_971_){
_start:
{
uint8_t v___x_972_; 
v___x_972_ = lean_usize_dec_eq(v_i_970_, v_stop_971_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = 1;
v___x_974_ = lean_array_uget_borrowed(v_as_969_, v_i_970_);
v___x_975_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v___x_974_);
if (v___x_975_ == 0)
{
return v___x_973_;
}
else
{
if (v___x_972_ == 0)
{
size_t v___x_976_; size_t v___x_977_; 
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_add(v_i_970_, v___x_976_);
v_i_970_ = v___x_977_;
goto _start;
}
else
{
return v___x_973_;
}
}
}
else
{
uint8_t v___x_979_; 
v___x_979_ = 0;
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0___boxed(lean_object* v_as_980_, lean_object* v_i_981_, lean_object* v_stop_982_){
_start:
{
size_t v_i_boxed_983_; size_t v_stop_boxed_984_; uint8_t v_res_985_; lean_object* v_r_986_; 
v_i_boxed_983_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_stop_boxed_984_ = lean_unbox_usize(v_stop_982_);
lean_dec(v_stop_982_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_as_980_, v_i_boxed_983_, v_stop_boxed_984_);
lean_dec_ref(v_as_980_);
v_r_986_ = lean_box(v_res_985_);
return v_r_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral___boxed(lean_object* v_x_987_){
_start:
{
uint8_t v_res_988_; lean_object* v_r_989_; 
v_res_988_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_x_987_);
lean_dec(v_x_987_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(lean_object* v_msg_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_panic_fn_borrowed(v___x_991_, v_msg_990_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1));
v___x_996_ = lean_unsigned_to_nat(9u);
v___x_997_ = lean_unsigned_to_nat(279u);
v___x_998_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0));
v___x_999_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0));
v___x_1000_ = l_mkPanicMessageWithDecl(v___x_999_, v___x_998_, v___x_997_, v___x_996_, v___x_995_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(lean_object* v_a_1001_){
_start:
{
if (lean_obj_tag(v_a_1001_) == 2)
{
lean_object* v_i_1005_; 
v_i_1005_ = lean_ctor_get(v_a_1001_, 0);
if (lean_obj_tag(v_i_1005_) == 1)
{
lean_object* v_pre_1006_; 
v_pre_1006_ = lean_ctor_get(v_i_1005_, 0);
if (lean_obj_tag(v_pre_1006_) == 1)
{
lean_object* v_pre_1007_; 
v_pre_1007_ = lean_ctor_get(v_pre_1006_, 0);
if (lean_obj_tag(v_pre_1007_) == 0)
{
lean_object* v_vs_1008_; lean_object* v_str_1009_; lean_object* v_str_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_vs_1008_ = lean_ctor_get(v_a_1001_, 1);
v_str_1009_ = lean_ctor_get(v_i_1005_, 1);
v_str_1010_ = lean_ctor_get(v_pre_1006_, 1);
v___x_1011_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5));
v___x_1012_ = lean_string_dec_eq(v_str_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
goto v___jp_1002_;
}
else
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__6));
v___x_1014_ = lean_string_dec_eq(v_str_1009_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__7));
v___x_1016_ = lean_string_dec_eq(v_str_1009_, v___x_1015_);
if (v___x_1016_ == 0)
{
goto v___jp_1002_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1017_ = lean_array_get_size(v_vs_1008_);
v___x_1018_ = lean_unsigned_to_nat(1u);
v___x_1019_ = lean_nat_dec_eq(v___x_1017_, v___x_1018_);
if (v___x_1019_ == 0)
{
goto v___jp_1002_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_array_fget_borrowed(v_vs_1008_, v___x_1020_);
v___x_1022_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_1021_);
v___x_1023_ = lean_nat_add(v___x_1022_, v___x_1018_);
lean_dec(v___x_1022_);
return v___x_1023_;
}
}
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1024_ = lean_array_get_size(v_vs_1008_);
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_nat_dec_eq(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
goto v___jp_1002_;
}
else
{
return v___x_1025_;
}
}
}
}
else
{
goto v___jp_1002_;
}
}
else
{
goto v___jp_1002_;
}
}
else
{
goto v___jp_1002_;
}
}
else
{
goto v___jp_1002_;
}
v___jp_1002_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2);
v___x_1004_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(v___x_1003_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___boxed(lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v_a_1027_);
lean_dec(v_a_1027_);
return v_res_1028_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_instMonadEIO(lean_box(0));
return v___x_1029_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Array_instInhabited(lean_box(0));
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object* v_msg_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_toApplicative_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1076_; 
v___x_1039_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__0);
v___x_1040_ = l_StateRefT_x27_instMonad___redArg(v___x_1039_);
v_toApplicative_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v___x_1040_, 1);
lean_dec(v_unused_1077_);
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1076_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_toApplicative_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1076_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_toFunctor_1045_; lean_object* v_toSeq_1046_; lean_object* v_toSeqLeft_1047_; lean_object* v_toSeqRight_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1074_; 
v_toFunctor_1045_ = lean_ctor_get(v_toApplicative_1041_, 0);
v_toSeq_1046_ = lean_ctor_get(v_toApplicative_1041_, 2);
v_toSeqLeft_1047_ = lean_ctor_get(v_toApplicative_1041_, 3);
v_toSeqRight_1048_ = lean_ctor_get(v_toApplicative_1041_, 4);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_toApplicative_1041_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v_toApplicative_1041_, 1);
lean_dec(v_unused_1075_);
v___x_1050_ = v_toApplicative_1041_;
v_isShared_1051_ = v_isSharedCheck_1074_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_toSeqRight_1048_);
lean_inc(v_toSeqLeft_1047_);
lean_inc(v_toSeq_1046_);
lean_inc(v_toFunctor_1045_);
lean_dec(v_toApplicative_1041_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1074_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___x_1061_; 
v___f_1052_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__1));
v___f_1053_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_1045_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toFunctor_1045_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toFunctor_1045_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___f_1054_);
lean_ctor_set(v___x_1056_, 1, v___f_1055_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toSeqRight_1048_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toSeqLeft_1047_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toSeq_1046_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 4, v___f_1057_);
lean_ctor_set(v___x_1050_, 3, v___f_1058_);
lean_ctor_set(v___x_1050_, 2, v___f_1059_);
lean_ctor_set(v___x_1050_, 1, v___f_1052_);
lean_ctor_set(v___x_1050_, 0, v___x_1056_);
v___x_1061_ = v___x_1050_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___f_1052_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v___f_1059_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v___f_1058_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v___f_1057_);
v___x_1061_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___f_1053_);
lean_ctor_set(v___x_1043_, 0, v___x_1061_);
v___x_1063_ = v___x_1043_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___f_1053_);
v___x_1063_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_2391__overap_1070_; lean_object* v___x_1071_; 
v___x_1064_ = l_StateRefT_x27_instMonad___redArg(v___x_1063_);
v___x_1065_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___closed__3);
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l_instInhabitedOfMonad___redArg(v___x_1064_, v___x_1067_);
v___f_1069_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
v___x_2391__overap_1070_ = lean_panic_fn_borrowed(v___f_1069_, v_msg_1033_);
lean_dec_ref(v___f_1069_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
v___x_1071_ = lean_apply_5(v___x_2391__overap_1070_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, lean_box(0));
return v___x_1071_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object* v_msg_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_msg_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(lean_object* v_as_1085_, size_t v_i_1086_, size_t v_stop_1087_, lean_object* v_b_1088_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_usize_dec_eq(v_i_1086_, v_stop_1087_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1107_; 
v___x_1090_ = lean_array_uget_borrowed(v_as_1085_, v_i_1086_);
v_fst_1091_ = lean_ctor_get(v___x_1090_, 0);
v_snd_1092_ = lean_ctor_get(v___x_1090_, 1);
v_fst_1093_ = lean_ctor_get(v_b_1088_, 0);
v_snd_1094_ = lean_ctor_get(v_b_1088_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_b_1088_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1096_ = v_b_1088_;
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_inc(v_fst_1093_);
lean_dec(v_b_1088_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1098_ = l_Array_append___redArg(v_fst_1093_, v_fst_1091_);
lean_inc(v_snd_1092_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_snd_1092_);
v___x_1100_ = lean_array_push(v_snd_1094_, v___x_1099_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1100_);
lean_ctor_set(v___x_1096_, 0, v___x_1098_);
v___x_1102_ = v___x_1096_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
size_t v___x_1103_; size_t v___x_1104_; 
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_add(v_i_1086_, v___x_1103_);
v_i_1086_ = v___x_1104_;
v_b_1088_ = v___x_1102_;
goto _start;
}
}
}
else
{
return v_b_1088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object* v_as_1108_, lean_object* v_i_1109_, lean_object* v_stop_1110_, lean_object* v_b_1111_){
_start:
{
size_t v_i_boxed_1112_; size_t v_stop_boxed_1113_; lean_object* v_res_1114_; 
v_i_boxed_1112_ = lean_unbox_usize(v_i_1109_);
lean_dec(v_i_1109_);
v_stop_boxed_1113_ = lean_unbox_usize(v_stop_1110_);
lean_dec(v_stop_1110_);
v_res_1114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_as_1108_, v_i_boxed_1112_, v_stop_boxed_1113_, v_b_1111_);
lean_dec_ref(v_as_1108_);
return v_res_1114_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1116_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2));
v___x_1117_ = lean_unsigned_to_nat(69u);
v___x_1118_ = lean_unsigned_to_nat(266u);
v___x_1119_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0));
v___x_1120_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0));
v___x_1121_ = l_mkPanicMessageWithDecl(v___x_1120_, v___x_1119_, v___x_1118_, v___x_1117_, v___x_1116_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2));
v___x_1132_ = lean_unsigned_to_nat(9u);
v___x_1133_ = lean_unsigned_to_nat(274u);
v___x_1134_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__0));
v___x_1135_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__0));
v___x_1136_ = l_mkPanicMessageWithDecl(v___x_1135_, v___x_1134_, v___x_1133_, v___x_1132_, v___x_1131_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v_val_1199_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; 
if (lean_obj_tag(v_a_1137_) == 2)
{
lean_object* v_i_1243_; lean_object* v_vs_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1341_; 
v_i_1243_ = lean_ctor_get(v_a_1137_, 0);
v_vs_1244_ = lean_ctor_get(v_a_1137_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_a_1137_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1246_ = v_a_1137_;
v_isShared_1247_ = v_isSharedCheck_1341_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_vs_1244_);
lean_inc(v_i_1243_);
lean_dec(v_a_1137_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1341_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_ctorName_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; 
if (lean_obj_tag(v_i_1243_) == 1)
{
lean_object* v_pre_1259_; 
v_pre_1259_ = lean_ctor_get(v_i_1243_, 0);
if (lean_obj_tag(v_pre_1259_) == 1)
{
lean_object* v_pre_1260_; 
v_pre_1260_ = lean_ctor_get(v_pre_1259_, 0);
if (lean_obj_tag(v_pre_1260_) == 0)
{
lean_object* v_str_1261_; lean_object* v_str_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_str_1261_ = lean_ctor_get(v_i_1243_, 1);
v_str_1262_ = lean_ctor_get(v_pre_1259_, 1);
v___x_1263_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__5));
v___x_1264_ = lean_string_dec_eq(v_str_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_del_object(v___x_1246_);
v_ctorName_1249_ = v_i_1243_;
v___y_1250_ = v_a_1138_;
v___y_1251_ = v_a_1139_;
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
lean_inc_ref(v_str_1261_);
lean_inc(v_pre_1260_);
lean_dec_ref_known(v_i_1243_, 2);
v___x_1265_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__6));
v___x_1266_ = lean_string_dec_eq(v_str_1261_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__7));
v___x_1268_ = lean_string_dec_eq(v_str_1261_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_del_object(v___x_1246_);
v___x_1269_ = l_Lean_Name_str___override(v_pre_1260_, v___x_1263_);
v___x_1270_ = l_Lean_Name_str___override(v___x_1269_, v_str_1261_);
v_ctorName_1249_ = v___x_1270_;
v___y_1250_ = v_a_1138_;
v___y_1251_ = v_a_1139_;
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
lean_dec_ref(v_str_1261_);
v___x_1271_ = lean_array_get_size(v_vs_1244_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_del_object(v___x_1246_);
v___x_1274_ = l_Lean_Name_str___override(v_pre_1260_, v___x_1263_);
v___x_1275_ = l_Lean_Name_str___override(v___x_1274_, v___x_1267_);
v_ctorName_1249_ = v___x_1275_;
v___y_1250_ = v_a_1138_;
v___y_1251_ = v_a_1139_;
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_val_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = lean_array_fget(v_vs_1244_, v___x_1276_);
lean_dec_ref(v_vs_1244_);
v___x_1278_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_1277_);
lean_dec(v___x_1277_);
v_val_1279_ = lean_nat_add(v___x_1278_, v___x_1272_);
lean_dec(v___x_1278_);
v___x_1280_ = 0;
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_val_1279_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
v___x_1283_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3));
v___x_1284_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1280_, v___x_1282_, v___x_1283_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1299_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1299_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1299_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_fvarId_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v_fvarId_1289_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_fvarId_1289_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_a_1285_);
v___x_1291_ = lean_mk_empty_array_with_capacity(v___x_1272_);
v___x_1292_ = lean_array_push(v___x_1291_, v___x_1290_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 0);
lean_ctor_set(v___x_1246_, 1, v_fvarId_1289_);
lean_ctor_set(v___x_1246_, 0, v___x_1292_);
v___x_1294_ = v___x_1246_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_fvarId_1289_);
v___x_1294_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1294_);
v___x_1296_ = v___x_1287_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
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
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_del_object(v___x_1246_);
v_a_1300_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1284_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1284_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
lean_dec_ref(v_str_1261_);
v___x_1308_ = lean_array_get_size(v_vs_1244_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_nat_dec_eq(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_del_object(v___x_1246_);
v___x_1311_ = l_Lean_Name_str___override(v_pre_1260_, v___x_1263_);
v___x_1312_ = l_Lean_Name_str___override(v___x_1311_, v___x_1265_);
v_ctorName_1249_ = v___x_1312_;
v___y_1250_ = v_a_1138_;
v___y_1251_ = v_a_1139_;
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
goto v___jp_1248_;
}
else
{
uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref(v_vs_1244_);
v___x_1313_ = 0;
v___x_1314_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6));
v___x_1315_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3));
v___x_1316_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1313_, v___x_1314_, v___x_1315_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1332_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_fvarId_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_fvarId_1321_ = lean_ctor_get(v_a_1317_, 0);
lean_inc(v_fvarId_1321_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_a_1317_);
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_mk_empty_array_with_capacity(v___x_1323_);
v___x_1325_ = lean_array_push(v___x_1324_, v___x_1322_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 0);
lean_ctor_set(v___x_1246_, 1, v_fvarId_1321_);
lean_ctor_set(v___x_1246_, 0, v___x_1325_);
v___x_1327_ = v___x_1246_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_fvarId_1321_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1327_);
v___x_1329_ = v___x_1319_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_del_object(v___x_1246_);
v_a_1333_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1316_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1316_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1246_);
v_ctorName_1249_ = v_i_1243_;
v___y_1250_ = v_a_1138_;
v___y_1251_ = v_a_1139_;
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
goto v___jp_1248_;
}
}
else
{
lean_del_object(v___x_1246_);
v_ctorName_1249_ = v_i_1243_;
v___y_1250_ = v_a_1138_;
v___y_1251_ = v_a_1139_;
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
goto v___jp_1248_;
}
}
else
{
lean_del_object(v___x_1246_);
v_ctorName_1249_ = v_i_1243_;
v___y_1250_ = v_a_1138_;
v___y_1251_ = v_a_1139_;
v___y_1252_ = v_a_1140_;
v___y_1253_ = v_a_1141_;
goto v___jp_1248_;
}
v___jp_1248_:
{
lean_object* v___x_1254_; lean_object* v_env_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_st_ref_get(v___y_1253_);
v_env_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc_ref_n(v_env_1255_, 2);
lean_dec(v___x_1254_);
lean_inc(v_ctorName_1249_);
v___x_1256_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_1255_, v_ctorName_1249_);
if (lean_obj_tag(v___x_1256_) == 1)
{
lean_object* v_val_1257_; 
v_val_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v___x_1256_, 1);
if (lean_obj_tag(v_val_1257_) == 2)
{
lean_object* v_info_1258_; 
lean_dec_ref(v_env_1255_);
v_info_1258_ = lean_ctor_get(v_val_1257_, 1);
lean_inc_ref(v_info_1258_);
lean_dec_ref_known(v_val_1257_, 2);
v___y_1193_ = v_ctorName_1249_;
v___y_1194_ = v_vs_1244_;
v___y_1195_ = v___y_1252_;
v___y_1196_ = v___y_1250_;
v___y_1197_ = v___y_1253_;
v___y_1198_ = v___y_1251_;
v_val_1199_ = v_info_1258_;
goto v___jp_1192_;
}
else
{
lean_dec(v_val_1257_);
v___y_1226_ = v_env_1255_;
v___y_1227_ = v_ctorName_1249_;
v___y_1228_ = v_vs_1244_;
v___y_1229_ = v___y_1252_;
v___y_1230_ = v___y_1250_;
v___y_1231_ = v___y_1253_;
v___y_1232_ = v___y_1251_;
goto v___jp_1225_;
}
}
else
{
lean_dec(v___x_1256_);
v___y_1226_ = v_env_1255_;
v___y_1227_ = v_ctorName_1249_;
v___y_1228_ = v_vs_1244_;
v___y_1229_ = v___y_1252_;
v___y_1230_ = v___y_1250_;
v___y_1231_ = v___y_1253_;
v___y_1232_ = v___y_1251_;
goto v___jp_1225_;
}
}
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_a_1137_);
v___x_1342_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7);
v___x_1343_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v___x_1342_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
return v___x_1343_;
}
v___jp_1143_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1);
v___x_1149_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v___x_1148_, v___y_1145_, v___y_1147_, v___y_1144_, v___y_1146_);
return v___x_1149_;
}
v___jp_1150_:
{
uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1158_ = 0;
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1160_, 0, v___y_1151_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
lean_ctor_set(v___x_1160_, 2, v_snd_1157_);
v___x_1161_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3));
v___x_1162_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1158_, v___x_1160_, v___x_1161_, v___y_1153_, v___y_1155_, v___y_1152_, v___y_1154_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1174_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fvarId_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v_fvarId_1167_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_fvarId_1167_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1163_);
v___x_1169_ = lean_array_push(v_fst_1156_, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_fvarId_1167_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1170_);
v___x_1172_ = v___x_1165_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_fst_1156_);
v_a_1175_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1162_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1162_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
v___jp_1183_:
{
lean_object* v_fst_1190_; lean_object* v_snd_1191_; 
v_fst_1190_ = lean_ctor_get(v___y_1189_, 0);
lean_inc(v_fst_1190_);
v_snd_1191_ = lean_ctor_get(v___y_1189_, 1);
lean_inc(v_snd_1191_);
lean_dec_ref(v___y_1189_);
v___y_1151_ = v___y_1184_;
v___y_1152_ = v___y_1185_;
v___y_1153_ = v___y_1186_;
v___y_1154_ = v___y_1187_;
v___y_1155_ = v___y_1188_;
v_fst_1156_ = v_fst_1190_;
v_snd_1157_ = v_snd_1191_;
goto v___jp_1150_;
}
v___jp_1192_:
{
size_t v_sz_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v_sz_1200_ = lean_array_size(v___y_1194_);
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v_sz_1200_, v___x_1201_, v___y_1194_, v___y_1196_, v___y_1198_, v___y_1195_, v___y_1197_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_numParams_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v_numParams_1204_ = lean_ctor_get(v_val_1199_, 2);
lean_inc(v_numParams_1204_);
lean_dec_ref(v_val_1199_);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4));
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_mk_array(v_numParams_1204_, v___x_1207_);
v___x_1209_ = lean_array_get_size(v_a_1203_);
v___x_1210_ = lean_nat_dec_lt(v___x_1205_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_dec(v_a_1203_);
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1195_;
v___y_1153_ = v___y_1196_;
v___y_1154_ = v___y_1197_;
v___y_1155_ = v___y_1198_;
v_fst_1156_ = v___x_1206_;
v_snd_1157_ = v___x_1208_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
lean_inc_ref(v___x_1208_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1206_);
lean_ctor_set(v___x_1211_, 1, v___x_1208_);
v___x_1212_ = lean_nat_dec_le(v___x_1209_, v___x_1209_);
if (v___x_1212_ == 0)
{
if (v___x_1210_ == 0)
{
lean_dec_ref_known(v___x_1211_, 2);
lean_dec(v_a_1203_);
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1195_;
v___y_1153_ = v___y_1196_;
v___y_1154_ = v___y_1197_;
v___y_1155_ = v___y_1198_;
v_fst_1156_ = v___x_1206_;
v_snd_1157_ = v___x_1208_;
goto v___jp_1150_;
}
else
{
size_t v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref(v___x_1208_);
v___x_1213_ = lean_usize_of_nat(v___x_1209_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_a_1203_, v___x_1201_, v___x_1213_, v___x_1211_);
lean_dec(v_a_1203_);
v___y_1184_ = v___y_1193_;
v___y_1185_ = v___y_1195_;
v___y_1186_ = v___y_1196_;
v___y_1187_ = v___y_1197_;
v___y_1188_ = v___y_1198_;
v___y_1189_ = v___x_1214_;
goto v___jp_1183_;
}
}
else
{
size_t v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v___x_1208_);
v___x_1215_ = lean_usize_of_nat(v___x_1209_);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_a_1203_, v___x_1201_, v___x_1215_, v___x_1211_);
lean_dec(v_a_1203_);
v___y_1184_ = v___y_1193_;
v___y_1185_ = v___y_1195_;
v___y_1186_ = v___y_1196_;
v___y_1187_ = v___y_1197_;
v___y_1188_ = v___y_1198_;
v___y_1189_ = v___x_1216_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_val_1199_);
lean_dec(v___y_1193_);
v_a_1217_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1202_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1202_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
v___jp_1225_:
{
uint8_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = 0;
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
v___x_1234_ = l_Lean_Environment_find_x3f(v___y_1226_, v___y_1227_, v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
v___y_1144_ = v___y_1229_;
v___y_1145_ = v___y_1230_;
v___y_1146_ = v___y_1231_;
v___y_1147_ = v___y_1232_;
goto v___jp_1143_;
}
else
{
lean_object* v_val_1235_; 
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v___x_1234_, 1);
if (lean_obj_tag(v_val_1235_) == 6)
{
lean_object* v_val_1236_; lean_object* v_induct_1237_; lean_object* v_cidx_1238_; lean_object* v_numParams_1239_; lean_object* v_numFields_1240_; uint8_t v___x_1241_; 
v_val_1236_ = lean_ctor_get(v_val_1235_, 0);
lean_inc_ref(v_val_1236_);
lean_dec_ref_known(v_val_1235_, 1);
v_induct_1237_ = lean_ctor_get(v_val_1236_, 1);
lean_inc_n(v_induct_1237_, 2);
v_cidx_1238_ = lean_ctor_get(v_val_1236_, 2);
lean_inc(v_cidx_1238_);
v_numParams_1239_ = lean_ctor_get(v_val_1236_, 3);
lean_inc(v_numParams_1239_);
v_numFields_1240_ = lean_ctor_get(v_val_1236_, 4);
lean_inc(v_numFields_1240_);
lean_dec_ref(v_val_1236_);
v___x_1241_ = l_Lean_Compiler_hasInductiveOverride(v___y_1226_, v_induct_1237_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1242_, 0, v_induct_1237_);
lean_ctor_set(v___x_1242_, 1, v_cidx_1238_);
lean_ctor_set(v___x_1242_, 2, v_numParams_1239_);
lean_ctor_set(v___x_1242_, 3, v_numFields_1240_);
v___y_1193_ = v___y_1227_;
v___y_1194_ = v___y_1228_;
v___y_1195_ = v___y_1229_;
v___y_1196_ = v___y_1230_;
v___y_1197_ = v___y_1231_;
v___y_1198_ = v___y_1232_;
v_val_1199_ = v___x_1242_;
goto v___jp_1192_;
}
else
{
lean_dec(v_numFields_1240_);
lean_dec(v_numParams_1239_);
lean_dec(v_cidx_1238_);
lean_dec(v_induct_1237_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
v___y_1144_ = v___y_1229_;
v___y_1145_ = v___y_1230_;
v___y_1146_ = v___y_1231_;
v___y_1147_ = v___y_1232_;
goto v___jp_1143_;
}
}
else
{
lean_dec(v_val_1235_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
v___y_1144_ = v___y_1229_;
v___y_1145_ = v___y_1230_;
v___y_1146_ = v___y_1231_;
v___y_1147_ = v___y_1232_;
goto v___jp_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(size_t v_sz_1344_, size_t v_i_1345_, lean_object* v_bs_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_usize_dec_lt(v_i_1345_, v_sz_1344_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_bs_1346_);
return v___x_1353_;
}
else
{
lean_object* v_v_1354_; lean_object* v___x_1355_; 
v_v_1354_ = lean_array_uget_borrowed(v_bs_1346_, v_i_1345_);
lean_inc(v_v_1354_);
v___x_1355_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1354_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; lean_object* v_bs_x27_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = lean_unsigned_to_nat(0u);
v_bs_x27_1358_ = lean_array_uset(v_bs_1346_, v_i_1345_, v___x_1357_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_i_1345_, v___x_1359_);
v___x_1361_ = lean_array_uset(v_bs_x27_1358_, v_i_1345_, v_a_1356_);
v_i_1345_ = v___x_1360_;
v_bs_1346_ = v___x_1361_;
goto _start;
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v_bs_1346_);
v_a_1363_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1355_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1355_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object* v_sz_1371_, lean_object* v_i_1372_, lean_object* v_bs_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
size_t v_sz_boxed_1379_; size_t v_i_boxed_1380_; lean_object* v_res_1381_; 
v_sz_boxed_1379_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v_i_boxed_1380_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_res_1381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v_sz_boxed_1379_, v_i_boxed_1380_, v_bs_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(lean_object* v_v_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_v_1389_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec(v_v_1389_);
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_a_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1398_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral___boxed(lean_object* v_v_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_v_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(lean_object* v_a_1423_, lean_object* v_b_1424_){
_start:
{
lean_object* v_fst_1425_; lean_object* v_fst_1426_; uint8_t v___x_1427_; 
v_fst_1425_ = lean_ctor_get(v_a_1423_, 0);
v_fst_1426_ = lean_ctor_get(v_b_1424_, 0);
v___x_1427_ = l_Lean_Name_quickLt(v_fst_1425_, v_fst_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed(lean_object* v_a_1428_, lean_object* v_b_1429_){
_start:
{
uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_res_1430_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(v_a_1428_, v_b_1429_);
lean_dec_ref(v_b_1429_);
lean_dec_ref(v_a_1428_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(lean_object* v_entries_1434_, lean_object* v_fid_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_array_get_size(v_entries_1434_);
v___x_1438_ = lean_nat_dec_lt(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_dec(v_fid_1435_);
v___x_1439_ = lean_box(0);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_sub(v___x_1437_, v___x_1440_);
v___x_1442_ = lean_nat_dec_le(v___x_1436_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v___x_1441_);
lean_dec(v_fid_1435_);
v___x_1443_ = lean_box(0);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_fid_1435_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0));
v___x_1447_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1));
v___x_1448_ = l_Array_binSearchAux___redArg(v___x_1446_, v___x_1447_, v_entries_1434_, v___x_1445_, v___x_1436_, v___x_1441_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
else
{
lean_object* v_val_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_val_1450_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v___x_1448_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_val_1450_);
lean_dec(v___x_1448_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_snd_1454_; lean_object* v___x_1456_; 
v_snd_1454_ = lean_ctor_get(v_val_1450_, 1);
lean_inc(v_snd_1454_);
lean_dec(v_val_1450_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_snd_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_snd_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___boxed(lean_object* v_entries_1459_, lean_object* v_fid_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(v_entries_1459_, v_fid_1460_);
lean_dec_ref(v_entries_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_es_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_array_mk(v_es_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1464_, lean_object* v_i_1465_, lean_object* v_k_1466_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_array_get_size(v_keys_1464_);
v___x_1468_ = lean_nat_dec_lt(v_i_1465_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_dec(v_i_1465_);
return v___x_1468_;
}
else
{
lean_object* v_k_x27_1469_; uint8_t v___x_1470_; 
v_k_x27_1469_ = lean_array_fget_borrowed(v_keys_1464_, v_i_1465_);
v___x_1470_ = lean_name_eq(v_k_1466_, v_k_x27_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_unsigned_to_nat(1u);
v___x_1472_ = lean_nat_add(v_i_1465_, v___x_1471_);
lean_dec(v_i_1465_);
v_i_1465_ = v___x_1472_;
goto _start;
}
else
{
lean_dec(v_i_1465_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1474_, lean_object* v_i_1475_, lean_object* v_k_1476_){
_start:
{
uint8_t v_res_1477_; lean_object* v_r_1478_; 
v_res_1477_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1474_, v_i_1475_, v_k_1476_);
lean_dec(v_k_1476_);
lean_dec_ref(v_keys_1474_);
v_r_1478_ = lean_box(v_res_1477_);
return v_r_1478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1479_, size_t v_x_1480_, lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1479_) == 0)
{
lean_object* v_es_1482_; lean_object* v___x_1483_; size_t v___x_1484_; size_t v___x_1485_; lean_object* v_j_1486_; lean_object* v___x_1487_; 
v_es_1482_ = lean_ctor_get(v_x_1479_, 0);
v___x_1483_ = lean_box(2);
v___x_1484_ = ((size_t)31ULL);
v___x_1485_ = lean_usize_land(v_x_1480_, v___x_1484_);
v_j_1486_ = lean_usize_to_nat(v___x_1485_);
v___x_1487_ = lean_array_get_borrowed(v___x_1483_, v_es_1482_, v_j_1486_);
lean_dec(v_j_1486_);
switch(lean_obj_tag(v___x_1487_))
{
case 0:
{
lean_object* v_key_1488_; uint8_t v___x_1489_; 
v_key_1488_ = lean_ctor_get(v___x_1487_, 0);
v___x_1489_ = lean_name_eq(v_x_1481_, v_key_1488_);
return v___x_1489_;
}
case 1:
{
lean_object* v_node_1490_; size_t v___x_1491_; size_t v___x_1492_; 
v_node_1490_ = lean_ctor_get(v___x_1487_, 0);
v___x_1491_ = ((size_t)5ULL);
v___x_1492_ = lean_usize_shift_right(v_x_1480_, v___x_1491_);
v_x_1479_ = v_node_1490_;
v_x_1480_ = v___x_1492_;
goto _start;
}
default: 
{
uint8_t v___x_1494_; 
v___x_1494_ = 0;
return v___x_1494_;
}
}
}
else
{
lean_object* v_ks_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v_ks_1495_ = lean_ctor_get(v_x_1479_, 0);
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1495_, v___x_1496_, v_x_1481_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
size_t v_x_1163__boxed_1501_; uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_x_1163__boxed_1501_ = lean_unbox_usize(v_x_1499_);
lean_dec(v_x_1499_);
v_res_1502_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1498_, v_x_1163__boxed_1501_, v_x_1500_);
lean_dec(v_x_1500_);
lean_dec_ref(v_x_1498_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1504_; uint64_t v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(1723u);
v___x_1505_ = lean_uint64_of_nat(v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
uint64_t v___y_1509_; 
if (lean_obj_tag(v_x_1507_) == 0)
{
uint64_t v___x_1512_; 
v___x_1512_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1509_ = v___x_1512_;
goto v___jp_1508_;
}
else
{
uint64_t v_hash_1513_; 
v_hash_1513_ = lean_ctor_get_uint64(v_x_1507_, sizeof(void*)*2);
v___y_1509_ = v_hash_1513_;
goto v___jp_1508_;
}
v___jp_1508_:
{
size_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = lean_uint64_to_usize(v___y_1509_);
v___x_1511_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1506_, v___x_1510_, v_x_1507_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1514_, v_x_1515_);
lean_dec(v_x_1515_);
lean_dec_ref(v_x_1514_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x1_1518_, lean_object* v_x2_1519_){
_start:
{
lean_object* v_fst_1520_; uint8_t v___x_1521_; 
v_fst_1520_ = lean_ctor_get(v_x2_1519_, 0);
v___x_1521_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x1_1518_, v_fst_1520_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; 
v___x_1522_ = 1;
return v___x_1522_;
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = 0;
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x1_1524_, lean_object* v_x2_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x1_1524_, v_x2_1525_);
lean_dec_ref(v_x2_1525_);
lean_dec_ref(v_x1_1524_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_f_1528_, lean_object* v_keys_1529_, lean_object* v_vals_1530_, lean_object* v_i_1531_, lean_object* v_acc_1532_){
_start:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_array_get_size(v_keys_1529_);
v___x_1534_ = lean_nat_dec_lt(v_i_1531_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_dec(v_i_1531_);
lean_dec(v_f_1528_);
return v_acc_1532_;
}
else
{
lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_k_1535_ = lean_array_fget_borrowed(v_keys_1529_, v_i_1531_);
v_v_1536_ = lean_array_fget_borrowed(v_vals_1530_, v_i_1531_);
lean_inc(v_f_1528_);
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
v___x_1537_ = lean_apply_3(v_f_1528_, v_acc_1532_, v_k_1535_, v_v_1536_);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_add(v_i_1531_, v___x_1538_);
lean_dec(v_i_1531_);
v_i_1531_ = v___x_1539_;
v_acc_1532_ = v___x_1537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_f_1541_, lean_object* v_keys_1542_, lean_object* v_vals_1543_, lean_object* v_i_1544_, lean_object* v_acc_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1541_, v_keys_1542_, v_vals_1543_, v_i_1544_, v_acc_1545_);
lean_dec_ref(v_vals_1543_);
lean_dec_ref(v_keys_1542_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_){
_start:
{
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v_es_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_es_1550_ = lean_ctor_get(v_x_1548_, 0);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = lean_array_get_size(v_es_1550_);
v___x_1553_ = lean_nat_dec_lt(v___x_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec(v_f_1547_);
return v_x_1549_;
}
else
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_nat_dec_le(v___x_1552_, v___x_1552_);
if (v___x_1554_ == 0)
{
if (v___x_1553_ == 0)
{
lean_dec(v_f_1547_);
return v_x_1549_;
}
else
{
size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = lean_usize_of_nat(v___x_1552_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1547_, v_es_1550_, v___x_1555_, v___x_1556_, v_x_1549_);
return v___x_1557_;
}
}
else
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = ((size_t)0ULL);
v___x_1559_ = lean_usize_of_nat(v___x_1552_);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1547_, v_es_1550_, v___x_1558_, v___x_1559_, v_x_1549_);
return v___x_1560_;
}
}
}
else
{
lean_object* v_ks_1561_; lean_object* v_vs_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_ks_1561_ = lean_ctor_get(v_x_1548_, 0);
v_vs_1562_ = lean_ctor_get(v_x_1548_, 1);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1547_, v_ks_1561_, v_vs_1562_, v___x_1563_, v_x_1549_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1565_, lean_object* v_as_1566_, size_t v_i_1567_, size_t v_stop_1568_, lean_object* v_b_1569_){
_start:
{
lean_object* v___y_1571_; uint8_t v___x_1575_; 
v___x_1575_ = lean_usize_dec_eq(v_i_1567_, v_stop_1568_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_array_uget_borrowed(v_as_1566_, v_i_1567_);
switch(lean_obj_tag(v___x_1576_))
{
case 0:
{
lean_object* v_key_1577_; lean_object* v_val_1578_; lean_object* v___x_1579_; 
v_key_1577_ = lean_ctor_get(v___x_1576_, 0);
v_val_1578_ = lean_ctor_get(v___x_1576_, 1);
lean_inc(v_f_1565_);
lean_inc(v_val_1578_);
lean_inc(v_key_1577_);
v___x_1579_ = lean_apply_3(v_f_1565_, v_b_1569_, v_key_1577_, v_val_1578_);
v___y_1571_ = v___x_1579_;
goto v___jp_1570_;
}
case 1:
{
lean_object* v_node_1580_; lean_object* v___x_1581_; 
v_node_1580_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_f_1565_);
v___x_1581_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1565_, v_node_1580_, v_b_1569_);
v___y_1571_ = v___x_1581_;
goto v___jp_1570_;
}
default: 
{
v___y_1571_ = v_b_1569_;
goto v___jp_1570_;
}
}
}
else
{
lean_dec(v_f_1565_);
return v_b_1569_;
}
v___jp_1570_:
{
size_t v___x_1572_; size_t v___x_1573_; 
v___x_1572_ = ((size_t)1ULL);
v___x_1573_ = lean_usize_add(v_i_1567_, v___x_1572_);
v_i_1567_ = v___x_1573_;
v_b_1569_ = v___y_1571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1582_, lean_object* v_as_1583_, lean_object* v_i_1584_, lean_object* v_stop_1585_, lean_object* v_b_1586_){
_start:
{
size_t v_i_boxed_1587_; size_t v_stop_boxed_1588_; lean_object* v_res_1589_; 
v_i_boxed_1587_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_stop_boxed_1588_ = lean_unbox_usize(v_stop_1585_);
lean_dec(v_stop_1585_);
v_res_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1582_, v_as_1583_, v_i_boxed_1587_, v_stop_boxed_1588_, v_b_1586_);
lean_dec_ref(v_as_1583_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1590_, v_x_1591_, v_x_1592_);
lean_dec_ref(v_x_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1594_, lean_object* v_x1_1595_, lean_object* v_x2_1596_, lean_object* v_x3_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_apply_3(v_f_1594_, v_x1_1595_, v_x2_1596_, v_x3_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1599_, lean_object* v_f_1600_, lean_object* v_init_1601_){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1603_; 
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1602_, 0, v_f_1600_);
v___x_1603_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1602_, v_map_1599_, v_init_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1604_, lean_object* v_f_1605_, lean_object* v_init_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1604_, v_f_1605_, v_init_1606_);
lean_dec_ref(v_map_1604_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1608_, lean_object* v_k_1609_, lean_object* v_v_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_k_1609_);
lean_ctor_set(v___x_1611_, 1, v_v_1610_);
v___x_1612_ = lean_array_push(v_ps_1608_, v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1616_){
_start:
{
lean_object* v___f_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___f_1617_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1618_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1619_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1616_, v___f_1617_, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1620_);
lean_dec_ref(v_m_1620_);
return v_res_1621_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_fst_1624_; lean_object* v_fst_1625_; uint8_t v___x_1626_; 
v_fst_1624_ = lean_ctor_get(v___y_1622_, 0);
v_fst_1625_ = lean_ctor_get(v___y_1623_, 0);
v___x_1626_ = l_Lean_Name_quickLt(v_fst_1624_, v_fst_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1627_, v___y_1628_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v___y_1627_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_hi_1631_, lean_object* v_pivot_1632_, lean_object* v_as_1633_, lean_object* v_i_1634_, lean_object* v_k_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_nat_dec_lt(v_k_1635_, v_hi_1631_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec(v_k_1635_);
v___x_1637_ = lean_array_fswap(v_as_1633_, v_i_1634_, v_hi_1631_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_i_1634_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
return v___x_1638_;
}
else
{
lean_object* v___x_1639_; lean_object* v_fst_1640_; lean_object* v_fst_1641_; uint8_t v___x_1642_; 
v___x_1639_ = lean_array_fget_borrowed(v_as_1633_, v_k_1635_);
v_fst_1640_ = lean_ctor_get(v___x_1639_, 0);
v_fst_1641_ = lean_ctor_get(v_pivot_1632_, 0);
v___x_1642_ = l_Lean_Name_quickLt(v_fst_1640_, v_fst_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_add(v_k_1635_, v___x_1643_);
lean_dec(v_k_1635_);
v_k_1635_ = v___x_1644_;
goto _start;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1646_ = lean_array_fswap(v_as_1633_, v_i_1634_, v_k_1635_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_i_1634_, v___x_1647_);
lean_dec(v_i_1634_);
v___x_1649_ = lean_nat_add(v_k_1635_, v___x_1647_);
lean_dec(v_k_1635_);
v_as_1633_ = v___x_1646_;
v_i_1634_ = v___x_1648_;
v_k_1635_ = v___x_1649_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_hi_1651_, lean_object* v_pivot_1652_, lean_object* v_as_1653_, lean_object* v_i_1654_, lean_object* v_k_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1651_, v_pivot_1652_, v_as_1653_, v_i_1654_, v_k_1655_);
lean_dec_ref(v_pivot_1652_);
lean_dec(v_hi_1651_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_1657_, lean_object* v_as_1658_, lean_object* v_lo_1659_, lean_object* v_hi_1660_){
_start:
{
lean_object* v___y_1662_; uint8_t v___x_1672_; 
v___x_1672_ = lean_nat_dec_lt(v_lo_1659_, v_hi_1660_);
if (v___x_1672_ == 0)
{
lean_dec(v_lo_1659_);
return v_as_1658_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_mid_1675_; lean_object* v___y_1677_; lean_object* v___y_1683_; lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1673_ = lean_nat_add(v_lo_1659_, v_hi_1660_);
v___x_1674_ = lean_unsigned_to_nat(1u);
v_mid_1675_ = lean_nat_shiftr(v___x_1673_, v___x_1674_);
lean_dec(v___x_1673_);
v___x_1688_ = lean_array_fget_borrowed(v_as_1658_, v_mid_1675_);
v___x_1689_ = lean_array_fget_borrowed(v_as_1658_, v_lo_1659_);
v___x_1690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
v___y_1683_ = v_as_1658_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_array_fswap(v_as_1658_, v_lo_1659_, v_mid_1675_);
v___y_1683_ = v___x_1691_;
goto v___jp_1682_;
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = lean_array_fget_borrowed(v___y_1677_, v_mid_1675_);
v___x_1679_ = lean_array_fget_borrowed(v___y_1677_, v_hi_1660_);
v___x_1680_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_dec(v_mid_1675_);
v___y_1662_ = v___y_1677_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_array_fswap(v___y_1677_, v_mid_1675_, v_hi_1660_);
lean_dec(v_mid_1675_);
v___y_1662_ = v___x_1681_;
goto v___jp_1661_;
}
}
v___jp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1684_ = lean_array_fget_borrowed(v___y_1683_, v_hi_1660_);
v___x_1685_ = lean_array_fget_borrowed(v___y_1683_, v_lo_1659_);
v___x_1686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1684_, v___x_1685_);
if (v___x_1686_ == 0)
{
v___y_1677_ = v___y_1683_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_array_fswap(v___y_1683_, v_lo_1659_, v_hi_1660_);
v___y_1677_ = v___x_1687_;
goto v___jp_1676_;
}
}
}
v___jp_1661_:
{
lean_object* v_pivot_1663_; lean_object* v___x_1664_; lean_object* v_fst_1665_; lean_object* v_snd_1666_; uint8_t v___x_1667_; 
v_pivot_1663_ = lean_array_fget(v___y_1662_, v_hi_1660_);
lean_inc_n(v_lo_1659_, 2);
v___x_1664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1660_, v_pivot_1663_, v___y_1662_, v_lo_1659_, v_lo_1659_);
lean_dec(v_pivot_1663_);
v_fst_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_fst_1665_);
v_snd_1666_ = lean_ctor_get(v___x_1664_, 1);
lean_inc(v_snd_1666_);
lean_dec_ref(v___x_1664_);
v___x_1667_ = lean_nat_dec_le(v_hi_1660_, v_fst_1665_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1657_, v_snd_1666_, v_lo_1659_, v_fst_1665_);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v_fst_1665_, v___x_1669_);
lean_dec(v_fst_1665_);
v_as_1658_ = v___x_1668_;
v_lo_1659_ = v___x_1670_;
goto _start;
}
else
{
lean_dec(v_fst_1665_);
lean_dec(v_lo_1659_);
return v_snd_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_1692_, lean_object* v_as_1693_, lean_object* v_lo_1694_, lean_object* v_hi_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1692_, v_as_1693_, v_lo_1694_, v_hi_1695_);
lean_dec(v_hi_1695_);
lean_dec(v_n_1692_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1699_, lean_object* v_s_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___x_1711_; 
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1704_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1700_);
v___x_1705_ = lean_array_get_size(v___x_1704_);
v___x_1711_ = lean_nat_dec_eq(v___x_1705_, v___x_1702_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___y_1715_; uint8_t v___x_1717_; 
v___x_1712_ = lean_unsigned_to_nat(1u);
v___x_1713_ = lean_nat_sub(v___x_1705_, v___x_1712_);
v___x_1717_ = lean_nat_dec_le(v___x_1702_, v___x_1713_);
if (v___x_1717_ == 0)
{
lean_inc(v___x_1713_);
v___y_1715_ = v___x_1713_;
goto v___jp_1714_;
}
else
{
v___y_1715_ = v___x_1702_;
goto v___jp_1714_;
}
v___jp_1714_:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_nat_dec_le(v___y_1715_, v___x_1713_);
if (v___x_1716_ == 0)
{
lean_dec(v___x_1713_);
lean_inc(v___y_1715_);
v___y_1707_ = v___y_1715_;
v___y_1708_ = v___y_1715_;
goto v___jp_1706_;
}
else
{
v___y_1707_ = v___y_1715_;
v___y_1708_ = v___x_1713_;
goto v___jp_1706_;
}
}
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1703_);
lean_ctor_set(v___x_1718_, 1, v___x_1703_);
lean_ctor_set(v___x_1718_, 2, v___x_1704_);
return v___x_1718_;
}
v___jp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1705_, v___x_1704_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
v___x_1710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1703_);
lean_ctor_set(v___x_1710_, 1, v___x_1703_);
lean_ctor_set(v___x_1710_, 2, v___x_1709_);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1719_, lean_object* v_s_1720_, lean_object* v_x_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1719_, v_s_1720_, v_x_1721_);
lean_dec(v_x_1721_);
lean_dec_ref(v_s_1720_);
lean_dec_ref(v_x_1719_);
return v_res_1722_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1723_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1728_);
lean_dec_ref(v_x_1728_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
lean_object* v_ks_1734_; lean_object* v_vs_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1759_; 
v_ks_1734_ = lean_ctor_get(v_x_1730_, 0);
v_vs_1735_ = lean_ctor_get(v_x_1730_, 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_x_1730_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1737_ = v_x_1730_;
v_isShared_1738_ = v_isSharedCheck_1759_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_vs_1735_);
lean_inc(v_ks_1734_);
lean_dec(v_x_1730_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1759_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_array_get_size(v_ks_1734_);
v___x_1740_ = lean_nat_dec_lt(v_x_1731_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_dec(v_x_1731_);
v___x_1741_ = lean_array_push(v_ks_1734_, v_x_1732_);
v___x_1742_ = lean_array_push(v_vs_1735_, v_x_1733_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v___x_1742_);
lean_ctor_set(v___x_1737_, 0, v___x_1741_);
v___x_1744_ = v___x_1737_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
else
{
lean_object* v_k_x27_1746_; uint8_t v___x_1747_; 
v_k_x27_1746_ = lean_array_fget_borrowed(v_ks_1734_, v_x_1731_);
v___x_1747_ = lean_name_eq(v_x_1732_, v_k_x27_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1749_; 
if (v_isShared_1738_ == 0)
{
v___x_1749_ = v___x_1737_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_ks_1734_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_vs_1735_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_x_1731_, v___x_1750_);
lean_dec(v_x_1731_);
v_x_1730_ = v___x_1749_;
v_x_1731_ = v___x_1751_;
goto _start;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = lean_array_fset(v_ks_1734_, v_x_1731_, v_x_1732_);
v___x_1755_ = lean_array_fset(v_vs_1735_, v_x_1731_, v_x_1733_);
lean_dec(v_x_1731_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v___x_1755_);
lean_ctor_set(v___x_1737_, 0, v___x_1754_);
v___x_1757_ = v___x_1737_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_n_1760_, lean_object* v_k_1761_, lean_object* v_v_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_n_1760_, v___x_1763_, v_k_1761_, v_v_1762_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_x_1766_, size_t v_x_1767_, size_t v_x_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
lean_object* v_es_1771_; size_t v___x_1772_; size_t v___x_1773_; lean_object* v_j_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_es_1771_ = lean_ctor_get(v_x_1766_, 0);
v___x_1772_ = ((size_t)31ULL);
v___x_1773_ = lean_usize_land(v_x_1767_, v___x_1772_);
v_j_1774_ = lean_usize_to_nat(v___x_1773_);
v___x_1775_ = lean_array_get_size(v_es_1771_);
v___x_1776_ = lean_nat_dec_lt(v_j_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec(v_j_1774_);
lean_dec(v_x_1770_);
lean_dec(v_x_1769_);
return v_x_1766_;
}
else
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1815_; 
lean_inc_ref(v_es_1771_);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_x_1766_, 0);
lean_dec(v_unused_1816_);
v___x_1778_ = v_x_1766_;
v_isShared_1779_ = v_isSharedCheck_1815_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v_x_1766_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1815_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_v_1780_; lean_object* v___x_1781_; lean_object* v_xs_x27_1782_; lean_object* v___y_1784_; 
v_v_1780_ = lean_array_fget(v_es_1771_, v_j_1774_);
v___x_1781_ = lean_box(0);
v_xs_x27_1782_ = lean_array_fset(v_es_1771_, v_j_1774_, v___x_1781_);
switch(lean_obj_tag(v_v_1780_))
{
case 0:
{
lean_object* v_key_1789_; lean_object* v_val_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1800_; 
v_key_1789_ = lean_ctor_get(v_v_1780_, 0);
v_val_1790_ = lean_ctor_get(v_v_1780_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_v_1780_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1792_ = v_v_1780_;
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_val_1790_);
lean_inc(v_key_1789_);
lean_dec(v_v_1780_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_name_eq(v_x_1769_, v_key_1789_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_del_object(v___x_1792_);
v___x_1795_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1789_, v_val_1790_, v_x_1769_, v_x_1770_);
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
v___y_1784_ = v___x_1796_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1798_; 
lean_dec(v_val_1790_);
lean_dec(v_key_1789_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v_x_1770_);
lean_ctor_set(v___x_1792_, 0, v_x_1769_);
v___x_1798_ = v___x_1792_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_x_1769_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_x_1770_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
v___y_1784_ = v___x_1798_;
goto v___jp_1783_;
}
}
}
}
case 1:
{
lean_object* v_node_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1813_; 
v_node_1801_ = lean_ctor_get(v_v_1780_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_v_1780_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1803_ = v_v_1780_;
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_node_1801_);
lean_dec(v_v_1780_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
size_t v___x_1805_; size_t v___x_1806_; size_t v___x_1807_; size_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1805_ = ((size_t)5ULL);
v___x_1806_ = lean_usize_shift_right(v_x_1767_, v___x_1805_);
v___x_1807_ = ((size_t)1ULL);
v___x_1808_ = lean_usize_add(v_x_1768_, v___x_1807_);
v___x_1809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_node_1801_, v___x_1806_, v___x_1808_, v_x_1769_, v_x_1770_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1809_);
v___x_1811_ = v___x_1803_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v___y_1784_ = v___x_1811_;
goto v___jp_1783_;
}
}
}
default: 
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_x_1769_);
lean_ctor_set(v___x_1814_, 1, v_x_1770_);
v___y_1784_ = v___x_1814_;
goto v___jp_1783_;
}
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = lean_array_fset(v_xs_x27_1782_, v_j_1774_, v___y_1784_);
lean_dec(v_j_1774_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1785_);
v___x_1787_ = v___x_1778_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
else
{
lean_object* v_ks_1817_; lean_object* v_vs_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1838_; 
v_ks_1817_ = lean_ctor_get(v_x_1766_, 0);
v_vs_1818_ = lean_ctor_get(v_x_1766_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1820_ = v_x_1766_;
v_isShared_1821_ = v_isSharedCheck_1838_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_vs_1818_);
lean_inc(v_ks_1817_);
lean_dec(v_x_1766_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1838_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_ks_1817_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_vs_1818_);
v___x_1823_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v_newNode_1824_; uint8_t v___y_1826_; size_t v___x_1832_; uint8_t v___x_1833_; 
v_newNode_1824_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v___x_1823_, v_x_1769_, v_x_1770_);
v___x_1832_ = ((size_t)7ULL);
v___x_1833_ = lean_usize_dec_le(v___x_1832_, v_x_1768_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1834_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1824_);
v___x_1835_ = lean_unsigned_to_nat(4u);
v___x_1836_ = lean_nat_dec_lt(v___x_1834_, v___x_1835_);
lean_dec(v___x_1834_);
v___y_1826_ = v___x_1836_;
goto v___jp_1825_;
}
else
{
v___y_1826_ = v___x_1833_;
goto v___jp_1825_;
}
v___jp_1825_:
{
if (v___y_1826_ == 0)
{
lean_object* v_ks_1827_; lean_object* v_vs_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_ks_1827_ = lean_ctor_get(v_newNode_1824_, 0);
lean_inc_ref(v_ks_1827_);
v_vs_1828_ = lean_ctor_get(v_newNode_1824_, 1);
lean_inc_ref(v_vs_1828_);
lean_dec_ref(v_newNode_1824_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0);
v___x_1831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_x_1768_, v_ks_1827_, v_vs_1828_, v___x_1829_, v___x_1830_);
lean_dec_ref(v_vs_1828_);
lean_dec_ref(v_ks_1827_);
return v___x_1831_;
}
else
{
return v_newNode_1824_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t v_depth_1839_, lean_object* v_keys_1840_, lean_object* v_vals_1841_, lean_object* v_i_1842_, lean_object* v_entries_1843_){
_start:
{
lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = lean_array_get_size(v_keys_1840_);
v___x_1845_ = lean_nat_dec_lt(v_i_1842_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_dec(v_i_1842_);
return v_entries_1843_;
}
else
{
lean_object* v_k_1846_; lean_object* v_v_1847_; uint64_t v___y_1849_; 
v_k_1846_ = lean_array_fget_borrowed(v_keys_1840_, v_i_1842_);
v_v_1847_ = lean_array_fget_borrowed(v_vals_1841_, v_i_1842_);
if (lean_obj_tag(v_k_1846_) == 0)
{
uint64_t v___x_1860_; 
v___x_1860_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1849_ = v___x_1860_;
goto v___jp_1848_;
}
else
{
uint64_t v_hash_1861_; 
v_hash_1861_ = lean_ctor_get_uint64(v_k_1846_, sizeof(void*)*2);
v___y_1849_ = v_hash_1861_;
goto v___jp_1848_;
}
v___jp_1848_:
{
size_t v_h_1850_; size_t v___x_1851_; lean_object* v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; size_t v_h_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_h_1850_ = lean_uint64_to_usize(v___y_1849_);
v___x_1851_ = ((size_t)5ULL);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_sub(v_depth_1839_, v___x_1853_);
v___x_1855_ = lean_usize_mul(v___x_1851_, v___x_1854_);
v_h_1856_ = lean_usize_shift_right(v_h_1850_, v___x_1855_);
v___x_1857_ = lean_nat_add(v_i_1842_, v___x_1852_);
lean_dec(v_i_1842_);
lean_inc(v_v_1847_);
lean_inc(v_k_1846_);
v___x_1858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_entries_1843_, v_h_1856_, v_depth_1839_, v_k_1846_, v_v_1847_);
v_i_1842_ = v___x_1857_;
v_entries_1843_ = v___x_1858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_1862_, lean_object* v_keys_1863_, lean_object* v_vals_1864_, lean_object* v_i_1865_, lean_object* v_entries_1866_){
_start:
{
size_t v_depth_boxed_1867_; lean_object* v_res_1868_; 
v_depth_boxed_1867_ = lean_unbox_usize(v_depth_1862_);
lean_dec(v_depth_1862_);
v_res_1868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_boxed_1867_, v_keys_1863_, v_vals_1864_, v_i_1865_, v_entries_1866_);
lean_dec_ref(v_vals_1864_);
lean_dec_ref(v_keys_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
size_t v_x_1574__boxed_1874_; size_t v_x_1575__boxed_1875_; lean_object* v_res_1876_; 
v_x_1574__boxed_1874_ = lean_unbox_usize(v_x_1870_);
lean_dec(v_x_1870_);
v_x_1575__boxed_1875_ = lean_unbox_usize(v_x_1871_);
lean_dec(v_x_1871_);
v_res_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1869_, v_x_1574__boxed_1874_, v_x_1575__boxed_1875_, v_x_1872_, v_x_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
uint64_t v___y_1881_; 
if (lean_obj_tag(v_x_1878_) == 0)
{
uint64_t v___x_1885_; 
v___x_1885_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1881_ = v___x_1885_;
goto v___jp_1880_;
}
else
{
uint64_t v_hash_1886_; 
v_hash_1886_ = lean_ctor_get_uint64(v_x_1878_, sizeof(void*)*2);
v___y_1881_ = v_hash_1886_;
goto v___jp_1880_;
}
v___jp_1880_:
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_uint64_to_usize(v___y_1881_);
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1877_, v___x_1882_, v___x_1883_, v_x_1878_, v_x_1879_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_fst_1889_; lean_object* v_snd_1890_; lean_object* v___x_1891_; 
v_fst_1889_ = lean_ctor_get(v_x_1888_, 0);
lean_inc(v_fst_1889_);
v_snd_1890_ = lean_ctor_get(v_x_1888_, 1);
lean_inc(v_snd_1890_);
lean_dec_ref(v_x_1888_);
v___x_1891_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1887_, v_fst_1889_, v_snd_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1925_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1927_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1929_, v_x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_res_1935_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1932_, v_x_1933_, v_x_1934_);
lean_dec(v_x_1934_);
lean_dec_ref(v_x_1933_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1937_, lean_object* v_m_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1940_, lean_object* v_m_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1940_, v_m_1941_);
lean_dec_ref(v_m_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1943_, lean_object* v_as_1944_, lean_object* v_lo_1945_, lean_object* v_hi_1946_, lean_object* v_w_1947_, lean_object* v_hlo_1948_, lean_object* v_hhi_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1943_, v_as_1944_, v_lo_1945_, v_hi_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1951_, lean_object* v_as_1952_, lean_object* v_lo_1953_, lean_object* v_hi_1954_, lean_object* v_w_1955_, lean_object* v_hlo_1956_, lean_object* v_hhi_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1951_, v_as_1952_, v_lo_1953_, v_hi_1954_, v_w_1955_, v_hlo_1956_, v_hhi_1957_);
lean_dec(v_hi_1954_);
lean_dec(v_n_1951_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1959_, lean_object* v_x_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1960_, v_x_1961_, v_x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1964_, lean_object* v_x_1965_, size_t v_x_1966_, lean_object* v_x_1967_){
_start:
{
uint8_t v___x_1968_; 
v___x_1968_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1965_, v_x_1966_, v_x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
size_t v_x_1881__boxed_1973_; uint8_t v_res_1974_; lean_object* v_r_1975_; 
v_x_1881__boxed_1973_ = lean_unbox_usize(v_x_1971_);
lean_dec(v_x_1971_);
v_res_1974_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1969_, v_x_1970_, v_x_1881__boxed_1973_, v_x_1972_);
lean_dec(v_x_1972_);
lean_dec_ref(v_x_1970_);
v_r_1975_ = lean_box(v_res_1974_);
return v_r_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1976_, lean_object* v_00_u03b2_1977_, lean_object* v_map_1978_, lean_object* v_f_1979_, lean_object* v_init_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1978_, v_f_1979_, v_init_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1982_, lean_object* v_00_u03b2_1983_, lean_object* v_map_1984_, lean_object* v_f_1985_, lean_object* v_init_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1982_, v_00_u03b2_1983_, v_map_1984_, v_f_1985_, v_init_1986_);
lean_dec_ref(v_map_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_n_1988_, lean_object* v_lo_1989_, lean_object* v_hi_1990_, lean_object* v_hhi_1991_, lean_object* v_pivot_1992_, lean_object* v_as_1993_, lean_object* v_i_1994_, lean_object* v_k_1995_, lean_object* v_ilo_1996_, lean_object* v_ik_1997_, lean_object* v_w_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1990_, v_pivot_1992_, v_as_1993_, v_i_1994_, v_k_1995_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_n_2000_, lean_object* v_lo_2001_, lean_object* v_hi_2002_, lean_object* v_hhi_2003_, lean_object* v_pivot_2004_, lean_object* v_as_2005_, lean_object* v_i_2006_, lean_object* v_k_2007_, lean_object* v_ilo_2008_, lean_object* v_ik_2009_, lean_object* v_w_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(v_n_2000_, v_lo_2001_, v_hi_2002_, v_hhi_2003_, v_pivot_2004_, v_as_2005_, v_i_2006_, v_k_2007_, v_ilo_2008_, v_ik_2009_, v_w_2010_);
lean_dec_ref(v_pivot_2004_);
lean_dec(v_hi_2002_);
lean_dec(v_lo_2001_);
lean_dec(v_n_2000_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_2012_, lean_object* v_x_2013_, size_t v_x_2014_, size_t v_x_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_2013_, v_x_2014_, v_x_2015_, v_x_2016_, v_x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
size_t v_x_1896__boxed_2025_; size_t v_x_1897__boxed_2026_; lean_object* v_res_2027_; 
v_x_1896__boxed_2025_ = lean_unbox_usize(v_x_2021_);
lean_dec(v_x_2021_);
v_x_1897__boxed_2026_ = lean_unbox_usize(v_x_2022_);
lean_dec(v_x_2022_);
v_res_2027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_2019_, v_x_2020_, v_x_1896__boxed_2025_, v_x_1897__boxed_2026_, v_x_2023_, v_x_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2028_, lean_object* v_keys_2029_, lean_object* v_vals_2030_, lean_object* v_heq_2031_, lean_object* v_i_2032_, lean_object* v_k_2033_){
_start:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_2029_, v_i_2032_, v_k_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2035_, lean_object* v_keys_2036_, lean_object* v_vals_2037_, lean_object* v_heq_2038_, lean_object* v_i_2039_, lean_object* v_k_2040_){
_start:
{
uint8_t v_res_2041_; lean_object* v_r_2042_; 
v_res_2041_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2035_, v_keys_2036_, v_vals_2037_, v_heq_2038_, v_i_2039_, v_k_2040_);
lean_dec(v_k_2040_);
lean_dec_ref(v_vals_2037_);
lean_dec_ref(v_keys_2036_);
v_r_2042_ = lean_box(v_res_2041_);
return v_r_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_2043_, lean_object* v_f_2044_, lean_object* v_init_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2044_, v_map_2043_, v_init_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_2047_, lean_object* v_f_2048_, lean_object* v_init_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_2047_, v_f_2048_, v_init_2049_);
lean_dec_ref(v_map_2047_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_2051_, lean_object* v_00_u03b2_2052_, lean_object* v_map_2053_, lean_object* v_f_2054_, lean_object* v_init_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2054_, v_map_2053_, v_init_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_2057_, lean_object* v_00_u03b2_2058_, lean_object* v_map_2059_, lean_object* v_f_2060_, lean_object* v_init_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_2057_, v_00_u03b2_2058_, v_map_2059_, v_f_2060_, v_init_2061_);
lean_dec_ref(v_map_2059_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_2063_, lean_object* v_n_2064_, lean_object* v_k_2065_, lean_object* v_v_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_n_2064_, v_k_2065_, v_v_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object* v_00_u03b2_2068_, size_t v_depth_2069_, lean_object* v_keys_2070_, lean_object* v_vals_2071_, lean_object* v_heq_2072_, lean_object* v_i_2073_, lean_object* v_entries_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_2069_, v_keys_2070_, v_vals_2071_, v_i_2073_, v_entries_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2076_, lean_object* v_depth_2077_, lean_object* v_keys_2078_, lean_object* v_vals_2079_, lean_object* v_heq_2080_, lean_object* v_i_2081_, lean_object* v_entries_2082_){
_start:
{
size_t v_depth_boxed_2083_; lean_object* v_res_2084_; 
v_depth_boxed_2083_ = lean_unbox_usize(v_depth_2077_);
lean_dec(v_depth_2077_);
v_res_2084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(v_00_u03b2_2076_, v_depth_boxed_2083_, v_keys_2078_, v_vals_2079_, v_heq_2080_, v_i_2081_, v_entries_2082_);
lean_dec_ref(v_vals_2079_);
lean_dec_ref(v_keys_2078_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2085_, lean_object* v_00_u03b1_2086_, lean_object* v_00_u03b2_2087_, lean_object* v_f_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2088_, v_x_2089_, v_x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2092_, lean_object* v_00_u03b1_2093_, lean_object* v_00_u03b2_2094_, lean_object* v_f_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_2092_, v_00_u03b1_2093_, v_00_u03b2_2094_, v_f_2095_, v_x_2096_, v_x_2097_);
lean_dec_ref(v_x_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_x_2100_, v_x_2101_, v_x_2102_, v_x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_2105_, lean_object* v_00_u03b2_2106_, lean_object* v_00_u03c3_2107_, lean_object* v_f_2108_, lean_object* v_as_2109_, size_t v_i_2110_, size_t v_stop_2111_, lean_object* v_b_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_2108_, v_as_2109_, v_i_2110_, v_stop_2111_, v_b_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_00_u03b2_2115_, lean_object* v_00_u03c3_2116_, lean_object* v_f_2117_, lean_object* v_as_2118_, lean_object* v_i_2119_, lean_object* v_stop_2120_, lean_object* v_b_2121_){
_start:
{
size_t v_i_boxed_2122_; size_t v_stop_boxed_2123_; lean_object* v_res_2124_; 
v_i_boxed_2122_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_stop_boxed_2123_ = lean_unbox_usize(v_stop_2120_);
lean_dec(v_stop_2120_);
v_res_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_2114_, v_00_u03b2_2115_, v_00_u03c3_2116_, v_f_2117_, v_as_2118_, v_i_boxed_2122_, v_stop_boxed_2123_, v_b_2121_);
lean_dec_ref(v_as_2118_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03c3_2125_, lean_object* v_00_u03b1_2126_, lean_object* v_00_u03b2_2127_, lean_object* v_f_2128_, lean_object* v_keys_2129_, lean_object* v_vals_2130_, lean_object* v_heq_2131_, lean_object* v_i_2132_, lean_object* v_acc_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_2128_, v_keys_2129_, v_vals_2130_, v_i_2132_, v_acc_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03c3_2135_, lean_object* v_00_u03b1_2136_, lean_object* v_00_u03b2_2137_, lean_object* v_f_2138_, lean_object* v_keys_2139_, lean_object* v_vals_2140_, lean_object* v_heq_2141_, lean_object* v_i_2142_, lean_object* v_acc_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(v_00_u03c3_2135_, v_00_u03b1_2136_, v_00_u03b2_2137_, v_f_2138_, v_keys_2139_, v_vals_2140_, v_heq_2141_, v_i_2142_, v_acc_2143_);
lean_dec_ref(v_vals_2140_);
lean_dec_ref(v_keys_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2145_, lean_object* v_fid_2146_, lean_object* v_v_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v_toEnvExtension_2149_; lean_object* v_asyncMode_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2148_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2149_ = lean_ctor_get(v___x_2148_, 0);
v_asyncMode_2150_ = lean_ctor_get(v_toEnvExtension_2149_, 2);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_fid_2146_);
lean_ctor_set(v___x_2151_, 1, v_v_2147_);
v___x_2152_ = lean_box(0);
v___x_2153_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2148_, v_env_2145_, v___x_2151_, v_asyncMode_2150_, v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2154_, lean_object* v_vals_2155_, lean_object* v_i_2156_, lean_object* v_k_2157_){
_start:
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = lean_array_get_size(v_keys_2154_);
v___x_2159_ = lean_nat_dec_lt(v_i_2156_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
lean_dec(v_i_2156_);
v___x_2160_ = lean_box(0);
return v___x_2160_;
}
else
{
lean_object* v_k_x27_2161_; uint8_t v___x_2162_; 
v_k_x27_2161_ = lean_array_fget_borrowed(v_keys_2154_, v_i_2156_);
v___x_2162_ = lean_name_eq(v_k_2157_, v_k_x27_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_unsigned_to_nat(1u);
v___x_2164_ = lean_nat_add(v_i_2156_, v___x_2163_);
lean_dec(v_i_2156_);
v_i_2156_ = v___x_2164_;
goto _start;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_array_fget_borrowed(v_vals_2155_, v_i_2156_);
lean_dec(v_i_2156_);
lean_inc(v___x_2166_);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2168_, lean_object* v_vals_2169_, lean_object* v_i_2170_, lean_object* v_k_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2168_, v_vals_2169_, v_i_2170_, v_k_2171_);
lean_dec(v_k_2171_);
lean_dec_ref(v_vals_2169_);
lean_dec_ref(v_keys_2168_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2173_, size_t v_x_2174_, lean_object* v_x_2175_){
_start:
{
if (lean_obj_tag(v_x_2173_) == 0)
{
lean_object* v_es_2176_; lean_object* v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; lean_object* v_j_2180_; lean_object* v___x_2181_; 
v_es_2176_ = lean_ctor_get(v_x_2173_, 0);
v___x_2177_ = lean_box(2);
v___x_2178_ = ((size_t)31ULL);
v___x_2179_ = lean_usize_land(v_x_2174_, v___x_2178_);
v_j_2180_ = lean_usize_to_nat(v___x_2179_);
v___x_2181_ = lean_array_get_borrowed(v___x_2177_, v_es_2176_, v_j_2180_);
lean_dec(v_j_2180_);
switch(lean_obj_tag(v___x_2181_))
{
case 0:
{
lean_object* v_key_2182_; lean_object* v_val_2183_; uint8_t v___x_2184_; 
v_key_2182_ = lean_ctor_get(v___x_2181_, 0);
v_val_2183_ = lean_ctor_get(v___x_2181_, 1);
v___x_2184_ = lean_name_eq(v_x_2175_, v_key_2182_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_box(0);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; 
lean_inc(v_val_2183_);
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_val_2183_);
return v___x_2186_;
}
}
case 1:
{
lean_object* v_node_2187_; size_t v___x_2188_; size_t v___x_2189_; 
v_node_2187_ = lean_ctor_get(v___x_2181_, 0);
v___x_2188_ = ((size_t)5ULL);
v___x_2189_ = lean_usize_shift_right(v_x_2174_, v___x_2188_);
v_x_2173_ = v_node_2187_;
v_x_2174_ = v___x_2189_;
goto _start;
}
default: 
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_box(0);
return v___x_2191_;
}
}
}
else
{
lean_object* v_ks_2192_; lean_object* v_vs_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_ks_2192_ = lean_ctor_get(v_x_2173_, 0);
v_vs_2193_ = lean_ctor_get(v_x_2173_, 1);
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2192_, v_vs_2193_, v___x_2194_, v_x_2175_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
size_t v_x_386__boxed_2199_; lean_object* v_res_2200_; 
v_x_386__boxed_2199_ = lean_unbox_usize(v_x_2197_);
lean_dec(v_x_2197_);
v_res_2200_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2196_, v_x_386__boxed_2199_, v_x_2198_);
lean_dec(v_x_2198_);
lean_dec_ref(v_x_2196_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
uint64_t v___y_2204_; 
if (lean_obj_tag(v_x_2202_) == 0)
{
uint64_t v___x_2207_; 
v___x_2207_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_2204_ = v___x_2207_;
goto v___jp_2203_;
}
else
{
uint64_t v_hash_2208_; 
v_hash_2208_ = lean_ctor_get_uint64(v_x_2202_, sizeof(void*)*2);
v___y_2204_ = v_hash_2208_;
goto v___jp_2203_;
}
v___jp_2203_:
{
size_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_uint64_to_usize(v___y_2204_);
v___x_2206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2201_, v___x_2205_, v_x_2202_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2209_, v_x_2210_);
lean_dec(v_x_2210_);
lean_dec_ref(v_x_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2212_, lean_object* v_k_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v_m_2218_; lean_object* v_a_2219_; uint8_t v___x_2220_; 
v___x_2216_ = lean_nat_add(v_x_2214_, v_x_2215_);
v___x_2217_ = lean_unsigned_to_nat(1u);
v_m_2218_ = lean_nat_shiftr(v___x_2216_, v___x_2217_);
lean_dec(v___x_2216_);
v_a_2219_ = lean_array_fget_borrowed(v_as_2212_, v_m_2218_);
v___x_2220_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2219_, v_k_2213_);
if (v___x_2220_ == 0)
{
uint8_t v___x_2221_; 
lean_dec(v_x_2215_);
v___x_2221_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2213_, v_a_2219_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec(v_m_2218_);
lean_dec(v_x_2214_);
lean_inc(v_a_2219_);
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2219_);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = lean_nat_dec_eq(v_m_2218_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = lean_nat_sub(v_m_2218_, v___x_2217_);
lean_dec(v_m_2218_);
v___x_2226_ = lean_nat_dec_lt(v___x_2225_, v_x_2214_);
if (v___x_2226_ == 0)
{
v_x_2215_ = v___x_2225_;
goto _start;
}
else
{
lean_object* v___x_2228_; 
lean_dec(v___x_2225_);
lean_dec(v_x_2214_);
v___x_2228_ = lean_box(0);
return v___x_2228_;
}
}
else
{
lean_object* v___x_2229_; 
lean_dec(v_m_2218_);
lean_dec(v_x_2214_);
v___x_2229_ = lean_box(0);
return v___x_2229_;
}
}
}
else
{
lean_object* v___x_2230_; uint8_t v___x_2231_; 
lean_dec(v_x_2214_);
v___x_2230_ = lean_nat_add(v_m_2218_, v___x_2217_);
lean_dec(v_m_2218_);
v___x_2231_ = lean_nat_dec_le(v___x_2230_, v_x_2215_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; 
lean_dec(v___x_2230_);
lean_dec(v_x_2215_);
v___x_2232_ = lean_box(0);
return v___x_2232_;
}
else
{
v_x_2214_ = v___x_2230_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2234_, lean_object* v_k_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2234_, v_k_2235_, v_x_2236_, v_x_2237_);
lean_dec_ref(v_k_2235_);
lean_dec_ref(v_as_2234_);
return v_res_2238_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2242_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2243_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2242_, v___x_2241_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v___x_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2247_, lean_object* v_fid_2248_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2258_; 
v___x_2249_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2250_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2258_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2247_, v_fid_2248_);
if (lean_obj_tag(v___x_2258_) == 0)
{
goto v___jp_2251_;
}
else
{
lean_object* v_val_2259_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_val_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2281_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_2249_, v___x_2250_, v_env_2247_, v_val_2259_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = lean_array_get_size(v___x_2281_);
v___x_2284_ = lean_nat_dec_lt(v___x_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_dec_ref(v___x_2281_);
goto v___jp_2260_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2285_ = lean_unsigned_to_nat(1u);
v___x_2286_ = lean_nat_sub(v___x_2283_, v___x_2285_);
v___x_2287_ = lean_nat_dec_le(v___x_2282_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_dec(v___x_2286_);
lean_dec_ref(v___x_2281_);
goto v___jp_2260_;
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_box(0);
lean_inc(v_fid_2248_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_fid_2248_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2281_, v___x_2289_, v___x_2282_, v___x_2286_);
lean_dec_ref_known(v___x_2289_, 2);
lean_dec_ref(v___x_2281_);
if (lean_obj_tag(v___x_2290_) == 0)
{
goto v___jp_2260_;
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_val_2259_);
lean_dec(v_fid_2248_);
lean_dec_ref(v_env_2247_);
v_val_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_val_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_snd_2295_; lean_object* v___x_2297_; 
v_snd_2295_ = lean_ctor_get(v_val_2291_, 1);
lean_inc(v_snd_2295_);
lean_dec(v_val_2291_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v_snd_2295_);
v___x_2297_ = v___x_2293_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_snd_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
v___jp_2260_:
{
uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2261_ = 0;
v___x_2262_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2249_, v___x_2250_, v_env_2247_, v_val_2259_, v___x_2261_);
lean_dec(v_val_2259_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_array_get_size(v___x_2262_);
v___x_2265_ = lean_nat_dec_lt(v___x_2263_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_dec_ref(v___x_2262_);
goto v___jp_2251_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_sub(v___x_2264_, v___x_2266_);
v___x_2268_ = lean_nat_dec_le(v___x_2263_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_dec(v___x_2267_);
lean_dec_ref(v___x_2262_);
goto v___jp_2251_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = lean_box(0);
lean_inc(v_fid_2248_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v_fid_2248_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2262_, v___x_2270_, v___x_2263_, v___x_2267_);
lean_dec_ref_known(v___x_2270_, 2);
lean_dec_ref(v___x_2262_);
if (lean_obj_tag(v___x_2271_) == 0)
{
goto v___jp_2251_;
}
else
{
lean_object* v_val_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_fid_2248_);
lean_dec_ref(v_env_2247_);
v_val_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_val_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v_snd_2276_; lean_object* v___x_2278_; 
v_snd_2276_ = lean_ctor_get(v_val_2272_, 1);
lean_inc(v_snd_2276_);
lean_dec(v_val_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v_snd_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_snd_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
}
v___jp_2251_:
{
lean_object* v_toEnvExtension_2252_; lean_object* v_asyncMode_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_snd_2256_; lean_object* v___x_2257_; 
v_toEnvExtension_2252_ = lean_ctor_get(v___x_2250_, 0);
v_asyncMode_2253_ = lean_ctor_get(v_toEnvExtension_2252_, 2);
v___x_2254_ = lean_box(0);
v___x_2255_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2249_, v___x_2250_, v_env_2247_, v_asyncMode_2253_, v___x_2254_);
v_snd_2256_ = lean_ctor_get(v___x_2255_, 1);
lean_inc(v_snd_2256_);
lean_dec(v___x_2255_);
v___x_2257_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2256_, v_fid_2248_);
lean_dec(v_fid_2248_);
lean_dec(v_snd_2256_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2301_, v_x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2304_, v_x_2305_, v_x_2306_);
lean_dec(v_x_2306_);
lean_dec_ref(v_x_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2308_, lean_object* v_k_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2308_, v_k_2309_, v_x_2310_, v_x_2311_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2314_, lean_object* v_k_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2314_, v_k_2315_, v_x_2316_, v_x_2317_, v_x_2318_);
lean_dec_ref(v_k_2315_);
lean_dec_ref(v_as_2314_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2320_, lean_object* v_x_2321_, size_t v_x_2322_, lean_object* v_x_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2321_, v_x_2322_, v_x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
size_t v_x_625__boxed_2329_; lean_object* v_res_2330_; 
v_x_625__boxed_2329_ = lean_unbox_usize(v_x_2327_);
lean_dec(v_x_2327_);
v_res_2330_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2325_, v_x_2326_, v_x_625__boxed_2329_, v_x_2328_);
lean_dec(v_x_2328_);
lean_dec_ref(v_x_2326_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2331_, lean_object* v_keys_2332_, lean_object* v_vals_2333_, lean_object* v_heq_2334_, lean_object* v_i_2335_, lean_object* v_k_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2332_, v_vals_2333_, v_i_2335_, v_k_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2338_, lean_object* v_keys_2339_, lean_object* v_vals_2340_, lean_object* v_heq_2341_, lean_object* v_i_2342_, lean_object* v_k_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2338_, v_keys_2339_, v_vals_2340_, v_heq_2341_, v_i_2342_, v_k_2343_);
lean_dec(v_k_2343_);
lean_dec_ref(v_vals_2340_);
lean_dec_ref(v_keys_2339_);
return v_res_2344_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2348_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2349_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2348_, v___x_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v_assignments_2354_; lean_object* v_currFnIdx_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2353_ = lean_st_ref_get(v_a_2351_);
v_assignments_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_ref(v_assignments_2354_);
lean_dec(v___x_2353_);
v_currFnIdx_2355_ = lean_ctor_get(v_a_2350_, 1);
v___x_2356_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2357_ = lean_array_get(v___x_2356_, v_assignments_2354_, v_currFnIdx_2355_);
lean_dec_ref(v_assignments_2354_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2363_, v_a_2364_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v_funVals_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2382_ = lean_st_ref_get(v_a_2380_);
v_funVals_2383_ = lean_ctor_get(v___x_2382_, 1);
lean_inc_ref(v_funVals_2383_);
lean_dec(v___x_2382_);
v___x_2384_ = lean_box(0);
v___x_2385_ = lean_array_get(v___x_2384_, v_funVals_2383_, v_funIdx_2379_);
lean_dec_ref(v_funVals_2383_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec(v_funIdx_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2391_, v_a_2393_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_funIdx_2400_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2409_, lean_object* v_as_2410_, lean_object* v_j_2411_){
_start:
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = lean_array_get_size(v_as_2410_);
v___x_2413_ = lean_nat_dec_lt(v_j_2411_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; 
lean_dec(v_j_2411_);
v___x_2414_ = lean_box(0);
return v___x_2414_;
}
else
{
lean_object* v___x_2415_; lean_object* v_toSignature_2416_; lean_object* v_name_2417_; uint8_t v___x_2418_; 
v___x_2415_ = lean_array_fget_borrowed(v_as_2410_, v_j_2411_);
v_toSignature_2416_ = lean_ctor_get(v___x_2415_, 0);
v_name_2417_ = lean_ctor_get(v_toSignature_2416_, 0);
v___x_2418_ = lean_name_eq(v_name_2417_, v_declName_2409_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(1u);
v___x_2420_ = lean_nat_add(v_j_2411_, v___x_2419_);
lean_dec(v_j_2411_);
v_j_2411_ = v___x_2420_;
goto _start;
}
else
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v_j_2411_);
return v___x_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2423_, lean_object* v_as_2424_, lean_object* v_j_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2423_, v_as_2424_, v_j_2425_);
lean_dec_ref(v_as_2424_);
lean_dec(v_declName_2423_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_decls_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_decls_2431_ = lean_ctor_get(v_a_2428_, 0);
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2427_, v_decls_2431_, v___x_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
else
{
lean_object* v_val_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2452_; 
v_val_2436_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2438_ = v___x_2433_;
v_isShared_2439_ = v_isSharedCheck_2452_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_val_2436_);
lean_dec(v___x_2433_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2452_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2451_; 
v___x_2440_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2436_, v_a_2429_);
lean_dec(v_val_2436_);
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2451_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2451_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v_a_2441_);
v___x_2446_ = v___x_2438_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2448_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2446_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_declName_2453_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2458_, v_a_2459_, v_a_2460_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_declName_2467_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v___x_2480_; lean_object* v_currFnIdx_2481_; lean_object* v_assignments_2482_; lean_object* v_funVals_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2501_; 
v___x_2480_ = lean_st_ref_take(v_a_2478_);
v_currFnIdx_2481_ = lean_ctor_get(v_a_2477_, 1);
v_assignments_2482_ = lean_ctor_get(v___x_2480_, 0);
v_funVals_2483_ = lean_ctor_get(v___x_2480_, 1);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2485_ = v___x_2480_;
v_isShared_2486_ = v_isSharedCheck_2501_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_funVals_2483_);
lean_inc(v_assignments_2482_);
lean_dec(v___x_2480_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2501_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___y_2489_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2487_ = lean_box(0);
v___x_2495_ = lean_array_get_size(v_assignments_2482_);
v___x_2496_ = lean_nat_dec_lt(v_currFnIdx_2481_, v___x_2495_);
if (v___x_2496_ == 0)
{
lean_dec_ref(v_f_2476_);
v___y_2489_ = v_assignments_2482_;
goto v___jp_2488_;
}
else
{
lean_object* v_v_2497_; lean_object* v_xs_x27_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_v_2497_ = lean_array_fget(v_assignments_2482_, v_currFnIdx_2481_);
v_xs_x27_2498_ = lean_array_fset(v_assignments_2482_, v_currFnIdx_2481_, v___x_2487_);
v___x_2499_ = lean_apply_1(v_f_2476_, v_v_2497_);
v___x_2500_ = lean_array_fset(v_xs_x27_2498_, v_currFnIdx_2481_, v___x_2499_);
v___y_2489_ = v___x_2500_;
goto v___jp_2488_;
}
v___jp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___y_2489_);
v___x_2491_ = v___x_2485_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___y_2489_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_funVals_2483_);
v___x_2491_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_st_ref_set(v_a_2478_, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2487_);
return v___x_2493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2507_, v_a_2508_, v_a_2509_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2525_, lean_object* v_fallback_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
lean_inc(v_fallback_2526_);
return v_fallback_2526_;
}
else
{
lean_object* v_key_2528_; lean_object* v_value_2529_; lean_object* v_tail_2530_; uint8_t v___x_2531_; 
v_key_2528_ = lean_ctor_get(v_x_2527_, 0);
v_value_2529_ = lean_ctor_get(v_x_2527_, 1);
v_tail_2530_ = lean_ctor_get(v_x_2527_, 2);
v___x_2531_ = l_Lean_instBEqFVarId_beq(v_key_2528_, v_a_2525_);
if (v___x_2531_ == 0)
{
v_x_2527_ = v_tail_2530_;
goto _start;
}
else
{
lean_inc(v_value_2529_);
return v_value_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2533_, lean_object* v_fallback_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2533_, v_fallback_2534_, v_x_2535_);
lean_dec(v_x_2535_);
lean_dec(v_fallback_2534_);
lean_dec(v_a_2533_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2537_, lean_object* v_a_2538_, lean_object* v_fallback_2539_){
_start:
{
lean_object* v_buckets_2540_; lean_object* v___x_2541_; uint64_t v___x_2542_; uint64_t v___x_2543_; uint64_t v___x_2544_; uint64_t v_fold_2545_; uint64_t v___x_2546_; uint64_t v___x_2547_; uint64_t v___x_2548_; size_t v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_buckets_2540_ = lean_ctor_get(v_m_2537_, 1);
v___x_2541_ = lean_array_get_size(v_buckets_2540_);
v___x_2542_ = l_Lean_instHashableFVarId_hash(v_a_2538_);
v___x_2543_ = 32ULL;
v___x_2544_ = lean_uint64_shift_right(v___x_2542_, v___x_2543_);
v_fold_2545_ = lean_uint64_xor(v___x_2542_, v___x_2544_);
v___x_2546_ = 16ULL;
v___x_2547_ = lean_uint64_shift_right(v_fold_2545_, v___x_2546_);
v___x_2548_ = lean_uint64_xor(v_fold_2545_, v___x_2547_);
v___x_2549_ = lean_uint64_to_usize(v___x_2548_);
v___x_2550_ = lean_usize_of_nat(v___x_2541_);
v___x_2551_ = ((size_t)1ULL);
v___x_2552_ = lean_usize_sub(v___x_2550_, v___x_2551_);
v___x_2553_ = lean_usize_land(v___x_2549_, v___x_2552_);
v___x_2554_ = lean_array_uget_borrowed(v_buckets_2540_, v___x_2553_);
v___x_2555_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2538_, v_fallback_2539_, v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2556_, lean_object* v_a_2557_, lean_object* v_fallback_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2556_, v_a_2557_, v_fallback_2558_);
lean_dec(v_fallback_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_m_2556_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2574_; 
v___x_2564_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2561_, v_a_2562_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2574_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2574_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2569_ = lean_box(0);
v___x_2570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2565_, v_var_2560_, v___x_2569_);
lean_dec(v_a_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2570_);
v___x_2572_ = v___x_2567_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2575_, v_a_2576_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_var_2575_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2580_, v_a_2581_, v_a_2582_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_var_2589_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2598_, lean_object* v_m_2599_, lean_object* v_a_2600_, lean_object* v_fallback_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2599_, v_a_2600_, v_fallback_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2603_, lean_object* v_m_2604_, lean_object* v_a_2605_, lean_object* v_fallback_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2603_, v_m_2604_, v_a_2605_, v_fallback_2606_);
lean_dec(v_fallback_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_m_2604_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2608_, lean_object* v_a_2609_, lean_object* v_fallback_2610_, lean_object* v_x_2611_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2609_, v_fallback_2610_, v_x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2613_, lean_object* v_a_2614_, lean_object* v_fallback_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2613_, v_a_2614_, v_fallback_2615_, v_x_2616_);
lean_dec(v_x_2616_);
lean_dec(v_fallback_2615_);
lean_dec(v_a_2614_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
if (lean_obj_tag(v_arg_2618_) == 1)
{
lean_object* v_fvarId_2622_; lean_object* v___x_2623_; 
v_fvarId_2622_ = lean_ctor_get(v_arg_2618_, 0);
v___x_2623_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2622_, v_a_2619_, v_a_2620_);
return v___x_2623_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_box(1);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2626_, v_a_2627_, v_a_2628_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_arg_2626_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2631_, v_a_2632_, v_a_2633_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_arg_2640_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2649_, lean_object* v_b_2650_, lean_object* v_x_2651_){
_start:
{
if (lean_obj_tag(v_x_2651_) == 0)
{
lean_dec(v_b_2650_);
lean_dec(v_a_2649_);
return v_x_2651_;
}
else
{
lean_object* v_key_2652_; lean_object* v_value_2653_; lean_object* v_tail_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2666_; 
v_key_2652_ = lean_ctor_get(v_x_2651_, 0);
v_value_2653_ = lean_ctor_get(v_x_2651_, 1);
v_tail_2654_ = lean_ctor_get(v_x_2651_, 2);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_x_2651_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2656_ = v_x_2651_;
v_isShared_2657_ = v_isSharedCheck_2666_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_tail_2654_);
lean_inc(v_value_2653_);
lean_inc(v_key_2652_);
lean_dec(v_x_2651_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2666_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
uint8_t v___x_2658_; 
v___x_2658_ = l_Lean_instBEqFVarId_beq(v_key_2652_, v_a_2649_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2649_, v_b_2650_, v_tail_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 2, v___x_2659_);
v___x_2661_ = v___x_2656_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_key_2652_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_value_2653_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
else
{
lean_object* v___x_2664_; 
lean_dec(v_value_2653_);
lean_dec(v_key_2652_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v_b_2650_);
lean_ctor_set(v___x_2656_, 0, v_a_2649_);
v___x_2664_ = v___x_2656_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2649_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_b_2650_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v_tail_2654_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2667_, lean_object* v_x_2668_){
_start:
{
if (lean_obj_tag(v_x_2668_) == 0)
{
return v_x_2667_;
}
else
{
lean_object* v_key_2669_; lean_object* v_value_2670_; lean_object* v_tail_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2694_; 
v_key_2669_ = lean_ctor_get(v_x_2668_, 0);
v_value_2670_ = lean_ctor_get(v_x_2668_, 1);
v_tail_2671_ = lean_ctor_get(v_x_2668_, 2);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_x_2668_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2673_ = v_x_2668_;
v_isShared_2674_ = v_isSharedCheck_2694_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_tail_2671_);
lean_inc(v_value_2670_);
lean_inc(v_key_2669_);
lean_dec(v_x_2668_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2694_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; uint64_t v___x_2676_; uint64_t v___x_2677_; uint64_t v___x_2678_; uint64_t v_fold_2679_; uint64_t v___x_2680_; uint64_t v___x_2681_; uint64_t v___x_2682_; size_t v___x_2683_; size_t v___x_2684_; size_t v___x_2685_; size_t v___x_2686_; size_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2675_ = lean_array_get_size(v_x_2667_);
v___x_2676_ = l_Lean_instHashableFVarId_hash(v_key_2669_);
v___x_2677_ = 32ULL;
v___x_2678_ = lean_uint64_shift_right(v___x_2676_, v___x_2677_);
v_fold_2679_ = lean_uint64_xor(v___x_2676_, v___x_2678_);
v___x_2680_ = 16ULL;
v___x_2681_ = lean_uint64_shift_right(v_fold_2679_, v___x_2680_);
v___x_2682_ = lean_uint64_xor(v_fold_2679_, v___x_2681_);
v___x_2683_ = lean_uint64_to_usize(v___x_2682_);
v___x_2684_ = lean_usize_of_nat(v___x_2675_);
v___x_2685_ = ((size_t)1ULL);
v___x_2686_ = lean_usize_sub(v___x_2684_, v___x_2685_);
v___x_2687_ = lean_usize_land(v___x_2683_, v___x_2686_);
v___x_2688_ = lean_array_uget_borrowed(v_x_2667_, v___x_2687_);
lean_inc(v___x_2688_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 2, v___x_2688_);
v___x_2690_ = v___x_2673_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_key_2669_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_value_2670_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_array_uset(v_x_2667_, v___x_2687_, v___x_2690_);
v_x_2667_ = v___x_2691_;
v_x_2668_ = v_tail_2671_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2695_, lean_object* v_source_2696_, lean_object* v_target_2697_){
_start:
{
lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = lean_array_get_size(v_source_2696_);
v___x_2699_ = lean_nat_dec_lt(v_i_2695_, v___x_2698_);
if (v___x_2699_ == 0)
{
lean_dec_ref(v_source_2696_);
lean_dec(v_i_2695_);
return v_target_2697_;
}
else
{
lean_object* v_es_2700_; lean_object* v___x_2701_; lean_object* v_source_2702_; lean_object* v_target_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_es_2700_ = lean_array_fget(v_source_2696_, v_i_2695_);
v___x_2701_ = lean_box(0);
v_source_2702_ = lean_array_fset(v_source_2696_, v_i_2695_, v___x_2701_);
v_target_2703_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2697_, v_es_2700_);
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = lean_nat_add(v_i_2695_, v___x_2704_);
lean_dec(v_i_2695_);
v_i_2695_ = v___x_2705_;
v_source_2696_ = v_source_2702_;
v_target_2697_ = v_target_2703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2707_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v_nbuckets_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2708_ = lean_array_get_size(v_data_2707_);
v___x_2709_ = lean_unsigned_to_nat(2u);
v_nbuckets_2710_ = lean_nat_mul(v___x_2708_, v___x_2709_);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_mk_array(v_nbuckets_2710_, v___x_2712_);
v___x_2714_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2711_, v_data_2707_, v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2715_, lean_object* v_x_2716_){
_start:
{
if (lean_obj_tag(v_x_2716_) == 0)
{
uint8_t v___x_2717_; 
v___x_2717_ = 0;
return v___x_2717_;
}
else
{
lean_object* v_key_2718_; lean_object* v_tail_2719_; uint8_t v___x_2720_; 
v_key_2718_ = lean_ctor_get(v_x_2716_, 0);
v_tail_2719_ = lean_ctor_get(v_x_2716_, 2);
v___x_2720_ = l_Lean_instBEqFVarId_beq(v_key_2718_, v_a_2715_);
if (v___x_2720_ == 0)
{
v_x_2716_ = v_tail_2719_;
goto _start;
}
else
{
return v___x_2720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2722_, lean_object* v_x_2723_){
_start:
{
uint8_t v_res_2724_; lean_object* v_r_2725_; 
v_res_2724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2722_, v_x_2723_);
lean_dec(v_x_2723_);
lean_dec(v_a_2722_);
v_r_2725_ = lean_box(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2726_, lean_object* v_a_2727_, lean_object* v_b_2728_){
_start:
{
lean_object* v_size_2729_; lean_object* v_buckets_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2773_; 
v_size_2729_ = lean_ctor_get(v_m_2726_, 0);
v_buckets_2730_ = lean_ctor_get(v_m_2726_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_m_2726_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2732_ = v_m_2726_;
v_isShared_2733_ = v_isSharedCheck_2773_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_buckets_2730_);
lean_inc(v_size_2729_);
lean_dec(v_m_2726_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2773_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; uint64_t v___x_2735_; uint64_t v___x_2736_; uint64_t v___x_2737_; uint64_t v_fold_2738_; uint64_t v___x_2739_; uint64_t v___x_2740_; uint64_t v___x_2741_; size_t v___x_2742_; size_t v___x_2743_; size_t v___x_2744_; size_t v___x_2745_; size_t v___x_2746_; lean_object* v_bkt_2747_; uint8_t v___x_2748_; 
v___x_2734_ = lean_array_get_size(v_buckets_2730_);
v___x_2735_ = l_Lean_instHashableFVarId_hash(v_a_2727_);
v___x_2736_ = 32ULL;
v___x_2737_ = lean_uint64_shift_right(v___x_2735_, v___x_2736_);
v_fold_2738_ = lean_uint64_xor(v___x_2735_, v___x_2737_);
v___x_2739_ = 16ULL;
v___x_2740_ = lean_uint64_shift_right(v_fold_2738_, v___x_2739_);
v___x_2741_ = lean_uint64_xor(v_fold_2738_, v___x_2740_);
v___x_2742_ = lean_uint64_to_usize(v___x_2741_);
v___x_2743_ = lean_usize_of_nat(v___x_2734_);
v___x_2744_ = ((size_t)1ULL);
v___x_2745_ = lean_usize_sub(v___x_2743_, v___x_2744_);
v___x_2746_ = lean_usize_land(v___x_2742_, v___x_2745_);
v_bkt_2747_ = lean_array_uget_borrowed(v_buckets_2730_, v___x_2746_);
v___x_2748_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2727_, v_bkt_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v_size_x27_2750_; lean_object* v___x_2751_; lean_object* v_buckets_x27_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2749_ = lean_unsigned_to_nat(1u);
v_size_x27_2750_ = lean_nat_add(v_size_2729_, v___x_2749_);
lean_dec(v_size_2729_);
lean_inc(v_bkt_2747_);
v___x_2751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2751_, 0, v_a_2727_);
lean_ctor_set(v___x_2751_, 1, v_b_2728_);
lean_ctor_set(v___x_2751_, 2, v_bkt_2747_);
v_buckets_x27_2752_ = lean_array_uset(v_buckets_2730_, v___x_2746_, v___x_2751_);
v___x_2753_ = lean_unsigned_to_nat(4u);
v___x_2754_ = lean_nat_mul(v_size_x27_2750_, v___x_2753_);
v___x_2755_ = lean_unsigned_to_nat(3u);
v___x_2756_ = lean_nat_div(v___x_2754_, v___x_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_array_get_size(v_buckets_x27_2752_);
v___x_2758_ = lean_nat_dec_le(v___x_2756_, v___x_2757_);
lean_dec(v___x_2756_);
if (v___x_2758_ == 0)
{
lean_object* v_val_2759_; lean_object* v___x_2761_; 
v_val_2759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2752_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v_val_2759_);
lean_ctor_set(v___x_2732_, 0, v_size_x27_2750_);
v___x_2761_ = v___x_2732_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_size_x27_2750_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_val_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
else
{
lean_object* v___x_2764_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v_buckets_x27_2752_);
lean_ctor_set(v___x_2732_, 0, v_size_x27_2750_);
v___x_2764_ = v___x_2732_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_size_x27_2750_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_buckets_x27_2752_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v___x_2766_; lean_object* v_buckets_x27_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
lean_inc(v_bkt_2747_);
v___x_2766_ = lean_box(0);
v_buckets_x27_2767_ = lean_array_uset(v_buckets_2730_, v___x_2746_, v___x_2766_);
v___x_2768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2727_, v_b_2728_, v_bkt_2747_);
v___x_2769_ = lean_array_uset(v_buckets_x27_2767_, v___x_2746_, v___x_2768_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v___x_2769_);
v___x_2771_ = v___x_2732_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_size_2729_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2774_, lean_object* v___x_2775_, lean_object* v_x_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2776_, v_var_2774_, v___x_2775_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2778_, lean_object* v_newVal_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_st_ref_get(v_a_2782_);
v___x_2785_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2778_, v_a_2780_, v_a_2781_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v_env_2787_; lean_object* v___x_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v_env_2787_ = lean_ctor_get(v___x_2784_, 0);
lean_inc_ref(v_env_2787_);
lean_dec(v___x_2784_);
v___x_2788_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2787_, v_a_2786_, v_newVal_2779_);
v___f_2789_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2789_, 0, v_var_2778_);
lean_closure_set(v___f_2789_, 1, v___x_2788_);
v___x_2790_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2789_, v_a_2780_, v_a_2781_);
return v___x_2790_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v___x_2784_);
lean_dec(v_newVal_2779_);
lean_dec(v_var_2778_);
v_a_2791_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2785_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2785_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2799_, lean_object* v_newVal_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2799_, v_newVal_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2806_, lean_object* v_newVal_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2806_, v_newVal_2807_, v_a_2808_, v_a_2809_, v_a_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2816_, lean_object* v_newVal_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2816_, v_newVal_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2826_, lean_object* v_m_2827_, lean_object* v_a_2828_, lean_object* v_b_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2827_, v_a_2828_, v_b_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2831_, lean_object* v_a_2832_, lean_object* v_x_2833_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2832_, v_x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2835_, lean_object* v_a_2836_, lean_object* v_x_2837_){
_start:
{
uint8_t v_res_2838_; lean_object* v_r_2839_; 
v_res_2838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2835_, v_a_2836_, v_x_2837_);
lean_dec(v_x_2837_);
lean_dec(v_a_2836_);
v_r_2839_ = lean_box(v_res_2838_);
return v_r_2839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2840_, lean_object* v_data_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2843_, lean_object* v_a_2844_, lean_object* v_b_2845_, lean_object* v_x_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2844_, v_b_2845_, v_x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2848_, lean_object* v_i_2849_, lean_object* v_source_2850_, lean_object* v_target_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2849_, v_source_2850_, v_target_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2853_, lean_object* v_x_2854_, lean_object* v_x_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2854_, v_x_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2857_, lean_object* v_x_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_box(0);
v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2858_, v_var_2857_, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v___f_2865_; lean_object* v___x_2866_; 
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2865_, 0, v_var_2861_);
v___x_2866_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2865_, v_a_2862_, v_a_2863_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2867_, v_a_2868_, v_a_2869_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2872_, v_a_2873_, v_a_2874_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_fst_2898_; lean_object* v_snd_2899_; lean_object* v_currFnIdx_2902_; lean_object* v_assignments_2903_; lean_object* v_funVals_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2895_ = lean_st_ref_get(v_a_2893_);
v___x_2896_ = lean_st_ref_take(v_a_2892_);
v_currFnIdx_2902_ = lean_ctor_get(v_a_2891_, 1);
v_assignments_2903_ = lean_ctor_get(v___x_2896_, 0);
lean_inc_ref(v_assignments_2903_);
v_funVals_2904_ = lean_ctor_get(v___x_2896_, 1);
lean_inc_ref(v_funVals_2904_);
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_array_get_size(v_funVals_2904_);
v___x_2907_ = lean_nat_dec_lt(v_currFnIdx_2902_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v_funVals_2904_);
lean_dec_ref(v_assignments_2903_);
lean_dec(v___x_2895_);
lean_dec(v_v_2890_);
v_fst_2898_ = v___x_2905_;
v_snd_2899_ = v___x_2896_;
goto v___jp_2897_;
}
else
{
lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2919_; 
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; lean_object* v_unused_2921_; 
v_unused_2920_ = lean_ctor_get(v___x_2896_, 1);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v___x_2896_, 0);
lean_dec(v_unused_2921_);
v___x_2909_ = v___x_2896_;
v_isShared_2910_ = v_isSharedCheck_2919_;
goto v_resetjp_2908_;
}
else
{
lean_dec(v___x_2896_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2919_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_env_2911_; lean_object* v_v_2912_; lean_object* v_xs_x27_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v_env_2911_ = lean_ctor_get(v___x_2895_, 0);
lean_inc_ref(v_env_2911_);
lean_dec(v___x_2895_);
v_v_2912_ = lean_array_fget(v_funVals_2904_, v_currFnIdx_2902_);
v_xs_x27_2913_ = lean_array_fset(v_funVals_2904_, v_currFnIdx_2902_, v___x_2905_);
v___x_2914_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2911_, v_v_2890_, v_v_2912_);
v___x_2915_ = lean_array_fset(v_xs_x27_2913_, v_currFnIdx_2902_, v___x_2914_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_2915_);
v___x_2917_ = v___x_2909_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_assignments_2903_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
v_fst_2898_ = v___x_2905_;
v_snd_2899_ = v___x_2917_;
goto v___jp_2897_;
}
}
}
v___jp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_st_ref_set(v_a_2892_, v_snd_2899_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_fst_2898_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2928_, v_a_2929_, v_a_2930_, v_a_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2946_, uint8_t v_b_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_array_2952_; lean_object* v_start_2953_; lean_object* v_stop_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2991_; 
v_array_2952_ = lean_ctor_get(v_a_2946_, 0);
v_start_2953_ = lean_ctor_get(v_a_2946_, 1);
v_stop_2954_ = lean_ctor_get(v_a_2946_, 2);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_a_2946_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2956_ = v_a_2946_;
v_isShared_2957_ = v_isSharedCheck_2991_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_stop_2954_);
lean_inc(v_start_2953_);
lean_inc(v_array_2952_);
lean_dec(v_a_2946_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2991_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
uint8_t v___x_2958_; 
v___x_2958_ = lean_nat_dec_lt(v_start_2953_, v_stop_2954_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_del_object(v___x_2956_);
lean_dec(v_stop_2954_);
lean_dec(v_start_2953_);
lean_dec_ref(v_array_2952_);
v___x_2959_ = lean_box(v_b_2947_);
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
else
{
lean_object* v___x_2961_; lean_object* v_fvarId_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_array_fget_borrowed(v_array_2952_, v_start_2953_);
v_fvarId_2962_ = lean_ctor_get(v___x_2961_, 0);
v___x_2963_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2962_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = lean_box(1);
lean_inc(v_fvarId_2962_);
v___x_2966_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2962_, v___x_2965_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2966_, 1);
v___x_2967_ = lean_unsigned_to_nat(1u);
v___x_2968_ = lean_nat_add(v_start_2953_, v___x_2967_);
lean_dec(v_start_2953_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2968_);
v___x_2970_ = v___x_2956_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_array_2952_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_stop_2954_);
v___x_2970_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_box(0);
v___x_2972_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2964_, v___x_2971_);
lean_dec(v_a_2964_);
v_a_2946_ = v___x_2970_;
v_b_2947_ = v___x_2972_;
goto _start;
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_a_2964_);
lean_del_object(v___x_2956_);
lean_dec(v_stop_2954_);
lean_dec(v_start_2953_);
lean_dec_ref(v_array_2952_);
v_a_2975_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2966_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2966_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_del_object(v___x_2956_);
lean_dec(v_stop_2954_);
lean_dec(v_start_2953_);
lean_dec_ref(v_array_2952_);
v_a_2983_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2963_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2963_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2992_, lean_object* v_b_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v_b_boxed_2998_; lean_object* v_res_2999_; 
v_b_boxed_2998_ = lean_unbox(v_b_2993_);
v_res_2999_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2992_, v_b_boxed_2998_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_3000_, lean_object* v___x_3001_, lean_object* v_x_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_3002_, v_fvarId_3000_, v___x_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_3004_, lean_object* v_as_3005_, size_t v_sz_3006_, size_t v_i_3007_, lean_object* v_b_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_a_3013_; uint8_t v___x_3017_; 
v___x_3017_ = lean_usize_dec_lt(v_i_3007_, v_sz_3006_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; 
lean_dec_ref(v___x_3004_);
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_b_3008_);
return v___x_3018_;
}
else
{
lean_object* v_snd_3019_; lean_object* v_fst_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3086_; 
v_snd_3019_ = lean_ctor_get(v_b_3008_, 1);
v_fst_3020_ = lean_ctor_get(v_b_3008_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_b_3008_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3022_ = v_b_3008_;
v_isShared_3023_ = v_isSharedCheck_3086_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_snd_3019_);
lean_inc(v_fst_3020_);
lean_dec(v_b_3008_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3086_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_array_3024_; lean_object* v_start_3025_; lean_object* v_stop_3026_; uint8_t v___x_3027_; 
v_array_3024_ = lean_ctor_get(v_snd_3019_, 0);
v_start_3025_ = lean_ctor_get(v_snd_3019_, 1);
v_stop_3026_ = lean_ctor_get(v_snd_3019_, 2);
v___x_3027_ = lean_nat_dec_lt(v_start_3025_, v_stop_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3029_; 
lean_dec_ref(v___x_3004_);
if (v_isShared_3023_ == 0)
{
v___x_3029_ = v___x_3022_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_fst_3020_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_snd_3019_);
v___x_3029_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
return v___x_3030_;
}
}
else
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3082_; 
lean_inc(v_stop_3026_);
lean_inc(v_start_3025_);
lean_inc_ref(v_array_3024_);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_snd_3019_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; lean_object* v_unused_3084_; lean_object* v_unused_3085_; 
v_unused_3083_ = lean_ctor_get(v_snd_3019_, 2);
lean_dec(v_unused_3083_);
v_unused_3084_ = lean_ctor_get(v_snd_3019_, 1);
lean_dec(v_unused_3084_);
v_unused_3085_ = lean_ctor_get(v_snd_3019_, 0);
lean_dec(v_unused_3085_);
v___x_3033_ = v_snd_3019_;
v_isShared_3034_ = v_isSharedCheck_3082_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v_snd_3019_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3082_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v_a_3035_; lean_object* v_fvarId_3036_; lean_object* v___x_3037_; 
v_a_3035_ = lean_array_uget_borrowed(v_as_3005_, v_i_3007_);
v_fvarId_3036_ = lean_ctor_get(v_a_3035_, 0);
v___x_3037_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3036_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3039_ = lean_array_fget_borrowed(v_array_3024_, v_start_3025_);
v___x_3040_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_3039_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v___x_3042_ = lean_unsigned_to_nat(1u);
v___x_3043_ = lean_nat_add(v_start_3025_, v___x_3042_);
lean_dec(v_start_3025_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v___x_3043_);
v___x_3045_ = v___x_3033_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_array_3024_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_stop_3026_);
v___x_3045_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
lean_inc(v_a_3038_);
lean_inc_ref(v___x_3004_);
v___x_3046_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_3004_, v_a_3038_, v_a_3041_);
v___x_3047_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3046_, v_a_3038_);
lean_dec(v_a_3038_);
if (v___x_3047_ == 0)
{
lean_object* v___f_3048_; lean_object* v___x_3049_; 
lean_dec(v_fst_3020_);
lean_inc(v_fvarId_3036_);
v___f_3048_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3048_, 0, v_fvarId_3036_);
lean_closure_set(v___f_3048_, 1, v___x_3046_);
v___x_3049_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3048_, v___y_3009_, v___y_3010_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3052_; 
lean_dec_ref_known(v___x_3049_, 1);
v___x_3050_ = lean_box(v___x_3027_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3045_);
lean_ctor_set(v___x_3022_, 0, v___x_3050_);
v___x_3052_ = v___x_3022_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3045_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
v_a_3013_ = v___x_3052_;
goto v___jp_3012_;
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___x_3045_);
lean_del_object(v___x_3022_);
lean_dec_ref(v___x_3004_);
v_a_3054_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3049_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3049_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
else
{
lean_object* v___x_3063_; 
lean_dec(v___x_3046_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3045_);
v___x_3063_ = v___x_3022_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_fst_3020_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3045_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
v_a_3013_ = v___x_3063_;
goto v___jp_3012_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v_a_3038_);
lean_del_object(v___x_3033_);
lean_dec(v_stop_3026_);
lean_dec(v_start_3025_);
lean_dec_ref(v_array_3024_);
lean_del_object(v___x_3022_);
lean_dec(v_fst_3020_);
lean_dec_ref(v___x_3004_);
v_a_3066_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3040_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3040_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_del_object(v___x_3033_);
lean_dec(v_stop_3026_);
lean_dec(v_start_3025_);
lean_dec_ref(v_array_3024_);
lean_del_object(v___x_3022_);
lean_dec(v_fst_3020_);
lean_dec_ref(v___x_3004_);
v_a_3074_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3037_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3037_);
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
}
}
}
v___jp_3012_:
{
size_t v___x_3014_; size_t v___x_3015_; 
v___x_3014_ = ((size_t)1ULL);
v___x_3015_ = lean_usize_add(v_i_3007_, v___x_3014_);
v_i_3007_ = v___x_3015_;
v_b_3008_ = v_a_3013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3087_, lean_object* v_as_3088_, lean_object* v_sz_3089_, lean_object* v_i_3090_, lean_object* v_b_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
size_t v_sz_boxed_3095_; size_t v_i_boxed_3096_; lean_object* v_res_3097_; 
v_sz_boxed_3095_ = lean_unbox_usize(v_sz_3089_);
lean_dec(v_sz_3089_);
v_i_boxed_3096_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_res_3097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3087_, v_as_3088_, v_sz_boxed_3095_, v_i_boxed_3096_, v_b_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v_as_3088_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3098_, lean_object* v_args_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v___x_3107_; lean_object* v_env_3108_; uint8_t v_ret_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; size_t v_sz_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3107_ = lean_st_ref_get(v_a_3105_);
v_env_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc_ref(v_env_3108_);
lean_dec(v___x_3107_);
v_ret_3109_ = 0;
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_array_get_size(v_args_3099_);
v___x_3112_ = l_Array_toSubarray___redArg(v_args_3099_, v___x_3110_, v___x_3111_);
v___x_3113_ = lean_box(v_ret_3109_);
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v___x_3112_);
v_sz_3115_ = lean_array_size(v_params_3098_);
v___x_3116_ = ((size_t)0ULL);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3108_, v_params_3098_, v_sz_3115_, v___x_3116_, v___x_3114_, v_a_3100_, v_a_3101_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3135_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3135_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3135_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v_fst_3122_; lean_object* v_lower_3124_; lean_object* v_upper_3125_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_fst_3122_ = lean_ctor_get(v_a_3118_, 0);
lean_inc(v_fst_3122_);
lean_dec(v_a_3118_);
v___x_3129_ = lean_array_get_size(v_params_3098_);
v___x_3130_ = lean_nat_dec_eq(v___x_3129_, v___x_3111_);
if (v___x_3130_ == 0)
{
uint8_t v___x_3131_; 
lean_del_object(v___x_3120_);
v___x_3131_ = lean_nat_dec_le(v___x_3111_, v___x_3110_);
if (v___x_3131_ == 0)
{
v_lower_3124_ = v___x_3111_;
v_upper_3125_ = v___x_3129_;
goto v___jp_3123_;
}
else
{
v_lower_3124_ = v___x_3110_;
v_upper_3125_ = v___x_3129_;
goto v___jp_3123_;
}
}
else
{
lean_object* v___x_3133_; 
lean_dec_ref(v_params_3098_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v_fst_3122_);
v___x_3133_ = v___x_3120_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_fst_3122_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
v___jp_3123_:
{
lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = l_Array_toSubarray___redArg(v_params_3098_, v_lower_3124_, v_upper_3125_);
v___x_3127_ = lean_unbox(v_fst_3122_);
lean_dec(v_fst_3122_);
v___x_3128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3126_, v___x_3127_, v_a_3100_, v_a_3101_, v_a_3105_);
return v___x_3128_;
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v_params_3098_);
v_a_3136_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3117_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3117_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3144_, lean_object* v_args_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3144_, v_args_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3154_, lean_object* v_as_3155_, size_t v_sz_3156_, size_t v_i_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3154_, v_as_3155_, v_sz_3156_, v_i_3157_, v_b_3158_, v___y_3159_, v___y_3160_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3167_, lean_object* v_as_3168_, lean_object* v_sz_3169_, lean_object* v_i_3170_, lean_object* v_b_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
size_t v_sz_boxed_3179_; size_t v_i_boxed_3180_; lean_object* v_res_3181_; 
v_sz_boxed_3179_ = lean_unbox_usize(v_sz_3169_);
lean_dec(v_sz_3169_);
v_i_boxed_3180_ = lean_unbox_usize(v_i_3170_);
lean_dec(v_i_3170_);
v_res_3181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3167_, v_as_3168_, v_sz_boxed_3179_, v_i_boxed_3180_, v_b_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v_as_3168_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3182_, lean_object* v_R_3183_, lean_object* v_a_3184_, uint8_t v_b_3185_, lean_object* v_c_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3184_, v_b_3185_, v___y_3187_, v___y_3188_, v___y_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3195_, lean_object* v_R_3196_, lean_object* v_a_3197_, lean_object* v_b_3198_, lean_object* v_c_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
uint8_t v_b_boxed_3207_; lean_object* v_res_3208_; 
v_b_boxed_3207_ = lean_unbox(v_b_3198_);
v_res_3208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3195_, v_R_3196_, v_a_3197_, v_b_boxed_3207_, v_c_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3209_, size_t v_sz_3210_, size_t v_i_3211_, uint8_t v_b_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
uint8_t v_a_3217_; uint8_t v___x_3221_; 
v___x_3221_ = lean_usize_dec_lt(v_i_3211_, v_sz_3210_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_box(v_b_3212_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
else
{
lean_object* v_a_3224_; lean_object* v_fvarId_3225_; lean_object* v___x_3226_; 
v_a_3224_ = lean_array_uget_borrowed(v_as_3209_, v_i_3211_);
v_fvarId_3225_ = lean_ctor_get(v_a_3224_, 0);
v___x_3226_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3225_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = lean_box(1);
v___x_3229_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3228_, v_a_3227_);
lean_dec(v_a_3227_);
if (v___x_3229_ == 0)
{
lean_object* v___f_3230_; lean_object* v___x_3231_; 
lean_inc(v_fvarId_3225_);
v___f_3230_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3230_, 0, v_fvarId_3225_);
lean_closure_set(v___f_3230_, 1, v___x_3228_);
v___x_3231_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3230_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_dec_ref_known(v___x_3231_, 1);
v_a_3217_ = v___x_3221_;
goto v___jp_3216_;
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
v_a_3217_ = v_b_3212_;
goto v___jp_3216_;
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
v_a_3240_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3226_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3226_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
v___jp_3216_:
{
size_t v___x_3218_; size_t v___x_3219_; 
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_add(v_i_3211_, v___x_3218_);
v_i_3211_ = v___x_3219_;
v_b_3212_ = v_a_3217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3248_, lean_object* v_sz_3249_, lean_object* v_i_3250_, lean_object* v_b_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
size_t v_sz_boxed_3255_; size_t v_i_boxed_3256_; uint8_t v_b_boxed_3257_; lean_object* v_res_3258_; 
v_sz_boxed_3255_ = lean_unbox_usize(v_sz_3249_);
lean_dec(v_sz_3249_);
v_i_boxed_3256_ = lean_unbox_usize(v_i_3250_);
lean_dec(v_i_3250_);
v_b_boxed_3257_ = lean_unbox(v_b_3251_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3248_, v_sz_boxed_3255_, v_i_boxed_3256_, v_b_boxed_3257_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v_as_3248_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
uint8_t v_ret_3267_; size_t v_sz_3268_; size_t v___x_3269_; lean_object* v___x_3270_; 
v_ret_3267_ = 0;
v_sz_3268_ = lean_array_size(v_params_3259_);
v___x_3269_ = ((size_t)0ULL);
v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3259_, v_sz_3268_, v___x_3269_, v_ret_3267_, v_a_3260_, v_a_3261_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec_ref(v_params_3271_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3280_, size_t v_sz_3281_, size_t v_i_3282_, uint8_t v_b_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3280_, v_sz_3281_, v_i_3282_, v_b_3283_, v___y_3284_, v___y_3285_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3292_, lean_object* v_sz_3293_, lean_object* v_i_3294_, lean_object* v_b_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
size_t v_sz_boxed_3303_; size_t v_i_boxed_3304_; uint8_t v_b_boxed_3305_; lean_object* v_res_3306_; 
v_sz_boxed_3303_ = lean_unbox_usize(v_sz_3293_);
lean_dec(v_sz_3293_);
v_i_boxed_3304_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_b_boxed_3305_ = lean_unbox(v_b_3295_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3292_, v_sz_boxed_3303_, v_i_boxed_3304_, v_b_boxed_3305_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v_as_3292_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3307_, size_t v_i_3308_, size_t v_stop_3309_, lean_object* v_b_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
uint8_t v___x_3314_; 
v___x_3314_ = lean_usize_dec_eq(v_i_3308_, v_stop_3309_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v_fvarId_3316_; lean_object* v___x_3317_; 
v___x_3315_ = lean_array_uget_borrowed(v_as_3307_, v_i_3308_);
v_fvarId_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_fvarId_3316_);
v___x_3317_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3316_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; size_t v___x_3319_; size_t v___x_3320_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = ((size_t)1ULL);
v___x_3320_ = lean_usize_add(v_i_3308_, v___x_3319_);
v_i_3308_ = v___x_3320_;
v_b_3310_ = v_a_3318_;
goto _start;
}
else
{
return v___x_3317_;
}
}
else
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v_b_3310_);
return v___x_3322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3323_, lean_object* v_i_3324_, lean_object* v_stop_3325_, lean_object* v_b_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
size_t v_i_boxed_3330_; size_t v_stop_boxed_3331_; lean_object* v_res_3332_; 
v_i_boxed_3330_ = lean_unbox_usize(v_i_3324_);
lean_dec(v_i_3324_);
v_stop_boxed_3331_ = lean_unbox_usize(v_stop_3325_);
lean_dec(v_stop_3325_);
v_res_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3323_, v_i_boxed_3330_, v_stop_boxed_3331_, v_b_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v_as_3323_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v_decl_3352_; lean_object* v_k_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; 
switch(lean_obj_tag(v_x_3333_))
{
case 0:
{
lean_object* v_k_3374_; 
v_k_3374_ = lean_ctor_get(v_x_3333_, 1);
lean_inc_ref(v_k_3374_);
lean_dec_ref_known(v_x_3333_, 2);
v_x_3333_ = v_k_3374_;
goto _start;
}
case 3:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec_ref_known(v_x_3333_, 2);
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
return v___x_3377_;
}
case 4:
{
lean_object* v_cases_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3400_; 
v_cases_3378_ = lean_ctor_get(v_x_3333_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_x_3333_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3380_ = v_x_3333_;
v_isShared_3381_ = v_isSharedCheck_3400_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_cases_3378_);
lean_dec(v_x_3333_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3400_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v_alts_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_alts_3382_ = lean_ctor_get(v_cases_3378_, 3);
lean_inc_ref(v_alts_3382_);
lean_dec_ref(v_cases_3378_);
v___x_3383_ = lean_unsigned_to_nat(0u);
v___x_3384_ = lean_array_get_size(v_alts_3382_);
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_nat_dec_lt(v___x_3383_, v___x_3384_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3388_; 
lean_dec_ref(v_alts_3382_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3385_);
v___x_3388_ = v___x_3380_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3385_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
else
{
uint8_t v___x_3390_; 
v___x_3390_ = lean_nat_dec_le(v___x_3384_, v___x_3384_);
if (v___x_3390_ == 0)
{
if (v___x_3386_ == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref(v_alts_3382_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3385_);
v___x_3392_ = v___x_3380_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3385_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
else
{
size_t v___x_3394_; size_t v___x_3395_; lean_object* v___x_3396_; 
lean_del_object(v___x_3380_);
v___x_3394_ = ((size_t)0ULL);
v___x_3395_ = lean_usize_of_nat(v___x_3384_);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3382_, v___x_3394_, v___x_3395_, v___x_3385_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec_ref(v_alts_3382_);
return v___x_3396_;
}
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
lean_del_object(v___x_3380_);
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3384_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3382_, v___x_3397_, v___x_3398_, v___x_3385_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec_ref(v_alts_3382_);
return v___x_3399_;
}
}
}
}
case 5:
{
lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3408_; 
v_isSharedCheck_3408_ = !lean_is_exclusive(v_x_3333_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v_x_3333_, 0);
lean_dec(v_unused_3409_);
v___x_3402_ = v_x_3333_;
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
else
{
lean_dec(v_x_3333_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = lean_box(0);
if (v_isShared_3403_ == 0)
{
lean_ctor_set_tag(v___x_3402_, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3404_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
case 6:
{
lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3417_; 
v_isSharedCheck_3417_ = !lean_is_exclusive(v_x_3333_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v_x_3333_, 0);
lean_dec(v_unused_3418_);
v___x_3411_ = v_x_3333_;
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
else
{
lean_dec(v_x_3333_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3415_ = v___x_3411_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
default: 
{
lean_object* v_decl_3419_; lean_object* v_k_3420_; 
v_decl_3419_ = lean_ctor_get(v_x_3333_, 0);
lean_inc_ref(v_decl_3419_);
v_k_3420_ = lean_ctor_get(v_x_3333_, 1);
lean_inc_ref(v_k_3420_);
lean_dec_ref(v_x_3333_);
v_decl_3352_ = v_decl_3419_;
v_k_3353_ = v_k_3420_;
v___y_3354_ = v_a_3334_;
v___y_3355_ = v_a_3335_;
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
goto v___jp_3351_;
}
}
v___jp_3341_:
{
if (lean_obj_tag(v___y_3349_) == 0)
{
lean_dec_ref_known(v___y_3349_, 1);
v_x_3333_ = v___y_3345_;
v_a_3334_ = v___y_3348_;
v_a_3335_ = v___y_3343_;
v_a_3336_ = v___y_3347_;
v_a_3337_ = v___y_3344_;
v_a_3338_ = v___y_3346_;
v_a_3339_ = v___y_3342_;
goto _start;
}
else
{
lean_dec_ref(v___y_3345_);
return v___y_3349_;
}
}
v___jp_3351_:
{
lean_object* v_params_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_params_3360_ = lean_ctor_get(v_decl_3352_, 2);
lean_inc_ref(v_params_3360_);
lean_dec_ref(v_decl_3352_);
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = lean_array_get_size(v_params_3360_);
v___x_3363_ = lean_nat_dec_lt(v___x_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
lean_dec_ref(v_params_3360_);
v_x_3333_ = v_k_3353_;
v_a_3334_ = v___y_3354_;
v_a_3335_ = v___y_3355_;
v_a_3336_ = v___y_3356_;
v_a_3337_ = v___y_3357_;
v_a_3338_ = v___y_3358_;
v_a_3339_ = v___y_3359_;
goto _start;
}
else
{
lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_nat_dec_le(v___x_3362_, v___x_3362_);
if (v___x_3366_ == 0)
{
if (v___x_3363_ == 0)
{
lean_dec_ref(v_params_3360_);
v_x_3333_ = v_k_3353_;
v_a_3334_ = v___y_3354_;
v_a_3335_ = v___y_3355_;
v_a_3336_ = v___y_3356_;
v_a_3337_ = v___y_3357_;
v_a_3338_ = v___y_3358_;
v_a_3339_ = v___y_3359_;
goto _start;
}
else
{
size_t v___x_3368_; size_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = lean_usize_of_nat(v___x_3362_);
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3360_, v___x_3368_, v___x_3369_, v___x_3365_, v___y_3354_, v___y_3355_);
lean_dec_ref(v_params_3360_);
v___y_3342_ = v___y_3359_;
v___y_3343_ = v___y_3355_;
v___y_3344_ = v___y_3357_;
v___y_3345_ = v_k_3353_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3356_;
v___y_3348_ = v___y_3354_;
v___y_3349_ = v___x_3370_;
goto v___jp_3341_;
}
}
else
{
size_t v___x_3371_; size_t v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = ((size_t)0ULL);
v___x_3372_ = lean_usize_of_nat(v___x_3362_);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3360_, v___x_3371_, v___x_3372_, v___x_3365_, v___y_3354_, v___y_3355_);
lean_dec_ref(v_params_3360_);
v___y_3342_ = v___y_3359_;
v___y_3343_ = v___y_3355_;
v___y_3344_ = v___y_3357_;
v___y_3345_ = v_k_3353_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3356_;
v___y_3348_ = v___y_3354_;
v___y_3349_ = v___x_3373_;
goto v___jp_3341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3421_, size_t v_i_3422_, size_t v_stop_3423_, lean_object* v_b_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___y_3433_; uint8_t v___x_3439_; 
v___x_3439_ = lean_usize_dec_eq(v_i_3422_, v_stop_3423_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_array_uget_borrowed(v_as_3421_, v_i_3422_);
switch(lean_obj_tag(v___x_3440_))
{
case 0:
{
lean_object* v_code_3441_; 
v_code_3441_ = lean_ctor_get(v___x_3440_, 2);
lean_inc_ref(v_code_3441_);
v___y_3433_ = v_code_3441_;
goto v___jp_3432_;
}
case 1:
{
lean_object* v_code_3442_; 
v_code_3442_ = lean_ctor_get(v___x_3440_, 1);
lean_inc_ref(v_code_3442_);
v___y_3433_ = v_code_3442_;
goto v___jp_3432_;
}
default: 
{
lean_object* v_code_3443_; 
v_code_3443_ = lean_ctor_get(v___x_3440_, 0);
lean_inc_ref(v_code_3443_);
v___y_3433_ = v_code_3443_;
goto v___jp_3432_;
}
}
}
else
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_b_3424_);
return v___x_3444_;
}
v___jp_3432_:
{
lean_object* v___x_3434_; 
v___x_3434_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3433_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; size_t v___x_3436_; size_t v___x_3437_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = ((size_t)1ULL);
v___x_3437_ = lean_usize_add(v_i_3422_, v___x_3436_);
v_i_3422_ = v___x_3437_;
v_b_3424_ = v_a_3435_;
goto _start;
}
else
{
return v___x_3434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3445_, lean_object* v_i_3446_, lean_object* v_stop_3447_, lean_object* v_b_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
size_t v_i_boxed_3456_; size_t v_stop_boxed_3457_; lean_object* v_res_3458_; 
v_i_boxed_3456_ = lean_unbox_usize(v_i_3446_);
lean_dec(v_i_3446_);
v_stop_boxed_3457_ = lean_unbox_usize(v_stop_3447_);
lean_dec(v_stop_3447_);
v_res_3458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3445_, v_i_boxed_3456_, v_stop_boxed_3457_, v_b_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec_ref(v_as_3445_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3468_, size_t v_i_3469_, size_t v_stop_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3468_, v_i_3469_, v_stop_3470_, v_b_3471_, v___y_3472_, v___y_3473_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3480_, lean_object* v_i_3481_, lean_object* v_stop_3482_, lean_object* v_b_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
size_t v_i_boxed_3491_; size_t v_stop_boxed_3492_; lean_object* v_res_3493_; 
v_i_boxed_3491_ = lean_unbox_usize(v_i_3481_);
lean_dec(v_i_3481_);
v_stop_boxed_3492_ = lean_unbox_usize(v_stop_3482_);
lean_dec(v_stop_3482_);
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3480_, v_i_boxed_3491_, v_stop_boxed_3492_, v_b_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v_as_3480_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3494_, lean_object* v_b_3495_){
_start:
{
lean_object* v_array_3496_; lean_object* v_start_3497_; lean_object* v_stop_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3511_; 
v_array_3496_ = lean_ctor_get(v_a_3494_, 0);
v_start_3497_ = lean_ctor_get(v_a_3494_, 1);
v_stop_3498_ = lean_ctor_get(v_a_3494_, 2);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_a_3494_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3500_ = v_a_3494_;
v_isShared_3501_ = v_isSharedCheck_3511_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_stop_3498_);
lean_inc(v_start_3497_);
lean_inc(v_array_3496_);
lean_dec(v_a_3494_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3511_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_nat_dec_lt(v_start_3497_, v_stop_3498_);
if (v___x_3502_ == 0)
{
lean_del_object(v___x_3500_);
lean_dec(v_stop_3498_);
lean_dec(v_start_3497_);
lean_dec_ref(v_array_3496_);
return v_b_3495_;
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3506_; 
v___x_3503_ = lean_unsigned_to_nat(1u);
v___x_3504_ = lean_nat_add(v_start_3497_, v___x_3503_);
lean_inc_ref(v_array_3496_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3504_);
v___x_3506_ = v___x_3500_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_array_3496_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_stop_3498_);
v___x_3506_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_array_fget(v_array_3496_, v_start_3497_);
lean_dec(v_start_3497_);
lean_dec_ref(v_array_3496_);
v___x_3508_ = lean_array_push(v_b_3495_, v___x_3507_);
v_a_3494_ = v___x_3506_;
v_b_3495_ = v___x_3508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3512_, size_t v_i_3513_, lean_object* v_bs_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v___x_3518_; 
v___x_3518_ = lean_usize_dec_lt(v_i_3513_, v_sz_3512_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_bs_3514_);
return v___x_3519_;
}
else
{
lean_object* v_v_3520_; lean_object* v___x_3521_; 
v_v_3520_ = lean_array_uget_borrowed(v_bs_3514_, v_i_3513_);
v___x_3521_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3520_, v___y_3515_, v___y_3516_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; lean_object* v_bs_x27_3524_; size_t v___x_3525_; size_t v___x_3526_; lean_object* v___x_3527_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = lean_unsigned_to_nat(0u);
v_bs_x27_3524_ = lean_array_uset(v_bs_3514_, v_i_3513_, v___x_3523_);
v___x_3525_ = ((size_t)1ULL);
v___x_3526_ = lean_usize_add(v_i_3513_, v___x_3525_);
v___x_3527_ = lean_array_uset(v_bs_x27_3524_, v_i_3513_, v_a_3522_);
v_i_3513_ = v___x_3526_;
v_bs_3514_ = v___x_3527_;
goto _start;
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v_bs_3514_);
v_a_3529_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3521_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3521_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3537_, lean_object* v_i_3538_, lean_object* v_bs_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
size_t v_sz_boxed_3543_; size_t v_i_boxed_3544_; lean_object* v_res_3545_; 
v_sz_boxed_3543_ = lean_unbox_usize(v_sz_3537_);
lean_dec(v_sz_3537_);
v_i_boxed_3544_ = lean_unbox_usize(v_i_3538_);
lean_dec(v_i_3538_);
v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3543_, v_i_boxed_3544_, v_bs_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3546_, size_t v_i_3547_, size_t v_stop_3548_, lean_object* v_b_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v___x_3554_; 
v___x_3554_ = lean_usize_dec_eq(v_i_3547_, v_stop_3548_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v_fvarId_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3555_ = lean_array_uget_borrowed(v_as_3546_, v_i_3547_);
v_fvarId_3556_ = lean_ctor_get(v___x_3555_, 0);
v___x_3557_ = lean_box(1);
lean_inc(v_fvarId_3556_);
v___x_3558_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3556_, v___x_3557_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; size_t v___x_3560_; size_t v___x_3561_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
v___x_3560_ = ((size_t)1ULL);
v___x_3561_ = lean_usize_add(v_i_3547_, v___x_3560_);
v_i_3547_ = v___x_3561_;
v_b_3549_ = v_a_3559_;
goto _start;
}
else
{
return v___x_3558_;
}
}
else
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v_b_3549_);
return v___x_3563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3564_, lean_object* v_i_3565_, lean_object* v_stop_3566_, lean_object* v_b_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
size_t v_i_boxed_3572_; size_t v_stop_boxed_3573_; lean_object* v_res_3574_; 
v_i_boxed_3572_ = lean_unbox_usize(v_i_3565_);
lean_dec(v_i_3565_);
v_stop_boxed_3573_ = lean_unbox_usize(v_stop_3566_);
lean_dec(v_stop_3566_);
v_res_3574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3564_, v_i_boxed_3572_, v_stop_boxed_3573_, v_b_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_as_3564_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3575_, size_t v_i_3576_, size_t v_stop_3577_, lean_object* v_b_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
uint8_t v___x_3583_; 
v___x_3583_ = lean_usize_dec_eq(v_i_3576_, v_stop_3577_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; lean_object* v_fst_3585_; lean_object* v_snd_3586_; lean_object* v_fvarId_3587_; lean_object* v___x_3588_; 
v___x_3584_ = lean_array_uget_borrowed(v_as_3575_, v_i_3576_);
v_fst_3585_ = lean_ctor_get(v___x_3584_, 0);
v_snd_3586_ = lean_ctor_get(v___x_3584_, 1);
v_fvarId_3587_ = lean_ctor_get(v_fst_3585_, 0);
lean_inc(v_snd_3586_);
lean_inc(v_fvarId_3587_);
v___x_3588_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3587_, v_snd_3586_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; size_t v___x_3590_; size_t v___x_3591_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = ((size_t)1ULL);
v___x_3591_ = lean_usize_add(v_i_3576_, v___x_3590_);
v_i_3576_ = v___x_3591_;
v_b_3578_ = v_a_3589_;
goto _start;
}
else
{
return v___x_3588_;
}
}
else
{
lean_object* v___x_3593_; 
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v_b_3578_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3594_, lean_object* v_i_3595_, lean_object* v_stop_3596_, lean_object* v_b_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
size_t v_i_boxed_3602_; size_t v_stop_boxed_3603_; lean_object* v_res_3604_; 
v_i_boxed_3602_ = lean_unbox_usize(v_i_3595_);
lean_dec(v_i_3595_);
v_stop_boxed_3603_ = lean_unbox_usize(v_stop_3596_);
lean_dec(v_stop_3596_);
v_res_3604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3594_, v_i_boxed_3602_, v_stop_boxed_3603_, v_b_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v_as_3594_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3607_, size_t v_i_3608_, size_t v_stop_3609_, lean_object* v_b_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v___x_3618_; 
v___x_3618_ = lean_usize_dec_eq(v_i_3608_, v_stop_3609_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = lean_array_uget_borrowed(v_as_3607_, v_i_3608_);
v___x_3620_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3619_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; size_t v___x_3622_; size_t v___x_3623_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = ((size_t)1ULL);
v___x_3623_ = lean_usize_add(v_i_3608_, v___x_3622_);
v_i_3608_ = v___x_3623_;
v_b_3610_ = v_a_3621_;
goto _start;
}
else
{
return v___x_3620_;
}
}
else
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3625_, 0, v_b_3610_);
return v___x_3625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v___y_3641_; 
switch(lean_obj_tag(v_letVal_3626_))
{
case 0:
{
lean_object* v_value_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3658_; 
v_value_3650_ = lean_ctor_get(v_letVal_3626_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_letVal_3626_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3652_ = v_letVal_3626_;
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_value_3650_);
lean_dec(v_letVal_3626_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3650_);
lean_dec_ref(v_value_3650_);
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
}
case 1:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_box(1);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
return v___x_3660_;
}
case 2:
{
lean_object* v_idx_3661_; lean_object* v_struct_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_idx_3661_ = lean_ctor_get(v_letVal_3626_, 1);
lean_inc(v_idx_3661_);
v_struct_3662_ = lean_ctor_get(v_letVal_3626_, 2);
lean_inc(v_struct_3662_);
lean_dec_ref_known(v_letVal_3626_, 3);
v___x_3663_ = lean_st_ref_get(v_a_3632_);
v___x_3664_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3662_, v_a_3627_, v_a_3628_);
lean_dec(v_struct_3662_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3674_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3674_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3674_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_env_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v_env_3669_ = lean_ctor_get(v___x_3663_, 0);
lean_inc_ref(v_env_3669_);
lean_dec(v___x_3663_);
v___x_3670_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3669_, v_a_3665_, v_idx_3661_);
lean_dec(v_idx_3661_);
lean_dec(v_a_3665_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3670_);
v___x_3672_ = v___x_3667_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
else
{
lean_dec(v___x_3663_);
lean_dec(v_idx_3661_);
return v___x_3664_;
}
}
case 3:
{
lean_object* v_declName_3675_; lean_object* v_args_3676_; lean_object* v___x_3677_; lean_object* v_env_3678_; lean_object* v___x_3679_; lean_object* v___y_3681_; lean_object* v_lower_3682_; lean_object* v_upper_3683_; lean_object* v___x_3712_; lean_object* v_val_3714_; lean_object* v_numParams_3715_; lean_object* v___y_3718_; lean_object* v___y_3796_; uint8_t v___x_3805_; 
v_declName_3675_ = lean_ctor_get(v_letVal_3626_, 0);
lean_inc(v_declName_3675_);
v_args_3676_ = lean_ctor_get(v_letVal_3626_, 2);
lean_inc_ref(v_args_3676_);
lean_dec_ref_known(v_letVal_3626_, 3);
v___x_3677_ = lean_st_ref_get(v_a_3632_);
v_env_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc_ref(v_env_3678_);
lean_dec(v___x_3677_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3712_ = lean_array_get_size(v_args_3676_);
v___x_3805_ = lean_nat_dec_lt(v___x_3679_, v___x_3712_);
if (v___x_3805_ == 0)
{
goto v___jp_3729_;
}
else
{
lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3806_ = lean_box(0);
v___x_3807_ = lean_nat_dec_le(v___x_3712_, v___x_3712_);
if (v___x_3807_ == 0)
{
if (v___x_3805_ == 0)
{
goto v___jp_3729_;
}
else
{
size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = ((size_t)0ULL);
v___x_3809_ = lean_usize_of_nat(v___x_3712_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3676_, v___x_3808_, v___x_3809_, v___x_3806_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
v___y_3796_ = v___x_3810_;
goto v___jp_3795_;
}
}
else
{
size_t v___x_3811_; size_t v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((size_t)0ULL);
v___x_3812_ = lean_usize_of_nat(v___x_3712_);
v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3676_, v___x_3811_, v___x_3812_, v___x_3806_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
v___y_3796_ = v___x_3813_;
goto v___jp_3795_;
}
}
v___jp_3680_:
{
lean_object* v_numFields_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_numFields_3684_ = lean_ctor_get(v___y_3681_, 3);
lean_inc(v_numFields_3684_);
lean_dec_ref(v___y_3681_);
v___x_3685_ = l_Array_toSubarray___redArg(v_args_3676_, v_lower_3682_, v_upper_3683_);
v___x_3686_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3687_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3685_, v___x_3686_);
v___x_3688_ = lean_array_get_size(v___x_3687_);
v___x_3689_ = lean_nat_dec_eq(v_numFields_3684_, v___x_3688_);
lean_dec(v_numFields_3684_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
lean_dec_ref(v___x_3687_);
lean_dec(v_declName_3675_);
v___x_3690_ = lean_box(1);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
else
{
size_t v_sz_3692_; size_t v___x_3693_; lean_object* v___x_3694_; 
v_sz_3692_ = lean_array_size(v___x_3687_);
v___x_3693_ = ((size_t)0ULL);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3692_, v___x_3693_, v___x_3687_, v_a_3627_, v_a_3628_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3703_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3703_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3703_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3701_; 
v___x_3699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3699_, 0, v_declName_3675_);
lean_ctor_set(v___x_3699_, 1, v_a_3695_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3699_);
v___x_3701_ = v___x_3697_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_declName_3675_);
v_a_3704_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3694_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3694_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
v___jp_3713_:
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_nat_dec_le(v_numParams_3715_, v___x_3679_);
if (v___x_3716_ == 0)
{
v___y_3681_ = v_val_3714_;
v_lower_3682_ = v_numParams_3715_;
v_upper_3683_ = v___x_3712_;
goto v___jp_3680_;
}
else
{
lean_dec(v_numParams_3715_);
v___y_3681_ = v_val_3714_;
v_lower_3682_ = v___x_3679_;
v_upper_3683_ = v___x_3712_;
goto v___jp_3680_;
}
}
v___jp_3717_:
{
uint8_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = 0;
lean_inc(v_declName_3675_);
lean_inc_ref(v___y_3718_);
v___x_3720_ = l_Lean_Environment_find_x3f(v___y_3718_, v_declName_3675_, v___x_3719_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_args_3676_);
lean_dec(v_declName_3675_);
goto v___jp_3634_;
}
else
{
lean_object* v_val_3721_; 
v_val_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_val_3721_);
lean_dec_ref_known(v___x_3720_, 1);
if (lean_obj_tag(v_val_3721_) == 6)
{
lean_object* v_val_3722_; lean_object* v_induct_3723_; lean_object* v_cidx_3724_; lean_object* v_numParams_3725_; lean_object* v_numFields_3726_; uint8_t v___x_3727_; 
v_val_3722_ = lean_ctor_get(v_val_3721_, 0);
lean_inc_ref(v_val_3722_);
lean_dec_ref_known(v_val_3721_, 1);
v_induct_3723_ = lean_ctor_get(v_val_3722_, 1);
lean_inc_n(v_induct_3723_, 2);
v_cidx_3724_ = lean_ctor_get(v_val_3722_, 2);
lean_inc(v_cidx_3724_);
v_numParams_3725_ = lean_ctor_get(v_val_3722_, 3);
lean_inc(v_numParams_3725_);
v_numFields_3726_ = lean_ctor_get(v_val_3722_, 4);
lean_inc(v_numFields_3726_);
lean_dec_ref(v_val_3722_);
v___x_3727_ = l_Lean_Compiler_hasInductiveOverride(v___y_3718_, v_induct_3723_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; 
lean_inc(v_numParams_3725_);
v___x_3728_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3728_, 0, v_induct_3723_);
lean_ctor_set(v___x_3728_, 1, v_cidx_3724_);
lean_ctor_set(v___x_3728_, 2, v_numParams_3725_);
lean_ctor_set(v___x_3728_, 3, v_numFields_3726_);
v_val_3714_ = v___x_3728_;
v_numParams_3715_ = v_numParams_3725_;
goto v___jp_3713_;
}
else
{
lean_dec(v_numFields_3726_);
lean_dec(v_numParams_3725_);
lean_dec(v_cidx_3724_);
lean_dec(v_induct_3723_);
lean_dec_ref(v_args_3676_);
lean_dec(v_declName_3675_);
goto v___jp_3634_;
}
}
else
{
lean_dec(v_val_3721_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_args_3676_);
lean_dec(v_declName_3675_);
goto v___jp_3634_;
}
}
}
v___jp_3729_:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3629_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3732_ = lean_unbox(v_a_3731_);
lean_dec(v_a_3731_);
lean_inc(v_declName_3675_);
v___x_3733_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3675_, v___x_3732_, v_a_3631_, v_a_3632_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3778_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3778_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3778_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
if (lean_obj_tag(v_a_3734_) == 1)
{
lean_object* v_val_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
lean_dec_ref(v_args_3676_);
v_val_3738_ = lean_ctor_get(v_a_3734_, 0);
lean_inc(v_val_3738_);
lean_dec_ref_known(v_a_3734_, 1);
v___x_3739_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3738_);
lean_dec(v_val_3738_);
v___x_3740_ = lean_nat_dec_eq(v___x_3739_, v___x_3712_);
lean_dec(v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
lean_dec_ref(v_env_3678_);
lean_dec(v_declName_3675_);
v___x_3741_ = lean_box(1);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3741_);
v___x_3743_ = v___x_3736_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
else
{
lean_object* v___x_3745_; 
lean_inc(v_declName_3675_);
v___x_3745_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3678_, v_declName_3675_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v___x_3746_; 
lean_del_object(v___x_3736_);
v___x_3746_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3675_, v_a_3627_, v_a_3628_);
lean_dec(v_declName_3675_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3759_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3759_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3759_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
if (lean_obj_tag(v_a_3747_) == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3751_ = lean_box(1);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3751_);
v___x_3753_ = v___x_3749_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
else
{
lean_object* v_val_3755_; lean_object* v___x_3757_; 
v_val_3755_ = lean_ctor_get(v_a_3747_, 0);
lean_inc(v_val_3755_);
lean_dec_ref_known(v_a_3747_, 1);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v_val_3755_);
v___x_3757_ = v___x_3749_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_val_3755_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_a_3760_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3746_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3746_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_val_3768_; lean_object* v___x_3770_; 
lean_dec(v_declName_3675_);
v_val_3768_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_val_3768_);
lean_dec_ref_known(v___x_3745_, 1);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v_val_3768_);
v___x_3770_ = v___x_3736_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_val_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v___x_3772_; lean_object* v_env_3773_; lean_object* v___x_3774_; 
lean_del_object(v___x_3736_);
lean_dec(v_a_3734_);
lean_dec_ref(v_env_3678_);
v___x_3772_ = lean_st_ref_get(v_a_3632_);
v_env_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc_ref_n(v_env_3773_, 2);
lean_dec(v___x_3772_);
lean_inc(v_declName_3675_);
v___x_3774_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_3773_, v_declName_3675_);
if (lean_obj_tag(v___x_3774_) == 1)
{
lean_object* v_val_3775_; 
v_val_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v___x_3774_, 1);
if (lean_obj_tag(v_val_3775_) == 2)
{
lean_object* v_info_3776_; lean_object* v_numParams_3777_; 
lean_dec_ref(v_env_3773_);
v_info_3776_ = lean_ctor_get(v_val_3775_, 1);
lean_inc_ref(v_info_3776_);
lean_dec_ref_known(v_val_3775_, 2);
v_numParams_3777_ = lean_ctor_get(v_info_3776_, 2);
lean_inc(v_numParams_3777_);
v_val_3714_ = v_info_3776_;
v_numParams_3715_ = v_numParams_3777_;
goto v___jp_3713_;
}
else
{
lean_dec(v_val_3775_);
v___y_3718_ = v_env_3773_;
goto v___jp_3717_;
}
}
else
{
lean_dec(v___x_3774_);
v___y_3718_ = v_env_3773_;
goto v___jp_3717_;
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v_env_3678_);
lean_dec_ref(v_args_3676_);
lean_dec(v_declName_3675_);
v_a_3779_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3733_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3733_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v_env_3678_);
lean_dec_ref(v_args_3676_);
lean_dec(v_declName_3675_);
v_a_3787_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3730_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3730_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
v___jp_3795_:
{
if (lean_obj_tag(v___y_3796_) == 0)
{
lean_dec_ref_known(v___y_3796_, 1);
goto v___jp_3729_;
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_env_3678_);
lean_dec_ref(v_args_3676_);
lean_dec(v_declName_3675_);
v_a_3797_ = lean_ctor_get(v___y_3796_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___y_3796_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___y_3796_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___y_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
default: 
{
lean_object* v_args_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_args_3814_ = lean_ctor_get(v_letVal_3626_, 1);
lean_inc_ref(v_args_3814_);
lean_dec_ref_known(v_letVal_3626_, 2);
v___x_3815_ = lean_unsigned_to_nat(0u);
v___x_3816_ = lean_array_get_size(v_args_3814_);
v___x_3817_ = lean_nat_dec_lt(v___x_3815_, v___x_3816_);
if (v___x_3817_ == 0)
{
lean_dec_ref(v_args_3814_);
goto v___jp_3637_;
}
else
{
lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3818_ = lean_box(0);
v___x_3819_ = lean_nat_dec_le(v___x_3816_, v___x_3816_);
if (v___x_3819_ == 0)
{
if (v___x_3817_ == 0)
{
lean_dec_ref(v_args_3814_);
goto v___jp_3637_;
}
else
{
size_t v___x_3820_; size_t v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = lean_usize_of_nat(v___x_3816_);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3814_, v___x_3820_, v___x_3821_, v___x_3818_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
lean_dec_ref(v_args_3814_);
v___y_3641_ = v___x_3822_;
goto v___jp_3640_;
}
}
else
{
size_t v___x_3823_; size_t v___x_3824_; lean_object* v___x_3825_; 
v___x_3823_ = ((size_t)0ULL);
v___x_3824_ = lean_usize_of_nat(v___x_3816_);
v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3814_, v___x_3823_, v___x_3824_, v___x_3818_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
lean_dec_ref(v_args_3814_);
v___y_3641_ = v___x_3825_;
goto v___jp_3640_;
}
}
}
}
v___jp_3634_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_box(1);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
v___jp_3637_:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = lean_box(1);
v___x_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
return v___x_3639_;
}
v___jp_3640_:
{
if (lean_obj_tag(v___y_3641_) == 0)
{
lean_dec_ref_known(v___y_3641_, 1);
goto v___jp_3637_;
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
v_a_3642_ = lean_ctor_get(v___y_3641_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___y_3641_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___y_3641_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___y_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3826_, lean_object* v_args_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_params_3835_; lean_object* v_value_3836_; lean_object* v___x_3837_; 
v_params_3835_ = lean_ctor_get(v_funDecl_3826_, 2);
lean_inc_ref(v_params_3835_);
v_value_3836_ = lean_ctor_get(v_funDecl_3826_, 4);
lean_inc_ref(v_value_3836_);
lean_dec_ref(v_funDecl_3826_);
v___x_3837_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3835_, v_args_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3849_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3849_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3849_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
uint8_t v___x_3842_; 
v___x_3842_ = lean_unbox(v_a_3838_);
lean_dec(v_a_3838_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_dec_ref(v_value_3836_);
v___x_3843_ = lean_box(0);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3843_);
v___x_3845_ = v___x_3840_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
else
{
lean_object* v___x_3847_; 
lean_del_object(v___x_3840_);
lean_inc_ref(v_value_3836_);
v___x_3847_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3836_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v___x_3848_; 
lean_dec_ref_known(v___x_3847_, 1);
v___x_3848_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3836_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
return v___x_3848_;
}
else
{
lean_dec_ref(v_value_3836_);
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v_value_3836_);
v_a_3850_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3837_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3837_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3858_, lean_object* v_as_3859_, size_t v_sz_3860_, size_t v_i_3861_, lean_object* v_b_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_a_3871_; uint8_t v___x_3875_; 
v___x_3875_ = lean_usize_dec_lt(v_i_3861_, v_sz_3860_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v_b_3862_);
return v___x_3876_;
}
else
{
lean_object* v___x_3877_; lean_object* v_a_3878_; 
v___x_3877_ = lean_box(0);
v_a_3878_ = lean_array_uget_borrowed(v_as_3859_, v_i_3861_);
if (lean_obj_tag(v_a_3878_) == 0)
{
lean_object* v_ctorName_3879_; lean_object* v_params_3880_; lean_object* v_code_3881_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3891_; lean_object* v___y_3893_; lean_object* v___x_3894_; 
v_ctorName_3879_ = lean_ctor_get(v_a_3878_, 0);
v_params_3880_ = lean_ctor_get(v_a_3878_, 1);
v_code_3881_ = lean_ctor_get(v_a_3878_, 2);
v___x_3894_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3858_, v_ctorName_3879_);
if (lean_obj_tag(v___x_3894_) == 1)
{
lean_object* v_val_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v_val_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = l_Array_zip___redArg(v_params_3880_, v_val_3895_);
lean_dec(v_val_3895_);
v___x_3897_ = lean_unsigned_to_nat(0u);
v___x_3898_ = lean_array_get_size(v___x_3896_);
v___x_3899_ = lean_nat_dec_lt(v___x_3897_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_dec_ref(v___x_3896_);
v___y_3883_ = v___y_3863_;
v___y_3884_ = v___y_3864_;
v___y_3885_ = v___y_3865_;
v___y_3886_ = v___y_3866_;
v___y_3887_ = v___y_3867_;
v___y_3888_ = v___y_3868_;
goto v___jp_3882_;
}
else
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_nat_dec_le(v___x_3898_, v___x_3898_);
if (v___x_3900_ == 0)
{
if (v___x_3899_ == 0)
{
lean_dec_ref(v___x_3896_);
v___y_3883_ = v___y_3863_;
v___y_3884_ = v___y_3864_;
v___y_3885_ = v___y_3865_;
v___y_3886_ = v___y_3866_;
v___y_3887_ = v___y_3867_;
v___y_3888_ = v___y_3868_;
goto v___jp_3882_;
}
else
{
size_t v___x_3901_; size_t v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = ((size_t)0ULL);
v___x_3902_ = lean_usize_of_nat(v___x_3898_);
v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3896_, v___x_3901_, v___x_3902_, v___x_3877_, v___y_3863_, v___y_3864_, v___y_3868_);
lean_dec_ref(v___x_3896_);
v___y_3891_ = v___x_3903_;
goto v___jp_3890_;
}
}
else
{
size_t v___x_3904_; size_t v___x_3905_; lean_object* v___x_3906_; 
v___x_3904_ = ((size_t)0ULL);
v___x_3905_ = lean_usize_of_nat(v___x_3898_);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3896_, v___x_3904_, v___x_3905_, v___x_3877_, v___y_3863_, v___y_3864_, v___y_3868_);
lean_dec_ref(v___x_3896_);
v___y_3891_ = v___x_3906_;
goto v___jp_3890_;
}
}
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
lean_dec(v___x_3894_);
v___x_3907_ = lean_unsigned_to_nat(0u);
v___x_3908_ = lean_array_get_size(v_params_3880_);
v___x_3909_ = lean_nat_dec_lt(v___x_3907_, v___x_3908_);
if (v___x_3909_ == 0)
{
v___y_3883_ = v___y_3863_;
v___y_3884_ = v___y_3864_;
v___y_3885_ = v___y_3865_;
v___y_3886_ = v___y_3866_;
v___y_3887_ = v___y_3867_;
v___y_3888_ = v___y_3868_;
goto v___jp_3882_;
}
else
{
uint8_t v___x_3910_; 
v___x_3910_ = lean_nat_dec_le(v___x_3908_, v___x_3908_);
if (v___x_3910_ == 0)
{
if (v___x_3909_ == 0)
{
v___y_3883_ = v___y_3863_;
v___y_3884_ = v___y_3864_;
v___y_3885_ = v___y_3865_;
v___y_3886_ = v___y_3866_;
v___y_3887_ = v___y_3867_;
v___y_3888_ = v___y_3868_;
goto v___jp_3882_;
}
else
{
size_t v___x_3911_; size_t v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = ((size_t)0ULL);
v___x_3912_ = lean_usize_of_nat(v___x_3908_);
v___x_3913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3880_, v___x_3911_, v___x_3912_, v___x_3877_, v___y_3863_, v___y_3864_, v___y_3868_);
v___y_3893_ = v___x_3913_;
goto v___jp_3892_;
}
}
else
{
size_t v___x_3914_; size_t v___x_3915_; lean_object* v___x_3916_; 
v___x_3914_ = ((size_t)0ULL);
v___x_3915_ = lean_usize_of_nat(v___x_3908_);
v___x_3916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3880_, v___x_3914_, v___x_3915_, v___x_3877_, v___y_3863_, v___y_3864_, v___y_3868_);
v___y_3893_ = v___x_3916_;
goto v___jp_3892_;
}
}
}
v___jp_3882_:
{
lean_object* v___x_3889_; 
lean_inc_ref(v_code_3881_);
v___x_3889_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3881_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_dec_ref_known(v___x_3889_, 1);
v_a_3871_ = v___x_3877_;
goto v___jp_3870_;
}
else
{
return v___x_3889_;
}
}
v___jp_3890_:
{
if (lean_obj_tag(v___y_3891_) == 0)
{
lean_dec_ref_known(v___y_3891_, 1);
v___y_3883_ = v___y_3863_;
v___y_3884_ = v___y_3864_;
v___y_3885_ = v___y_3865_;
v___y_3886_ = v___y_3866_;
v___y_3887_ = v___y_3867_;
v___y_3888_ = v___y_3868_;
goto v___jp_3882_;
}
else
{
return v___y_3891_;
}
}
v___jp_3892_:
{
if (lean_obj_tag(v___y_3893_) == 0)
{
lean_dec_ref_known(v___y_3893_, 1);
v___y_3883_ = v___y_3863_;
v___y_3884_ = v___y_3864_;
v___y_3885_ = v___y_3865_;
v___y_3886_ = v___y_3866_;
v___y_3887_ = v___y_3867_;
v___y_3888_ = v___y_3868_;
goto v___jp_3882_;
}
else
{
return v___y_3893_;
}
}
}
else
{
lean_object* v_code_3917_; lean_object* v___x_3918_; 
v_code_3917_ = lean_ctor_get(v_a_3878_, 0);
lean_inc_ref(v_code_3917_);
v___x_3918_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3917_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_dec_ref_known(v___x_3918_, 1);
v_a_3871_ = v___x_3877_;
goto v___jp_3870_;
}
else
{
return v___x_3918_;
}
}
}
v___jp_3870_:
{
size_t v___x_3872_; size_t v___x_3873_; 
v___x_3872_ = ((size_t)1ULL);
v___x_3873_ = lean_usize_add(v_i_3861_, v___x_3872_);
v_i_3861_ = v___x_3873_;
v_b_3862_ = v_a_3871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_decl_3928_; lean_object* v_k_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; 
switch(lean_obj_tag(v_x_3919_))
{
case 0:
{
lean_object* v_decl_3939_; lean_object* v_k_3940_; lean_object* v_fvarId_3941_; lean_object* v_value_3942_; lean_object* v___x_3943_; 
v_decl_3939_ = lean_ctor_get(v_x_3919_, 0);
lean_inc_ref(v_decl_3939_);
v_k_3940_ = lean_ctor_get(v_x_3919_, 1);
lean_inc_ref(v_k_3940_);
lean_dec_ref_known(v_x_3919_, 2);
v_fvarId_3941_ = lean_ctor_get(v_decl_3939_, 0);
lean_inc(v_fvarId_3941_);
v_value_3942_ = lean_ctor_get(v_decl_3939_, 3);
lean_inc_n(v_value_3942_, 2);
lean_dec_ref(v_decl_3939_);
v___x_3943_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3942_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3941_, v_a_3944_, v_a_3920_, v_a_3921_, v_a_3925_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_dec_ref_known(v___x_3945_, 1);
if (lean_obj_tag(v_value_3942_) == 4)
{
lean_object* v_fvarId_3946_; lean_object* v_args_3947_; uint8_t v___x_3948_; lean_object* v___x_3949_; 
v_fvarId_3946_ = lean_ctor_get(v_value_3942_, 0);
lean_inc(v_fvarId_3946_);
v_args_3947_ = lean_ctor_get(v_value_3942_, 1);
lean_inc_ref(v_args_3947_);
lean_dec_ref_known(v_value_3942_, 2);
v___x_3948_ = 0;
v___x_3949_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3948_, v_fvarId_3946_, v_a_3923_);
lean_dec(v_fvarId_3946_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3949_, 1);
if (lean_obj_tag(v_a_3950_) == 1)
{
lean_object* v_val_3951_; lean_object* v___x_3952_; 
v_val_3951_ = lean_ctor_get(v_a_3950_, 0);
lean_inc(v_val_3951_);
lean_dec_ref_known(v_a_3950_, 1);
v___x_3952_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3951_, v_args_3947_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_dec_ref_known(v___x_3952_, 1);
v_x_3919_ = v_k_3940_;
goto _start;
}
else
{
lean_dec_ref(v_k_3940_);
return v___x_3952_;
}
}
else
{
lean_dec(v_a_3950_);
lean_dec_ref(v_args_3947_);
v_x_3919_ = v_k_3940_;
goto _start;
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref(v_args_3947_);
lean_dec_ref(v_k_3940_);
v_a_3955_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3949_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3949_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_dec(v_value_3942_);
v_x_3919_ = v_k_3940_;
goto _start;
}
}
else
{
lean_dec(v_value_3942_);
lean_dec_ref(v_k_3940_);
return v___x_3945_;
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_value_3942_);
lean_dec(v_fvarId_3941_);
lean_dec_ref(v_k_3940_);
v_a_3964_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3943_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3943_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3972_; lean_object* v_args_3973_; uint8_t v___x_3974_; lean_object* v___x_3975_; 
v_fvarId_3972_ = lean_ctor_get(v_x_3919_, 0);
lean_inc(v_fvarId_3972_);
v_args_3973_ = lean_ctor_get(v_x_3919_, 1);
lean_inc_ref(v_args_3973_);
lean_dec_ref_known(v_x_3919_, 2);
v___x_3974_ = 0;
v___x_3975_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3974_, v_fvarId_3972_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___y_3978_; lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref_known(v___x_3975_, 1);
v___x_3980_ = lean_unsigned_to_nat(0u);
v___x_3981_ = lean_array_get_size(v_args_3973_);
v___x_3982_ = lean_nat_dec_lt(v___x_3980_, v___x_3981_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
v___x_3983_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3976_, v_args_3973_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
return v___x_3983_;
}
else
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3984_ = lean_box(0);
v___x_3985_ = lean_nat_dec_le(v___x_3981_, v___x_3981_);
if (v___x_3985_ == 0)
{
if (v___x_3982_ == 0)
{
lean_object* v___x_3986_; 
v___x_3986_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3976_, v_args_3973_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
return v___x_3986_;
}
else
{
size_t v___x_3987_; size_t v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = ((size_t)0ULL);
v___x_3988_ = lean_usize_of_nat(v___x_3981_);
v___x_3989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3973_, v___x_3987_, v___x_3988_, v___x_3984_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
v___y_3978_ = v___x_3989_;
goto v___jp_3977_;
}
}
else
{
size_t v___x_3990_; size_t v___x_3991_; lean_object* v___x_3992_; 
v___x_3990_ = ((size_t)0ULL);
v___x_3991_ = lean_usize_of_nat(v___x_3981_);
v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3973_, v___x_3990_, v___x_3991_, v___x_3984_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
v___y_3978_ = v___x_3992_;
goto v___jp_3977_;
}
}
v___jp_3977_:
{
if (lean_obj_tag(v___y_3978_) == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref_known(v___y_3978_, 1);
v___x_3979_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3976_, v_args_3973_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
return v___x_3979_;
}
else
{
lean_dec(v_a_3976_);
lean_dec_ref(v_args_3973_);
return v___y_3978_;
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v_args_3973_);
v_a_3993_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3975_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3975_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
case 4:
{
lean_object* v_cases_4001_; lean_object* v_discr_4002_; lean_object* v_alts_4003_; lean_object* v___x_4004_; 
v_cases_4001_ = lean_ctor_get(v_x_3919_, 0);
lean_inc_ref(v_cases_4001_);
lean_dec_ref_known(v_x_3919_, 1);
v_discr_4002_ = lean_ctor_get(v_cases_4001_, 2);
lean_inc(v_discr_4002_);
v_alts_4003_ = lean_ctor_get(v_cases_4001_, 3);
lean_inc_ref(v_alts_4003_);
lean_dec_ref(v_cases_4001_);
v___x_4004_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_4002_, v_a_3920_, v_a_3921_);
lean_dec(v_discr_4002_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4006_; size_t v_sz_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___x_4006_ = lean_box(0);
v_sz_4007_ = lean_array_size(v_alts_4003_);
v___x_4008_ = ((size_t)0ULL);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4005_, v_alts_4003_, v_sz_4007_, v___x_4008_, v___x_4006_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
lean_dec_ref(v_alts_4003_);
lean_dec(v_a_4005_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; 
v_unused_4017_ = lean_ctor_get(v___x_4009_, 0);
lean_dec(v_unused_4017_);
v___x_4011_ = v___x_4009_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_dec(v___x_4009_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4006_);
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4006_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
return v___x_4009_;
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec_ref(v_alts_4003_);
v_a_4018_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4004_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4004_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_4026_; lean_object* v___x_4027_; 
v_fvarId_4026_ = lean_ctor_get(v_x_3919_, 0);
lean_inc(v_fvarId_4026_);
lean_dec_ref_known(v_x_3919_, 1);
v___x_4027_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4026_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v___x_4028_; 
lean_dec_ref_known(v___x_4027_, 1);
v___x_4028_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_4026_, v_a_3920_, v_a_3921_);
lean_dec(v_fvarId_4026_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4030_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4028_, 1);
v___x_4030_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_4029_, v_a_3920_, v_a_3921_, v_a_3925_);
return v___x_4030_;
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
v_a_4031_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4028_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4028_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
else
{
lean_dec(v_fvarId_4026_);
return v___x_4027_;
}
}
case 6:
{
lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4046_; 
v_isSharedCheck_4046_ = !lean_is_exclusive(v_x_3919_);
if (v_isSharedCheck_4046_ == 0)
{
lean_object* v_unused_4047_; 
v_unused_4047_ = lean_ctor_get(v_x_3919_, 0);
lean_dec(v_unused_4047_);
v___x_4040_ = v_x_3919_;
v_isShared_4041_ = v_isSharedCheck_4046_;
goto v_resetjp_4039_;
}
else
{
lean_dec(v_x_3919_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4046_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4044_; 
v___x_4042_ = lean_box(0);
if (v_isShared_4041_ == 0)
{
lean_ctor_set_tag(v___x_4040_, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4042_);
v___x_4044_ = v___x_4040_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
default: 
{
lean_object* v_decl_4048_; lean_object* v_k_4049_; 
v_decl_4048_ = lean_ctor_get(v_x_3919_, 0);
lean_inc_ref(v_decl_4048_);
v_k_4049_ = lean_ctor_get(v_x_3919_, 1);
lean_inc_ref(v_k_4049_);
lean_dec_ref(v_x_3919_);
v_decl_3928_ = v_decl_4048_;
v_k_3929_ = v_k_4049_;
v___y_3930_ = v_a_3920_;
v___y_3931_ = v_a_3921_;
v___y_3932_ = v_a_3922_;
v___y_3933_ = v_a_3923_;
v___y_3934_ = v_a_3924_;
v___y_3935_ = v_a_3925_;
goto v___jp_3927_;
}
}
v___jp_3927_:
{
lean_object* v_value_3936_; lean_object* v___x_3937_; 
v_value_3936_ = lean_ctor_get(v_decl_3928_, 4);
lean_inc_ref(v_value_3936_);
lean_dec_ref(v_decl_3928_);
v___x_3937_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3936_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_dec_ref_known(v___x_3937_, 1);
v_x_3919_ = v_k_3929_;
v_a_3920_ = v___y_3930_;
v_a_3921_ = v___y_3931_;
v_a_3922_ = v___y_3932_;
v_a_3923_ = v___y_3933_;
v_a_3924_ = v___y_3934_;
v_a_3925_ = v___y_3935_;
goto _start;
}
else
{
lean_dec_ref(v_k_3929_);
return v___x_3937_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_){
_start:
{
uint8_t v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = 0;
v___x_4059_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_4058_, v_var_4050_, v_a_4054_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4092_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4092_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4092_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
if (lean_obj_tag(v_a_4060_) == 1)
{
lean_object* v_val_4064_; lean_object* v_params_4065_; lean_object* v_value_4066_; lean_object* v___x_4067_; 
lean_del_object(v___x_4062_);
v_val_4064_ = lean_ctor_get(v_a_4060_, 0);
lean_inc(v_val_4064_);
lean_dec_ref_known(v_a_4060_, 1);
v_params_4065_ = lean_ctor_get(v_val_4064_, 2);
lean_inc_ref(v_params_4065_);
v_value_4066_ = lean_ctor_get(v_val_4064_, 4);
lean_inc_ref(v_value_4066_);
lean_dec(v_val_4064_);
v___x_4067_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_4065_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
lean_dec_ref(v_params_4065_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4079_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4079_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4067_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4079_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
uint8_t v___x_4072_; 
v___x_4072_ = lean_unbox(v_a_4068_);
lean_dec(v_a_4068_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
lean_dec_ref(v_value_4066_);
v___x_4073_ = lean_box(0);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 0, v___x_4073_);
v___x_4075_ = v___x_4070_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
else
{
lean_object* v___x_4077_; 
lean_del_object(v___x_4070_);
lean_inc_ref(v_value_4066_);
v___x_4077_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_4066_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v___x_4078_; 
lean_dec_ref_known(v___x_4077_, 1);
v___x_4078_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_4066_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
return v___x_4078_;
}
else
{
lean_dec_ref(v_value_4066_);
return v___x_4077_;
}
}
}
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
lean_dec_ref(v_value_4066_);
v_a_4080_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4067_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4067_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4090_; 
lean_dec(v_a_4060_);
v___x_4088_ = lean_box(0);
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 0, v___x_4088_);
v___x_4090_ = v___x_4062_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
v_a_4093_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4059_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4059_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
if (lean_obj_tag(v_arg_4101_) == 1)
{
lean_object* v_fvarId_4109_; lean_object* v___x_4110_; 
v_fvarId_4109_ = lean_ctor_get(v_arg_4101_, 0);
v___x_4110_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4109_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
return v___x_4110_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = lean_box(0);
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
return v___x_4112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
lean_dec(v_a_4115_);
lean_dec_ref(v_a_4114_);
lean_dec(v_arg_4113_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_4122_, lean_object* v_i_4123_, lean_object* v_stop_4124_, lean_object* v_b_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
size_t v_i_boxed_4133_; size_t v_stop_boxed_4134_; lean_object* v_res_4135_; 
v_i_boxed_4133_ = lean_unbox_usize(v_i_4123_);
lean_dec(v_i_4123_);
v_stop_boxed_4134_ = lean_unbox_usize(v_stop_4124_);
lean_dec(v_stop_4124_);
v_res_4135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_4122_, v_i_boxed_4133_, v_stop_boxed_4134_, v_b_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v_as_4122_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_4136_, lean_object* v_args_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_4136_, v_args_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
lean_dec(v_a_4152_);
lean_dec_ref(v_a_4151_);
lean_dec(v_a_4150_);
lean_dec_ref(v_a_4149_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_var_4146_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4155_, lean_object* v_as_4156_, lean_object* v_sz_4157_, lean_object* v_i_4158_, lean_object* v_b_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
size_t v_sz_boxed_4167_; size_t v_i_boxed_4168_; lean_object* v_res_4169_; 
v_sz_boxed_4167_ = lean_unbox_usize(v_sz_4157_);
lean_dec(v_sz_4157_);
v_i_boxed_4168_ = lean_unbox_usize(v_i_4158_);
lean_dec(v_i_4158_);
v_res_4169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4155_, v_as_4156_, v_sz_boxed_4167_, v_i_boxed_4168_, v_b_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec_ref(v_as_4156_);
lean_dec(v_a_4155_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec_ref(v_a_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4188_, lean_object* v_R_4189_, lean_object* v_a_4190_, lean_object* v_b_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4190_, v_b_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4193_, size_t v_i_4194_, lean_object* v_bs_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4193_, v_i_4194_, v_bs_4195_, v___y_4196_, v___y_4197_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4204_, lean_object* v_i_4205_, lean_object* v_bs_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
size_t v_sz_boxed_4214_; size_t v_i_boxed_4215_; lean_object* v_res_4216_; 
v_sz_boxed_4214_ = lean_unbox_usize(v_sz_4204_);
lean_dec(v_sz_4204_);
v_i_boxed_4215_ = lean_unbox_usize(v_i_4205_);
lean_dec(v_i_4205_);
v_res_4216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4214_, v_i_boxed_4215_, v_bs_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4217_, size_t v_i_4218_, size_t v_stop_4219_, lean_object* v_b_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4217_, v_i_4218_, v_stop_4219_, v_b_4220_, v___y_4221_, v___y_4222_, v___y_4226_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4229_, lean_object* v_i_4230_, lean_object* v_stop_4231_, lean_object* v_b_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
size_t v_i_boxed_4240_; size_t v_stop_boxed_4241_; lean_object* v_res_4242_; 
v_i_boxed_4240_ = lean_unbox_usize(v_i_4230_);
lean_dec(v_i_4230_);
v_stop_boxed_4241_ = lean_unbox_usize(v_stop_4231_);
lean_dec(v_stop_4231_);
v_res_4242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4229_, v_i_boxed_4240_, v_stop_boxed_4241_, v_b_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v_as_4229_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4243_, size_t v_i_4244_, size_t v_stop_4245_, lean_object* v_b_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4243_, v_i_4244_, v_stop_4245_, v_b_4246_, v___y_4247_, v___y_4248_, v___y_4252_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4255_, lean_object* v_i_4256_, lean_object* v_stop_4257_, lean_object* v_b_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
size_t v_i_boxed_4266_; size_t v_stop_boxed_4267_; lean_object* v_res_4268_; 
v_i_boxed_4266_ = lean_unbox_usize(v_i_4256_);
lean_dec(v_i_4256_);
v_stop_boxed_4267_ = lean_unbox_usize(v_stop_4257_);
lean_dec(v_stop_4257_);
v_res_4268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4255_, v_i_boxed_4266_, v_stop_boxed_4267_, v_b_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec_ref(v_as_4255_);
return v_res_4268_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4269_ = lean_unsigned_to_nat(32u);
v___x_4270_ = lean_mk_empty_array_with_capacity(v___x_4269_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
return v___x_4271_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4272_ = ((size_t)5ULL);
v___x_4273_ = lean_unsigned_to_nat(0u);
v___x_4274_ = lean_unsigned_to_nat(32u);
v___x_4275_ = lean_mk_empty_array_with_capacity(v___x_4274_);
v___x_4276_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4277_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
lean_ctor_set(v___x_4277_, 1, v___x_4275_);
lean_ctor_set(v___x_4277_, 2, v___x_4273_);
lean_ctor_set(v___x_4277_, 3, v___x_4273_);
lean_ctor_set_usize(v___x_4277_, 4, v___x_4272_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4278_){
_start:
{
lean_object* v___x_4280_; lean_object* v_traceState_4281_; lean_object* v_traces_4282_; lean_object* v___x_4283_; lean_object* v_traceState_4284_; lean_object* v_env_4285_; lean_object* v_nextMacroScope_4286_; lean_object* v_ngen_4287_; lean_object* v_auxDeclNGen_4288_; lean_object* v_cache_4289_; lean_object* v_messages_4290_; lean_object* v_infoState_4291_; lean_object* v_snapshotTasks_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4311_; 
v___x_4280_ = lean_st_ref_get(v___y_4278_);
v_traceState_4281_ = lean_ctor_get(v___x_4280_, 4);
lean_inc_ref(v_traceState_4281_);
lean_dec(v___x_4280_);
v_traces_4282_ = lean_ctor_get(v_traceState_4281_, 0);
lean_inc_ref(v_traces_4282_);
lean_dec_ref(v_traceState_4281_);
v___x_4283_ = lean_st_ref_take(v___y_4278_);
v_traceState_4284_ = lean_ctor_get(v___x_4283_, 4);
v_env_4285_ = lean_ctor_get(v___x_4283_, 0);
v_nextMacroScope_4286_ = lean_ctor_get(v___x_4283_, 1);
v_ngen_4287_ = lean_ctor_get(v___x_4283_, 2);
v_auxDeclNGen_4288_ = lean_ctor_get(v___x_4283_, 3);
v_cache_4289_ = lean_ctor_get(v___x_4283_, 5);
v_messages_4290_ = lean_ctor_get(v___x_4283_, 6);
v_infoState_4291_ = lean_ctor_get(v___x_4283_, 7);
v_snapshotTasks_4292_ = lean_ctor_get(v___x_4283_, 8);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4294_ = v___x_4283_;
v_isShared_4295_ = v_isSharedCheck_4311_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_snapshotTasks_4292_);
lean_inc(v_infoState_4291_);
lean_inc(v_messages_4290_);
lean_inc(v_cache_4289_);
lean_inc(v_traceState_4284_);
lean_inc(v_auxDeclNGen_4288_);
lean_inc(v_ngen_4287_);
lean_inc(v_nextMacroScope_4286_);
lean_inc(v_env_4285_);
lean_dec(v___x_4283_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4311_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
uint64_t v_tid_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4309_; 
v_tid_4296_ = lean_ctor_get_uint64(v_traceState_4284_, sizeof(void*)*1);
v_isSharedCheck_4309_ = !lean_is_exclusive(v_traceState_4284_);
if (v_isSharedCheck_4309_ == 0)
{
lean_object* v_unused_4310_; 
v_unused_4310_ = lean_ctor_get(v_traceState_4284_, 0);
lean_dec(v_unused_4310_);
v___x_4298_ = v_traceState_4284_;
v_isShared_4299_ = v_isSharedCheck_4309_;
goto v_resetjp_4297_;
}
else
{
lean_dec(v_traceState_4284_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4309_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v___x_4302_; 
v___x_4300_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 0, v___x_4300_);
v___x_4302_ = v___x_4298_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4300_);
lean_ctor_set_uint64(v_reuseFailAlloc_4308_, sizeof(void*)*1, v_tid_4296_);
v___x_4302_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v___x_4304_; 
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 4, v___x_4302_);
v___x_4304_ = v___x_4294_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_env_4285_);
lean_ctor_set(v_reuseFailAlloc_4307_, 1, v_nextMacroScope_4286_);
lean_ctor_set(v_reuseFailAlloc_4307_, 2, v_ngen_4287_);
lean_ctor_set(v_reuseFailAlloc_4307_, 3, v_auxDeclNGen_4288_);
lean_ctor_set(v_reuseFailAlloc_4307_, 4, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4307_, 5, v_cache_4289_);
lean_ctor_set(v_reuseFailAlloc_4307_, 6, v_messages_4290_);
lean_ctor_set(v_reuseFailAlloc_4307_, 7, v_infoState_4291_);
lean_ctor_set(v_reuseFailAlloc_4307_, 8, v_snapshotTasks_4292_);
v___x_4304_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4305_ = lean_st_ref_set(v___y_4278_, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v_traces_4282_);
return v___x_4306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4312_);
lean_dec(v___y_4312_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4320_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
return v_res_4330_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4331_, lean_object* v_opt_4332_){
_start:
{
lean_object* v_name_4333_; lean_object* v_defValue_4334_; lean_object* v_map_4335_; lean_object* v___x_4336_; 
v_name_4333_ = lean_ctor_get(v_opt_4332_, 0);
v_defValue_4334_ = lean_ctor_get(v_opt_4332_, 1);
v_map_4335_ = lean_ctor_get(v_opts_4331_, 0);
v___x_4336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4335_, v_name_4333_);
if (lean_obj_tag(v___x_4336_) == 0)
{
uint8_t v___x_4337_; 
v___x_4337_ = lean_unbox(v_defValue_4334_);
return v___x_4337_;
}
else
{
lean_object* v_val_4338_; 
v_val_4338_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_val_4338_);
lean_dec_ref_known(v___x_4336_, 1);
if (lean_obj_tag(v_val_4338_) == 1)
{
uint8_t v_v_4339_; 
v_v_4339_ = lean_ctor_get_uint8(v_val_4338_, 0);
lean_dec_ref_known(v_val_4338_, 0);
return v_v_4339_;
}
else
{
uint8_t v___x_4340_; 
lean_dec(v_val_4338_);
v___x_4340_ = lean_unbox(v_defValue_4334_);
return v___x_4340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4341_, lean_object* v_opt_4342_){
_start:
{
uint8_t v_res_4343_; lean_object* v_r_4344_; 
v_res_4343_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4341_, v_opt_4342_);
lean_dec_ref(v_opt_4342_);
lean_dec_ref(v_opts_4341_);
v_r_4344_ = lean_box(v_res_4343_);
return v_r_4344_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4347_ = l_Lean_stringToMessageData(v___x_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4348_, lean_object* v_x_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4357_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4358_ = l_Lean_MessageData_ofName(v_name_4348_);
v___x_4359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4357_);
lean_ctor_set(v___x_4359_, 1, v___x_4358_);
v___x_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4361_, v_x_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_x_4362_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4371_, lean_object* v_opt_4372_){
_start:
{
lean_object* v_name_4373_; lean_object* v_defValue_4374_; lean_object* v_map_4375_; lean_object* v___x_4376_; 
v_name_4373_ = lean_ctor_get(v_opt_4372_, 0);
v_defValue_4374_ = lean_ctor_get(v_opt_4372_, 1);
v_map_4375_ = lean_ctor_get(v_opts_4371_, 0);
v___x_4376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4375_, v_name_4373_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_inc(v_defValue_4374_);
return v_defValue_4374_;
}
else
{
lean_object* v_val_4377_; 
v_val_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc(v_val_4377_);
lean_dec_ref_known(v___x_4376_, 1);
if (lean_obj_tag(v_val_4377_) == 3)
{
lean_object* v_v_4378_; 
v_v_4378_ = lean_ctor_get(v_val_4377_, 0);
lean_inc(v_v_4378_);
lean_dec_ref_known(v_val_4377_, 1);
return v_v_4378_;
}
else
{
lean_dec(v_val_4377_);
lean_inc(v_defValue_4374_);
return v_defValue_4374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4379_, lean_object* v_opt_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4379_, v_opt_4380_);
lean_dec_ref(v_opt_4380_);
lean_dec_ref(v_opts_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4382_){
_start:
{
if (lean_obj_tag(v_e_4382_) == 0)
{
uint8_t v___x_4383_; 
v___x_4383_ = 2;
return v___x_4383_;
}
else
{
uint8_t v___x_4384_; 
v___x_4384_ = 0;
return v___x_4384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4385_){
_start:
{
uint8_t v_res_4386_; lean_object* v_r_4387_; 
v_res_4386_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4385_);
lean_dec_ref(v_e_4385_);
v_r_4387_ = lean_box(v_res_4386_);
return v_r_4387_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4388_){
_start:
{
if (lean_obj_tag(v_x_4388_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
v_a_4390_ = lean_ctor_get(v_x_4388_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_x_4388_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v_x_4388_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v_x_4388_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
lean_ctor_set_tag(v___x_4392_, 1);
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
v_a_4398_ = lean_ctor_get(v_x_4388_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_x_4388_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v_x_4388_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v_x_4388_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set_tag(v___x_4400_, 0);
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4406_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4409_, size_t v_i_4410_, lean_object* v_bs_4411_){
_start:
{
uint8_t v___x_4412_; 
v___x_4412_ = lean_usize_dec_lt(v_i_4410_, v_sz_4409_);
if (v___x_4412_ == 0)
{
return v_bs_4411_;
}
else
{
lean_object* v_v_4413_; lean_object* v_msg_4414_; lean_object* v___x_4415_; lean_object* v_bs_x27_4416_; size_t v___x_4417_; size_t v___x_4418_; lean_object* v___x_4419_; 
v_v_4413_ = lean_array_uget_borrowed(v_bs_4411_, v_i_4410_);
v_msg_4414_ = lean_ctor_get(v_v_4413_, 1);
lean_inc_ref(v_msg_4414_);
v___x_4415_ = lean_unsigned_to_nat(0u);
v_bs_x27_4416_ = lean_array_uset(v_bs_4411_, v_i_4410_, v___x_4415_);
v___x_4417_ = ((size_t)1ULL);
v___x_4418_ = lean_usize_add(v_i_4410_, v___x_4417_);
v___x_4419_ = lean_array_uset(v_bs_x27_4416_, v_i_4410_, v_msg_4414_);
v_i_4410_ = v___x_4418_;
v_bs_4411_ = v___x_4419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4421_, lean_object* v_i_4422_, lean_object* v_bs_4423_){
_start:
{
size_t v_sz_boxed_4424_; size_t v_i_boxed_4425_; lean_object* v_res_4426_; 
v_sz_boxed_4424_ = lean_unbox_usize(v_sz_4421_);
lean_dec(v_sz_4421_);
v_i_boxed_4425_ = lean_unbox_usize(v_i_4422_);
lean_dec(v_i_4422_);
v_res_4426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4424_, v_i_boxed_4425_, v_bs_4423_);
return v_res_4426_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4427_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
return v___x_4429_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4430_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4431_ = lean_unsigned_to_nat(0u);
v___x_4432_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
lean_ctor_set(v___x_4432_, 2, v___x_4431_);
lean_ctor_set(v___x_4432_, 3, v___x_4431_);
lean_ctor_set(v___x_4432_, 4, v___x_4430_);
lean_ctor_set(v___x_4432_, 5, v___x_4430_);
lean_ctor_set(v___x_4432_, 6, v___x_4430_);
lean_ctor_set(v___x_4432_, 7, v___x_4430_);
lean_ctor_set(v___x_4432_, 8, v___x_4430_);
lean_ctor_set(v___x_4432_, 9, v___x_4430_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4433_, lean_object* v_data_4434_, lean_object* v_ref_4435_, lean_object* v_msg_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_options_4442_; lean_object* v___x_4443_; lean_object* v_traceState_4444_; lean_object* v_traces_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_options_4442_ = lean_ctor_get(v___y_4439_, 2);
v___x_4443_ = lean_st_ref_get(v___y_4440_);
v_traceState_4444_ = lean_ctor_get(v___x_4443_, 4);
lean_inc_ref(v_traceState_4444_);
lean_dec(v___x_4443_);
v_traces_4445_ = lean_ctor_get(v_traceState_4444_, 0);
lean_inc_ref(v_traces_4445_);
lean_dec_ref(v_traceState_4444_);
v___x_4446_ = lean_st_ref_get(v___y_4440_);
v___x_4447_ = lean_st_ref_get(v___y_4438_);
v___x_4448_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4437_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4505_; 
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4451_ = v___x_4448_;
v_isShared_4452_ = v_isSharedCheck_4505_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4448_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4505_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v_env_4453_; lean_object* v_lctx_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4503_; 
v_env_4453_ = lean_ctor_get(v___x_4446_, 0);
lean_inc_ref(v_env_4453_);
lean_dec(v___x_4446_);
v_lctx_4454_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v___x_4447_, 1);
lean_dec(v_unused_4504_);
v___x_4456_ = v___x_4447_;
v_isShared_4457_ = v_isSharedCheck_4503_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_lctx_4454_);
lean_dec(v___x_4447_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4503_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v_traceState_4460_; lean_object* v_env_4461_; lean_object* v_nextMacroScope_4462_; lean_object* v_ngen_4463_; lean_object* v_auxDeclNGen_4464_; lean_object* v_cache_4465_; lean_object* v_messages_4466_; lean_object* v_infoState_4467_; lean_object* v_snapshotTasks_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4502_; 
v___x_4458_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4459_ = lean_st_ref_take(v___y_4440_);
v_traceState_4460_ = lean_ctor_get(v___x_4459_, 4);
v_env_4461_ = lean_ctor_get(v___x_4459_, 0);
v_nextMacroScope_4462_ = lean_ctor_get(v___x_4459_, 1);
v_ngen_4463_ = lean_ctor_get(v___x_4459_, 2);
v_auxDeclNGen_4464_ = lean_ctor_get(v___x_4459_, 3);
v_cache_4465_ = lean_ctor_get(v___x_4459_, 5);
v_messages_4466_ = lean_ctor_get(v___x_4459_, 6);
v_infoState_4467_ = lean_ctor_get(v___x_4459_, 7);
v_snapshotTasks_4468_ = lean_ctor_get(v___x_4459_, 8);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4470_ = v___x_4459_;
v_isShared_4471_ = v_isSharedCheck_4502_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_snapshotTasks_4468_);
lean_inc(v_infoState_4467_);
lean_inc(v_messages_4466_);
lean_inc(v_cache_4465_);
lean_inc(v_traceState_4460_);
lean_inc(v_auxDeclNGen_4464_);
lean_inc(v_ngen_4463_);
lean_inc(v_nextMacroScope_4462_);
lean_inc(v_env_4461_);
lean_dec(v___x_4459_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4502_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
uint64_t v_tid_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4500_; 
v_tid_4472_ = lean_ctor_get_uint64(v_traceState_4460_, sizeof(void*)*1);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_traceState_4460_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v_traceState_4460_, 0);
lean_dec(v_unused_4501_);
v___x_4474_ = v_traceState_4460_;
v_isShared_4475_ = v_isSharedCheck_4500_;
goto v_resetjp_4473_;
}
else
{
lean_dec(v_traceState_4460_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4500_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4476_; size_t v_sz_4477_; size_t v___x_4478_; lean_object* v___x_4479_; lean_object* v_msg_4480_; uint8_t v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4476_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4445_);
lean_dec_ref(v_traces_4445_);
v_sz_4477_ = lean_array_size(v___x_4476_);
v___x_4478_ = ((size_t)0ULL);
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4477_, v___x_4478_, v___x_4476_);
v_msg_4480_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4480_, 0, v_data_4434_);
lean_ctor_set(v_msg_4480_, 1, v_msg_4436_);
lean_ctor_set(v_msg_4480_, 2, v___x_4479_);
v___x_4481_ = lean_unbox(v_a_4449_);
lean_dec(v_a_4449_);
v___x_4482_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4454_, v___x_4481_);
lean_dec_ref(v_lctx_4454_);
lean_inc_ref(v_options_4442_);
v___x_4483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4483_, 0, v_env_4453_);
lean_ctor_set(v___x_4483_, 1, v___x_4458_);
lean_ctor_set(v___x_4483_, 2, v___x_4482_);
lean_ctor_set(v___x_4483_, 3, v_options_4442_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set_tag(v___x_4456_, 3);
lean_ctor_set(v___x_4456_, 1, v_msg_4480_);
lean_ctor_set(v___x_4456_, 0, v___x_4483_);
v___x_4485_ = v___x_4456_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4483_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_msg_4480_);
v___x_4485_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4486_, 0, v_ref_4435_);
lean_ctor_set(v___x_4486_, 1, v___x_4485_);
v___x_4487_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4433_, v___x_4486_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4487_);
v___x_4489_ = v___x_4474_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4487_);
lean_ctor_set_uint64(v_reuseFailAlloc_4498_, sizeof(void*)*1, v_tid_4472_);
v___x_4489_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4491_; 
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 4, v___x_4489_);
v___x_4491_ = v___x_4470_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_env_4461_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_nextMacroScope_4462_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_ngen_4463_);
lean_ctor_set(v_reuseFailAlloc_4497_, 3, v_auxDeclNGen_4464_);
lean_ctor_set(v_reuseFailAlloc_4497_, 4, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4497_, 5, v_cache_4465_);
lean_ctor_set(v_reuseFailAlloc_4497_, 6, v_messages_4466_);
lean_ctor_set(v_reuseFailAlloc_4497_, 7, v_infoState_4467_);
lean_ctor_set(v_reuseFailAlloc_4497_, 8, v_snapshotTasks_4468_);
v___x_4491_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
v___x_4492_ = lean_st_ref_set(v___y_4440_, v___x_4491_);
v___x_4493_ = lean_box(0);
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 0, v___x_4493_);
v___x_4495_ = v___x_4451_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
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
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v___x_4447_);
lean_dec(v___x_4446_);
lean_dec_ref(v_traces_4445_);
lean_dec_ref(v_msg_4436_);
lean_dec(v_ref_4435_);
lean_dec_ref(v_data_4434_);
lean_dec_ref(v_oldTraces_4433_);
v_a_4506_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4448_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4448_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4514_, lean_object* v_data_4515_, lean_object* v_ref_4516_, lean_object* v_msg_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4514_, v_data_4515_, v_ref_4516_, v_msg_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
return v_res_4523_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4524_; double v___x_4525_; 
v___x_4524_ = lean_unsigned_to_nat(0u);
v___x_4525_ = lean_float_of_nat(v___x_4524_);
return v___x_4525_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4528_ = l_Lean_stringToMessageData(v___x_4527_);
return v___x_4528_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4529_; double v___x_4530_; 
v___x_4529_ = lean_unsigned_to_nat(1000u);
v___x_4530_ = lean_float_of_nat(v___x_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4531_, uint8_t v_collapsed_4532_, lean_object* v_tag_4533_, lean_object* v_opts_4534_, uint8_t v_clsEnabled_4535_, lean_object* v_oldTraces_4536_, lean_object* v_msg_4537_, lean_object* v_resStartStop_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_fst_4546_; lean_object* v_snd_4547_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v_data_4551_; lean_object* v_fst_4554_; lean_object* v_snd_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; lean_object* v___y_4559_; lean_object* v_a_4560_; uint8_t v___y_4575_; double v___y_4606_; 
v_fst_4546_ = lean_ctor_get(v_resStartStop_4538_, 0);
lean_inc(v_fst_4546_);
v_snd_4547_ = lean_ctor_get(v_resStartStop_4538_, 1);
lean_inc(v_snd_4547_);
lean_dec_ref(v_resStartStop_4538_);
v_fst_4554_ = lean_ctor_get(v_snd_4547_, 0);
lean_inc(v_fst_4554_);
v_snd_4555_ = lean_ctor_get(v_snd_4547_, 1);
lean_inc(v_snd_4555_);
lean_dec(v_snd_4547_);
v___x_4556_ = l_Lean_trace_profiler;
v___x_4557_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4534_, v___x_4556_);
if (v___x_4557_ == 0)
{
v___y_4575_ = v___x_4557_;
goto v___jp_4574_;
}
else
{
lean_object* v___x_4611_; uint8_t v___x_4612_; 
v___x_4611_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4612_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4534_, v___x_4611_);
if (v___x_4612_ == 0)
{
lean_object* v___x_4613_; lean_object* v___x_4614_; double v___x_4615_; double v___x_4616_; double v___x_4617_; 
v___x_4613_ = l_Lean_trace_profiler_threshold;
v___x_4614_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4534_, v___x_4613_);
v___x_4615_ = lean_float_of_nat(v___x_4614_);
v___x_4616_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4617_ = lean_float_div(v___x_4615_, v___x_4616_);
v___y_4606_ = v___x_4617_;
goto v___jp_4605_;
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4619_; double v___x_4620_; 
v___x_4618_ = l_Lean_trace_profiler_threshold;
v___x_4619_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4534_, v___x_4618_);
v___x_4620_ = lean_float_of_nat(v___x_4619_);
v___y_4606_ = v___x_4620_;
goto v___jp_4605_;
}
}
v___jp_4548_:
{
lean_object* v___x_4552_; 
lean_inc(v___y_4549_);
v___x_4552_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4536_, v_data_4551_, v___y_4549_, v___y_4550_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v___x_4553_; 
lean_dec_ref_known(v___x_4552_, 1);
v___x_4553_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4546_);
return v___x_4553_;
}
else
{
lean_dec(v_fst_4546_);
return v___x_4552_;
}
}
v___jp_4558_:
{
uint8_t v_result_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; double v___x_4564_; lean_object* v_data_4565_; 
v_result_4561_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4546_);
v___x_4562_ = lean_box(v_result_4561_);
v___x_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
v___x_4564_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4533_);
lean_inc_ref(v___x_4563_);
lean_inc(v_cls_4531_);
v_data_4565_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4565_, 0, v_cls_4531_);
lean_ctor_set(v_data_4565_, 1, v___x_4563_);
lean_ctor_set(v_data_4565_, 2, v_tag_4533_);
lean_ctor_set_float(v_data_4565_, sizeof(void*)*3, v___x_4564_);
lean_ctor_set_float(v_data_4565_, sizeof(void*)*3 + 8, v___x_4564_);
lean_ctor_set_uint8(v_data_4565_, sizeof(void*)*3 + 16, v_collapsed_4532_);
if (v___x_4557_ == 0)
{
lean_dec_ref_known(v___x_4563_, 1);
lean_dec(v_snd_4555_);
lean_dec(v_fst_4554_);
lean_dec_ref(v_tag_4533_);
lean_dec(v_cls_4531_);
v___y_4549_ = v___y_4559_;
v___y_4550_ = v_a_4560_;
v_data_4551_ = v_data_4565_;
goto v___jp_4548_;
}
else
{
lean_object* v_data_4566_; double v___x_4567_; double v___x_4568_; 
lean_dec_ref_known(v_data_4565_, 3);
v_data_4566_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4566_, 0, v_cls_4531_);
lean_ctor_set(v_data_4566_, 1, v___x_4563_);
lean_ctor_set(v_data_4566_, 2, v_tag_4533_);
v___x_4567_ = lean_unbox_float(v_fst_4554_);
lean_dec(v_fst_4554_);
lean_ctor_set_float(v_data_4566_, sizeof(void*)*3, v___x_4567_);
v___x_4568_ = lean_unbox_float(v_snd_4555_);
lean_dec(v_snd_4555_);
lean_ctor_set_float(v_data_4566_, sizeof(void*)*3 + 8, v___x_4568_);
lean_ctor_set_uint8(v_data_4566_, sizeof(void*)*3 + 16, v_collapsed_4532_);
v___y_4549_ = v___y_4559_;
v___y_4550_ = v_a_4560_;
v_data_4551_ = v_data_4566_;
goto v___jp_4548_;
}
}
v___jp_4569_:
{
lean_object* v_ref_4570_; lean_object* v___x_4571_; 
v_ref_4570_ = lean_ctor_get(v___y_4543_, 5);
lean_inc(v___y_4544_);
lean_inc_ref(v___y_4543_);
lean_inc(v___y_4542_);
lean_inc_ref(v___y_4541_);
lean_inc(v___y_4540_);
lean_inc_ref(v___y_4539_);
lean_inc(v_fst_4546_);
v___x_4571_ = lean_apply_8(v_msg_4537_, v_fst_4546_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, lean_box(0));
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_a_4572_);
lean_dec_ref_known(v___x_4571_, 1);
v___y_4559_ = v_ref_4570_;
v_a_4560_ = v_a_4572_;
goto v___jp_4558_;
}
else
{
lean_object* v___x_4573_; 
lean_dec_ref_known(v___x_4571_, 1);
v___x_4573_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4559_ = v_ref_4570_;
v_a_4560_ = v___x_4573_;
goto v___jp_4558_;
}
}
v___jp_4574_:
{
if (v_clsEnabled_4535_ == 0)
{
if (v___y_4575_ == 0)
{
lean_object* v___x_4576_; lean_object* v_traceState_4577_; lean_object* v_env_4578_; lean_object* v_nextMacroScope_4579_; lean_object* v_ngen_4580_; lean_object* v_auxDeclNGen_4581_; lean_object* v_cache_4582_; lean_object* v_messages_4583_; lean_object* v_infoState_4584_; lean_object* v_snapshotTasks_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4604_; 
lean_dec(v_snd_4555_);
lean_dec(v_fst_4554_);
lean_dec_ref(v_msg_4537_);
lean_dec_ref(v_tag_4533_);
lean_dec(v_cls_4531_);
v___x_4576_ = lean_st_ref_take(v___y_4544_);
v_traceState_4577_ = lean_ctor_get(v___x_4576_, 4);
v_env_4578_ = lean_ctor_get(v___x_4576_, 0);
v_nextMacroScope_4579_ = lean_ctor_get(v___x_4576_, 1);
v_ngen_4580_ = lean_ctor_get(v___x_4576_, 2);
v_auxDeclNGen_4581_ = lean_ctor_get(v___x_4576_, 3);
v_cache_4582_ = lean_ctor_get(v___x_4576_, 5);
v_messages_4583_ = lean_ctor_get(v___x_4576_, 6);
v_infoState_4584_ = lean_ctor_get(v___x_4576_, 7);
v_snapshotTasks_4585_ = lean_ctor_get(v___x_4576_, 8);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4587_ = v___x_4576_;
v_isShared_4588_ = v_isSharedCheck_4604_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_snapshotTasks_4585_);
lean_inc(v_infoState_4584_);
lean_inc(v_messages_4583_);
lean_inc(v_cache_4582_);
lean_inc(v_traceState_4577_);
lean_inc(v_auxDeclNGen_4581_);
lean_inc(v_ngen_4580_);
lean_inc(v_nextMacroScope_4579_);
lean_inc(v_env_4578_);
lean_dec(v___x_4576_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4604_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
uint64_t v_tid_4589_; lean_object* v_traces_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4603_; 
v_tid_4589_ = lean_ctor_get_uint64(v_traceState_4577_, sizeof(void*)*1);
v_traces_4590_ = lean_ctor_get(v_traceState_4577_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_traceState_4577_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4592_ = v_traceState_4577_;
v_isShared_4593_ = v_isSharedCheck_4603_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_traces_4590_);
lean_dec(v_traceState_4577_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4603_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
v___x_4594_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4536_, v_traces_4590_);
lean_dec_ref(v_traces_4590_);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4594_);
v___x_4596_ = v___x_4592_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4594_);
lean_ctor_set_uint64(v_reuseFailAlloc_4602_, sizeof(void*)*1, v_tid_4589_);
v___x_4596_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4598_; 
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 4, v___x_4596_);
v___x_4598_ = v___x_4587_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_env_4578_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_nextMacroScope_4579_);
lean_ctor_set(v_reuseFailAlloc_4601_, 2, v_ngen_4580_);
lean_ctor_set(v_reuseFailAlloc_4601_, 3, v_auxDeclNGen_4581_);
lean_ctor_set(v_reuseFailAlloc_4601_, 4, v___x_4596_);
lean_ctor_set(v_reuseFailAlloc_4601_, 5, v_cache_4582_);
lean_ctor_set(v_reuseFailAlloc_4601_, 6, v_messages_4583_);
lean_ctor_set(v_reuseFailAlloc_4601_, 7, v_infoState_4584_);
lean_ctor_set(v_reuseFailAlloc_4601_, 8, v_snapshotTasks_4585_);
v___x_4598_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = lean_st_ref_set(v___y_4544_, v___x_4598_);
v___x_4600_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4546_);
return v___x_4600_;
}
}
}
}
}
else
{
goto v___jp_4569_;
}
}
else
{
goto v___jp_4569_;
}
}
v___jp_4605_:
{
double v___x_4607_; double v___x_4608_; double v___x_4609_; uint8_t v___x_4610_; 
v___x_4607_ = lean_unbox_float(v_snd_4555_);
v___x_4608_ = lean_unbox_float(v_fst_4554_);
v___x_4609_ = lean_float_sub(v___x_4607_, v___x_4608_);
v___x_4610_ = lean_float_decLt(v___y_4606_, v___x_4609_);
v___y_4575_ = v___x_4610_;
goto v___jp_4574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4621_, lean_object* v_collapsed_4622_, lean_object* v_tag_4623_, lean_object* v_opts_4624_, lean_object* v_clsEnabled_4625_, lean_object* v_oldTraces_4626_, lean_object* v_msg_4627_, lean_object* v_resStartStop_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
uint8_t v_collapsed_boxed_4636_; uint8_t v_clsEnabled_boxed_4637_; lean_object* v_res_4638_; 
v_collapsed_boxed_4636_ = lean_unbox(v_collapsed_4622_);
v_clsEnabled_boxed_4637_ = lean_unbox(v_clsEnabled_4625_);
v_res_4638_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4621_, v_collapsed_boxed_4636_, v_tag_4623_, v_opts_4624_, v_clsEnabled_boxed_4637_, v_oldTraces_4626_, v_msg_4627_, v_resStartStop_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec_ref(v_opts_4624_);
return v_res_4638_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4642_; double v___x_4643_; 
v___x_4642_ = lean_unsigned_to_nat(1000000000u);
v___x_4643_ = lean_float_of_nat(v___x_4642_);
return v___x_4643_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4652_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4653_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4654_ = l_Lean_Name_append(v___x_4653_, v___x_4652_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4655_, lean_object* v___x_4656_, lean_object* v_a_4657_, lean_object* v_b_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_a_4667_; uint8_t v___x_4671_; 
v___x_4671_ = lean_nat_dec_lt(v_a_4657_, v_upperBound_4655_);
if (v___x_4671_ == 0)
{
lean_object* v___x_4672_; 
lean_dec(v_a_4657_);
v___x_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4672_, 0, v_b_4658_);
return v___x_4672_;
}
else
{
lean_object* v___x_4673_; lean_object* v_toSignature_4674_; lean_object* v_value_4675_; lean_object* v_name_4676_; lean_object* v_params_4677_; uint8_t v_safe_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
lean_dec_ref(v_b_4658_);
v___x_4673_ = lean_array_fget_borrowed(v___x_4656_, v_a_4657_);
v_toSignature_4674_ = lean_ctor_get(v___x_4673_, 0);
v_value_4675_ = lean_ctor_get(v___x_4673_, 1);
v_name_4676_ = lean_ctor_get(v_toSignature_4674_, 0);
v_params_4677_ = lean_ctor_get(v_toSignature_4674_, 3);
v_safe_4678_ = lean_ctor_get_uint8(v_toSignature_4674_, sizeof(void*)*4);
v___x_4679_ = lean_box(0);
v___x_4680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4678_ == 0)
{
v_a_4667_ = v___x_4680_;
goto v___jp_4666_;
}
else
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4657_, v___y_4660_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___y_4684_; lean_object* v_decls_4714_; lean_object* v___f_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___y_4720_; uint8_t v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v_a_4726_; uint8_t v___y_4739_; lean_object* v___y_4740_; lean_object* v___y_4741_; lean_object* v___y_4742_; lean_object* v___y_4743_; lean_object* v___y_4744_; lean_object* v_a_4745_; uint8_t v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4825_; uint8_t v___x_4834_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
v_decls_4714_ = lean_ctor_get(v___y_4659_, 0);
lean_inc(v_name_4676_);
v___f_4715_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4715_, 0, v_name_4676_);
v___x_4716_ = lean_unsigned_to_nat(0u);
v___x_4717_ = lean_array_get_size(v_params_4677_);
lean_inc(v_a_4657_);
lean_inc_ref(v_decls_4714_);
v___x_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4718_, 0, v_decls_4714_);
lean_ctor_set(v___x_4718_, 1, v_a_4657_);
v___x_4834_ = lean_nat_dec_lt(v___x_4716_, v___x_4717_);
if (v___x_4834_ == 0)
{
goto v___jp_4808_;
}
else
{
uint8_t v___x_4835_; 
v___x_4835_ = lean_nat_dec_le(v___x_4717_, v___x_4717_);
if (v___x_4835_ == 0)
{
if (v___x_4834_ == 0)
{
goto v___jp_4808_;
}
else
{
size_t v___x_4836_; size_t v___x_4837_; lean_object* v___x_4838_; 
v___x_4836_ = ((size_t)0ULL);
v___x_4837_ = lean_usize_of_nat(v___x_4717_);
v___x_4838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4677_, v___x_4836_, v___x_4837_, v___x_4679_, v___x_4718_, v___y_4660_, v___y_4664_);
v___y_4825_ = v___x_4838_;
goto v___jp_4824_;
}
}
else
{
size_t v___x_4839_; size_t v___x_4840_; lean_object* v___x_4841_; 
v___x_4839_ = ((size_t)0ULL);
v___x_4840_ = lean_usize_of_nat(v___x_4717_);
v___x_4841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4677_, v___x_4839_, v___x_4840_, v___x_4679_, v___x_4718_, v___y_4660_, v___y_4664_);
v___y_4825_ = v___x_4841_;
goto v___jp_4824_;
}
}
v___jp_4683_:
{
if (lean_obj_tag(v___y_4684_) == 0)
{
lean_object* v___x_4685_; 
lean_dec_ref_known(v___y_4684_, 1);
v___x_4685_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4657_, v___y_4660_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4697_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4688_ = v___x_4685_;
v_isShared_4689_ = v_isSharedCheck_4697_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4685_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4697_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
uint8_t v___x_4690_; 
v___x_4690_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4682_, v_a_4686_);
lean_dec(v_a_4686_);
lean_dec(v_a_4682_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
lean_dec(v_a_4657_);
v___x_4691_ = lean_box(v_safe_4678_);
v___x_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
lean_ctor_set(v___x_4693_, 1, v___x_4679_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 0, v___x_4693_);
v___x_4695_ = v___x_4688_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
else
{
lean_del_object(v___x_4688_);
v_a_4667_ = v___x_4680_;
goto v___jp_4666_;
}
}
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_dec(v_a_4682_);
lean_dec(v_a_4657_);
v_a_4698_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4685_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4685_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
lean_dec(v_a_4682_);
lean_dec(v_a_4657_);
v_a_4706_ = lean_ctor_get(v___y_4684_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___y_4684_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___y_4684_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___y_4684_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
v___jp_4719_:
{
lean_object* v___x_4727_; double v___x_4728_; double v___x_4729_; double v___x_4730_; double v___x_4731_; double v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4727_ = lean_io_mono_nanos_now();
v___x_4728_ = lean_float_of_nat(v___y_4720_);
v___x_4729_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4730_ = lean_float_div(v___x_4728_, v___x_4729_);
v___x_4731_ = lean_float_of_nat(v___x_4727_);
v___x_4732_ = lean_float_div(v___x_4731_, v___x_4729_);
v___x_4733_ = lean_box_float(v___x_4730_);
v___x_4734_ = lean_box_float(v___x_4732_);
v___x_4735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4733_);
lean_ctor_set(v___x_4735_, 1, v___x_4734_);
v___x_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4736_, 0, v_a_4726_);
lean_ctor_set(v___x_4736_, 1, v___x_4735_);
lean_inc_ref(v___y_4722_);
lean_inc(v___y_4723_);
v___x_4737_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4723_, v_safe_4678_, v___y_4722_, v___y_4724_, v___y_4721_, v___y_4725_, v___f_4715_, v___x_4736_, v___x_4718_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec_ref_known(v___x_4718_, 2);
v___y_4684_ = v___x_4737_;
goto v___jp_4683_;
}
v___jp_4738_:
{
lean_object* v___x_4746_; double v___x_4747_; double v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4746_ = lean_io_get_num_heartbeats();
v___x_4747_ = lean_float_of_nat(v___y_4744_);
v___x_4748_ = lean_float_of_nat(v___x_4746_);
v___x_4749_ = lean_box_float(v___x_4747_);
v___x_4750_ = lean_box_float(v___x_4748_);
v___x_4751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4749_);
lean_ctor_set(v___x_4751_, 1, v___x_4750_);
v___x_4752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4752_, 0, v_a_4745_);
lean_ctor_set(v___x_4752_, 1, v___x_4751_);
lean_inc_ref(v___y_4740_);
lean_inc(v___y_4741_);
v___x_4753_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4741_, v_safe_4678_, v___y_4740_, v___y_4742_, v___y_4739_, v___y_4743_, v___f_4715_, v___x_4752_, v___x_4718_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec_ref_known(v___x_4718_, 2);
v___y_4684_ = v___x_4753_;
goto v___jp_4683_;
}
v___jp_4754_:
{
lean_object* v___x_4760_; 
v___x_4760_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4664_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v___x_4762_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4763_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4758_, v___x_4762_);
if (v___x_4763_ == 0)
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = lean_io_mono_nanos_now();
v___x_4765_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4759_, v___x_4718_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4765_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4765_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
lean_ctor_set_tag(v___x_4768_, 1);
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
v___y_4720_ = v___x_4764_;
v___y_4721_ = v___y_4755_;
v___y_4722_ = v___y_4756_;
v___y_4723_ = v___y_4757_;
v___y_4724_ = v___y_4758_;
v___y_4725_ = v_a_4761_;
v_a_4726_ = v___x_4771_;
goto v___jp_4719_;
}
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
v_a_4774_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4765_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4765_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
lean_ctor_set_tag(v___x_4776_, 0);
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
v___y_4720_ = v___x_4764_;
v___y_4721_ = v___y_4755_;
v___y_4722_ = v___y_4756_;
v___y_4723_ = v___y_4757_;
v___y_4724_ = v___y_4758_;
v___y_4725_ = v_a_4761_;
v_a_4726_ = v___x_4779_;
goto v___jp_4719_;
}
}
}
}
else
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = lean_io_get_num_heartbeats();
v___x_4783_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4759_, v___x_4718_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
lean_ctor_set_tag(v___x_4786_, 1);
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
v___y_4739_ = v___y_4755_;
v___y_4740_ = v___y_4756_;
v___y_4741_ = v___y_4757_;
v___y_4742_ = v___y_4758_;
v___y_4743_ = v_a_4761_;
v___y_4744_ = v___x_4782_;
v_a_4745_ = v___x_4789_;
goto v___jp_4738_;
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
v_a_4792_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4783_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4783_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
lean_ctor_set_tag(v___x_4794_, 0);
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
v___y_4739_ = v___y_4755_;
v___y_4740_ = v___y_4756_;
v___y_4741_ = v___y_4757_;
v___y_4742_ = v___y_4758_;
v___y_4743_ = v_a_4761_;
v___y_4744_ = v___x_4782_;
v_a_4745_ = v___x_4797_;
goto v___jp_4738_;
}
}
}
}
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_dec_ref(v___y_4759_);
lean_dec_ref_known(v___x_4718_, 2);
lean_dec_ref(v___f_4715_);
lean_dec(v_a_4682_);
lean_dec(v_a_4657_);
v_a_4800_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4760_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4760_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
v___jp_4808_:
{
if (lean_obj_tag(v_value_4675_) == 0)
{
lean_object* v_options_4809_; uint8_t v_hasTrace_4810_; 
v_options_4809_ = lean_ctor_get(v___y_4663_, 2);
v_hasTrace_4810_ = lean_ctor_get_uint8(v_options_4809_, sizeof(void*)*1);
if (v_hasTrace_4810_ == 0)
{
lean_object* v_code_4811_; lean_object* v___x_4812_; 
lean_dec_ref(v___f_4715_);
v_code_4811_ = lean_ctor_get(v_value_4675_, 0);
lean_inc_ref(v_code_4811_);
v___x_4812_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4811_, v___x_4718_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec_ref_known(v___x_4718_, 2);
v___y_4684_ = v___x_4812_;
goto v___jp_4683_;
}
else
{
lean_object* v_code_4813_; lean_object* v_inheritedTraceOptions_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v_code_4813_ = lean_ctor_get(v_value_4675_, 0);
v_inheritedTraceOptions_4814_ = lean_ctor_get(v___y_4663_, 13);
v___x_4815_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4816_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4817_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4818_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4814_, v_options_4809_, v___x_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; uint8_t v___x_4820_; 
v___x_4819_ = l_Lean_trace_profiler;
v___x_4820_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4809_, v___x_4819_);
if (v___x_4820_ == 0)
{
lean_object* v___x_4821_; 
lean_dec_ref(v___f_4715_);
lean_inc_ref(v_code_4813_);
v___x_4821_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4813_, v___x_4718_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec_ref_known(v___x_4718_, 2);
v___y_4684_ = v___x_4821_;
goto v___jp_4683_;
}
else
{
lean_inc_ref(v_code_4813_);
v___y_4755_ = v___x_4818_;
v___y_4756_ = v___x_4816_;
v___y_4757_ = v___x_4815_;
v___y_4758_ = v_options_4809_;
v___y_4759_ = v_code_4813_;
goto v___jp_4754_;
}
}
else
{
lean_inc_ref(v_code_4813_);
v___y_4755_ = v___x_4818_;
v___y_4756_ = v___x_4816_;
v___y_4757_ = v___x_4815_;
v___y_4758_ = v_options_4809_;
v___y_4759_ = v_code_4813_;
goto v___jp_4754_;
}
}
}
else
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
lean_dec_ref(v___f_4715_);
v___x_4822_ = lean_box(1);
v___x_4823_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4822_, v___x_4718_, v___y_4660_, v___y_4664_);
lean_dec_ref_known(v___x_4718_, 2);
v___y_4684_ = v___x_4823_;
goto v___jp_4683_;
}
}
v___jp_4824_:
{
if (lean_obj_tag(v___y_4825_) == 0)
{
lean_dec_ref_known(v___y_4825_, 1);
goto v___jp_4808_;
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
lean_dec_ref_known(v___x_4718_, 2);
lean_dec_ref(v___f_4715_);
lean_dec(v_a_4682_);
lean_dec(v_a_4657_);
v_a_4826_ = lean_ctor_get(v___y_4825_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___y_4825_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___y_4825_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___y_4825_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec(v_a_4657_);
v_a_4842_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4681_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4681_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
v___jp_4666_:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = lean_unsigned_to_nat(1u);
v___x_4669_ = lean_nat_add(v_a_4657_, v___x_4668_);
lean_dec(v_a_4657_);
lean_inc_ref(v_a_4667_);
v_a_4657_ = v___x_4669_;
v_b_4658_ = v_a_4667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4850_, lean_object* v___x_4851_, lean_object* v_a_4852_, lean_object* v_b_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4850_, v___x_4851_, v_a_4852_, v_b_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec_ref(v___x_4851_);
lean_dec(v_upperBound_4850_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_decls_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v_decls_4869_ = lean_ctor_get(v_a_4862_, 0);
v___x_4870_ = lean_array_get_size(v_decls_4869_);
v___x_4871_ = lean_unsigned_to_nat(0u);
v___x_4872_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4870_, v_decls_4869_, v___x_4871_, v___x_4872_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4888_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4888_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4888_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v_fst_4878_; 
v_fst_4878_ = lean_ctor_get(v_a_4874_, 0);
lean_inc(v_fst_4878_);
lean_dec(v_a_4874_);
if (lean_obj_tag(v_fst_4878_) == 0)
{
uint8_t v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4879_ = 0;
v___x_4880_ = lean_box(v___x_4879_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v___x_4880_);
v___x_4882_ = v___x_4876_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
else
{
lean_object* v_val_4884_; lean_object* v___x_4886_; 
v_val_4884_ = lean_ctor_get(v_fst_4878_, 0);
lean_inc(v_val_4884_);
lean_dec_ref_known(v_fst_4878_, 1);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v_val_4884_);
v___x_4886_ = v___x_4876_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_val_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
v_a_4889_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4873_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4873_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
lean_dec(v_a_4902_);
lean_dec_ref(v_a_4901_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec(v_a_4898_);
lean_dec_ref(v_a_4897_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4905_, lean_object* v_x_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4906_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4915_, lean_object* v_x_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4915_, v_x_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
lean_dec(v___y_4920_);
lean_dec_ref(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4925_, lean_object* v___x_4926_, lean_object* v_inst_4927_, lean_object* v_R_4928_, lean_object* v_a_4929_, lean_object* v_b_4930_, lean_object* v_c_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4925_, v___x_4926_, v_a_4929_, v_b_4930_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4940_, lean_object* v___x_4941_, lean_object* v_inst_4942_, lean_object* v_R_4943_, lean_object* v_a_4944_, lean_object* v_b_4945_, lean_object* v_c_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4940_, v___x_4941_, v_inst_4942_, v_R_4943_, v_a_4944_, v_b_4945_, v_c_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec_ref(v___x_4941_);
lean_dec(v_upperBound_4940_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4955_, lean_object* v_data_4956_, lean_object* v_ref_4957_, lean_object* v_msg_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v___x_4966_; 
v___x_4966_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4955_, v_data_4956_, v_ref_4957_, v_msg_4958_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4967_, lean_object* v_data_4968_, lean_object* v_ref_4969_, lean_object* v_msg_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4967_, v_data_4968_, v_ref_4969_, v_msg_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4981_, lean_object* v_msg_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_options_4988_; lean_object* v_ref_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v_options_4988_ = lean_ctor_get(v___y_4985_, 2);
v_ref_4989_ = lean_ctor_get(v___y_4985_, 5);
v___x_4990_ = lean_st_ref_get(v___y_4986_);
v___x_4991_ = lean_st_ref_get(v___y_4984_);
v___x_4992_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4983_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5051_; 
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_4995_ = v___x_4992_;
v_isShared_4996_ = v_isSharedCheck_5051_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4992_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5051_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v_env_4997_; lean_object* v_lctx_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5049_; 
v_env_4997_ = lean_ctor_get(v___x_4990_, 0);
lean_inc_ref(v_env_4997_);
lean_dec(v___x_4990_);
v_lctx_4998_ = lean_ctor_get(v___x_4991_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_5049_ == 0)
{
lean_object* v_unused_5050_; 
v_unused_5050_ = lean_ctor_get(v___x_4991_, 1);
lean_dec(v_unused_5050_);
v___x_5000_ = v___x_4991_;
v_isShared_5001_ = v_isSharedCheck_5049_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_lctx_4998_);
lean_dec(v___x_4991_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5049_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v_traceState_5004_; lean_object* v_env_5005_; lean_object* v_nextMacroScope_5006_; lean_object* v_ngen_5007_; lean_object* v_auxDeclNGen_5008_; lean_object* v_cache_5009_; lean_object* v_messages_5010_; lean_object* v_infoState_5011_; lean_object* v_snapshotTasks_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5048_; 
v___x_5002_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_5003_ = lean_st_ref_take(v___y_4986_);
v_traceState_5004_ = lean_ctor_get(v___x_5003_, 4);
v_env_5005_ = lean_ctor_get(v___x_5003_, 0);
v_nextMacroScope_5006_ = lean_ctor_get(v___x_5003_, 1);
v_ngen_5007_ = lean_ctor_get(v___x_5003_, 2);
v_auxDeclNGen_5008_ = lean_ctor_get(v___x_5003_, 3);
v_cache_5009_ = lean_ctor_get(v___x_5003_, 5);
v_messages_5010_ = lean_ctor_get(v___x_5003_, 6);
v_infoState_5011_ = lean_ctor_get(v___x_5003_, 7);
v_snapshotTasks_5012_ = lean_ctor_get(v___x_5003_, 8);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5014_ = v___x_5003_;
v_isShared_5015_ = v_isSharedCheck_5048_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_snapshotTasks_5012_);
lean_inc(v_infoState_5011_);
lean_inc(v_messages_5010_);
lean_inc(v_cache_5009_);
lean_inc(v_traceState_5004_);
lean_inc(v_auxDeclNGen_5008_);
lean_inc(v_ngen_5007_);
lean_inc(v_nextMacroScope_5006_);
lean_inc(v_env_5005_);
lean_dec(v___x_5003_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5048_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
uint64_t v_tid_5016_; lean_object* v_traces_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5047_; 
v_tid_5016_ = lean_ctor_get_uint64(v_traceState_5004_, sizeof(void*)*1);
v_traces_5017_ = lean_ctor_get(v_traceState_5004_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v_traceState_5004_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5019_ = v_traceState_5004_;
v_isShared_5020_ = v_isSharedCheck_5047_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_traces_5017_);
lean_dec(v_traceState_5004_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5047_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
uint8_t v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5025_; 
v___x_5021_ = lean_unbox(v_a_4993_);
lean_dec(v_a_4993_);
v___x_5022_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4998_, v___x_5021_);
lean_dec_ref(v_lctx_4998_);
lean_inc_ref(v_options_4988_);
v___x_5023_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5023_, 0, v_env_4997_);
lean_ctor_set(v___x_5023_, 1, v___x_5002_);
lean_ctor_set(v___x_5023_, 2, v___x_5022_);
lean_ctor_set(v___x_5023_, 3, v_options_4988_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set_tag(v___x_5000_, 3);
lean_ctor_set(v___x_5000_, 1, v_msg_4982_);
lean_ctor_set(v___x_5000_, 0, v___x_5023_);
v___x_5025_ = v___x_5000_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5023_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v_msg_4982_);
v___x_5025_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
lean_object* v___x_5026_; double v___x_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5026_ = lean_box(0);
v___x_5027_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5028_ = 0;
v___x_5029_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5030_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5030_, 0, v_cls_4981_);
lean_ctor_set(v___x_5030_, 1, v___x_5026_);
lean_ctor_set(v___x_5030_, 2, v___x_5029_);
lean_ctor_set_float(v___x_5030_, sizeof(void*)*3, v___x_5027_);
lean_ctor_set_float(v___x_5030_, sizeof(void*)*3 + 8, v___x_5027_);
lean_ctor_set_uint8(v___x_5030_, sizeof(void*)*3 + 16, v___x_5028_);
v___x_5031_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5032_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5030_);
lean_ctor_set(v___x_5032_, 1, v___x_5025_);
lean_ctor_set(v___x_5032_, 2, v___x_5031_);
lean_inc(v_ref_4989_);
v___x_5033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5033_, 0, v_ref_4989_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = l_Lean_PersistentArray_push___redArg(v_traces_5017_, v___x_5033_);
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 0, v___x_5034_);
v___x_5036_ = v___x_5019_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5034_);
lean_ctor_set_uint64(v_reuseFailAlloc_5045_, sizeof(void*)*1, v_tid_5016_);
v___x_5036_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5038_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 4, v___x_5036_);
v___x_5038_ = v___x_5014_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_env_5005_);
lean_ctor_set(v_reuseFailAlloc_5044_, 1, v_nextMacroScope_5006_);
lean_ctor_set(v_reuseFailAlloc_5044_, 2, v_ngen_5007_);
lean_ctor_set(v_reuseFailAlloc_5044_, 3, v_auxDeclNGen_5008_);
lean_ctor_set(v_reuseFailAlloc_5044_, 4, v___x_5036_);
lean_ctor_set(v_reuseFailAlloc_5044_, 5, v_cache_5009_);
lean_ctor_set(v_reuseFailAlloc_5044_, 6, v_messages_5010_);
lean_ctor_set(v_reuseFailAlloc_5044_, 7, v_infoState_5011_);
lean_ctor_set(v_reuseFailAlloc_5044_, 8, v_snapshotTasks_5012_);
v___x_5038_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5042_; 
v___x_5039_ = lean_st_ref_set(v___y_4986_, v___x_5038_);
v___x_5040_ = lean_box(0);
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 0, v___x_5040_);
v___x_5042_ = v___x_4995_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
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
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
lean_dec(v___x_4991_);
lean_dec(v___x_4990_);
lean_dec_ref(v_msg_4982_);
lean_dec(v_cls_4981_);
v_a_5052_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5054_ = v___x_4992_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_4992_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_5060_, lean_object* v_msg_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_5060_, v_msg_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_5068_, lean_object* v_msg_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v___x_5077_; 
v___x_5077_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_5068_, v_msg_5069_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_5078_, lean_object* v_msg_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_5078_, v_msg_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
lean_dec(v___y_5081_);
lean_dec_ref(v___y_5080_);
return v_res_5087_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___x_5088_ = lean_box(0);
v___x_5089_ = lean_unsigned_to_nat(16u);
v___x_5090_ = lean_mk_array(v___x_5089_, v___x_5088_);
return v___x_5090_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5091_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_5092_ = lean_unsigned_to_nat(0u);
v___x_5093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5092_);
lean_ctor_set(v___x_5093_, 1, v___x_5091_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_5094_, size_t v_i_5095_, lean_object* v_bs_5096_){
_start:
{
uint8_t v___x_5097_; 
v___x_5097_ = lean_usize_dec_lt(v_i_5095_, v_sz_5094_);
if (v___x_5097_ == 0)
{
return v_bs_5096_;
}
else
{
lean_object* v___x_5098_; lean_object* v_bs_x27_5099_; lean_object* v___x_5100_; size_t v___x_5101_; size_t v___x_5102_; lean_object* v___x_5103_; 
v___x_5098_ = lean_unsigned_to_nat(0u);
v_bs_x27_5099_ = lean_array_uset(v_bs_5096_, v_i_5095_, v___x_5098_);
v___x_5100_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5101_ = ((size_t)1ULL);
v___x_5102_ = lean_usize_add(v_i_5095_, v___x_5101_);
v___x_5103_ = lean_array_uset(v_bs_x27_5099_, v_i_5095_, v___x_5100_);
v_i_5095_ = v___x_5102_;
v_bs_5096_ = v___x_5103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_5105_, lean_object* v_i_5106_, lean_object* v_bs_5107_){
_start:
{
size_t v_sz_boxed_5108_; size_t v_i_boxed_5109_; lean_object* v_res_5110_; 
v_sz_boxed_5108_ = lean_unbox_usize(v_sz_5105_);
lean_dec(v_sz_5105_);
v_i_boxed_5109_ = lean_unbox_usize(v_i_5106_);
lean_dec(v_i_5106_);
v_res_5110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_5108_, v_i_boxed_5109_, v_bs_5107_);
return v_res_5110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___x_5112_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5113_ = l_Lean_stringToMessageData(v___x_5112_);
return v___x_5113_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5116_ = l_Lean_stringToMessageData(v___x_5115_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v___x_5128_; lean_object* v_decls_5129_; lean_object* v_funVals_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5169_; 
v___x_5128_ = lean_st_ref_take(v_a_5119_);
v_decls_5129_ = lean_ctor_get(v_a_5118_, 0);
v_funVals_5130_ = lean_ctor_get(v___x_5128_, 1);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5169_ == 0)
{
lean_object* v_unused_5170_; 
v_unused_5170_ = lean_ctor_get(v___x_5128_, 0);
lean_dec(v_unused_5170_);
v___x_5132_ = v___x_5128_;
v_isShared_5133_ = v_isSharedCheck_5169_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_funVals_5130_);
lean_dec(v___x_5128_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5169_;
goto v_resetjp_5131_;
}
v___jp_5125_:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5126_ = lean_box(0);
v___x_5127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5127_, 0, v___x_5126_);
return v___x_5127_;
}
v_resetjp_5131_:
{
size_t v_sz_5134_; size_t v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5138_; 
v_sz_5134_ = lean_array_size(v_decls_5129_);
v___x_5135_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5129_);
v___x_5136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5134_, v___x_5135_, v_decls_5129_);
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 0, v___x_5136_);
v___x_5138_ = v___x_5132_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5168_, 1, v_funVals_5130_);
v___x_5138_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5139_ = lean_st_ref_set(v_a_5119_, v___x_5138_);
v___x_5140_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; uint8_t v___x_5142_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___x_5140_, 1);
v___x_5142_ = lean_unbox(v_a_5141_);
lean_dec(v_a_5141_);
if (v___x_5142_ == 0)
{
lean_object* v_options_5143_; uint8_t v_hasTrace_5144_; 
v_options_5143_ = lean_ctor_get(v_a_5122_, 2);
v_hasTrace_5144_ = lean_ctor_get_uint8(v_options_5143_, sizeof(void*)*1);
if (v_hasTrace_5144_ == 0)
{
lean_dec(v_n_5117_);
goto v___jp_5125_;
}
else
{
lean_object* v_inheritedTraceOptions_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; uint8_t v___x_5148_; 
v_inheritedTraceOptions_5145_ = lean_ctor_get(v_a_5122_, 13);
v___x_5146_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5147_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5148_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5145_, v_options_5143_, v___x_5147_);
if (v___x_5148_ == 0)
{
lean_dec(v_n_5117_);
goto v___jp_5125_;
}
else
{
lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v___x_5149_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5150_ = l_Nat_reprFast(v_n_5117_);
v___x_5151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5151_, 0, v___x_5150_);
v___x_5152_ = l_Lean_MessageData_ofFormat(v___x_5151_);
v___x_5153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5149_);
lean_ctor_set(v___x_5153_, 1, v___x_5152_);
v___x_5154_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5153_);
lean_ctor_set(v___x_5155_, 1, v___x_5154_);
v___x_5156_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5146_, v___x_5155_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_dec_ref_known(v___x_5156_, 1);
goto v___jp_5125_;
}
else
{
return v___x_5156_;
}
}
}
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; 
v___x_5157_ = lean_unsigned_to_nat(1u);
v___x_5158_ = lean_nat_add(v_n_5117_, v___x_5157_);
lean_dec(v_n_5117_);
v_n_5117_ = v___x_5158_;
goto _start;
}
}
else
{
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5167_; 
lean_dec(v_n_5117_);
v_a_5160_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5162_ = v___x_5140_;
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v___x_5140_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
return v_res_5179_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5180_; lean_object* v___x_5181_; 
v___x_5180_ = 0;
v___x_5181_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5180_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5182_){
_start:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5183_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5184_ = lean_panic_fn_borrowed(v___x_5183_, v_msg_5182_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5185_, lean_object* v_msg_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v_options_5192_; lean_object* v_ref_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v_options_5192_ = lean_ctor_get(v___y_5189_, 2);
v_ref_5193_ = lean_ctor_get(v___y_5189_, 5);
v___x_5194_ = lean_st_ref_get(v___y_5190_);
v___x_5195_ = lean_st_ref_get(v___y_5188_);
v___x_5196_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5187_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5255_; 
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5199_ = v___x_5196_;
v_isShared_5200_ = v_isSharedCheck_5255_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5196_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5255_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v_env_5201_; lean_object* v_lctx_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5253_; 
v_env_5201_ = lean_ctor_get(v___x_5194_, 0);
lean_inc_ref(v_env_5201_);
lean_dec(v___x_5194_);
v_lctx_5202_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; 
v_unused_5254_ = lean_ctor_get(v___x_5195_, 1);
lean_dec(v_unused_5254_);
v___x_5204_ = v___x_5195_;
v_isShared_5205_ = v_isSharedCheck_5253_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_lctx_5202_);
lean_dec(v___x_5195_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5253_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v_traceState_5208_; lean_object* v_env_5209_; lean_object* v_nextMacroScope_5210_; lean_object* v_ngen_5211_; lean_object* v_auxDeclNGen_5212_; lean_object* v_cache_5213_; lean_object* v_messages_5214_; lean_object* v_infoState_5215_; lean_object* v_snapshotTasks_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5252_; 
v___x_5206_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_5207_ = lean_st_ref_take(v___y_5190_);
v_traceState_5208_ = lean_ctor_get(v___x_5207_, 4);
v_env_5209_ = lean_ctor_get(v___x_5207_, 0);
v_nextMacroScope_5210_ = lean_ctor_get(v___x_5207_, 1);
v_ngen_5211_ = lean_ctor_get(v___x_5207_, 2);
v_auxDeclNGen_5212_ = lean_ctor_get(v___x_5207_, 3);
v_cache_5213_ = lean_ctor_get(v___x_5207_, 5);
v_messages_5214_ = lean_ctor_get(v___x_5207_, 6);
v_infoState_5215_ = lean_ctor_get(v___x_5207_, 7);
v_snapshotTasks_5216_ = lean_ctor_get(v___x_5207_, 8);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5218_ = v___x_5207_;
v_isShared_5219_ = v_isSharedCheck_5252_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_snapshotTasks_5216_);
lean_inc(v_infoState_5215_);
lean_inc(v_messages_5214_);
lean_inc(v_cache_5213_);
lean_inc(v_traceState_5208_);
lean_inc(v_auxDeclNGen_5212_);
lean_inc(v_ngen_5211_);
lean_inc(v_nextMacroScope_5210_);
lean_inc(v_env_5209_);
lean_dec(v___x_5207_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5252_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
uint64_t v_tid_5220_; lean_object* v_traces_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5251_; 
v_tid_5220_ = lean_ctor_get_uint64(v_traceState_5208_, sizeof(void*)*1);
v_traces_5221_ = lean_ctor_get(v_traceState_5208_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v_traceState_5208_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5223_ = v_traceState_5208_;
v_isShared_5224_ = v_isSharedCheck_5251_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_traces_5221_);
lean_dec(v_traceState_5208_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5251_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
uint8_t v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5229_; 
v___x_5225_ = lean_unbox(v_a_5197_);
lean_dec(v_a_5197_);
v___x_5226_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5202_, v___x_5225_);
lean_dec_ref(v_lctx_5202_);
lean_inc_ref(v_options_5192_);
v___x_5227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5227_, 0, v_env_5201_);
lean_ctor_set(v___x_5227_, 1, v___x_5206_);
lean_ctor_set(v___x_5227_, 2, v___x_5226_);
lean_ctor_set(v___x_5227_, 3, v_options_5192_);
if (v_isShared_5205_ == 0)
{
lean_ctor_set_tag(v___x_5204_, 3);
lean_ctor_set(v___x_5204_, 1, v_msg_5186_);
lean_ctor_set(v___x_5204_, 0, v___x_5227_);
v___x_5229_ = v___x_5204_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5227_);
lean_ctor_set(v_reuseFailAlloc_5250_, 1, v_msg_5186_);
v___x_5229_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
lean_object* v___x_5230_; double v___x_5231_; uint8_t v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5240_; 
v___x_5230_ = lean_box(0);
v___x_5231_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5232_ = 0;
v___x_5233_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5234_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5234_, 0, v_cls_5185_);
lean_ctor_set(v___x_5234_, 1, v___x_5230_);
lean_ctor_set(v___x_5234_, 2, v___x_5233_);
lean_ctor_set_float(v___x_5234_, sizeof(void*)*3, v___x_5231_);
lean_ctor_set_float(v___x_5234_, sizeof(void*)*3 + 8, v___x_5231_);
lean_ctor_set_uint8(v___x_5234_, sizeof(void*)*3 + 16, v___x_5232_);
v___x_5235_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5236_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5234_);
lean_ctor_set(v___x_5236_, 1, v___x_5229_);
lean_ctor_set(v___x_5236_, 2, v___x_5235_);
lean_inc(v_ref_5193_);
v___x_5237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5237_, 0, v_ref_5193_);
lean_ctor_set(v___x_5237_, 1, v___x_5236_);
v___x_5238_ = l_Lean_PersistentArray_push___redArg(v_traces_5221_, v___x_5237_);
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 0, v___x_5238_);
v___x_5240_ = v___x_5223_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v___x_5238_);
lean_ctor_set_uint64(v_reuseFailAlloc_5249_, sizeof(void*)*1, v_tid_5220_);
v___x_5240_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
lean_object* v___x_5242_; 
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 4, v___x_5240_);
v___x_5242_ = v___x_5218_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_env_5209_);
lean_ctor_set(v_reuseFailAlloc_5248_, 1, v_nextMacroScope_5210_);
lean_ctor_set(v_reuseFailAlloc_5248_, 2, v_ngen_5211_);
lean_ctor_set(v_reuseFailAlloc_5248_, 3, v_auxDeclNGen_5212_);
lean_ctor_set(v_reuseFailAlloc_5248_, 4, v___x_5240_);
lean_ctor_set(v_reuseFailAlloc_5248_, 5, v_cache_5213_);
lean_ctor_set(v_reuseFailAlloc_5248_, 6, v_messages_5214_);
lean_ctor_set(v_reuseFailAlloc_5248_, 7, v_infoState_5215_);
lean_ctor_set(v_reuseFailAlloc_5248_, 8, v_snapshotTasks_5216_);
v___x_5242_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5246_; 
v___x_5243_ = lean_st_ref_set(v___y_5190_, v___x_5242_);
v___x_5244_ = lean_box(0);
if (v_isShared_5200_ == 0)
{
lean_ctor_set(v___x_5199_, 0, v___x_5244_);
v___x_5246_ = v___x_5199_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5244_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
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
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
lean_dec(v___x_5195_);
lean_dec(v___x_5194_);
lean_dec_ref(v_msg_5186_);
lean_dec(v_cls_5185_);
v_a_5256_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5196_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5196_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5264_, lean_object* v_msg_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5264_, v_msg_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5272_, size_t v_i_5273_, size_t v_stop_5274_, lean_object* v_b_5275_){
_start:
{
uint8_t v___x_5277_; 
v___x_5277_ = lean_usize_dec_eq(v_i_5273_, v_stop_5274_);
if (v___x_5277_ == 0)
{
lean_object* v_fst_5278_; lean_object* v_snd_5279_; lean_object* v___x_5280_; lean_object* v_snd_5281_; lean_object* v_fst_5282_; lean_object* v_fst_5283_; lean_object* v_snd_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5299_; 
v_fst_5278_ = lean_ctor_get(v_b_5275_, 0);
lean_inc(v_fst_5278_);
v_snd_5279_ = lean_ctor_get(v_b_5275_, 1);
lean_inc(v_snd_5279_);
lean_dec_ref(v_b_5275_);
v___x_5280_ = lean_array_uget_borrowed(v_as_5272_, v_i_5273_);
v_snd_5281_ = lean_ctor_get(v___x_5280_, 1);
lean_inc(v_snd_5281_);
v_fst_5282_ = lean_ctor_get(v___x_5280_, 0);
v_fst_5283_ = lean_ctor_get(v_snd_5281_, 0);
v_snd_5284_ = lean_ctor_get(v_snd_5281_, 1);
v_isSharedCheck_5299_ = !lean_is_exclusive(v_snd_5281_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5286_ = v_snd_5281_;
v_isShared_5287_ = v_isSharedCheck_5299_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_snd_5284_);
lean_inc(v_fst_5283_);
lean_dec(v_snd_5281_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5299_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v_fvarId_5288_; uint8_t v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5294_; 
v_fvarId_5288_ = lean_ctor_get(v_fst_5282_, 0);
v___x_5289_ = 0;
v___x_5290_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5289_, v_fst_5283_, v_fst_5278_);
lean_dec(v_fst_5283_);
v___x_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5291_, 0, v_snd_5284_);
lean_inc(v_fvarId_5288_);
v___x_5292_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5279_, v_fvarId_5288_, v___x_5291_);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 1, v___x_5292_);
lean_ctor_set(v___x_5286_, 0, v___x_5290_);
v___x_5294_ = v___x_5286_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5290_);
lean_ctor_set(v_reuseFailAlloc_5298_, 1, v___x_5292_);
v___x_5294_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
size_t v___x_5295_; size_t v___x_5296_; 
v___x_5295_ = ((size_t)1ULL);
v___x_5296_ = lean_usize_add(v_i_5273_, v___x_5295_);
v_i_5273_ = v___x_5296_;
v_b_5275_ = v___x_5294_;
goto _start;
}
}
}
else
{
lean_object* v___x_5300_; 
v___x_5300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5300_, 0, v_b_5275_);
return v___x_5300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5301_, lean_object* v_i_5302_, lean_object* v_stop_5303_, lean_object* v_b_5304_, lean_object* v___y_5305_){
_start:
{
size_t v_i_boxed_5306_; size_t v_stop_boxed_5307_; lean_object* v_res_5308_; 
v_i_boxed_5306_ = lean_unbox_usize(v_i_5302_);
lean_dec(v_i_5302_);
v_stop_boxed_5307_ = lean_unbox_usize(v_stop_5303_);
lean_dec(v_stop_5303_);
v_res_5308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5301_, v_i_boxed_5306_, v_stop_boxed_5307_, v_b_5304_);
lean_dec_ref(v_as_5301_);
return v_res_5308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5309_, lean_object* v_x_5310_){
_start:
{
if (lean_obj_tag(v_x_5310_) == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_box(0);
return v___x_5311_;
}
else
{
lean_object* v_key_5312_; lean_object* v_value_5313_; lean_object* v_tail_5314_; uint8_t v___x_5315_; 
v_key_5312_ = lean_ctor_get(v_x_5310_, 0);
v_value_5313_ = lean_ctor_get(v_x_5310_, 1);
v_tail_5314_ = lean_ctor_get(v_x_5310_, 2);
v___x_5315_ = l_Lean_instBEqFVarId_beq(v_key_5312_, v_a_5309_);
if (v___x_5315_ == 0)
{
v_x_5310_ = v_tail_5314_;
goto _start;
}
else
{
lean_object* v___x_5317_; 
lean_inc(v_value_5313_);
v___x_5317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5317_, 0, v_value_5313_);
return v___x_5317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5318_, lean_object* v_x_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5318_, v_x_5319_);
lean_dec(v_x_5319_);
lean_dec(v_a_5318_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5321_, lean_object* v_a_5322_){
_start:
{
lean_object* v_buckets_5323_; lean_object* v___x_5324_; uint64_t v___x_5325_; uint64_t v___x_5326_; uint64_t v___x_5327_; uint64_t v_fold_5328_; uint64_t v___x_5329_; uint64_t v___x_5330_; uint64_t v___x_5331_; size_t v___x_5332_; size_t v___x_5333_; size_t v___x_5334_; size_t v___x_5335_; size_t v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v_buckets_5323_ = lean_ctor_get(v_m_5321_, 1);
v___x_5324_ = lean_array_get_size(v_buckets_5323_);
v___x_5325_ = l_Lean_instHashableFVarId_hash(v_a_5322_);
v___x_5326_ = 32ULL;
v___x_5327_ = lean_uint64_shift_right(v___x_5325_, v___x_5326_);
v_fold_5328_ = lean_uint64_xor(v___x_5325_, v___x_5327_);
v___x_5329_ = 16ULL;
v___x_5330_ = lean_uint64_shift_right(v_fold_5328_, v___x_5329_);
v___x_5331_ = lean_uint64_xor(v_fold_5328_, v___x_5330_);
v___x_5332_ = lean_uint64_to_usize(v___x_5331_);
v___x_5333_ = lean_usize_of_nat(v___x_5324_);
v___x_5334_ = ((size_t)1ULL);
v___x_5335_ = lean_usize_sub(v___x_5333_, v___x_5334_);
v___x_5336_ = lean_usize_land(v___x_5332_, v___x_5335_);
v___x_5337_ = lean_array_uget_borrowed(v_buckets_5323_, v___x_5336_);
v___x_5338_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5322_, v___x_5337_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5339_, lean_object* v_a_5340_){
_start:
{
lean_object* v_res_5341_; 
v_res_5341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5339_, v_a_5340_);
lean_dec(v_a_5340_);
lean_dec_ref(v_m_5339_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5342_, lean_object* v_as_5343_, size_t v_i_5344_, size_t v_stop_5345_, lean_object* v_b_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_){
_start:
{
lean_object* v_a_5353_; uint8_t v___x_5357_; 
v___x_5357_ = lean_usize_dec_eq(v_i_5344_, v_stop_5345_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; lean_object* v_fvarId_5359_; lean_object* v___x_5360_; 
v___x_5358_ = lean_array_uget_borrowed(v_as_5343_, v_i_5344_);
v_fvarId_5359_ = lean_ctor_get(v___x_5358_, 0);
v___x_5360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5342_, v_fvarId_5359_);
if (lean_obj_tag(v___x_5360_) == 1)
{
lean_object* v_val_5361_; lean_object* v___x_5362_; 
v_val_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_val_5361_);
lean_dec_ref_known(v___x_5360_, 1);
v___x_5362_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5361_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_object* v_a_5363_; 
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
lean_inc(v_a_5363_);
lean_dec_ref_known(v___x_5362_, 1);
if (lean_obj_tag(v_a_5363_) == 1)
{
lean_object* v_val_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; 
v_val_5364_ = lean_ctor_get(v_a_5363_, 0);
lean_inc(v_val_5364_);
lean_dec_ref_known(v_a_5363_, 1);
lean_inc(v___x_5358_);
v___x_5365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5358_);
lean_ctor_set(v___x_5365_, 1, v_val_5364_);
v___x_5366_ = lean_array_push(v_b_5346_, v___x_5365_);
v_a_5353_ = v___x_5366_;
goto v___jp_5352_;
}
else
{
lean_dec(v_a_5363_);
v_a_5353_ = v_b_5346_;
goto v___jp_5352_;
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_dec_ref(v_b_5346_);
v_a_5367_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5362_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5362_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
else
{
lean_dec(v___x_5360_);
v_a_5353_ = v_b_5346_;
goto v___jp_5352_;
}
}
else
{
lean_object* v___x_5375_; 
v___x_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5375_, 0, v_b_5346_);
return v___x_5375_;
}
v___jp_5352_:
{
size_t v___x_5354_; size_t v___x_5355_; 
v___x_5354_ = ((size_t)1ULL);
v___x_5355_ = lean_usize_add(v_i_5344_, v___x_5354_);
v_i_5344_ = v___x_5355_;
v_b_5346_ = v_a_5353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5376_, lean_object* v_as_5377_, lean_object* v_i_5378_, lean_object* v_stop_5379_, lean_object* v_b_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_){
_start:
{
size_t v_i_boxed_5386_; size_t v_stop_boxed_5387_; lean_object* v_res_5388_; 
v_i_boxed_5386_ = lean_unbox_usize(v_i_5378_);
lean_dec(v_i_5378_);
v_stop_boxed_5387_ = lean_unbox_usize(v_stop_5379_);
lean_dec(v_stop_5379_);
v_res_5388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5376_, v_as_5377_, v_i_boxed_5386_, v_stop_boxed_5387_, v_b_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec_ref(v_as_5377_);
lean_dec_ref(v_assignment_5376_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5391_, lean_object* v_as_5392_, lean_object* v_start_5393_, lean_object* v_stop_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
lean_object* v___x_5400_; uint8_t v___x_5401_; 
v___x_5400_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5401_ = lean_nat_dec_lt(v_start_5393_, v_stop_5394_);
if (v___x_5401_ == 0)
{
lean_object* v___x_5402_; 
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5400_);
return v___x_5402_;
}
else
{
lean_object* v___x_5403_; uint8_t v___x_5404_; 
v___x_5403_ = lean_array_get_size(v_as_5392_);
v___x_5404_ = lean_nat_dec_le(v_stop_5394_, v___x_5403_);
if (v___x_5404_ == 0)
{
uint8_t v___x_5405_; 
v___x_5405_ = lean_nat_dec_lt(v_start_5393_, v___x_5403_);
if (v___x_5405_ == 0)
{
lean_object* v___x_5406_; 
v___x_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5400_);
return v___x_5406_;
}
else
{
size_t v___x_5407_; size_t v___x_5408_; lean_object* v___x_5409_; 
v___x_5407_ = lean_usize_of_nat(v_start_5393_);
v___x_5408_ = lean_usize_of_nat(v___x_5403_);
v___x_5409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5391_, v_as_5392_, v___x_5407_, v___x_5408_, v___x_5400_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
return v___x_5409_;
}
}
else
{
size_t v___x_5410_; size_t v___x_5411_; lean_object* v___x_5412_; 
v___x_5410_ = lean_usize_of_nat(v_start_5393_);
v___x_5411_ = lean_usize_of_nat(v_stop_5394_);
v___x_5412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5391_, v_as_5392_, v___x_5410_, v___x_5411_, v___x_5400_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
return v___x_5412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5413_, lean_object* v_as_5414_, lean_object* v_start_5415_, lean_object* v_stop_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5413_, v_as_5414_, v_start_5415_, v_stop_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v_stop_5416_);
lean_dec(v_start_5415_);
lean_dec_ref(v_as_5414_);
lean_dec_ref(v_assignment_5413_);
return v_res_5422_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5425_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___closed__2));
v___x_5426_ = lean_unsigned_to_nat(9u);
v___x_5427_ = lean_unsigned_to_nat(641u);
v___x_5428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5429_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5430_ = l_mkPanicMessageWithDecl(v___x_5429_, v___x_5428_, v___x_5427_, v___x_5426_, v___x_5425_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5433_, lean_object* v_discrVal_5434_, lean_object* v_discr_5435_, lean_object* v_assignment_5436_, lean_object* v_i_5437_, lean_object* v_as_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_){
_start:
{
lean_object* v___x_5444_; uint8_t v___x_5445_; 
v___x_5444_ = lean_array_get_size(v_as_5438_);
v___x_5445_ = lean_nat_dec_lt(v_i_5437_, v___x_5444_);
if (v___x_5445_ == 0)
{
lean_object* v___x_5446_; 
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v___x_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5446_, 0, v_as_5438_);
return v___x_5446_;
}
else
{
lean_object* v_a_5447_; lean_object* v_a_5449_; 
v_a_5447_ = lean_array_fget_borrowed(v_as_5438_, v_i_5437_);
if (lean_obj_tag(v_a_5447_) == 0)
{
lean_object* v_ctorName_5460_; lean_object* v_params_5461_; lean_object* v_code_5462_; uint8_t v___x_5463_; lean_object* v___y_5465_; lean_object* v___y_5466_; lean_object* v___y_5479_; uint8_t v___x_5483_; 
v_ctorName_5460_ = lean_ctor_get(v_a_5447_, 0);
v_params_5461_ = lean_ctor_get(v_a_5447_, 1);
v_code_5462_ = lean_ctor_get(v_a_5447_, 2);
v___x_5463_ = 0;
v___x_5483_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5434_, v_ctorName_5460_);
if (v___x_5483_ == 0)
{
lean_object* v_options_5484_; uint8_t v_hasTrace_5485_; 
v_options_5484_ = lean_ctor_get(v___y_5441_, 2);
v_hasTrace_5485_ = lean_ctor_get_uint8(v_options_5484_, sizeof(void*)*1);
if (v_hasTrace_5485_ == 0)
{
v___y_5479_ = v___y_5440_;
goto v___jp_5478_;
}
else
{
lean_object* v_inheritedTraceOptions_5486_; lean_object* v_cls_5487_; lean_object* v___x_5488_; uint8_t v___x_5489_; 
v_inheritedTraceOptions_5486_ = lean_ctor_get(v___y_5441_, 13);
v_cls_5487_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5488_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5486_, v_options_5484_, v___x_5488_);
if (v___x_5489_ == 0)
{
v___y_5479_ = v___y_5440_;
goto v___jp_5478_;
}
else
{
lean_object* v___x_5490_; 
lean_inc(v_discr_5435_);
v___x_5490_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5435_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v___x_5490_, 1);
v___x_5492_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5491_, v___x_5489_);
v___x_5494_ = lean_string_append(v___x_5492_, v___x_5493_);
lean_dec_ref(v___x_5493_);
v___x_5495_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5496_ = lean_string_append(v___x_5494_, v___x_5495_);
lean_inc(v_ctorName_5460_);
v___x_5497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5460_, v___x_5489_);
v___x_5498_ = lean_string_append(v___x_5496_, v___x_5497_);
lean_dec_ref(v___x_5497_);
v___x_5499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5498_);
v___x_5500_ = l_Lean_MessageData_ofFormat(v___x_5499_);
v___x_5501_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5487_, v___x_5500_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
if (lean_obj_tag(v___x_5501_) == 0)
{
lean_dec_ref_known(v___x_5501_, 1);
v___y_5479_ = v___y_5440_;
goto v___jp_5478_;
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5502_ = lean_ctor_get(v___x_5501_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5501_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5501_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5501_);
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
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5510_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5490_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5490_);
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
}
}
else
{
lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; 
v___x_5518_ = lean_unsigned_to_nat(0u);
v___x_5519_ = lean_array_get_size(v_params_5461_);
v___x_5520_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5436_, v_params_5461_, v___x_5518_, v___x_5519_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v___x_5534_; uint8_t v___x_5535_; lean_object* v_fst_5537_; lean_object* v_snd_5538_; lean_object* v___y_5551_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
lean_inc(v_a_5521_);
lean_dec_ref_known(v___x_5520_, 1);
v___x_5534_ = lean_array_get_size(v_a_5521_);
v___x_5535_ = lean_nat_dec_eq(v___x_5534_, v___x_5518_);
if (v___x_5535_ == 0)
{
if (v___x_5483_ == 0)
{
lean_dec(v_a_5521_);
goto v___jp_5522_;
}
else
{
lean_object* v___x_5563_; 
lean_inc_ref(v_code_5462_);
v___x_5563_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5436_, v_code_5462_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
if (lean_obj_tag(v___x_5563_) == 0)
{
lean_object* v_a_5564_; lean_object* v___x_5565_; uint8_t v___x_5566_; 
v_a_5564_ = lean_ctor_get(v___x_5563_, 0);
lean_inc(v_a_5564_);
lean_dec_ref_known(v___x_5563_, 1);
v___x_5565_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5566_ = lean_nat_dec_lt(v___x_5518_, v___x_5534_);
if (v___x_5566_ == 0)
{
lean_dec(v_a_5521_);
v_fst_5537_ = v_a_5564_;
v_snd_5538_ = v___x_5565_;
goto v___jp_5536_;
}
else
{
lean_object* v___x_5567_; uint8_t v___x_5568_; 
lean_inc(v_a_5564_);
v___x_5567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5567_, 0, v_a_5564_);
lean_ctor_set(v___x_5567_, 1, v___x_5565_);
v___x_5568_ = lean_nat_dec_le(v___x_5534_, v___x_5534_);
if (v___x_5568_ == 0)
{
if (v___x_5566_ == 0)
{
lean_dec_ref_known(v___x_5567_, 2);
lean_dec(v_a_5521_);
v_fst_5537_ = v_a_5564_;
v_snd_5538_ = v___x_5565_;
goto v___jp_5536_;
}
else
{
size_t v___x_5569_; size_t v___x_5570_; lean_object* v___x_5571_; 
lean_dec(v_a_5564_);
v___x_5569_ = ((size_t)0ULL);
v___x_5570_ = lean_usize_of_nat(v___x_5534_);
v___x_5571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5521_, v___x_5569_, v___x_5570_, v___x_5567_);
lean_dec(v_a_5521_);
v___y_5551_ = v___x_5571_;
goto v___jp_5550_;
}
}
else
{
size_t v___x_5572_; size_t v___x_5573_; lean_object* v___x_5574_; 
lean_dec(v_a_5564_);
v___x_5572_ = ((size_t)0ULL);
v___x_5573_ = lean_usize_of_nat(v___x_5534_);
v___x_5574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5521_, v___x_5572_, v___x_5573_, v___x_5567_);
lean_dec(v_a_5521_);
v___y_5551_ = v___x_5574_;
goto v___jp_5550_;
}
}
}
else
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
lean_dec(v_a_5521_);
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5575_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5563_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5563_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
}
else
{
lean_dec(v_a_5521_);
goto v___jp_5522_;
}
v___jp_5522_:
{
lean_object* v___x_5523_; 
lean_inc_ref(v_code_5462_);
v___x_5523_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5436_, v_code_5462_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
if (lean_obj_tag(v___x_5523_) == 0)
{
lean_object* v_a_5524_; lean_object* v___x_5525_; 
v_a_5524_ = lean_ctor_get(v___x_5523_, 0);
lean_inc(v_a_5524_);
lean_dec_ref_known(v___x_5523_, 1);
lean_inc_ref(v_a_5447_);
v___x_5525_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5447_, v_a_5524_);
v_a_5449_ = v___x_5525_;
goto v___jp_5448_;
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5526_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v___x_5523_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5523_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
v___jp_5536_:
{
lean_object* v___x_5539_; 
v___x_5539_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5463_, v_fst_5537_, v_snd_5538_, v___x_5535_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
lean_dec_ref(v_snd_5538_);
if (lean_obj_tag(v___x_5539_) == 0)
{
lean_object* v_a_5540_; lean_object* v___x_5541_; 
v_a_5540_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_a_5540_);
lean_dec_ref_known(v___x_5539_, 1);
lean_inc_ref(v_a_5447_);
v___x_5541_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5447_, v_a_5540_);
v_a_5449_ = v___x_5541_;
goto v___jp_5448_;
}
else
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5542_ = lean_ctor_get(v___x_5539_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5544_ = v___x_5539_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5539_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5542_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
v___jp_5550_:
{
if (lean_obj_tag(v___y_5551_) == 0)
{
lean_object* v_a_5552_; lean_object* v_fst_5553_; lean_object* v_snd_5554_; 
v_a_5552_ = lean_ctor_get(v___y_5551_, 0);
lean_inc(v_a_5552_);
lean_dec_ref_known(v___y_5551_, 1);
v_fst_5553_ = lean_ctor_get(v_a_5552_, 0);
lean_inc(v_fst_5553_);
v_snd_5554_ = lean_ctor_get(v_a_5552_, 1);
lean_inc(v_snd_5554_);
lean_dec(v_a_5552_);
v_fst_5537_ = v_fst_5553_;
v_snd_5538_ = v_snd_5554_;
goto v___jp_5536_;
}
else
{
lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5555_ = lean_ctor_get(v___y_5551_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___y_5551_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___y_5551_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___y_5551_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
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
}
else
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5590_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5583_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5585_ = v___x_5520_;
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v___x_5520_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
}
v___jp_5464_:
{
lean_object* v___x_5467_; 
v___x_5467_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5463_, v___y_5466_, v___y_5465_);
lean_dec_ref(v___y_5466_);
if (lean_obj_tag(v___x_5467_) == 0)
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
lean_dec_ref_known(v___x_5467_, 1);
lean_inc_ref(v_resultType_5433_);
v___x_5468_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5468_, 0, v_resultType_5433_);
lean_inc_ref(v_a_5447_);
v___x_5469_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5447_, v___x_5468_);
v_a_5449_ = v___x_5469_;
goto v___jp_5448_;
}
else
{
lean_object* v_a_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5477_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5470_ = lean_ctor_get(v___x_5467_, 0);
v_isSharedCheck_5477_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5477_ == 0)
{
v___x_5472_ = v___x_5467_;
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_a_5470_);
lean_dec(v___x_5467_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5475_; 
if (v_isShared_5473_ == 0)
{
v___x_5475_ = v___x_5472_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5470_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
}
v___jp_5478_:
{
switch(lean_obj_tag(v_a_5447_))
{
case 0:
{
lean_object* v_code_5480_; 
v_code_5480_ = lean_ctor_get(v_a_5447_, 2);
lean_inc_ref(v_code_5480_);
v___y_5465_ = v___y_5479_;
v___y_5466_ = v_code_5480_;
goto v___jp_5464_;
}
case 1:
{
lean_object* v_code_5481_; 
v_code_5481_ = lean_ctor_get(v_a_5447_, 1);
lean_inc_ref(v_code_5481_);
v___y_5465_ = v___y_5479_;
v___y_5466_ = v_code_5481_;
goto v___jp_5464_;
}
default: 
{
lean_object* v_code_5482_; 
v_code_5482_ = lean_ctor_get(v_a_5447_, 0);
lean_inc_ref(v_code_5482_);
v___y_5465_ = v___y_5479_;
v___y_5466_ = v_code_5482_;
goto v___jp_5464_;
}
}
}
}
else
{
lean_object* v_code_5591_; lean_object* v___x_5592_; 
v_code_5591_ = lean_ctor_get(v_a_5447_, 0);
lean_inc_ref(v_code_5591_);
v___x_5592_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5436_, v_code_5591_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5594_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_a_5593_);
lean_dec_ref_known(v___x_5592_, 1);
lean_inc_ref(v_a_5447_);
v___x_5594_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5447_, v_a_5593_);
v_a_5449_ = v___x_5594_;
goto v___jp_5448_;
}
else
{
lean_object* v_a_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5602_; 
lean_dec_ref(v_as_5438_);
lean_dec(v_i_5437_);
lean_dec(v_discr_5435_);
lean_dec_ref(v_resultType_5433_);
v_a_5595_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5597_ = v___x_5592_;
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_a_5595_);
lean_dec(v___x_5592_);
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
v___jp_5448_:
{
size_t v___x_5450_; size_t v___x_5451_; uint8_t v___x_5452_; 
v___x_5450_ = lean_ptr_addr(v_a_5447_);
v___x_5451_ = lean_ptr_addr(v_a_5449_);
v___x_5452_ = lean_usize_dec_eq(v___x_5450_, v___x_5451_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5453_ = lean_unsigned_to_nat(1u);
v___x_5454_ = lean_nat_add(v_i_5437_, v___x_5453_);
v___x_5455_ = lean_array_fset(v_as_5438_, v_i_5437_, v_a_5449_);
lean_dec(v_i_5437_);
v_i_5437_ = v___x_5454_;
v_as_5438_ = v___x_5455_;
goto _start;
}
else
{
lean_object* v___x_5457_; lean_object* v___x_5458_; 
lean_dec_ref(v_a_5449_);
v___x_5457_ = lean_unsigned_to_nat(1u);
v___x_5458_ = lean_nat_add(v_i_5437_, v___x_5457_);
lean_dec(v_i_5437_);
v_i_5437_ = v___x_5458_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5603_, lean_object* v_code_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_){
_start:
{
lean_object* v___y_5611_; lean_object* v___y_5612_; uint8_t v___y_5613_; lean_object* v___y_5618_; lean_object* v___y_5619_; uint8_t v___y_5620_; lean_object* v_decl_5625_; lean_object* v_k_5626_; lean_object* v___y_5627_; lean_object* v___y_5628_; lean_object* v___y_5629_; lean_object* v___y_5630_; 
switch(lean_obj_tag(v_code_5604_))
{
case 0:
{
lean_object* v_decl_5676_; lean_object* v_k_5677_; lean_object* v___x_5678_; 
v_decl_5676_ = lean_ctor_get(v_code_5604_, 0);
v_k_5677_ = lean_ctor_get(v_code_5604_, 1);
lean_inc_ref(v_k_5677_);
v___x_5678_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5603_, v_k_5677_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
if (lean_obj_tag(v___x_5678_) == 0)
{
lean_object* v_a_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5705_; 
v_a_5679_ = lean_ctor_get(v___x_5678_, 0);
v_isSharedCheck_5705_ = !lean_is_exclusive(v___x_5678_);
if (v_isSharedCheck_5705_ == 0)
{
v___x_5681_ = v___x_5678_;
v_isShared_5682_ = v_isSharedCheck_5705_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_a_5679_);
lean_dec(v___x_5678_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5705_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
uint8_t v___y_5684_; size_t v___x_5700_; size_t v___x_5701_; uint8_t v___x_5702_; 
v___x_5700_ = lean_ptr_addr(v_k_5677_);
v___x_5701_ = lean_ptr_addr(v_a_5679_);
v___x_5702_ = lean_usize_dec_eq(v___x_5700_, v___x_5701_);
if (v___x_5702_ == 0)
{
v___y_5684_ = v___x_5702_;
goto v___jp_5683_;
}
else
{
size_t v___x_5703_; uint8_t v___x_5704_; 
v___x_5703_ = lean_ptr_addr(v_decl_5676_);
v___x_5704_ = lean_usize_dec_eq(v___x_5703_, v___x_5703_);
v___y_5684_ = v___x_5704_;
goto v___jp_5683_;
}
v___jp_5683_:
{
if (v___y_5684_ == 0)
{
lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5694_; 
lean_inc_ref(v_decl_5676_);
v_isSharedCheck_5694_ = !lean_is_exclusive(v_code_5604_);
if (v_isSharedCheck_5694_ == 0)
{
lean_object* v_unused_5695_; lean_object* v_unused_5696_; 
v_unused_5695_ = lean_ctor_get(v_code_5604_, 1);
lean_dec(v_unused_5695_);
v_unused_5696_ = lean_ctor_get(v_code_5604_, 0);
lean_dec(v_unused_5696_);
v___x_5686_ = v_code_5604_;
v_isShared_5687_ = v_isSharedCheck_5694_;
goto v_resetjp_5685_;
}
else
{
lean_dec(v_code_5604_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5694_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5689_; 
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 1, v_a_5679_);
v___x_5689_ = v___x_5686_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_decl_5676_);
lean_ctor_set(v_reuseFailAlloc_5693_, 1, v_a_5679_);
v___x_5689_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
lean_object* v___x_5691_; 
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 0, v___x_5689_);
v___x_5691_ = v___x_5681_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5689_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
}
}
else
{
lean_object* v___x_5698_; 
lean_dec(v_a_5679_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 0, v_code_5604_);
v___x_5698_ = v___x_5681_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_code_5604_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
return v___x_5698_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_5604_, 2);
return v___x_5678_;
}
}
case 1:
{
lean_object* v_decl_5706_; lean_object* v_k_5707_; 
v_decl_5706_ = lean_ctor_get(v_code_5604_, 0);
v_k_5707_ = lean_ctor_get(v_code_5604_, 1);
lean_inc_ref(v_k_5707_);
lean_inc_ref(v_decl_5706_);
v_decl_5625_ = v_decl_5706_;
v_k_5626_ = v_k_5707_;
v___y_5627_ = v_a_5605_;
v___y_5628_ = v_a_5606_;
v___y_5629_ = v_a_5607_;
v___y_5630_ = v_a_5608_;
goto v___jp_5624_;
}
case 2:
{
lean_object* v_decl_5708_; lean_object* v_k_5709_; 
v_decl_5708_ = lean_ctor_get(v_code_5604_, 0);
v_k_5709_ = lean_ctor_get(v_code_5604_, 1);
lean_inc_ref(v_k_5709_);
lean_inc_ref(v_decl_5708_);
v_decl_5625_ = v_decl_5708_;
v_k_5626_ = v_k_5709_;
v___y_5627_ = v_a_5605_;
v___y_5628_ = v_a_5606_;
v___y_5629_ = v_a_5607_;
v___y_5630_ = v_a_5608_;
goto v___jp_5624_;
}
case 4:
{
lean_object* v_cases_5710_; lean_object* v_typeName_5711_; lean_object* v_resultType_5712_; lean_object* v_discr_5713_; lean_object* v_alts_5714_; lean_object* v___x_5716_; uint8_t v_isShared_5717_; uint8_t v_isSharedCheck_5755_; 
v_cases_5710_ = lean_ctor_get(v_code_5604_, 0);
lean_inc_ref(v_cases_5710_);
v_typeName_5711_ = lean_ctor_get(v_cases_5710_, 0);
v_resultType_5712_ = lean_ctor_get(v_cases_5710_, 1);
v_discr_5713_ = lean_ctor_get(v_cases_5710_, 2);
v_alts_5714_ = lean_ctor_get(v_cases_5710_, 3);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_cases_5710_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5716_ = v_cases_5710_;
v_isShared_5717_ = v_isSharedCheck_5755_;
goto v_resetjp_5715_;
}
else
{
lean_inc(v_alts_5714_);
lean_inc(v_discr_5713_);
lean_inc(v_resultType_5712_);
lean_inc(v_typeName_5711_);
lean_dec(v_cases_5710_);
v___x_5716_ = lean_box(0);
v_isShared_5717_ = v_isSharedCheck_5755_;
goto v_resetjp_5715_;
}
v_resetjp_5715_:
{
lean_object* v___x_5718_; lean_object* v_discrVal_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v___x_5718_ = lean_box(0);
v_discrVal_5719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5603_, v_discr_5713_, v___x_5718_);
v___x_5720_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5714_);
lean_inc(v_discr_5713_);
lean_inc_ref(v_resultType_5712_);
v___x_5721_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5712_, v_discrVal_5719_, v_discr_5713_, v_assignment_5603_, v___x_5720_, v_alts_5714_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
lean_dec(v_discrVal_5719_);
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v_a_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5746_; 
v_a_5722_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5746_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5746_ == 0)
{
v___x_5724_ = v___x_5721_;
v_isShared_5725_ = v_isSharedCheck_5746_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_a_5722_);
lean_dec(v___x_5721_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5746_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
size_t v___x_5726_; size_t v___x_5727_; uint8_t v___x_5728_; 
v___x_5726_ = lean_ptr_addr(v_alts_5714_);
lean_dec_ref(v_alts_5714_);
v___x_5727_ = lean_ptr_addr(v_a_5722_);
v___x_5728_ = lean_usize_dec_eq(v___x_5726_, v___x_5727_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5730_; uint8_t v_isShared_5731_; uint8_t v_isSharedCheck_5741_; 
v_isSharedCheck_5741_ = !lean_is_exclusive(v_code_5604_);
if (v_isSharedCheck_5741_ == 0)
{
lean_object* v_unused_5742_; 
v_unused_5742_ = lean_ctor_get(v_code_5604_, 0);
lean_dec(v_unused_5742_);
v___x_5730_ = v_code_5604_;
v_isShared_5731_ = v_isSharedCheck_5741_;
goto v_resetjp_5729_;
}
else
{
lean_dec(v_code_5604_);
v___x_5730_ = lean_box(0);
v_isShared_5731_ = v_isSharedCheck_5741_;
goto v_resetjp_5729_;
}
v_resetjp_5729_:
{
lean_object* v___x_5733_; 
if (v_isShared_5717_ == 0)
{
lean_ctor_set(v___x_5716_, 3, v_a_5722_);
v___x_5733_ = v___x_5716_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_typeName_5711_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_resultType_5712_);
lean_ctor_set(v_reuseFailAlloc_5740_, 2, v_discr_5713_);
lean_ctor_set(v_reuseFailAlloc_5740_, 3, v_a_5722_);
v___x_5733_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
lean_object* v___x_5735_; 
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 0, v___x_5733_);
v___x_5735_ = v___x_5730_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5733_);
v___x_5735_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
lean_object* v___x_5737_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 0, v___x_5735_);
v___x_5737_ = v___x_5724_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5738_; 
v_reuseFailAlloc_5738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5738_, 0, v___x_5735_);
v___x_5737_ = v_reuseFailAlloc_5738_;
goto v_reusejp_5736_;
}
v_reusejp_5736_:
{
return v___x_5737_;
}
}
}
}
}
else
{
lean_object* v___x_5744_; 
lean_dec(v_a_5722_);
lean_del_object(v___x_5716_);
lean_dec(v_discr_5713_);
lean_dec_ref(v_resultType_5712_);
lean_dec(v_typeName_5711_);
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 0, v_code_5604_);
v___x_5744_ = v___x_5724_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_code_5604_);
v___x_5744_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
return v___x_5744_;
}
}
}
}
else
{
lean_object* v_a_5747_; lean_object* v___x_5749_; uint8_t v_isShared_5750_; uint8_t v_isSharedCheck_5754_; 
lean_del_object(v___x_5716_);
lean_dec_ref(v_alts_5714_);
lean_dec(v_discr_5713_);
lean_dec_ref(v_resultType_5712_);
lean_dec(v_typeName_5711_);
lean_dec_ref_known(v_code_5604_, 1);
v_a_5747_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5754_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5754_ == 0)
{
v___x_5749_ = v___x_5721_;
v_isShared_5750_ = v_isSharedCheck_5754_;
goto v_resetjp_5748_;
}
else
{
lean_inc(v_a_5747_);
lean_dec(v___x_5721_);
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
default: 
{
lean_object* v___x_5756_; 
v___x_5756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5756_, 0, v_code_5604_);
return v___x_5756_;
}
}
v___jp_5610_:
{
if (v___y_5613_ == 0)
{
lean_object* v___x_5614_; lean_object* v___x_5615_; 
lean_dec_ref(v_code_5604_);
v___x_5614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5614_, 0, v___y_5612_);
lean_ctor_set(v___x_5614_, 1, v___y_5611_);
v___x_5615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5614_);
return v___x_5615_;
}
else
{
lean_object* v___x_5616_; 
lean_dec_ref(v___y_5612_);
lean_dec_ref(v___y_5611_);
v___x_5616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5616_, 0, v_code_5604_);
return v___x_5616_;
}
}
v___jp_5617_:
{
if (v___y_5620_ == 0)
{
lean_object* v___x_5621_; lean_object* v___x_5622_; 
lean_dec_ref(v_code_5604_);
v___x_5621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___y_5619_);
lean_ctor_set(v___x_5621_, 1, v___y_5618_);
v___x_5622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5621_);
return v___x_5622_;
}
else
{
lean_object* v___x_5623_; 
lean_dec_ref(v___y_5619_);
lean_dec_ref(v___y_5618_);
v___x_5623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5623_, 0, v_code_5604_);
return v___x_5623_;
}
}
v___jp_5624_:
{
lean_object* v_params_5631_; lean_object* v_type_5632_; lean_object* v_value_5633_; lean_object* v___x_5634_; 
v_params_5631_ = lean_ctor_get(v_decl_5625_, 2);
lean_inc_ref(v_params_5631_);
v_type_5632_ = lean_ctor_get(v_decl_5625_, 3);
lean_inc_ref(v_type_5632_);
v_value_5633_ = lean_ctor_get(v_decl_5625_, 4);
lean_inc_ref(v_value_5633_);
v___x_5634_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5603_, v_value_5633_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
if (lean_obj_tag(v___x_5634_) == 0)
{
lean_object* v_a_5635_; uint8_t v___x_5636_; lean_object* v___x_5637_; 
v_a_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc(v_a_5635_);
lean_dec_ref_known(v___x_5634_, 1);
v___x_5636_ = 0;
v___x_5637_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5636_, v_decl_5625_, v_type_5632_, v_params_5631_, v_a_5635_, v___y_5628_);
if (lean_obj_tag(v___x_5637_) == 0)
{
lean_object* v_a_5638_; lean_object* v___x_5639_; 
v_a_5638_ = lean_ctor_get(v___x_5637_, 0);
lean_inc(v_a_5638_);
lean_dec_ref_known(v___x_5637_, 1);
v___x_5639_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5603_, v_k_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
if (lean_obj_tag(v___x_5639_) == 0)
{
switch(lean_obj_tag(v_code_5604_))
{
case 1:
{
lean_object* v_a_5640_; lean_object* v_decl_5641_; lean_object* v_k_5642_; size_t v___x_5643_; size_t v___x_5644_; uint8_t v___x_5645_; 
v_a_5640_ = lean_ctor_get(v___x_5639_, 0);
lean_inc(v_a_5640_);
lean_dec_ref_known(v___x_5639_, 1);
v_decl_5641_ = lean_ctor_get(v_code_5604_, 0);
v_k_5642_ = lean_ctor_get(v_code_5604_, 1);
v___x_5643_ = lean_ptr_addr(v_k_5642_);
v___x_5644_ = lean_ptr_addr(v_a_5640_);
v___x_5645_ = lean_usize_dec_eq(v___x_5643_, v___x_5644_);
if (v___x_5645_ == 0)
{
v___y_5611_ = v_a_5640_;
v___y_5612_ = v_a_5638_;
v___y_5613_ = v___x_5645_;
goto v___jp_5610_;
}
else
{
size_t v___x_5646_; size_t v___x_5647_; uint8_t v___x_5648_; 
v___x_5646_ = lean_ptr_addr(v_decl_5641_);
v___x_5647_ = lean_ptr_addr(v_a_5638_);
v___x_5648_ = lean_usize_dec_eq(v___x_5646_, v___x_5647_);
v___y_5611_ = v_a_5640_;
v___y_5612_ = v_a_5638_;
v___y_5613_ = v___x_5648_;
goto v___jp_5610_;
}
}
case 2:
{
lean_object* v_a_5649_; lean_object* v_decl_5650_; lean_object* v_k_5651_; size_t v___x_5652_; size_t v___x_5653_; uint8_t v___x_5654_; 
v_a_5649_ = lean_ctor_get(v___x_5639_, 0);
lean_inc(v_a_5649_);
lean_dec_ref_known(v___x_5639_, 1);
v_decl_5650_ = lean_ctor_get(v_code_5604_, 0);
v_k_5651_ = lean_ctor_get(v_code_5604_, 1);
v___x_5652_ = lean_ptr_addr(v_k_5651_);
v___x_5653_ = lean_ptr_addr(v_a_5649_);
v___x_5654_ = lean_usize_dec_eq(v___x_5652_, v___x_5653_);
if (v___x_5654_ == 0)
{
v___y_5618_ = v_a_5649_;
v___y_5619_ = v_a_5638_;
v___y_5620_ = v___x_5654_;
goto v___jp_5617_;
}
else
{
size_t v___x_5655_; size_t v___x_5656_; uint8_t v___x_5657_; 
v___x_5655_ = lean_ptr_addr(v_decl_5650_);
v___x_5656_ = lean_ptr_addr(v_a_5638_);
v___x_5657_ = lean_usize_dec_eq(v___x_5655_, v___x_5656_);
v___y_5618_ = v_a_5649_;
v___y_5619_ = v_a_5638_;
v___y_5620_ = v___x_5657_;
goto v___jp_5617_;
}
}
default: 
{
lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5666_; 
lean_dec(v_a_5638_);
lean_dec_ref(v_code_5604_);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5666_ == 0)
{
lean_object* v_unused_5667_; 
v_unused_5667_ = lean_ctor_get(v___x_5639_, 0);
lean_dec(v_unused_5667_);
v___x_5659_ = v___x_5639_;
v_isShared_5660_ = v_isSharedCheck_5666_;
goto v_resetjp_5658_;
}
else
{
lean_dec(v___x_5639_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5666_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5664_; 
v___x_5661_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5662_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5661_);
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v___x_5662_);
v___x_5664_ = v___x_5659_;
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
lean_dec(v_a_5638_);
lean_dec_ref(v_code_5604_);
return v___x_5639_;
}
}
else
{
lean_object* v_a_5668_; lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5675_; 
lean_dec_ref(v_k_5626_);
lean_dec_ref(v_code_5604_);
v_a_5668_ = lean_ctor_get(v___x_5637_, 0);
v_isSharedCheck_5675_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5675_ == 0)
{
v___x_5670_ = v___x_5637_;
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
else
{
lean_inc(v_a_5668_);
lean_dec(v___x_5637_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v___x_5673_; 
if (v_isShared_5671_ == 0)
{
v___x_5673_ = v___x_5670_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
v___x_5673_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
return v___x_5673_;
}
}
}
}
else
{
lean_dec_ref(v_type_5632_);
lean_dec_ref(v_params_5631_);
lean_dec_ref(v_k_5626_);
lean_dec_ref(v_decl_5625_);
lean_dec_ref(v_code_5604_);
return v___x_5634_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5757_, lean_object* v_code_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5757_, v_code_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_);
lean_dec(v_a_5762_);
lean_dec_ref(v_a_5761_);
lean_dec(v_a_5760_);
lean_dec_ref(v_a_5759_);
lean_dec_ref(v_assignment_5757_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5765_, lean_object* v_discrVal_5766_, lean_object* v_discr_5767_, lean_object* v_assignment_5768_, lean_object* v_i_5769_, lean_object* v_as_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_){
_start:
{
lean_object* v_res_5776_; 
v_res_5776_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5765_, v_discrVal_5766_, v_discr_5767_, v_assignment_5768_, v_i_5769_, v_as_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_);
lean_dec(v___y_5774_);
lean_dec_ref(v___y_5773_);
lean_dec(v___y_5772_);
lean_dec_ref(v___y_5771_);
lean_dec_ref(v_assignment_5768_);
lean_dec(v_discrVal_5766_);
return v_res_5776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5777_, lean_object* v_m_5778_, lean_object* v_a_5779_){
_start:
{
lean_object* v___x_5780_; 
v___x_5780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5778_, v_a_5779_);
return v___x_5780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5781_, lean_object* v_m_5782_, lean_object* v_a_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5781_, v_m_5782_, v_a_5783_);
lean_dec(v_a_5783_);
lean_dec_ref(v_m_5782_);
return v_res_5784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5785_, size_t v_i_5786_, size_t v_stop_5787_, lean_object* v_b_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_){
_start:
{
lean_object* v___x_5794_; 
v___x_5794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5785_, v_i_5786_, v_stop_5787_, v_b_5788_);
return v___x_5794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5795_, lean_object* v_i_5796_, lean_object* v_stop_5797_, lean_object* v_b_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_){
_start:
{
size_t v_i_boxed_5804_; size_t v_stop_boxed_5805_; lean_object* v_res_5806_; 
v_i_boxed_5804_ = lean_unbox_usize(v_i_5796_);
lean_dec(v_i_5796_);
v_stop_boxed_5805_ = lean_unbox_usize(v_stop_5797_);
lean_dec(v_stop_5797_);
v_res_5806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5795_, v_i_boxed_5804_, v_stop_boxed_5805_, v_b_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
lean_dec_ref(v_as_5795_);
return v_res_5806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5807_, lean_object* v_a_5808_, lean_object* v_x_5809_){
_start:
{
lean_object* v___x_5810_; 
v___x_5810_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5808_, v_x_5809_);
return v___x_5810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5811_, lean_object* v_a_5812_, lean_object* v_x_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5811_, v_a_5812_, v_x_5813_);
lean_dec(v_x_5813_);
lean_dec(v_a_5812_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5815_, lean_object* v_v_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_){
_start:
{
if (lean_obj_tag(v_v_5816_) == 0)
{
lean_object* v_code_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5846_; 
v_code_5822_ = lean_ctor_get(v_v_5816_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v_v_5816_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5824_ = v_v_5816_;
v_isShared_5825_ = v_isSharedCheck_5846_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_code_5822_);
lean_dec(v_v_5816_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5846_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5826_; 
lean_inc(v___y_5820_);
lean_inc_ref(v___y_5819_);
lean_inc(v___y_5818_);
lean_inc_ref(v___y_5817_);
v___x_5826_ = lean_apply_6(v_f_5815_, v_code_5822_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, lean_box(0));
if (lean_obj_tag(v___x_5826_) == 0)
{
lean_object* v_a_5827_; lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5837_; 
v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5837_ == 0)
{
v___x_5829_ = v___x_5826_;
v_isShared_5830_ = v_isSharedCheck_5837_;
goto v_resetjp_5828_;
}
else
{
lean_inc(v_a_5827_);
lean_dec(v___x_5826_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5837_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
lean_object* v___x_5832_; 
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 0, v_a_5827_);
v___x_5832_ = v___x_5824_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5827_);
v___x_5832_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
lean_object* v___x_5834_; 
if (v_isShared_5830_ == 0)
{
lean_ctor_set(v___x_5829_, 0, v___x_5832_);
v___x_5834_ = v___x_5829_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v___x_5832_);
v___x_5834_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
return v___x_5834_;
}
}
}
}
else
{
lean_object* v_a_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5845_; 
lean_del_object(v___x_5824_);
v_a_5838_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5840_ = v___x_5826_;
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_a_5838_);
lean_dec(v___x_5826_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5843_; 
if (v_isShared_5841_ == 0)
{
v___x_5843_ = v___x_5840_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_a_5838_);
v___x_5843_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
return v___x_5843_;
}
}
}
}
}
else
{
lean_object* v___x_5847_; 
lean_dec_ref(v_f_5815_);
v___x_5847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5847_, 0, v_v_5816_);
return v___x_5847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5848_, lean_object* v_v_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5848_, v_v_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
lean_dec(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5856_, lean_object* v_f_5857_, lean_object* v_v_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_){
_start:
{
lean_object* v___x_5864_; 
v___x_5864_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5857_, v_v_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5865_, lean_object* v_f_5866_, lean_object* v_v_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_){
_start:
{
uint8_t v_pu_boxed_5873_; lean_object* v_res_5874_; 
v_pu_boxed_5873_ = lean_unbox(v_pu_5865_);
v_res_5874_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5873_, v_f_5866_, v_v_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_);
lean_dec(v___y_5871_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5869_);
lean_dec_ref(v___y_5868_);
return v_res_5874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5875_, lean_object* v_x_5876_){
_start:
{
if (lean_obj_tag(v_x_5876_) == 0)
{
return v_x_5875_;
}
else
{
lean_object* v_key_5877_; lean_object* v_value_5878_; lean_object* v_tail_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v_key_5877_ = lean_ctor_get(v_x_5876_, 0);
v_value_5878_ = lean_ctor_get(v_x_5876_, 1);
v_tail_5879_ = lean_ctor_get(v_x_5876_, 2);
lean_inc(v_value_5878_);
lean_inc(v_key_5877_);
v___x_5880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5880_, 0, v_key_5877_);
lean_ctor_set(v___x_5880_, 1, v_value_5878_);
v___x_5881_ = lean_array_push(v_x_5875_, v___x_5880_);
v_x_5875_ = v___x_5881_;
v_x_5876_ = v_tail_5879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5883_, lean_object* v_x_5884_){
_start:
{
lean_object* v_res_5885_; 
v_res_5885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5883_, v_x_5884_);
lean_dec(v_x_5884_);
return v_res_5885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5886_, size_t v_i_5887_, size_t v_stop_5888_, lean_object* v_b_5889_){
_start:
{
uint8_t v___x_5890_; 
v___x_5890_ = lean_usize_dec_eq(v_i_5887_, v_stop_5888_);
if (v___x_5890_ == 0)
{
lean_object* v___x_5891_; lean_object* v___x_5892_; size_t v___x_5893_; size_t v___x_5894_; 
v___x_5891_ = lean_array_uget_borrowed(v_as_5886_, v_i_5887_);
v___x_5892_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5889_, v___x_5891_);
v___x_5893_ = ((size_t)1ULL);
v___x_5894_ = lean_usize_add(v_i_5887_, v___x_5893_);
v_i_5887_ = v___x_5894_;
v_b_5889_ = v___x_5892_;
goto _start;
}
else
{
return v_b_5889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5896_, lean_object* v_i_5897_, lean_object* v_stop_5898_, lean_object* v_b_5899_){
_start:
{
size_t v_i_boxed_5900_; size_t v_stop_boxed_5901_; lean_object* v_res_5902_; 
v_i_boxed_5900_ = lean_unbox_usize(v_i_5897_);
lean_dec(v_i_5897_);
v_stop_boxed_5901_ = lean_unbox_usize(v_stop_5898_);
lean_dec(v_stop_5898_);
v_res_5902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5896_, v_i_boxed_5900_, v_stop_boxed_5901_, v_b_5899_);
lean_dec_ref(v_as_5896_);
return v_res_5902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5903_, size_t v_sz_5904_, size_t v_i_5905_, lean_object* v_bs_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_){
_start:
{
uint8_t v___x_5912_; 
v___x_5912_ = lean_usize_dec_lt(v_i_5905_, v_sz_5904_);
if (v___x_5912_ == 0)
{
lean_object* v___x_5913_; 
v___x_5913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5913_, 0, v_bs_5906_);
return v___x_5913_;
}
else
{
lean_object* v_v_5914_; lean_object* v_fst_5915_; lean_object* v_snd_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5940_; 
v_v_5914_ = lean_array_uget(v_bs_5906_, v_i_5905_);
v_fst_5915_ = lean_ctor_get(v_v_5914_, 0);
v_snd_5916_ = lean_ctor_get(v_v_5914_, 1);
v_isSharedCheck_5940_ = !lean_is_exclusive(v_v_5914_);
if (v_isSharedCheck_5940_ == 0)
{
v___x_5918_ = v_v_5914_;
v_isShared_5919_ = v_isSharedCheck_5940_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_snd_5916_);
lean_inc(v_fst_5915_);
lean_dec(v_v_5914_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5940_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5920_; 
v___x_5920_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5915_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
if (lean_obj_tag(v___x_5920_) == 0)
{
lean_object* v_a_5921_; lean_object* v___x_5922_; lean_object* v_bs_x27_5923_; lean_object* v___x_5924_; lean_object* v___x_5926_; 
v_a_5921_ = lean_ctor_get(v___x_5920_, 0);
lean_inc(v_a_5921_);
lean_dec_ref_known(v___x_5920_, 1);
v___x_5922_ = lean_unsigned_to_nat(0u);
v_bs_x27_5923_ = lean_array_uset(v_bs_5906_, v_i_5905_, v___x_5922_);
v___x_5924_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5921_, v_a_5903_);
if (v_isShared_5919_ == 0)
{
lean_ctor_set(v___x_5918_, 0, v___x_5924_);
v___x_5926_ = v___x_5918_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_snd_5916_);
v___x_5926_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
size_t v___x_5927_; size_t v___x_5928_; lean_object* v___x_5929_; 
v___x_5927_ = ((size_t)1ULL);
v___x_5928_ = lean_usize_add(v_i_5905_, v___x_5927_);
v___x_5929_ = lean_array_uset(v_bs_x27_5923_, v_i_5905_, v___x_5926_);
v_i_5905_ = v___x_5928_;
v_bs_5906_ = v___x_5929_;
goto _start;
}
}
else
{
lean_object* v_a_5932_; lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5939_; 
lean_del_object(v___x_5918_);
lean_dec(v_snd_5916_);
lean_dec_ref(v_bs_5906_);
v_a_5932_ = lean_ctor_get(v___x_5920_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v___x_5920_);
if (v_isSharedCheck_5939_ == 0)
{
v___x_5934_ = v___x_5920_;
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
else
{
lean_inc(v_a_5932_);
lean_dec(v___x_5920_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v___x_5937_; 
if (v_isShared_5935_ == 0)
{
v___x_5937_ = v___x_5934_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_a_5932_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5941_, lean_object* v_sz_5942_, lean_object* v_i_5943_, lean_object* v_bs_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_){
_start:
{
uint8_t v_a_2702__boxed_5950_; size_t v_sz_boxed_5951_; size_t v_i_boxed_5952_; lean_object* v_res_5953_; 
v_a_2702__boxed_5950_ = lean_unbox(v_a_5941_);
v_sz_boxed_5951_ = lean_unbox_usize(v_sz_5942_);
lean_dec(v_sz_5942_);
v_i_boxed_5952_ = lean_unbox_usize(v_i_5943_);
lean_dec(v_i_5943_);
v_res_5953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2702__boxed_5950_, v_sz_boxed_5951_, v_i_boxed_5952_, v_bs_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
lean_dec(v___y_5946_);
lean_dec_ref(v___y_5945_);
return v_res_5953_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5954_){
_start:
{
lean_object* v_fst_5955_; lean_object* v_snd_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5979_; 
v_fst_5955_ = lean_ctor_get(v_x_5954_, 0);
v_snd_5956_ = lean_ctor_get(v_x_5954_, 1);
v_isSharedCheck_5979_ = !lean_is_exclusive(v_x_5954_);
if (v_isSharedCheck_5979_ == 0)
{
v___x_5958_ = v_x_5954_;
v_isShared_5959_ = v_isSharedCheck_5979_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_snd_5956_);
lean_inc(v_fst_5955_);
lean_dec(v_x_5954_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5979_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5964_; 
v___x_5960_ = l_String_quote(v_fst_5955_);
v___x_5961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
v___x_5962_ = lean_box(0);
if (v_isShared_5959_ == 0)
{
lean_ctor_set_tag(v___x_5958_, 1);
lean_ctor_set(v___x_5958_, 1, v___x_5962_);
lean_ctor_set(v___x_5958_, 0, v___x_5961_);
v___x_5964_ = v___x_5958_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v___x_5961_);
lean_ctor_set(v_reuseFailAlloc_5978_, 1, v___x_5962_);
v___x_5964_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; uint8_t v___x_5976_; lean_object* v___x_5977_; 
v___x_5965_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5956_);
v___x_5966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
lean_ctor_set(v___x_5966_, 1, v___x_5964_);
v___x_5967_ = l_List_reverse___redArg(v___x_5966_);
v___x_5968_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5969_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5967_, v___x_5968_);
v___x_5970_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5971_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5971_);
lean_ctor_set(v___x_5972_, 1, v___x_5969_);
v___x_5973_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5972_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5970_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = 0;
v___x_5977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5977_, 0, v___x_5975_);
lean_ctor_set_uint8(v___x_5977_, sizeof(void*)*1, v___x_5976_);
return v___x_5977_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5980_, lean_object* v_x_5981_, lean_object* v_x_5982_){
_start:
{
if (lean_obj_tag(v_x_5982_) == 0)
{
lean_dec(v_x_5980_);
return v_x_5981_;
}
else
{
lean_object* v_head_5983_; lean_object* v_tail_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5994_; 
v_head_5983_ = lean_ctor_get(v_x_5982_, 0);
v_tail_5984_ = lean_ctor_get(v_x_5982_, 1);
v_isSharedCheck_5994_ = !lean_is_exclusive(v_x_5982_);
if (v_isSharedCheck_5994_ == 0)
{
v___x_5986_ = v_x_5982_;
v_isShared_5987_ = v_isSharedCheck_5994_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_tail_5984_);
lean_inc(v_head_5983_);
lean_dec(v_x_5982_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5994_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5989_; 
lean_inc(v_x_5980_);
if (v_isShared_5987_ == 0)
{
lean_ctor_set_tag(v___x_5986_, 5);
lean_ctor_set(v___x_5986_, 1, v_x_5980_);
lean_ctor_set(v___x_5986_, 0, v_x_5981_);
v___x_5989_ = v___x_5986_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_x_5981_);
lean_ctor_set(v_reuseFailAlloc_5993_, 1, v_x_5980_);
v___x_5989_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
lean_object* v___x_5990_; lean_object* v___x_5991_; 
v___x_5990_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5983_);
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v_x_5981_ = v___x_5991_;
v_x_5982_ = v_tail_5984_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5995_, lean_object* v_x_5996_, lean_object* v_x_5997_){
_start:
{
if (lean_obj_tag(v_x_5997_) == 0)
{
lean_dec(v_x_5995_);
return v_x_5996_;
}
else
{
lean_object* v_head_5998_; lean_object* v_tail_5999_; lean_object* v___x_6001_; uint8_t v_isShared_6002_; uint8_t v_isSharedCheck_6009_; 
v_head_5998_ = lean_ctor_get(v_x_5997_, 0);
v_tail_5999_ = lean_ctor_get(v_x_5997_, 1);
v_isSharedCheck_6009_ = !lean_is_exclusive(v_x_5997_);
if (v_isSharedCheck_6009_ == 0)
{
v___x_6001_ = v_x_5997_;
v_isShared_6002_ = v_isSharedCheck_6009_;
goto v_resetjp_6000_;
}
else
{
lean_inc(v_tail_5999_);
lean_inc(v_head_5998_);
lean_dec(v_x_5997_);
v___x_6001_ = lean_box(0);
v_isShared_6002_ = v_isSharedCheck_6009_;
goto v_resetjp_6000_;
}
v_resetjp_6000_:
{
lean_object* v___x_6004_; 
lean_inc(v_x_5995_);
if (v_isShared_6002_ == 0)
{
lean_ctor_set_tag(v___x_6001_, 5);
lean_ctor_set(v___x_6001_, 1, v_x_5995_);
lean_ctor_set(v___x_6001_, 0, v_x_5996_);
v___x_6004_ = v___x_6001_;
goto v_reusejp_6003_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_x_5996_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v_x_5995_);
v___x_6004_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6003_;
}
v_reusejp_6003_:
{
lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6005_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5998_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6004_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5995_, v___x_6006_, v_tail_5999_);
return v___x_6007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_6010_, lean_object* v_x_6011_){
_start:
{
if (lean_obj_tag(v_x_6010_) == 0)
{
lean_object* v___x_6012_; 
lean_dec(v_x_6011_);
v___x_6012_ = lean_box(0);
return v___x_6012_;
}
else
{
lean_object* v_tail_6013_; 
v_tail_6013_ = lean_ctor_get(v_x_6010_, 1);
if (lean_obj_tag(v_tail_6013_) == 0)
{
lean_object* v_head_6014_; lean_object* v___x_6015_; 
lean_dec(v_x_6011_);
v_head_6014_ = lean_ctor_get(v_x_6010_, 0);
lean_inc(v_head_6014_);
lean_dec_ref_known(v_x_6010_, 2);
v___x_6015_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_6014_);
return v___x_6015_;
}
else
{
lean_object* v_head_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; 
lean_inc(v_tail_6013_);
v_head_6016_ = lean_ctor_get(v_x_6010_, 0);
lean_inc(v_head_6016_);
lean_dec_ref_known(v_x_6010_, 2);
v___x_6017_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_6016_);
v___x_6018_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_6011_, v___x_6017_, v_tail_6013_);
return v___x_6018_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_6020_; lean_object* v___x_6021_; 
v___x_6020_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_6021_ = lean_string_length(v___x_6020_);
return v___x_6021_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6022_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_6023_ = lean_nat_to_int(v___x_6022_);
return v___x_6023_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_6029_){
_start:
{
lean_object* v___x_6030_; lean_object* v___x_6031_; uint8_t v___x_6032_; 
v___x_6030_ = lean_array_get_size(v_xs_6029_);
v___x_6031_ = lean_unsigned_to_nat(0u);
v___x_6032_ = lean_nat_dec_eq(v___x_6030_, v___x_6031_);
if (v___x_6032_ == 0)
{
lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; 
v___x_6033_ = lean_array_to_list(v_xs_6029_);
v___x_6034_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_6035_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_6033_, v___x_6034_);
v___x_6036_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_6037_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set(v___x_6038_, 1, v___x_6035_);
v___x_6039_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_6040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6038_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6036_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = l_Std_Format_fill(v___x_6041_);
return v___x_6042_;
}
else
{
lean_object* v___x_6043_; 
lean_dec_ref(v_xs_6029_);
v___x_6043_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_6043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_6046_, lean_object* v_decl_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_){
_start:
{
lean_object* v___y_6054_; lean_object* v___y_6055_; lean_object* v___y_6056_; lean_object* v___y_6057_; lean_object* v_options_6087_; uint8_t v_hasTrace_6088_; 
v_options_6087_ = lean_ctor_get(v_a_6050_, 2);
v_hasTrace_6088_ = lean_ctor_get_uint8(v_options_6087_, sizeof(void*)*1);
if (v_hasTrace_6088_ == 0)
{
v___y_6054_ = v_a_6048_;
v___y_6055_ = v_a_6049_;
v___y_6056_ = v_a_6050_;
v___y_6057_ = v_a_6051_;
goto v___jp_6053_;
}
else
{
lean_object* v_inheritedTraceOptions_6089_; lean_object* v_cls_6090_; uint8_t v___y_6092_; lean_object* v___y_6093_; lean_object* v___x_6129_; uint8_t v___x_6130_; 
v_inheritedTraceOptions_6089_ = lean_ctor_get(v_a_6050_, 13);
v_cls_6090_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6129_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6089_, v_options_6087_, v___x_6129_);
if (v___x_6130_ == 0)
{
v___y_6054_ = v_a_6048_;
v___y_6055_ = v_a_6049_;
v___y_6056_ = v_a_6050_;
v___y_6057_ = v_a_6051_;
goto v___jp_6053_;
}
else
{
lean_object* v_size_6131_; lean_object* v_buckets_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; uint8_t v___x_6136_; 
v_size_6131_ = lean_ctor_get(v_assignment_6046_, 0);
v_buckets_6132_ = lean_ctor_get(v_assignment_6046_, 1);
v___x_6133_ = lean_mk_empty_array_with_capacity(v_size_6131_);
v___x_6134_ = lean_unsigned_to_nat(0u);
v___x_6135_ = lean_array_get_size(v_buckets_6132_);
v___x_6136_ = lean_nat_dec_lt(v___x_6134_, v___x_6135_);
if (v___x_6136_ == 0)
{
v___y_6092_ = v___x_6130_;
v___y_6093_ = v___x_6133_;
goto v___jp_6091_;
}
else
{
uint8_t v___x_6137_; 
v___x_6137_ = lean_nat_dec_le(v___x_6135_, v___x_6135_);
if (v___x_6137_ == 0)
{
if (v___x_6136_ == 0)
{
v___y_6092_ = v___x_6130_;
v___y_6093_ = v___x_6133_;
goto v___jp_6091_;
}
else
{
size_t v___x_6138_; size_t v___x_6139_; lean_object* v___x_6140_; 
v___x_6138_ = ((size_t)0ULL);
v___x_6139_ = lean_usize_of_nat(v___x_6135_);
v___x_6140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6132_, v___x_6138_, v___x_6139_, v___x_6133_);
v___y_6092_ = v___x_6130_;
v___y_6093_ = v___x_6140_;
goto v___jp_6091_;
}
}
else
{
size_t v___x_6141_; size_t v___x_6142_; lean_object* v___x_6143_; 
v___x_6141_ = ((size_t)0ULL);
v___x_6142_ = lean_usize_of_nat(v___x_6135_);
v___x_6143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6132_, v___x_6141_, v___x_6142_, v___x_6133_);
v___y_6092_ = v___x_6130_;
v___y_6093_ = v___x_6143_;
goto v___jp_6091_;
}
}
}
v___jp_6091_:
{
size_t v_sz_6094_; size_t v___x_6095_; lean_object* v___x_6096_; 
v_sz_6094_ = lean_array_size(v___y_6093_);
v___x_6095_ = ((size_t)0ULL);
v___x_6096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6092_, v_sz_6094_, v___x_6095_, v___y_6093_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_);
if (lean_obj_tag(v___x_6096_) == 0)
{
lean_object* v_toSignature_6097_; lean_object* v_a_6098_; lean_object* v_name_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; 
v_toSignature_6097_ = lean_ctor_get(v_decl_6047_, 0);
v_a_6098_ = lean_ctor_get(v___x_6096_, 0);
lean_inc(v_a_6098_);
lean_dec_ref_known(v___x_6096_, 1);
v_name_6099_ = lean_ctor_get(v_toSignature_6097_, 0);
v___x_6100_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6099_);
v___x_6101_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6099_, v___y_6092_);
v___x_6102_ = lean_string_append(v___x_6100_, v___x_6101_);
lean_dec_ref(v___x_6101_);
v___x_6103_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6104_ = lean_string_append(v___x_6102_, v___x_6103_);
v___x_6105_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6098_);
v___x_6106_ = l_Std_Format_defWidth;
v___x_6107_ = lean_unsigned_to_nat(0u);
v___x_6108_ = l_Std_Format_pretty(v___x_6105_, v___x_6106_, v___x_6107_, v___x_6107_);
v___x_6109_ = lean_string_append(v___x_6104_, v___x_6108_);
lean_dec_ref(v___x_6108_);
v___x_6110_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6109_);
v___x_6111_ = l_Lean_MessageData_ofFormat(v___x_6110_);
v___x_6112_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_6090_, v___x_6111_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_);
if (lean_obj_tag(v___x_6112_) == 0)
{
lean_dec_ref_known(v___x_6112_, 1);
v___y_6054_ = v_a_6048_;
v___y_6055_ = v_a_6049_;
v___y_6056_ = v_a_6050_;
v___y_6057_ = v_a_6051_;
goto v___jp_6053_;
}
else
{
lean_object* v_a_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6120_; 
lean_dec_ref(v_decl_6047_);
lean_dec_ref(v_assignment_6046_);
v_a_6113_ = lean_ctor_get(v___x_6112_, 0);
v_isSharedCheck_6120_ = !lean_is_exclusive(v___x_6112_);
if (v_isSharedCheck_6120_ == 0)
{
v___x_6115_ = v___x_6112_;
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_a_6113_);
lean_dec(v___x_6112_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6118_; 
if (v_isShared_6116_ == 0)
{
v___x_6118_ = v___x_6115_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6119_; 
v_reuseFailAlloc_6119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_a_6113_);
v___x_6118_ = v_reuseFailAlloc_6119_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
return v___x_6118_;
}
}
}
}
else
{
lean_object* v_a_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6128_; 
lean_dec_ref(v_decl_6047_);
lean_dec_ref(v_assignment_6046_);
v_a_6121_ = lean_ctor_get(v___x_6096_, 0);
v_isSharedCheck_6128_ = !lean_is_exclusive(v___x_6096_);
if (v_isSharedCheck_6128_ == 0)
{
v___x_6123_ = v___x_6096_;
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
else
{
lean_inc(v_a_6121_);
lean_dec(v___x_6096_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
lean_object* v___x_6126_; 
if (v_isShared_6124_ == 0)
{
v___x_6126_ = v___x_6123_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
v___x_6126_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
return v___x_6126_;
}
}
}
}
}
v___jp_6053_:
{
lean_object* v_toSignature_6058_; lean_object* v_value_6059_; uint8_t v_recursive_6060_; lean_object* v_inlineAttr_x3f_6061_; lean_object* v___x_6063_; uint8_t v_isShared_6064_; uint8_t v_isSharedCheck_6086_; 
v_toSignature_6058_ = lean_ctor_get(v_decl_6047_, 0);
v_value_6059_ = lean_ctor_get(v_decl_6047_, 1);
v_recursive_6060_ = lean_ctor_get_uint8(v_decl_6047_, sizeof(void*)*3);
v_inlineAttr_x3f_6061_ = lean_ctor_get(v_decl_6047_, 2);
v_isSharedCheck_6086_ = !lean_is_exclusive(v_decl_6047_);
if (v_isSharedCheck_6086_ == 0)
{
v___x_6063_ = v_decl_6047_;
v_isShared_6064_ = v_isSharedCheck_6086_;
goto v_resetjp_6062_;
}
else
{
lean_inc(v_inlineAttr_x3f_6061_);
lean_inc(v_value_6059_);
lean_inc(v_toSignature_6058_);
lean_dec(v_decl_6047_);
v___x_6063_ = lean_box(0);
v_isShared_6064_ = v_isSharedCheck_6086_;
goto v_resetjp_6062_;
}
v_resetjp_6062_:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; 
v___x_6065_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_6065_, 0, v_assignment_6046_);
v___x_6066_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_6065_, v_value_6059_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_);
if (lean_obj_tag(v___x_6066_) == 0)
{
lean_object* v_a_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6077_; 
v_a_6067_ = lean_ctor_get(v___x_6066_, 0);
v_isSharedCheck_6077_ = !lean_is_exclusive(v___x_6066_);
if (v_isSharedCheck_6077_ == 0)
{
v___x_6069_ = v___x_6066_;
v_isShared_6070_ = v_isSharedCheck_6077_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_a_6067_);
lean_dec(v___x_6066_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6077_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6072_; 
if (v_isShared_6064_ == 0)
{
lean_ctor_set(v___x_6063_, 1, v_a_6067_);
v___x_6072_ = v___x_6063_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v_toSignature_6058_);
lean_ctor_set(v_reuseFailAlloc_6076_, 1, v_a_6067_);
lean_ctor_set(v_reuseFailAlloc_6076_, 2, v_inlineAttr_x3f_6061_);
lean_ctor_set_uint8(v_reuseFailAlloc_6076_, sizeof(void*)*3, v_recursive_6060_);
v___x_6072_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
lean_object* v___x_6074_; 
if (v_isShared_6070_ == 0)
{
lean_ctor_set(v___x_6069_, 0, v___x_6072_);
v___x_6074_ = v___x_6069_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v___x_6072_);
v___x_6074_ = v_reuseFailAlloc_6075_;
goto v_reusejp_6073_;
}
v_reusejp_6073_:
{
return v___x_6074_;
}
}
}
}
else
{
lean_object* v_a_6078_; lean_object* v___x_6080_; uint8_t v_isShared_6081_; uint8_t v_isSharedCheck_6085_; 
lean_del_object(v___x_6063_);
lean_dec(v_inlineAttr_x3f_6061_);
lean_dec_ref(v_toSignature_6058_);
v_a_6078_ = lean_ctor_get(v___x_6066_, 0);
v_isSharedCheck_6085_ = !lean_is_exclusive(v___x_6066_);
if (v_isSharedCheck_6085_ == 0)
{
v___x_6080_ = v___x_6066_;
v_isShared_6081_ = v_isSharedCheck_6085_;
goto v_resetjp_6079_;
}
else
{
lean_inc(v_a_6078_);
lean_dec(v___x_6066_);
v___x_6080_ = lean_box(0);
v_isShared_6081_ = v_isSharedCheck_6085_;
goto v_resetjp_6079_;
}
v_resetjp_6079_:
{
lean_object* v___x_6083_; 
if (v_isShared_6081_ == 0)
{
v___x_6083_ = v___x_6080_;
goto v_reusejp_6082_;
}
else
{
lean_object* v_reuseFailAlloc_6084_; 
v_reuseFailAlloc_6084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6084_, 0, v_a_6078_);
v___x_6083_ = v_reuseFailAlloc_6084_;
goto v_reusejp_6082_;
}
v_reusejp_6082_:
{
return v___x_6083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6144_, lean_object* v_decl_6145_, lean_object* v_a_6146_, lean_object* v_a_6147_, lean_object* v_a_6148_, lean_object* v_a_6149_, lean_object* v_a_6150_){
_start:
{
lean_object* v_res_6151_; 
v_res_6151_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6144_, v_decl_6145_, v_a_6146_, v_a_6147_, v_a_6148_, v_a_6149_);
lean_dec(v_a_6149_);
lean_dec_ref(v_a_6148_);
lean_dec(v_a_6147_);
lean_dec_ref(v_a_6146_);
return v_res_6151_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6152_, lean_object* v_x_6153_){
_start:
{
lean_object* v___x_6154_; 
v___x_6154_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6152_);
return v___x_6154_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6155_, lean_object* v_x_6156_){
_start:
{
lean_object* v_res_6157_; 
v_res_6157_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6155_, v_x_6156_);
lean_dec(v_x_6156_);
return v_res_6157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6158_, size_t v_i_6159_, lean_object* v_bs_6160_){
_start:
{
uint8_t v___x_6161_; 
v___x_6161_ = lean_usize_dec_lt(v_i_6159_, v_sz_6158_);
if (v___x_6161_ == 0)
{
return v_bs_6160_;
}
else
{
lean_object* v_v_6162_; lean_object* v_toSignature_6163_; lean_object* v_name_6164_; lean_object* v___x_6165_; lean_object* v_bs_x27_6166_; size_t v___x_6167_; size_t v___x_6168_; lean_object* v___x_6169_; 
v_v_6162_ = lean_array_uget_borrowed(v_bs_6160_, v_i_6159_);
v_toSignature_6163_ = lean_ctor_get(v_v_6162_, 0);
v_name_6164_ = lean_ctor_get(v_toSignature_6163_, 0);
lean_inc(v_name_6164_);
v___x_6165_ = lean_unsigned_to_nat(0u);
v_bs_x27_6166_ = lean_array_uset(v_bs_6160_, v_i_6159_, v___x_6165_);
v___x_6167_ = ((size_t)1ULL);
v___x_6168_ = lean_usize_add(v_i_6159_, v___x_6167_);
v___x_6169_ = lean_array_uset(v_bs_x27_6166_, v_i_6159_, v_name_6164_);
v_i_6159_ = v___x_6168_;
v_bs_6160_ = v___x_6169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6171_, lean_object* v_i_6172_, lean_object* v_bs_6173_){
_start:
{
size_t v_sz_boxed_6174_; size_t v_i_boxed_6175_; lean_object* v_res_6176_; 
v_sz_boxed_6174_ = lean_unbox_usize(v_sz_6171_);
lean_dec(v_sz_6171_);
v_i_boxed_6175_ = lean_unbox_usize(v_i_6172_);
lean_dec(v_i_6172_);
v_res_6176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6174_, v_i_boxed_6175_, v_bs_6173_);
return v_res_6176_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6177_, lean_object* v_a_6178_){
_start:
{
if (lean_obj_tag(v_a_6177_) == 0)
{
lean_object* v___x_6179_; 
v___x_6179_ = l_List_reverse___redArg(v_a_6178_);
return v___x_6179_;
}
else
{
lean_object* v_head_6180_; lean_object* v_tail_6181_; lean_object* v___x_6183_; uint8_t v_isShared_6184_; uint8_t v_isSharedCheck_6190_; 
v_head_6180_ = lean_ctor_get(v_a_6177_, 0);
v_tail_6181_ = lean_ctor_get(v_a_6177_, 1);
v_isSharedCheck_6190_ = !lean_is_exclusive(v_a_6177_);
if (v_isSharedCheck_6190_ == 0)
{
v___x_6183_ = v_a_6177_;
v_isShared_6184_ = v_isSharedCheck_6190_;
goto v_resetjp_6182_;
}
else
{
lean_inc(v_tail_6181_);
lean_inc(v_head_6180_);
lean_dec(v_a_6177_);
v___x_6183_ = lean_box(0);
v_isShared_6184_ = v_isSharedCheck_6190_;
goto v_resetjp_6182_;
}
v_resetjp_6182_:
{
lean_object* v___x_6185_; lean_object* v___x_6187_; 
v___x_6185_ = l_Lean_MessageData_ofName(v_head_6180_);
if (v_isShared_6184_ == 0)
{
lean_ctor_set(v___x_6183_, 1, v_a_6178_);
lean_ctor_set(v___x_6183_, 0, v___x_6185_);
v___x_6187_ = v___x_6183_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6189_; 
v_reuseFailAlloc_6189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6189_, 0, v___x_6185_);
lean_ctor_set(v_reuseFailAlloc_6189_, 1, v_a_6178_);
v___x_6187_ = v_reuseFailAlloc_6189_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
v_a_6177_ = v_tail_6181_;
v_a_6178_ = v___x_6187_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6192_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6193_ = l_Lean_stringToMessageData(v___x_6192_);
return v___x_6193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6194_, lean_object* v_x_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_){
_start:
{
lean_object* v___x_6203_; size_t v_sz_6204_; size_t v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; 
v___x_6203_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6204_ = lean_array_size(v___y_6194_);
v___x_6205_ = ((size_t)0ULL);
v___x_6206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6204_, v___x_6205_, v___y_6194_);
v___x_6207_ = lean_array_to_list(v___x_6206_);
v___x_6208_ = lean_box(0);
v___x_6209_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6207_, v___x_6208_);
v___x_6210_ = l_Lean_MessageData_ofList(v___x_6209_);
v___x_6211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6211_, 0, v___x_6203_);
lean_ctor_set(v___x_6211_, 1, v___x_6210_);
v___x_6212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6211_);
return v___x_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6213_, lean_object* v_x_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_){
_start:
{
lean_object* v_res_6222_; 
v_res_6222_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6213_, v_x_6214_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_);
lean_dec(v___y_6220_);
lean_dec_ref(v___y_6219_);
lean_dec(v___y_6218_);
lean_dec_ref(v___y_6217_);
lean_dec(v___y_6216_);
lean_dec_ref(v___y_6215_);
lean_dec_ref(v_x_6214_);
return v_res_6222_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6223_; lean_object* v___x_6224_; 
v___x_6223_ = 0;
v___x_6224_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6223_);
return v___x_6224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6225_, lean_object* v_n_6226_, lean_object* v_j_6227_, lean_object* v_a_6228_){
_start:
{
lean_object* v_zero_6229_; uint8_t v_isZero_6230_; 
v_zero_6229_ = lean_unsigned_to_nat(0u);
v_isZero_6230_ = lean_nat_dec_eq(v_j_6227_, v_zero_6229_);
if (v_isZero_6230_ == 1)
{
lean_dec(v_j_6227_);
return v_a_6228_;
}
else
{
lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v_toSignature_6234_; uint8_t v_safe_6235_; lean_object* v_one_6236_; lean_object* v_n_6237_; 
v___x_6231_ = lean_nat_sub(v_n_6226_, v_j_6227_);
v___x_6232_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6233_ = lean_array_get_borrowed(v___x_6232_, v___y_6225_, v___x_6231_);
lean_dec(v___x_6231_);
v_toSignature_6234_ = lean_ctor_get(v___x_6233_, 0);
v_safe_6235_ = lean_ctor_get_uint8(v_toSignature_6234_, sizeof(void*)*4);
v_one_6236_ = lean_unsigned_to_nat(1u);
v_n_6237_ = lean_nat_sub(v_j_6227_, v_one_6236_);
lean_dec(v_j_6227_);
if (v_safe_6235_ == 0)
{
lean_object* v___x_6238_; lean_object* v___x_6239_; 
v___x_6238_ = lean_box(1);
v___x_6239_ = lean_array_push(v_a_6228_, v___x_6238_);
v_j_6227_ = v_n_6237_;
v_a_6228_ = v___x_6239_;
goto _start;
}
else
{
lean_object* v___x_6241_; lean_object* v___x_6242_; 
v___x_6241_ = lean_box(0);
v___x_6242_ = lean_array_push(v_a_6228_, v___x_6241_);
v_j_6227_ = v_n_6237_;
v_a_6228_ = v___x_6242_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6244_, lean_object* v_n_6245_, lean_object* v_j_6246_, lean_object* v_a_6247_){
_start:
{
lean_object* v_res_6248_; 
v_res_6248_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6244_, v_n_6245_, v_j_6246_, v_a_6247_);
lean_dec(v_n_6245_);
lean_dec_ref(v___y_6244_);
return v_res_6248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6249_, size_t v_sz_6250_, size_t v_i_6251_, lean_object* v_bs_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_){
_start:
{
uint8_t v___x_6258_; 
v___x_6258_ = lean_usize_dec_lt(v_i_6251_, v_sz_6250_);
if (v___x_6258_ == 0)
{
lean_object* v___x_6259_; 
v___x_6259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6259_, 0, v_bs_6252_);
return v___x_6259_;
}
else
{
lean_object* v_v_6260_; lean_object* v_toSignature_6261_; uint8_t v_safe_6262_; lean_object* v___x_6263_; lean_object* v_bs_x27_6264_; lean_object* v_a_6266_; 
v_v_6260_ = lean_array_uget(v_bs_6252_, v_i_6251_);
v_toSignature_6261_ = lean_ctor_get(v_v_6260_, 0);
v_safe_6262_ = lean_ctor_get_uint8(v_toSignature_6261_, sizeof(void*)*4);
v___x_6263_ = lean_unsigned_to_nat(0u);
v_bs_x27_6264_ = lean_array_uset(v_bs_6252_, v_i_6251_, v___x_6263_);
if (v_safe_6262_ == 0)
{
v_a_6266_ = v_v_6260_;
goto v___jp_6265_;
}
else
{
lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; 
v___x_6271_ = lean_usize_to_nat(v_i_6251_);
v___x_6272_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6273_ = lean_array_get_borrowed(v___x_6272_, v___x_6249_, v___x_6271_);
lean_dec(v___x_6271_);
lean_inc(v___x_6273_);
v___x_6274_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6273_, v_v_6260_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
if (lean_obj_tag(v___x_6274_) == 0)
{
lean_object* v_a_6275_; 
v_a_6275_ = lean_ctor_get(v___x_6274_, 0);
lean_inc(v_a_6275_);
lean_dec_ref_known(v___x_6274_, 1);
v_a_6266_ = v_a_6275_;
goto v___jp_6265_;
}
else
{
lean_object* v_a_6276_; lean_object* v___x_6278_; uint8_t v_isShared_6279_; uint8_t v_isSharedCheck_6283_; 
lean_dec_ref(v_bs_x27_6264_);
v_a_6276_ = lean_ctor_get(v___x_6274_, 0);
v_isSharedCheck_6283_ = !lean_is_exclusive(v___x_6274_);
if (v_isSharedCheck_6283_ == 0)
{
v___x_6278_ = v___x_6274_;
v_isShared_6279_ = v_isSharedCheck_6283_;
goto v_resetjp_6277_;
}
else
{
lean_inc(v_a_6276_);
lean_dec(v___x_6274_);
v___x_6278_ = lean_box(0);
v_isShared_6279_ = v_isSharedCheck_6283_;
goto v_resetjp_6277_;
}
v_resetjp_6277_:
{
lean_object* v___x_6281_; 
if (v_isShared_6279_ == 0)
{
v___x_6281_ = v___x_6278_;
goto v_reusejp_6280_;
}
else
{
lean_object* v_reuseFailAlloc_6282_; 
v_reuseFailAlloc_6282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6282_, 0, v_a_6276_);
v___x_6281_ = v_reuseFailAlloc_6282_;
goto v_reusejp_6280_;
}
v_reusejp_6280_:
{
return v___x_6281_;
}
}
}
}
v___jp_6265_:
{
size_t v___x_6267_; size_t v___x_6268_; lean_object* v___x_6269_; 
v___x_6267_ = ((size_t)1ULL);
v___x_6268_ = lean_usize_add(v_i_6251_, v___x_6267_);
v___x_6269_ = lean_array_uset(v_bs_x27_6264_, v_i_6251_, v_a_6266_);
v_i_6251_ = v___x_6268_;
v_bs_6252_ = v___x_6269_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6284_, lean_object* v_sz_6285_, lean_object* v_i_6286_, lean_object* v_bs_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_){
_start:
{
size_t v_sz_boxed_6293_; size_t v_i_boxed_6294_; lean_object* v_res_6295_; 
v_sz_boxed_6293_ = lean_unbox_usize(v_sz_6285_);
lean_dec(v_sz_6285_);
v_i_boxed_6294_ = lean_unbox_usize(v_i_6286_);
lean_dec(v_i_6286_);
v_res_6295_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6284_, v_sz_boxed_6293_, v_i_boxed_6294_, v_bs_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec_ref(v___x_6284_);
return v_res_6295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6298_, lean_object* v_pivot_6299_, lean_object* v_as_6300_, lean_object* v_i_6301_, lean_object* v_k_6302_){
_start:
{
uint8_t v___x_6303_; 
v___x_6303_ = lean_nat_dec_lt(v_k_6302_, v_hi_6298_);
if (v___x_6303_ == 0)
{
lean_object* v___x_6304_; lean_object* v___x_6305_; 
lean_dec(v_k_6302_);
lean_dec_ref(v_pivot_6299_);
v___x_6304_ = lean_array_fswap(v_as_6300_, v_i_6301_, v_hi_6298_);
v___x_6305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6305_, 0, v_i_6301_);
lean_ctor_set(v___x_6305_, 1, v___x_6304_);
return v___x_6305_;
}
else
{
lean_object* v___x_6306_; lean_object* v_toSignature_6307_; lean_object* v_toSignature_6308_; lean_object* v_name_6309_; lean_object* v_name_6310_; uint8_t v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; uint8_t v___x_6321_; 
v___x_6306_ = lean_array_fget_borrowed(v_as_6300_, v_k_6302_);
v_toSignature_6307_ = lean_ctor_get(v___x_6306_, 0);
v_toSignature_6308_ = lean_ctor_get(v_pivot_6299_, 0);
v_name_6309_ = lean_ctor_get(v_toSignature_6307_, 0);
v_name_6310_ = lean_ctor_get(v_toSignature_6308_, 0);
v___x_6311_ = 0;
v___x_6312_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6311_, v___x_6306_);
v___x_6313_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6314_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6315_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6309_);
v___x_6316_ = l_Lean_Name_toString(v_name_6309_, v___x_6303_);
v___x_6317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6317_, 0, v___x_6312_);
lean_ctor_set(v___x_6317_, 1, v___x_6316_);
v___x_6318_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6311_, v_pivot_6299_);
lean_inc(v_name_6310_);
v___x_6319_ = l_Lean_Name_toString(v_name_6310_, v___x_6303_);
v___x_6320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6320_, 0, v___x_6318_);
lean_ctor_set(v___x_6320_, 1, v___x_6319_);
v___x_6321_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6313_, v___x_6314_, v___x_6315_, v___x_6317_, v___x_6320_);
if (v___x_6321_ == 0)
{
lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6322_ = lean_unsigned_to_nat(1u);
v___x_6323_ = lean_nat_add(v_k_6302_, v___x_6322_);
lean_dec(v_k_6302_);
v_k_6302_ = v___x_6323_;
goto _start;
}
else
{
lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6325_ = lean_array_fswap(v_as_6300_, v_i_6301_, v_k_6302_);
v___x_6326_ = lean_unsigned_to_nat(1u);
v___x_6327_ = lean_nat_add(v_i_6301_, v___x_6326_);
lean_dec(v_i_6301_);
v___x_6328_ = lean_nat_add(v_k_6302_, v___x_6326_);
lean_dec(v_k_6302_);
v_as_6300_ = v___x_6325_;
v_i_6301_ = v___x_6327_;
v_k_6302_ = v___x_6328_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6330_, lean_object* v_pivot_6331_, lean_object* v_as_6332_, lean_object* v_i_6333_, lean_object* v_k_6334_){
_start:
{
lean_object* v_res_6335_; 
v_res_6335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6330_, v_pivot_6331_, v_as_6332_, v_i_6333_, v_k_6334_);
lean_dec(v_hi_6330_);
return v_res_6335_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6336_, lean_object* v_l_6337_, lean_object* v_r_6338_){
_start:
{
lean_object* v_toSignature_6339_; lean_object* v_toSignature_6340_; lean_object* v_name_6341_; lean_object* v_name_6342_; uint8_t v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; uint8_t v___x_6353_; 
v_toSignature_6339_ = lean_ctor_get(v_l_6337_, 0);
v_toSignature_6340_ = lean_ctor_get(v_r_6338_, 0);
v_name_6341_ = lean_ctor_get(v_toSignature_6339_, 0);
lean_inc(v_name_6341_);
v_name_6342_ = lean_ctor_get(v_toSignature_6340_, 0);
lean_inc(v_name_6342_);
v___x_6343_ = 0;
v___x_6344_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6343_, v_l_6337_);
lean_dec_ref(v_l_6337_);
v___x_6345_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6346_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6347_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6348_ = l_Lean_Name_toString(v_name_6341_, v___x_6336_);
v___x_6349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6349_, 0, v___x_6344_);
lean_ctor_set(v___x_6349_, 1, v___x_6348_);
v___x_6350_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6343_, v_r_6338_);
lean_dec_ref(v_r_6338_);
v___x_6351_ = l_Lean_Name_toString(v_name_6342_, v___x_6336_);
v___x_6352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6352_, 0, v___x_6350_);
lean_ctor_set(v___x_6352_, 1, v___x_6351_);
v___x_6353_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6345_, v___x_6346_, v___x_6347_, v___x_6349_, v___x_6352_);
return v___x_6353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6354_, lean_object* v_l_6355_, lean_object* v_r_6356_){
_start:
{
uint8_t v___x_13129__boxed_6357_; uint8_t v_res_6358_; lean_object* v_r_6359_; 
v___x_13129__boxed_6357_ = lean_unbox(v___x_6354_);
v_res_6358_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13129__boxed_6357_, v_l_6355_, v_r_6356_);
v_r_6359_ = lean_box(v_res_6358_);
return v_r_6359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6360_, lean_object* v_as_6361_, lean_object* v_lo_6362_, lean_object* v_hi_6363_){
_start:
{
lean_object* v___y_6365_; uint8_t v___x_6375_; 
v___x_6375_ = lean_nat_dec_lt(v_lo_6362_, v_hi_6363_);
if (v___x_6375_ == 0)
{
lean_dec(v_lo_6362_);
return v_as_6361_;
}
else
{
lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v_mid_6378_; lean_object* v___y_6380_; lean_object* v___y_6386_; lean_object* v___x_6391_; lean_object* v___x_6392_; uint8_t v___x_6393_; 
v___x_6376_ = lean_nat_add(v_lo_6362_, v_hi_6363_);
v___x_6377_ = lean_unsigned_to_nat(1u);
v_mid_6378_ = lean_nat_shiftr(v___x_6376_, v___x_6377_);
lean_dec(v___x_6376_);
v___x_6391_ = lean_array_fget_borrowed(v_as_6361_, v_mid_6378_);
v___x_6392_ = lean_array_fget_borrowed(v_as_6361_, v_lo_6362_);
lean_inc(v___x_6392_);
lean_inc(v___x_6391_);
v___x_6393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6375_, v___x_6391_, v___x_6392_);
if (v___x_6393_ == 0)
{
v___y_6386_ = v_as_6361_;
goto v___jp_6385_;
}
else
{
lean_object* v___x_6394_; 
v___x_6394_ = lean_array_fswap(v_as_6361_, v_lo_6362_, v_mid_6378_);
v___y_6386_ = v___x_6394_;
goto v___jp_6385_;
}
v___jp_6379_:
{
lean_object* v___x_6381_; lean_object* v___x_6382_; uint8_t v___x_6383_; 
v___x_6381_ = lean_array_fget_borrowed(v___y_6380_, v_mid_6378_);
v___x_6382_ = lean_array_fget_borrowed(v___y_6380_, v_hi_6363_);
lean_inc(v___x_6382_);
lean_inc(v___x_6381_);
v___x_6383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6375_, v___x_6381_, v___x_6382_);
if (v___x_6383_ == 0)
{
lean_dec(v_mid_6378_);
v___y_6365_ = v___y_6380_;
goto v___jp_6364_;
}
else
{
lean_object* v___x_6384_; 
v___x_6384_ = lean_array_fswap(v___y_6380_, v_mid_6378_, v_hi_6363_);
lean_dec(v_mid_6378_);
v___y_6365_ = v___x_6384_;
goto v___jp_6364_;
}
}
v___jp_6385_:
{
lean_object* v___x_6387_; lean_object* v___x_6388_; uint8_t v___x_6389_; 
v___x_6387_ = lean_array_fget_borrowed(v___y_6386_, v_hi_6363_);
v___x_6388_ = lean_array_fget_borrowed(v___y_6386_, v_lo_6362_);
lean_inc(v___x_6388_);
lean_inc(v___x_6387_);
v___x_6389_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6375_, v___x_6387_, v___x_6388_);
if (v___x_6389_ == 0)
{
v___y_6380_ = v___y_6386_;
goto v___jp_6379_;
}
else
{
lean_object* v___x_6390_; 
v___x_6390_ = lean_array_fswap(v___y_6386_, v_lo_6362_, v_hi_6363_);
v___y_6380_ = v___x_6390_;
goto v___jp_6379_;
}
}
}
v___jp_6364_:
{
lean_object* v_pivot_6366_; lean_object* v___x_6367_; lean_object* v_fst_6368_; lean_object* v_snd_6369_; uint8_t v___x_6370_; 
v_pivot_6366_ = lean_array_fget(v___y_6365_, v_hi_6363_);
lean_inc_n(v_lo_6362_, 2);
v___x_6367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6363_, v_pivot_6366_, v___y_6365_, v_lo_6362_, v_lo_6362_);
v_fst_6368_ = lean_ctor_get(v___x_6367_, 0);
lean_inc(v_fst_6368_);
v_snd_6369_ = lean_ctor_get(v___x_6367_, 1);
lean_inc(v_snd_6369_);
lean_dec_ref(v___x_6367_);
v___x_6370_ = lean_nat_dec_le(v_hi_6363_, v_fst_6368_);
if (v___x_6370_ == 0)
{
lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6360_, v_snd_6369_, v_lo_6362_, v_fst_6368_);
v___x_6372_ = lean_unsigned_to_nat(1u);
v___x_6373_ = lean_nat_add(v_fst_6368_, v___x_6372_);
lean_dec(v_fst_6368_);
v_as_6361_ = v___x_6371_;
v_lo_6362_ = v___x_6373_;
goto _start;
}
else
{
lean_dec(v_fst_6368_);
lean_dec(v_lo_6362_);
return v_snd_6369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6395_, lean_object* v_as_6396_, lean_object* v_lo_6397_, lean_object* v_hi_6398_){
_start:
{
lean_object* v_res_6399_; 
v_res_6399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6395_, v_as_6396_, v_lo_6397_, v_hi_6398_);
lean_dec(v_hi_6398_);
lean_dec(v_n_6395_);
return v_res_6399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6400_, lean_object* v___x_6401_, lean_object* v_n_6402_, lean_object* v_j_6403_, lean_object* v_a_6404_){
_start:
{
lean_object* v_zero_6405_; uint8_t v_isZero_6406_; 
v_zero_6405_ = lean_unsigned_to_nat(0u);
v_isZero_6406_ = lean_nat_dec_eq(v_j_6403_, v_zero_6405_);
if (v_isZero_6406_ == 1)
{
lean_dec(v_j_6403_);
return v_a_6404_;
}
else
{
lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v_toSignature_6409_; lean_object* v_name_6410_; lean_object* v___x_6411_; lean_object* v_one_6412_; lean_object* v_n_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6407_ = lean_nat_sub(v_n_6402_, v_j_6403_);
v___x_6408_ = lean_array_fget_borrowed(v___y_6400_, v___x_6407_);
v_toSignature_6409_ = lean_ctor_get(v___x_6408_, 0);
v_name_6410_ = lean_ctor_get(v_toSignature_6409_, 0);
v___x_6411_ = lean_box(0);
v_one_6412_ = lean_unsigned_to_nat(1u);
v_n_6413_ = lean_nat_sub(v_j_6403_, v_one_6412_);
lean_dec(v_j_6403_);
v___x_6414_ = lean_array_get_borrowed(v___x_6411_, v___x_6401_, v___x_6407_);
lean_dec(v___x_6407_);
lean_inc(v___x_6414_);
lean_inc(v_name_6410_);
v___x_6415_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6404_, v_name_6410_, v___x_6414_);
v_j_6403_ = v_n_6413_;
v_a_6404_ = v___x_6415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6417_, lean_object* v___x_6418_, lean_object* v_n_6419_, lean_object* v_j_6420_, lean_object* v_a_6421_){
_start:
{
lean_object* v_res_6422_; 
v_res_6422_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6417_, v___x_6418_, v_n_6419_, v_j_6420_, v_a_6421_);
lean_dec(v_n_6419_);
lean_dec_ref(v___x_6418_);
lean_dec_ref(v___y_6417_);
return v_res_6422_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6423_; 
v___x_6423_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6423_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; 
v___x_6424_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6425_, 0, v___x_6424_);
return v___x_6425_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6426_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6427_, 0, v___x_6426_);
lean_ctor_set(v___x_6427_, 1, v___x_6426_);
return v___x_6427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6430_, lean_object* v_a_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_){
_start:
{
size_t v___y_6437_; lean_object* v___y_6438_; size_t v___y_6439_; lean_object* v___y_6440_; lean_object* v___y_6441_; lean_object* v___y_6442_; lean_object* v___y_6476_; lean_object* v___y_6477_; uint8_t v___y_6478_; size_t v___y_6479_; lean_object* v___y_6480_; lean_object* v___y_6481_; size_t v___y_6482_; lean_object* v___y_6483_; uint8_t v___y_6484_; lean_object* v___y_6485_; lean_object* v___y_6486_; lean_object* v___y_6487_; lean_object* v___y_6488_; lean_object* v___y_6489_; lean_object* v_a_6490_; lean_object* v___y_6500_; lean_object* v___y_6501_; uint8_t v___y_6502_; size_t v___y_6503_; lean_object* v___y_6504_; lean_object* v___y_6505_; size_t v___y_6506_; lean_object* v___y_6507_; uint8_t v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6510_; lean_object* v___y_6511_; lean_object* v___y_6512_; lean_object* v___y_6513_; lean_object* v_a_6514_; lean_object* v___x_6526_; lean_object* v___y_6528_; lean_object* v___y_6529_; uint8_t v___y_6530_; size_t v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; size_t v___y_6534_; lean_object* v___y_6535_; uint8_t v___y_6536_; lean_object* v___y_6537_; lean_object* v___y_6538_; lean_object* v___y_6539_; lean_object* v___y_6581_; lean_object* v___x_6603_; lean_object* v___y_6605_; lean_object* v___y_6606_; uint8_t v___x_6608_; 
v___x_6526_ = lean_unsigned_to_nat(0u);
v___x_6603_ = lean_array_get_size(v_decls_6430_);
v___x_6608_ = lean_nat_dec_eq(v___x_6603_, v___x_6526_);
if (v___x_6608_ == 0)
{
lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___y_6612_; uint8_t v___x_6614_; 
v___x_6609_ = lean_unsigned_to_nat(1u);
v___x_6610_ = lean_nat_sub(v___x_6603_, v___x_6609_);
v___x_6614_ = lean_nat_dec_le(v___x_6526_, v___x_6610_);
if (v___x_6614_ == 0)
{
lean_inc(v___x_6610_);
v___y_6612_ = v___x_6610_;
goto v___jp_6611_;
}
else
{
v___y_6612_ = v___x_6526_;
goto v___jp_6611_;
}
v___jp_6611_:
{
uint8_t v___x_6613_; 
v___x_6613_ = lean_nat_dec_le(v___y_6612_, v___x_6610_);
if (v___x_6613_ == 0)
{
lean_dec(v___x_6610_);
lean_inc(v___y_6612_);
v___y_6605_ = v___y_6612_;
v___y_6606_ = v___y_6612_;
goto v___jp_6604_;
}
else
{
v___y_6605_ = v___y_6612_;
v___y_6606_ = v___x_6610_;
goto v___jp_6604_;
}
}
}
else
{
v___y_6581_ = v_decls_6430_;
goto v___jp_6580_;
}
v___jp_6436_:
{
if (lean_obj_tag(v___y_6442_) == 0)
{
lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v_assignments_6445_; lean_object* v_funVals_6446_; lean_object* v_env_6447_; lean_object* v_nextMacroScope_6448_; lean_object* v_ngen_6449_; lean_object* v_auxDeclNGen_6450_; lean_object* v_traceState_6451_; lean_object* v_messages_6452_; lean_object* v_infoState_6453_; lean_object* v_snapshotTasks_6454_; lean_object* v___x_6456_; uint8_t v_isShared_6457_; uint8_t v_isSharedCheck_6465_; 
lean_dec_ref_known(v___y_6442_, 1);
v___x_6443_ = lean_st_ref_get(v___y_6438_);
lean_dec(v___y_6438_);
v___x_6444_ = lean_st_ref_take(v_a_6434_);
v_assignments_6445_ = lean_ctor_get(v___x_6443_, 0);
lean_inc_ref(v_assignments_6445_);
v_funVals_6446_ = lean_ctor_get(v___x_6443_, 1);
lean_inc_ref(v_funVals_6446_);
lean_dec(v___x_6443_);
v_env_6447_ = lean_ctor_get(v___x_6444_, 0);
v_nextMacroScope_6448_ = lean_ctor_get(v___x_6444_, 1);
v_ngen_6449_ = lean_ctor_get(v___x_6444_, 2);
v_auxDeclNGen_6450_ = lean_ctor_get(v___x_6444_, 3);
v_traceState_6451_ = lean_ctor_get(v___x_6444_, 4);
v_messages_6452_ = lean_ctor_get(v___x_6444_, 6);
v_infoState_6453_ = lean_ctor_get(v___x_6444_, 7);
v_snapshotTasks_6454_ = lean_ctor_get(v___x_6444_, 8);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___x_6444_);
if (v_isSharedCheck_6465_ == 0)
{
lean_object* v_unused_6466_; 
v_unused_6466_ = lean_ctor_get(v___x_6444_, 5);
lean_dec(v_unused_6466_);
v___x_6456_ = v___x_6444_;
v_isShared_6457_ = v_isSharedCheck_6465_;
goto v_resetjp_6455_;
}
else
{
lean_inc(v_snapshotTasks_6454_);
lean_inc(v_infoState_6453_);
lean_inc(v_messages_6452_);
lean_inc(v_traceState_6451_);
lean_inc(v_auxDeclNGen_6450_);
lean_inc(v_ngen_6449_);
lean_inc(v_nextMacroScope_6448_);
lean_inc(v_env_6447_);
lean_dec(v___x_6444_);
v___x_6456_ = lean_box(0);
v_isShared_6457_ = v_isSharedCheck_6465_;
goto v_resetjp_6455_;
}
v_resetjp_6455_:
{
lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6461_; 
lean_inc(v___y_6441_);
v___x_6458_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6440_, v_funVals_6446_, v___y_6441_, v___y_6441_, v_env_6447_);
lean_dec(v___y_6441_);
lean_dec_ref(v_funVals_6446_);
v___x_6459_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6457_ == 0)
{
lean_ctor_set(v___x_6456_, 5, v___x_6459_);
lean_ctor_set(v___x_6456_, 0, v___x_6458_);
v___x_6461_ = v___x_6456_;
goto v_reusejp_6460_;
}
else
{
lean_object* v_reuseFailAlloc_6464_; 
v_reuseFailAlloc_6464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6464_, 0, v___x_6458_);
lean_ctor_set(v_reuseFailAlloc_6464_, 1, v_nextMacroScope_6448_);
lean_ctor_set(v_reuseFailAlloc_6464_, 2, v_ngen_6449_);
lean_ctor_set(v_reuseFailAlloc_6464_, 3, v_auxDeclNGen_6450_);
lean_ctor_set(v_reuseFailAlloc_6464_, 4, v_traceState_6451_);
lean_ctor_set(v_reuseFailAlloc_6464_, 5, v___x_6459_);
lean_ctor_set(v_reuseFailAlloc_6464_, 6, v_messages_6452_);
lean_ctor_set(v_reuseFailAlloc_6464_, 7, v_infoState_6453_);
lean_ctor_set(v_reuseFailAlloc_6464_, 8, v_snapshotTasks_6454_);
v___x_6461_ = v_reuseFailAlloc_6464_;
goto v_reusejp_6460_;
}
v_reusejp_6460_:
{
lean_object* v___x_6462_; lean_object* v___x_6463_; 
v___x_6462_ = lean_st_ref_set(v_a_6434_, v___x_6461_);
v___x_6463_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6445_, v___y_6437_, v___y_6439_, v___y_6440_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
lean_dec_ref(v_assignments_6445_);
return v___x_6463_;
}
}
}
else
{
lean_object* v_a_6467_; lean_object* v___x_6469_; uint8_t v_isShared_6470_; uint8_t v_isSharedCheck_6474_; 
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec(v___y_6438_);
v_a_6467_ = lean_ctor_get(v___y_6442_, 0);
v_isSharedCheck_6474_ = !lean_is_exclusive(v___y_6442_);
if (v_isSharedCheck_6474_ == 0)
{
v___x_6469_ = v___y_6442_;
v_isShared_6470_ = v_isSharedCheck_6474_;
goto v_resetjp_6468_;
}
else
{
lean_inc(v_a_6467_);
lean_dec(v___y_6442_);
v___x_6469_ = lean_box(0);
v_isShared_6470_ = v_isSharedCheck_6474_;
goto v_resetjp_6468_;
}
v_resetjp_6468_:
{
lean_object* v___x_6472_; 
if (v_isShared_6470_ == 0)
{
v___x_6472_ = v___x_6469_;
goto v_reusejp_6471_;
}
else
{
lean_object* v_reuseFailAlloc_6473_; 
v_reuseFailAlloc_6473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6467_);
v___x_6472_ = v_reuseFailAlloc_6473_;
goto v_reusejp_6471_;
}
v_reusejp_6471_:
{
return v___x_6472_;
}
}
}
}
v___jp_6475_:
{
lean_object* v___x_6491_; double v___x_6492_; double v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; 
v___x_6491_ = lean_io_get_num_heartbeats();
v___x_6492_ = lean_float_of_nat(v___y_6488_);
v___x_6493_ = lean_float_of_nat(v___x_6491_);
v___x_6494_ = lean_box_float(v___x_6492_);
v___x_6495_ = lean_box_float(v___x_6493_);
v___x_6496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6496_, 0, v___x_6494_);
lean_ctor_set(v___x_6496_, 1, v___x_6495_);
v___x_6497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6497_, 0, v_a_6490_);
lean_ctor_set(v___x_6497_, 1, v___x_6496_);
lean_inc_ref(v___y_6489_);
lean_inc(v___y_6480_);
v___x_6498_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6480_, v___y_6484_, v___y_6489_, v___y_6485_, v___y_6478_, v___y_6487_, v___y_6477_, v___x_6497_, v___y_6486_, v___y_6481_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
lean_dec_ref(v___y_6486_);
v___y_6437_ = v___y_6479_;
v___y_6438_ = v___y_6481_;
v___y_6439_ = v___y_6482_;
v___y_6440_ = v___y_6476_;
v___y_6441_ = v___y_6483_;
v___y_6442_ = v___x_6498_;
goto v___jp_6436_;
}
v___jp_6499_:
{
lean_object* v___x_6515_; double v___x_6516_; double v___x_6517_; double v___x_6518_; double v___x_6519_; double v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; 
v___x_6515_ = lean_io_mono_nanos_now();
v___x_6516_ = lean_float_of_nat(v___y_6512_);
v___x_6517_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6518_ = lean_float_div(v___x_6516_, v___x_6517_);
v___x_6519_ = lean_float_of_nat(v___x_6515_);
v___x_6520_ = lean_float_div(v___x_6519_, v___x_6517_);
v___x_6521_ = lean_box_float(v___x_6518_);
v___x_6522_ = lean_box_float(v___x_6520_);
v___x_6523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6523_, 0, v___x_6521_);
lean_ctor_set(v___x_6523_, 1, v___x_6522_);
v___x_6524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6524_, 0, v_a_6514_);
lean_ctor_set(v___x_6524_, 1, v___x_6523_);
lean_inc_ref(v___y_6513_);
lean_inc(v___y_6504_);
v___x_6525_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6504_, v___y_6508_, v___y_6513_, v___y_6509_, v___y_6502_, v___y_6511_, v___y_6501_, v___x_6524_, v___y_6510_, v___y_6505_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
lean_dec_ref(v___y_6510_);
v___y_6437_ = v___y_6503_;
v___y_6438_ = v___y_6505_;
v___y_6439_ = v___y_6506_;
v___y_6440_ = v___y_6500_;
v___y_6441_ = v___y_6507_;
v___y_6442_ = v___x_6525_;
goto v___jp_6436_;
}
v___jp_6527_:
{
lean_object* v___x_6540_; lean_object* v_a_6541_; lean_object* v___x_6542_; uint8_t v___x_6543_; 
v___x_6540_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6434_);
v_a_6541_ = lean_ctor_get(v___x_6540_, 0);
lean_inc(v_a_6541_);
lean_dec_ref(v___x_6540_);
v___x_6542_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6543_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6537_, v___x_6542_);
if (v___x_6543_ == 0)
{
lean_object* v___x_6544_; lean_object* v___x_6545_; 
v___x_6544_ = lean_io_mono_nanos_now();
v___x_6545_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6526_, v___y_6538_, v___y_6533_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
if (lean_obj_tag(v___x_6545_) == 0)
{
lean_object* v_a_6546_; lean_object* v___x_6548_; uint8_t v_isShared_6549_; uint8_t v_isSharedCheck_6553_; 
v_a_6546_ = lean_ctor_get(v___x_6545_, 0);
v_isSharedCheck_6553_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6553_ == 0)
{
v___x_6548_ = v___x_6545_;
v_isShared_6549_ = v_isSharedCheck_6553_;
goto v_resetjp_6547_;
}
else
{
lean_inc(v_a_6546_);
lean_dec(v___x_6545_);
v___x_6548_ = lean_box(0);
v_isShared_6549_ = v_isSharedCheck_6553_;
goto v_resetjp_6547_;
}
v_resetjp_6547_:
{
lean_object* v___x_6551_; 
if (v_isShared_6549_ == 0)
{
lean_ctor_set_tag(v___x_6548_, 1);
v___x_6551_ = v___x_6548_;
goto v_reusejp_6550_;
}
else
{
lean_object* v_reuseFailAlloc_6552_; 
v_reuseFailAlloc_6552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_a_6546_);
v___x_6551_ = v_reuseFailAlloc_6552_;
goto v_reusejp_6550_;
}
v_reusejp_6550_:
{
v___y_6500_ = v___y_6528_;
v___y_6501_ = v___y_6529_;
v___y_6502_ = v___y_6530_;
v___y_6503_ = v___y_6531_;
v___y_6504_ = v___y_6532_;
v___y_6505_ = v___y_6533_;
v___y_6506_ = v___y_6534_;
v___y_6507_ = v___y_6535_;
v___y_6508_ = v___y_6536_;
v___y_6509_ = v___y_6537_;
v___y_6510_ = v___y_6538_;
v___y_6511_ = v_a_6541_;
v___y_6512_ = v___x_6544_;
v___y_6513_ = v___y_6539_;
v_a_6514_ = v___x_6551_;
goto v___jp_6499_;
}
}
}
else
{
lean_object* v_a_6554_; lean_object* v___x_6556_; uint8_t v_isShared_6557_; uint8_t v_isSharedCheck_6561_; 
v_a_6554_ = lean_ctor_get(v___x_6545_, 0);
v_isSharedCheck_6561_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6556_ = v___x_6545_;
v_isShared_6557_ = v_isSharedCheck_6561_;
goto v_resetjp_6555_;
}
else
{
lean_inc(v_a_6554_);
lean_dec(v___x_6545_);
v___x_6556_ = lean_box(0);
v_isShared_6557_ = v_isSharedCheck_6561_;
goto v_resetjp_6555_;
}
v_resetjp_6555_:
{
lean_object* v___x_6559_; 
if (v_isShared_6557_ == 0)
{
lean_ctor_set_tag(v___x_6556_, 0);
v___x_6559_ = v___x_6556_;
goto v_reusejp_6558_;
}
else
{
lean_object* v_reuseFailAlloc_6560_; 
v_reuseFailAlloc_6560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6560_, 0, v_a_6554_);
v___x_6559_ = v_reuseFailAlloc_6560_;
goto v_reusejp_6558_;
}
v_reusejp_6558_:
{
v___y_6500_ = v___y_6528_;
v___y_6501_ = v___y_6529_;
v___y_6502_ = v___y_6530_;
v___y_6503_ = v___y_6531_;
v___y_6504_ = v___y_6532_;
v___y_6505_ = v___y_6533_;
v___y_6506_ = v___y_6534_;
v___y_6507_ = v___y_6535_;
v___y_6508_ = v___y_6536_;
v___y_6509_ = v___y_6537_;
v___y_6510_ = v___y_6538_;
v___y_6511_ = v_a_6541_;
v___y_6512_ = v___x_6544_;
v___y_6513_ = v___y_6539_;
v_a_6514_ = v___x_6559_;
goto v___jp_6499_;
}
}
}
}
else
{
lean_object* v___x_6562_; lean_object* v___x_6563_; 
v___x_6562_ = lean_io_get_num_heartbeats();
v___x_6563_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6526_, v___y_6538_, v___y_6533_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
if (lean_obj_tag(v___x_6563_) == 0)
{
lean_object* v_a_6564_; lean_object* v___x_6566_; uint8_t v_isShared_6567_; uint8_t v_isSharedCheck_6571_; 
v_a_6564_ = lean_ctor_get(v___x_6563_, 0);
v_isSharedCheck_6571_ = !lean_is_exclusive(v___x_6563_);
if (v_isSharedCheck_6571_ == 0)
{
v___x_6566_ = v___x_6563_;
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
else
{
lean_inc(v_a_6564_);
lean_dec(v___x_6563_);
v___x_6566_ = lean_box(0);
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
v_resetjp_6565_:
{
lean_object* v___x_6569_; 
if (v_isShared_6567_ == 0)
{
lean_ctor_set_tag(v___x_6566_, 1);
v___x_6569_ = v___x_6566_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6570_; 
v_reuseFailAlloc_6570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6570_, 0, v_a_6564_);
v___x_6569_ = v_reuseFailAlloc_6570_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
v___y_6476_ = v___y_6528_;
v___y_6477_ = v___y_6529_;
v___y_6478_ = v___y_6530_;
v___y_6479_ = v___y_6531_;
v___y_6480_ = v___y_6532_;
v___y_6481_ = v___y_6533_;
v___y_6482_ = v___y_6534_;
v___y_6483_ = v___y_6535_;
v___y_6484_ = v___y_6536_;
v___y_6485_ = v___y_6537_;
v___y_6486_ = v___y_6538_;
v___y_6487_ = v_a_6541_;
v___y_6488_ = v___x_6562_;
v___y_6489_ = v___y_6539_;
v_a_6490_ = v___x_6569_;
goto v___jp_6475_;
}
}
}
else
{
lean_object* v_a_6572_; lean_object* v___x_6574_; uint8_t v_isShared_6575_; uint8_t v_isSharedCheck_6579_; 
v_a_6572_ = lean_ctor_get(v___x_6563_, 0);
v_isSharedCheck_6579_ = !lean_is_exclusive(v___x_6563_);
if (v_isSharedCheck_6579_ == 0)
{
v___x_6574_ = v___x_6563_;
v_isShared_6575_ = v_isSharedCheck_6579_;
goto v_resetjp_6573_;
}
else
{
lean_inc(v_a_6572_);
lean_dec(v___x_6563_);
v___x_6574_ = lean_box(0);
v_isShared_6575_ = v_isSharedCheck_6579_;
goto v_resetjp_6573_;
}
v_resetjp_6573_:
{
lean_object* v___x_6577_; 
if (v_isShared_6575_ == 0)
{
lean_ctor_set_tag(v___x_6574_, 0);
v___x_6577_ = v___x_6574_;
goto v_reusejp_6576_;
}
else
{
lean_object* v_reuseFailAlloc_6578_; 
v_reuseFailAlloc_6578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6578_, 0, v_a_6572_);
v___x_6577_ = v_reuseFailAlloc_6578_;
goto v_reusejp_6576_;
}
v_reusejp_6576_:
{
v___y_6476_ = v___y_6528_;
v___y_6477_ = v___y_6529_;
v___y_6478_ = v___y_6530_;
v___y_6479_ = v___y_6531_;
v___y_6480_ = v___y_6532_;
v___y_6481_ = v___y_6533_;
v___y_6482_ = v___y_6534_;
v___y_6483_ = v___y_6535_;
v___y_6484_ = v___y_6536_;
v___y_6485_ = v___y_6537_;
v___y_6486_ = v___y_6538_;
v___y_6487_ = v_a_6541_;
v___y_6488_ = v___x_6562_;
v___y_6489_ = v___y_6539_;
v_a_6490_ = v___x_6577_;
goto v___jp_6475_;
}
}
}
}
}
v___jp_6580_:
{
size_t v_sz_6582_; size_t v___x_6583_; lean_object* v_assignments_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v_funVals_6587_; lean_object* v_state_6588_; lean_object* v___x_6589_; lean_object* v_options_6590_; lean_object* v_inheritedTraceOptions_6591_; uint8_t v_hasTrace_6592_; lean_object* v_ctx_6593_; 
v_sz_6582_ = lean_array_size(v___y_6581_);
v___x_6583_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6581_, 2);
v_assignments_6584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6582_, v___x_6583_, v___y_6581_);
v___x_6585_ = lean_array_get_size(v___y_6581_);
v___x_6586_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6587_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6581_, v___x_6585_, v___x_6585_, v___x_6586_);
v_state_6588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6588_, 0, v_assignments_6584_);
lean_ctor_set(v_state_6588_, 1, v_funVals_6587_);
v___x_6589_ = lean_st_mk_ref(v_state_6588_);
v_options_6590_ = lean_ctor_get(v_a_6433_, 2);
v_inheritedTraceOptions_6591_ = lean_ctor_get(v_a_6433_, 13);
v_hasTrace_6592_ = lean_ctor_get_uint8(v_options_6590_, sizeof(void*)*1);
v_ctx_6593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6593_, 0, v___y_6581_);
lean_ctor_set(v_ctx_6593_, 1, v___x_6526_);
if (v_hasTrace_6592_ == 0)
{
lean_object* v___x_6594_; 
v___x_6594_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6526_, v_ctx_6593_, v___x_6589_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
lean_dec_ref_known(v_ctx_6593_, 2);
v___y_6437_ = v_sz_6582_;
v___y_6438_ = v___x_6589_;
v___y_6439_ = v___x_6583_;
v___y_6440_ = v___y_6581_;
v___y_6441_ = v___x_6585_;
v___y_6442_ = v___x_6594_;
goto v___jp_6436_;
}
else
{
lean_object* v___f_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; uint8_t v___x_6599_; 
lean_inc_ref(v___y_6581_);
v___f_6595_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6595_, 0, v___y_6581_);
v___x_6596_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6597_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6598_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6599_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6591_, v_options_6590_, v___x_6598_);
if (v___x_6599_ == 0)
{
lean_object* v___x_6600_; uint8_t v___x_6601_; 
v___x_6600_ = l_Lean_trace_profiler;
v___x_6601_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6590_, v___x_6600_);
if (v___x_6601_ == 0)
{
lean_object* v___x_6602_; 
lean_dec_ref(v___f_6595_);
v___x_6602_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6526_, v_ctx_6593_, v___x_6589_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
lean_dec_ref_known(v_ctx_6593_, 2);
v___y_6437_ = v_sz_6582_;
v___y_6438_ = v___x_6589_;
v___y_6439_ = v___x_6583_;
v___y_6440_ = v___y_6581_;
v___y_6441_ = v___x_6585_;
v___y_6442_ = v___x_6602_;
goto v___jp_6436_;
}
else
{
v___y_6528_ = v___y_6581_;
v___y_6529_ = v___f_6595_;
v___y_6530_ = v___x_6599_;
v___y_6531_ = v_sz_6582_;
v___y_6532_ = v___x_6596_;
v___y_6533_ = v___x_6589_;
v___y_6534_ = v___x_6583_;
v___y_6535_ = v___x_6585_;
v___y_6536_ = v_hasTrace_6592_;
v___y_6537_ = v_options_6590_;
v___y_6538_ = v_ctx_6593_;
v___y_6539_ = v___x_6597_;
goto v___jp_6527_;
}
}
else
{
v___y_6528_ = v___y_6581_;
v___y_6529_ = v___f_6595_;
v___y_6530_ = v___x_6599_;
v___y_6531_ = v_sz_6582_;
v___y_6532_ = v___x_6596_;
v___y_6533_ = v___x_6589_;
v___y_6534_ = v___x_6583_;
v___y_6535_ = v___x_6585_;
v___y_6536_ = v_hasTrace_6592_;
v___y_6537_ = v_options_6590_;
v___y_6538_ = v_ctx_6593_;
v___y_6539_ = v___x_6597_;
goto v___jp_6527_;
}
}
}
v___jp_6604_:
{
lean_object* v___x_6607_; 
v___x_6607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6603_, v_decls_6430_, v___y_6605_, v___y_6606_);
lean_dec(v___y_6606_);
v___y_6581_ = v___x_6607_;
goto v___jp_6580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_){
_start:
{
lean_object* v_res_6621_; 
v_res_6621_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6615_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_);
lean_dec(v_a_6619_);
lean_dec_ref(v_a_6618_);
lean_dec(v_a_6617_);
lean_dec_ref(v_a_6616_);
return v_res_6621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6622_, lean_object* v_n_6623_, lean_object* v_j_6624_, lean_object* v_a_6625_, lean_object* v_a_6626_){
_start:
{
lean_object* v___x_6627_; 
v___x_6627_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6622_, v_n_6623_, v_j_6624_, v_a_6626_);
return v___x_6627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6628_, lean_object* v_n_6629_, lean_object* v_j_6630_, lean_object* v_a_6631_, lean_object* v_a_6632_){
_start:
{
lean_object* v_res_6633_; 
v_res_6633_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6628_, v_n_6629_, v_j_6630_, v_a_6631_, v_a_6632_);
lean_dec(v_n_6629_);
lean_dec_ref(v___y_6628_);
return v_res_6633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6634_, lean_object* v___x_6635_, lean_object* v_n_6636_, lean_object* v_j_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_){
_start:
{
lean_object* v___x_6640_; 
v___x_6640_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6634_, v___x_6635_, v_n_6636_, v_j_6637_, v_a_6639_);
return v___x_6640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6641_, lean_object* v___x_6642_, lean_object* v_n_6643_, lean_object* v_j_6644_, lean_object* v_a_6645_, lean_object* v_a_6646_){
_start:
{
lean_object* v_res_6647_; 
v_res_6647_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6641_, v___x_6642_, v_n_6643_, v_j_6644_, v_a_6645_, v_a_6646_);
lean_dec(v_n_6643_);
lean_dec_ref(v___x_6642_);
lean_dec_ref(v___y_6641_);
return v_res_6647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6648_, lean_object* v_as_6649_, size_t v_sz_6650_, size_t v_i_6651_, lean_object* v_bs_6652_, lean_object* v___y_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_){
_start:
{
lean_object* v___x_6658_; 
v___x_6658_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6648_, v_sz_6650_, v_i_6651_, v_bs_6652_, v___y_6653_, v___y_6654_, v___y_6655_, v___y_6656_);
return v___x_6658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6659_, lean_object* v_as_6660_, lean_object* v_sz_6661_, lean_object* v_i_6662_, lean_object* v_bs_6663_, lean_object* v___y_6664_, lean_object* v___y_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_){
_start:
{
size_t v_sz_boxed_6669_; size_t v_i_boxed_6670_; lean_object* v_res_6671_; 
v_sz_boxed_6669_ = lean_unbox_usize(v_sz_6661_);
lean_dec(v_sz_6661_);
v_i_boxed_6670_ = lean_unbox_usize(v_i_6662_);
lean_dec(v_i_6662_);
v_res_6671_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6659_, v_as_6660_, v_sz_boxed_6669_, v_i_boxed_6670_, v_bs_6663_, v___y_6664_, v___y_6665_, v___y_6666_, v___y_6667_);
lean_dec(v___y_6667_);
lean_dec_ref(v___y_6666_);
lean_dec(v___y_6665_);
lean_dec_ref(v___y_6664_);
lean_dec_ref(v_as_6660_);
lean_dec_ref(v___x_6659_);
return v_res_6671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6672_, lean_object* v_as_6673_, lean_object* v_lo_6674_, lean_object* v_hi_6675_, lean_object* v_w_6676_, lean_object* v_hlo_6677_, lean_object* v_hhi_6678_){
_start:
{
lean_object* v___x_6679_; 
v___x_6679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6672_, v_as_6673_, v_lo_6674_, v_hi_6675_);
return v___x_6679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6680_, lean_object* v_as_6681_, lean_object* v_lo_6682_, lean_object* v_hi_6683_, lean_object* v_w_6684_, lean_object* v_hlo_6685_, lean_object* v_hhi_6686_){
_start:
{
lean_object* v_res_6687_; 
v_res_6687_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6680_, v_as_6681_, v_lo_6682_, v_hi_6683_, v_w_6684_, v_hlo_6685_, v_hhi_6686_);
lean_dec(v_hi_6683_);
lean_dec(v_n_6680_);
return v_res_6687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6688_, lean_object* v_lo_6689_, lean_object* v_hi_6690_, lean_object* v_hhi_6691_, lean_object* v_pivot_6692_, lean_object* v_as_6693_, lean_object* v_i_6694_, lean_object* v_k_6695_, lean_object* v_ilo_6696_, lean_object* v_ik_6697_, lean_object* v_w_6698_){
_start:
{
lean_object* v___x_6699_; 
v___x_6699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6690_, v_pivot_6692_, v_as_6693_, v_i_6694_, v_k_6695_);
return v___x_6699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6700_, lean_object* v_lo_6701_, lean_object* v_hi_6702_, lean_object* v_hhi_6703_, lean_object* v_pivot_6704_, lean_object* v_as_6705_, lean_object* v_i_6706_, lean_object* v_k_6707_, lean_object* v_ilo_6708_, lean_object* v_ik_6709_, lean_object* v_w_6710_){
_start:
{
lean_object* v_res_6711_; 
v_res_6711_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6700_, v_lo_6701_, v_hi_6702_, v_hhi_6703_, v_pivot_6704_, v_as_6705_, v_i_6706_, v_k_6707_, v_ilo_6708_, v_ik_6709_, v_w_6710_);
lean_dec(v_hi_6702_);
lean_dec(v_lo_6701_);
lean_dec(v_n_6700_);
return v_res_6711_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; 
v___x_6771_ = lean_unsigned_to_nat(3955956072u);
v___x_6772_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6773_ = l_Lean_Name_num___override(v___x_6772_, v___x_6771_);
return v___x_6773_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; 
v___x_6775_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6776_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6777_ = l_Lean_Name_str___override(v___x_6776_, v___x_6775_);
return v___x_6777_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; 
v___x_6779_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6780_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6781_ = l_Lean_Name_str___override(v___x_6780_, v___x_6779_);
return v___x_6781_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6782_; lean_object* v___x_6783_; lean_object* v___x_6784_; 
v___x_6782_ = lean_unsigned_to_nat(2u);
v___x_6783_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6784_ = l_Lean_Name_num___override(v___x_6783_, v___x_6782_);
return v___x_6784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6786_; uint8_t v___x_6787_; lean_object* v___x_6788_; lean_object* v___x_6789_; 
v___x_6786_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6787_ = 1;
v___x_6788_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6789_ = l_Lean_registerTraceClass(v___x_6786_, v___x_6787_, v___x_6788_);
return v___x_6789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6790_){
_start:
{
lean_object* v_res_6791_; 
v_res_6791_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6791_;
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
