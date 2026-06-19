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
lean_object* l_String_quote(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; lean_object* v___x_1981__overap_1024_; lean_object* v___x_1025_; 
v___x_1018_ = l_StateRefT_x27_instMonad___redArg(v___x_1017_);
v___x_1019_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_instInhabitedOfMonad___redArg(v___x_1018_, v___x_1021_);
v___f_1023_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1023_, 0, v___x_1022_);
v___x_1981__overap_1024_ = lean_panic_fn_borrowed(v___f_1023_, v_msg_987_);
lean_dec_ref(v___f_1023_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
v___x_1025_ = lean_apply_5(v___x_1981__overap_1024_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
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
lean_inc_ref(v_str_1192_);
lean_inc(v_pre_1191_);
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
v___y_1098_ = v___y_1153_;
v___y_1099_ = v___y_1155_;
v___y_1100_ = v_ctorName_1152_;
v___y_1101_ = v___y_1154_;
v___y_1102_ = v___y_1156_;
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
v___y_1098_ = v___y_1153_;
v___y_1099_ = v___y_1155_;
v___y_1100_ = v_ctorName_1152_;
v___y_1101_ = v___y_1154_;
v___y_1102_ = v___y_1156_;
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
v___y_1131_ = v___y_1153_;
v___y_1132_ = v___y_1155_;
v___y_1133_ = v_ctorName_1152_;
v___y_1134_ = v___y_1154_;
v___y_1135_ = v___y_1156_;
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
v___y_1131_ = v___y_1153_;
v___y_1132_ = v___y_1155_;
v___y_1133_ = v_ctorName_1152_;
v___y_1134_ = v___y_1154_;
v___y_1135_ = v___y_1156_;
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
lean_ctor_set(v___x_1107_, 0, v___y_1100_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
lean_ctor_set(v___x_1107_, 2, v_snd_1104_);
v___x_1108_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1109_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1105_, v___x_1107_, v___x_1108_, v___y_1098_, v___y_1101_, v___y_1099_, v___y_1102_);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1406_; size_t v___x_1407_; size_t v___x_1408_; 
v___x_1406_ = ((size_t)5ULL);
v___x_1407_ = ((size_t)1ULL);
v___x_1408_ = lean_usize_shift_left(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; 
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_1411_ = lean_usize_sub(v___x_1410_, v___x_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1412_, size_t v_x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 0)
{
lean_object* v_es_1415_; lean_object* v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; lean_object* v_j_1420_; lean_object* v___x_1421_; 
v_es_1415_ = lean_ctor_get(v_x_1412_, 0);
v___x_1416_ = lean_box(2);
v___x_1417_ = ((size_t)5ULL);
v___x_1418_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1419_ = lean_usize_land(v_x_1413_, v___x_1418_);
v_j_1420_ = lean_usize_to_nat(v___x_1419_);
v___x_1421_ = lean_array_get_borrowed(v___x_1416_, v_es_1415_, v_j_1420_);
lean_dec(v_j_1420_);
switch(lean_obj_tag(v___x_1421_))
{
case 0:
{
lean_object* v_key_1422_; uint8_t v___x_1423_; 
v_key_1422_ = lean_ctor_get(v___x_1421_, 0);
v___x_1423_ = lean_name_eq(v_x_1414_, v_key_1422_);
return v___x_1423_;
}
case 1:
{
lean_object* v_node_1424_; size_t v___x_1425_; 
v_node_1424_ = lean_ctor_get(v___x_1421_, 0);
v___x_1425_ = lean_usize_shift_right(v_x_1413_, v___x_1417_);
v_x_1412_ = v_node_1424_;
v_x_1413_ = v___x_1425_;
goto _start;
}
default: 
{
uint8_t v___x_1427_; 
v___x_1427_ = 0;
return v___x_1427_;
}
}
}
else
{
lean_object* v_ks_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v_ks_1428_ = lean_ctor_get(v_x_1412_, 0);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1428_, v___x_1429_, v_x_1414_);
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
size_t v_x_1181__boxed_1434_; uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_x_1181__boxed_1434_ = lean_unbox_usize(v_x_1432_);
lean_dec(v_x_1432_);
v_res_1435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1431_, v_x_1181__boxed_1434_, v_x_1433_);
lean_dec(v_x_1433_);
lean_dec_ref(v_x_1431_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1437_; uint64_t v___x_1438_; 
v___x_1437_ = lean_unsigned_to_nat(1723u);
v___x_1438_ = lean_uint64_of_nat(v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
uint64_t v___y_1442_; 
if (lean_obj_tag(v_x_1440_) == 0)
{
uint64_t v___x_1445_; 
v___x_1445_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1442_ = v___x_1445_;
goto v___jp_1441_;
}
else
{
uint64_t v_hash_1446_; 
v_hash_1446_ = lean_ctor_get_uint64(v_x_1440_, sizeof(void*)*2);
v___y_1442_ = v_hash_1446_;
goto v___jp_1441_;
}
v___jp_1441_:
{
size_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = lean_uint64_to_usize(v___y_1442_);
v___x_1444_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1439_, v___x_1443_, v_x_1440_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
uint8_t v_res_1449_; lean_object* v_r_1450_; 
v_res_1449_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1447_, v_x_1448_);
lean_dec(v_x_1448_);
lean_dec_ref(v_x_1447_);
v_r_1450_ = lean_box(v_res_1449_);
return v_r_1450_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x1_1451_, lean_object* v_x2_1452_){
_start:
{
lean_object* v_fst_1453_; uint8_t v___x_1454_; 
v_fst_1453_ = lean_ctor_get(v_x2_1452_, 0);
v___x_1454_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x1_1451_, v_fst_1453_);
if (v___x_1454_ == 0)
{
uint8_t v___x_1455_; 
v___x_1455_ = 1;
return v___x_1455_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = 0;
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x1_1457_, lean_object* v_x2_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x1_1457_, v_x2_1458_);
lean_dec_ref(v_x2_1458_);
lean_dec_ref(v_x1_1457_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_f_1461_, lean_object* v_keys_1462_, lean_object* v_vals_1463_, lean_object* v_i_1464_, lean_object* v_acc_1465_){
_start:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_array_get_size(v_keys_1462_);
v___x_1467_ = lean_nat_dec_lt(v_i_1464_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_dec(v_i_1464_);
lean_dec(v_f_1461_);
return v_acc_1465_;
}
else
{
lean_object* v_k_1468_; lean_object* v_v_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_k_1468_ = lean_array_fget_borrowed(v_keys_1462_, v_i_1464_);
v_v_1469_ = lean_array_fget_borrowed(v_vals_1463_, v_i_1464_);
lean_inc(v_f_1461_);
lean_inc(v_v_1469_);
lean_inc(v_k_1468_);
v___x_1470_ = lean_apply_3(v_f_1461_, v_acc_1465_, v_k_1468_, v_v_1469_);
v___x_1471_ = lean_unsigned_to_nat(1u);
v___x_1472_ = lean_nat_add(v_i_1464_, v___x_1471_);
lean_dec(v_i_1464_);
v_i_1464_ = v___x_1472_;
v_acc_1465_ = v___x_1470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_f_1474_, lean_object* v_keys_1475_, lean_object* v_vals_1476_, lean_object* v_i_1477_, lean_object* v_acc_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1474_, v_keys_1475_, v_vals_1476_, v_i_1477_, v_acc_1478_);
lean_dec_ref(v_vals_1476_);
lean_dec_ref(v_keys_1475_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v_es_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_es_1483_ = lean_ctor_get(v_x_1481_, 0);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_array_get_size(v_es_1483_);
v___x_1486_ = lean_nat_dec_lt(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec(v_f_1480_);
return v_x_1482_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_nat_dec_le(v___x_1485_, v___x_1485_);
if (v___x_1487_ == 0)
{
if (v___x_1486_ == 0)
{
lean_dec(v_f_1480_);
return v_x_1482_;
}
else
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1485_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1480_, v_es_1483_, v___x_1488_, v___x_1489_, v_x_1482_);
return v___x_1490_;
}
}
else
{
size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = lean_usize_of_nat(v___x_1485_);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1480_, v_es_1483_, v___x_1491_, v___x_1492_, v_x_1482_);
return v___x_1493_;
}
}
}
else
{
lean_object* v_ks_1494_; lean_object* v_vs_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_ks_1494_ = lean_ctor_get(v_x_1481_, 0);
v_vs_1495_ = lean_ctor_get(v_x_1481_, 1);
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1480_, v_ks_1494_, v_vs_1495_, v___x_1496_, v_x_1482_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1498_, lean_object* v_as_1499_, size_t v_i_1500_, size_t v_stop_1501_, lean_object* v_b_1502_){
_start:
{
lean_object* v___y_1504_; uint8_t v___x_1508_; 
v___x_1508_ = lean_usize_dec_eq(v_i_1500_, v_stop_1501_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_array_uget_borrowed(v_as_1499_, v_i_1500_);
switch(lean_obj_tag(v___x_1509_))
{
case 0:
{
lean_object* v_key_1510_; lean_object* v_val_1511_; lean_object* v___x_1512_; 
v_key_1510_ = lean_ctor_get(v___x_1509_, 0);
v_val_1511_ = lean_ctor_get(v___x_1509_, 1);
lean_inc(v_f_1498_);
lean_inc(v_val_1511_);
lean_inc(v_key_1510_);
v___x_1512_ = lean_apply_3(v_f_1498_, v_b_1502_, v_key_1510_, v_val_1511_);
v___y_1504_ = v___x_1512_;
goto v___jp_1503_;
}
case 1:
{
lean_object* v_node_1513_; lean_object* v___x_1514_; 
v_node_1513_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_f_1498_);
v___x_1514_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1498_, v_node_1513_, v_b_1502_);
v___y_1504_ = v___x_1514_;
goto v___jp_1503_;
}
default: 
{
v___y_1504_ = v_b_1502_;
goto v___jp_1503_;
}
}
}
else
{
lean_dec(v_f_1498_);
return v_b_1502_;
}
v___jp_1503_:
{
size_t v___x_1505_; size_t v___x_1506_; 
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1500_, v___x_1505_);
v_i_1500_ = v___x_1506_;
v_b_1502_ = v___y_1504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1515_, lean_object* v_as_1516_, lean_object* v_i_1517_, lean_object* v_stop_1518_, lean_object* v_b_1519_){
_start:
{
size_t v_i_boxed_1520_; size_t v_stop_boxed_1521_; lean_object* v_res_1522_; 
v_i_boxed_1520_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_stop_boxed_1521_ = lean_unbox_usize(v_stop_1518_);
lean_dec(v_stop_1518_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1515_, v_as_1516_, v_i_boxed_1520_, v_stop_boxed_1521_, v_b_1519_);
lean_dec_ref(v_as_1516_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1523_, v_x_1524_, v_x_1525_);
lean_dec_ref(v_x_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1527_, lean_object* v_x1_1528_, lean_object* v_x2_1529_, lean_object* v_x3_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_apply_3(v_f_1527_, v_x1_1528_, v_x2_1529_, v_x3_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1532_, lean_object* v_f_1533_, lean_object* v_init_1534_){
_start:
{
lean_object* v___f_1535_; lean_object* v___x_1536_; 
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1535_, 0, v_f_1533_);
v___x_1536_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1535_, v_map_1532_, v_init_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1537_, lean_object* v_f_1538_, lean_object* v_init_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1537_, v_f_1538_, v_init_1539_);
lean_dec_ref(v_map_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1541_, lean_object* v_k_1542_, lean_object* v_v_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_k_1542_);
lean_ctor_set(v___x_1544_, 1, v_v_1543_);
v___x_1545_ = lean_array_push(v_ps_1541_, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1549_){
_start:
{
lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___f_1550_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1551_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1552_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1549_, v___f_1550_, v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1553_);
lean_dec_ref(v_m_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_fst_1557_; lean_object* v_fst_1558_; uint8_t v___x_1559_; 
v_fst_1557_ = lean_ctor_get(v___y_1555_, 0);
v_fst_1558_ = lean_ctor_get(v___y_1556_, 0);
v___x_1559_ = l_Lean_Name_quickLt(v_fst_1557_, v_fst_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v_res_1562_; lean_object* v_r_1563_; 
v_res_1562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1560_, v___y_1561_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v___y_1560_);
v_r_1563_ = lean_box(v_res_1562_);
return v_r_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_hi_1564_, lean_object* v_pivot_1565_, lean_object* v_as_1566_, lean_object* v_i_1567_, lean_object* v_k_1568_){
_start:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_lt(v_k_1568_, v_hi_1564_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v_k_1568_);
v___x_1570_ = lean_array_fswap(v_as_1566_, v_i_1567_, v_hi_1564_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_i_1567_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; lean_object* v_fst_1573_; lean_object* v_fst_1574_; uint8_t v___x_1575_; 
v___x_1572_ = lean_array_fget_borrowed(v_as_1566_, v_k_1568_);
v_fst_1573_ = lean_ctor_get(v___x_1572_, 0);
v_fst_1574_ = lean_ctor_get(v_pivot_1565_, 0);
v___x_1575_ = l_Lean_Name_quickLt(v_fst_1573_, v_fst_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_add(v_k_1568_, v___x_1576_);
lean_dec(v_k_1568_);
v_k_1568_ = v___x_1577_;
goto _start;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1579_ = lean_array_fswap(v_as_1566_, v_i_1567_, v_k_1568_);
v___x_1580_ = lean_unsigned_to_nat(1u);
v___x_1581_ = lean_nat_add(v_i_1567_, v___x_1580_);
lean_dec(v_i_1567_);
v___x_1582_ = lean_nat_add(v_k_1568_, v___x_1580_);
lean_dec(v_k_1568_);
v_as_1566_ = v___x_1579_;
v_i_1567_ = v___x_1581_;
v_k_1568_ = v___x_1582_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_hi_1584_, lean_object* v_pivot_1585_, lean_object* v_as_1586_, lean_object* v_i_1587_, lean_object* v_k_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1584_, v_pivot_1585_, v_as_1586_, v_i_1587_, v_k_1588_);
lean_dec_ref(v_pivot_1585_);
lean_dec(v_hi_1584_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_1590_, lean_object* v_as_1591_, lean_object* v_lo_1592_, lean_object* v_hi_1593_){
_start:
{
lean_object* v___y_1595_; uint8_t v___x_1605_; 
v___x_1605_ = lean_nat_dec_lt(v_lo_1592_, v_hi_1593_);
if (v___x_1605_ == 0)
{
lean_dec(v_lo_1592_);
return v_as_1591_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_mid_1608_; lean_object* v___y_1610_; lean_object* v___y_1616_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1606_ = lean_nat_add(v_lo_1592_, v_hi_1593_);
v___x_1607_ = lean_unsigned_to_nat(1u);
v_mid_1608_ = lean_nat_shiftr(v___x_1606_, v___x_1607_);
lean_dec(v___x_1606_);
v___x_1621_ = lean_array_fget_borrowed(v_as_1591_, v_mid_1608_);
v___x_1622_ = lean_array_fget_borrowed(v_as_1591_, v_lo_1592_);
v___x_1623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
v___y_1616_ = v_as_1591_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_array_fswap(v_as_1591_, v_lo_1592_, v_mid_1608_);
v___y_1616_ = v___x_1624_;
goto v___jp_1615_;
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = lean_array_fget_borrowed(v___y_1610_, v_mid_1608_);
v___x_1612_ = lean_array_fget_borrowed(v___y_1610_, v_hi_1593_);
v___x_1613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_dec(v_mid_1608_);
v___y_1595_ = v___y_1610_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_array_fswap(v___y_1610_, v_mid_1608_, v_hi_1593_);
lean_dec(v_mid_1608_);
v___y_1595_ = v___x_1614_;
goto v___jp_1594_;
}
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = lean_array_fget_borrowed(v___y_1616_, v_hi_1593_);
v___x_1618_ = lean_array_fget_borrowed(v___y_1616_, v_lo_1592_);
v___x_1619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
v___y_1610_ = v___y_1616_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_array_fswap(v___y_1616_, v_lo_1592_, v_hi_1593_);
v___y_1610_ = v___x_1620_;
goto v___jp_1609_;
}
}
}
v___jp_1594_:
{
lean_object* v_pivot_1596_; lean_object* v___x_1597_; lean_object* v_fst_1598_; lean_object* v_snd_1599_; uint8_t v___x_1600_; 
v_pivot_1596_ = lean_array_fget(v___y_1595_, v_hi_1593_);
lean_inc_n(v_lo_1592_, 2);
v___x_1597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1593_, v_pivot_1596_, v___y_1595_, v_lo_1592_, v_lo_1592_);
lean_dec(v_pivot_1596_);
v_fst_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_fst_1598_);
v_snd_1599_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_snd_1599_);
lean_dec_ref(v___x_1597_);
v___x_1600_ = lean_nat_dec_le(v_hi_1593_, v_fst_1598_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1590_, v_snd_1599_, v_lo_1592_, v_fst_1598_);
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_add(v_fst_1598_, v___x_1602_);
lean_dec(v_fst_1598_);
v_as_1591_ = v___x_1601_;
v_lo_1592_ = v___x_1603_;
goto _start;
}
else
{
lean_dec(v_fst_1598_);
lean_dec(v_lo_1592_);
return v_snd_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_1625_, lean_object* v_as_1626_, lean_object* v_lo_1627_, lean_object* v_hi_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1625_, v_as_1626_, v_lo_1627_, v_hi_1628_);
lean_dec(v_hi_1628_);
lean_dec(v_n_1625_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1632_, lean_object* v_s_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___y_1640_; lean_object* v___y_1641_; uint8_t v___x_1644_; 
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1637_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1633_);
v___x_1638_ = lean_array_get_size(v___x_1637_);
v___x_1644_ = lean_nat_dec_eq(v___x_1638_, v___x_1635_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___y_1648_; uint8_t v___x_1650_; 
v___x_1645_ = lean_unsigned_to_nat(1u);
v___x_1646_ = lean_nat_sub(v___x_1638_, v___x_1645_);
v___x_1650_ = lean_nat_dec_le(v___x_1635_, v___x_1646_);
if (v___x_1650_ == 0)
{
lean_inc(v___x_1646_);
v___y_1648_ = v___x_1646_;
goto v___jp_1647_;
}
else
{
v___y_1648_ = v___x_1635_;
goto v___jp_1647_;
}
v___jp_1647_:
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_nat_dec_le(v___y_1648_, v___x_1646_);
if (v___x_1649_ == 0)
{
lean_dec(v___x_1646_);
lean_inc(v___y_1648_);
v___y_1640_ = v___y_1648_;
v___y_1641_ = v___y_1648_;
goto v___jp_1639_;
}
else
{
v___y_1640_ = v___y_1648_;
v___y_1641_ = v___x_1646_;
goto v___jp_1639_;
}
}
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1636_);
lean_ctor_set(v___x_1651_, 1, v___x_1636_);
lean_ctor_set(v___x_1651_, 2, v___x_1637_);
return v___x_1651_;
}
v___jp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1638_, v___x_1637_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
v___x_1643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1636_);
lean_ctor_set(v___x_1643_, 1, v___x_1636_);
lean_ctor_set(v___x_1643_, 2, v___x_1642_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1652_, lean_object* v_s_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1652_, v_s_1653_, v_x_1654_);
lean_dec(v_x_1654_);
lean_dec_ref(v_s_1653_);
lean_dec_ref(v_x_1652_);
return v_res_1655_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1656_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1661_);
lean_dec_ref(v_x_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v_ks_1667_; lean_object* v_vs_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1692_; 
v_ks_1667_ = lean_ctor_get(v_x_1663_, 0);
v_vs_1668_ = lean_ctor_get(v_x_1663_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1670_ = v_x_1663_;
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_vs_1668_);
lean_inc(v_ks_1667_);
lean_dec(v_x_1663_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = lean_array_get_size(v_ks_1667_);
v___x_1673_ = lean_nat_dec_lt(v_x_1664_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_dec(v_x_1664_);
v___x_1674_ = lean_array_push(v_ks_1667_, v_x_1665_);
v___x_1675_ = lean_array_push(v_vs_1668_, v_x_1666_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1675_);
lean_ctor_set(v___x_1670_, 0, v___x_1674_);
v___x_1677_ = v___x_1670_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
else
{
lean_object* v_k_x27_1679_; uint8_t v___x_1680_; 
v_k_x27_1679_ = lean_array_fget_borrowed(v_ks_1667_, v_x_1664_);
v___x_1680_ = lean_name_eq(v_x_1665_, v_k_x27_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1682_; 
if (v_isShared_1671_ == 0)
{
v___x_1682_ = v___x_1670_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_ks_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_vs_1668_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_add(v_x_1664_, v___x_1683_);
lean_dec(v_x_1664_);
v_x_1663_ = v___x_1682_;
v_x_1664_ = v___x_1684_;
goto _start;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1687_ = lean_array_fset(v_ks_1667_, v_x_1664_, v_x_1665_);
v___x_1688_ = lean_array_fset(v_vs_1668_, v_x_1664_, v_x_1666_);
lean_dec(v_x_1664_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1688_);
lean_ctor_set(v___x_1670_, 0, v___x_1687_);
v___x_1690_ = v___x_1670_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_n_1693_, lean_object* v_k_1694_, lean_object* v_v_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_n_1693_, v___x_1696_, v_k_1694_, v_v_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_x_1699_, size_t v_x_1700_, size_t v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
lean_object* v_es_1704_; size_t v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; lean_object* v_j_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_es_1704_ = lean_ctor_get(v_x_1699_, 0);
v___x_1705_ = ((size_t)5ULL);
v___x_1706_ = ((size_t)1ULL);
v___x_1707_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1708_ = lean_usize_land(v_x_1700_, v___x_1707_);
v_j_1709_ = lean_usize_to_nat(v___x_1708_);
v___x_1710_ = lean_array_get_size(v_es_1704_);
v___x_1711_ = lean_nat_dec_lt(v_j_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_dec(v_j_1709_);
lean_dec(v_x_1703_);
lean_dec(v_x_1702_);
return v_x_1699_;
}
else
{
lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1748_; 
lean_inc_ref(v_es_1704_);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1699_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v_x_1699_, 0);
lean_dec(v_unused_1749_);
v___x_1713_ = v_x_1699_;
v_isShared_1714_ = v_isSharedCheck_1748_;
goto v_resetjp_1712_;
}
else
{
lean_dec(v_x_1699_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1748_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_v_1715_; lean_object* v___x_1716_; lean_object* v_xs_x27_1717_; lean_object* v___y_1719_; 
v_v_1715_ = lean_array_fget(v_es_1704_, v_j_1709_);
v___x_1716_ = lean_box(0);
v_xs_x27_1717_ = lean_array_fset(v_es_1704_, v_j_1709_, v___x_1716_);
switch(lean_obj_tag(v_v_1715_))
{
case 0:
{
lean_object* v_key_1724_; lean_object* v_val_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1735_; 
v_key_1724_ = lean_ctor_get(v_v_1715_, 0);
v_val_1725_ = lean_ctor_get(v_v_1715_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_v_1715_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1727_ = v_v_1715_;
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_val_1725_);
lean_inc(v_key_1724_);
lean_dec(v_v_1715_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_name_eq(v_x_1702_, v_key_1724_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_del_object(v___x_1727_);
v___x_1730_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1724_, v_val_1725_, v_x_1702_, v_x_1703_);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
v___y_1719_ = v___x_1731_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1733_; 
lean_dec(v_val_1725_);
lean_dec(v_key_1724_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v_x_1703_);
lean_ctor_set(v___x_1727_, 0, v_x_1702_);
v___x_1733_ = v___x_1727_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_x_1702_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_x_1703_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
v___y_1719_ = v___x_1733_;
goto v___jp_1718_;
}
}
}
}
case 1:
{
lean_object* v_node_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1746_; 
v_node_1736_ = lean_ctor_get(v_v_1715_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_v_1715_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1738_ = v_v_1715_;
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_node_1736_);
lean_dec(v_v_1715_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1740_ = lean_usize_shift_right(v_x_1700_, v___x_1705_);
v___x_1741_ = lean_usize_add(v_x_1701_, v___x_1706_);
v___x_1742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_node_1736_, v___x_1740_, v___x_1741_, v_x_1702_, v_x_1703_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1742_);
v___x_1744_ = v___x_1738_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v___y_1719_ = v___x_1744_;
goto v___jp_1718_;
}
}
}
default: 
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_x_1702_);
lean_ctor_set(v___x_1747_, 1, v_x_1703_);
v___y_1719_ = v___x_1747_;
goto v___jp_1718_;
}
}
v___jp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = lean_array_fset(v_xs_x27_1717_, v_j_1709_, v___y_1719_);
lean_dec(v_j_1709_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1720_);
v___x_1722_ = v___x_1713_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
else
{
lean_object* v_ks_1750_; lean_object* v_vs_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1771_; 
v_ks_1750_ = lean_ctor_get(v_x_1699_, 0);
v_vs_1751_ = lean_ctor_get(v_x_1699_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_x_1699_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1753_ = v_x_1699_;
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_vs_1751_);
lean_inc(v_ks_1750_);
lean_dec(v_x_1699_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_ks_1750_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_vs_1751_);
v___x_1756_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v_newNode_1757_; uint8_t v___y_1759_; size_t v___x_1765_; uint8_t v___x_1766_; 
v_newNode_1757_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v___x_1756_, v_x_1702_, v_x_1703_);
v___x_1765_ = ((size_t)7ULL);
v___x_1766_ = lean_usize_dec_le(v___x_1765_, v_x_1701_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1757_);
v___x_1768_ = lean_unsigned_to_nat(4u);
v___x_1769_ = lean_nat_dec_lt(v___x_1767_, v___x_1768_);
lean_dec(v___x_1767_);
v___y_1759_ = v___x_1769_;
goto v___jp_1758_;
}
else
{
v___y_1759_ = v___x_1766_;
goto v___jp_1758_;
}
v___jp_1758_:
{
if (v___y_1759_ == 0)
{
lean_object* v_ks_1760_; lean_object* v_vs_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_ks_1760_ = lean_ctor_get(v_newNode_1757_, 0);
lean_inc_ref(v_ks_1760_);
v_vs_1761_ = lean_ctor_get(v_newNode_1757_, 1);
lean_inc_ref(v_vs_1761_);
lean_dec_ref(v_newNode_1757_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0);
v___x_1764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_x_1701_, v_ks_1760_, v_vs_1761_, v___x_1762_, v___x_1763_);
lean_dec_ref(v_vs_1761_);
lean_dec_ref(v_ks_1760_);
return v___x_1764_;
}
else
{
return v_newNode_1757_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t v_depth_1772_, lean_object* v_keys_1773_, lean_object* v_vals_1774_, lean_object* v_i_1775_, lean_object* v_entries_1776_){
_start:
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_array_get_size(v_keys_1773_);
v___x_1778_ = lean_nat_dec_lt(v_i_1775_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec(v_i_1775_);
return v_entries_1776_;
}
else
{
lean_object* v_k_1779_; lean_object* v_v_1780_; uint64_t v___y_1782_; 
v_k_1779_ = lean_array_fget_borrowed(v_keys_1773_, v_i_1775_);
v_v_1780_ = lean_array_fget_borrowed(v_vals_1774_, v_i_1775_);
if (lean_obj_tag(v_k_1779_) == 0)
{
uint64_t v___x_1793_; 
v___x_1793_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1782_ = v___x_1793_;
goto v___jp_1781_;
}
else
{
uint64_t v_hash_1794_; 
v_hash_1794_ = lean_ctor_get_uint64(v_k_1779_, sizeof(void*)*2);
v___y_1782_ = v_hash_1794_;
goto v___jp_1781_;
}
v___jp_1781_:
{
size_t v_h_1783_; size_t v___x_1784_; lean_object* v___x_1785_; size_t v___x_1786_; size_t v___x_1787_; size_t v___x_1788_; size_t v_h_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_h_1783_ = lean_uint64_to_usize(v___y_1782_);
v___x_1784_ = ((size_t)5ULL);
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = ((size_t)1ULL);
v___x_1787_ = lean_usize_sub(v_depth_1772_, v___x_1786_);
v___x_1788_ = lean_usize_mul(v___x_1784_, v___x_1787_);
v_h_1789_ = lean_usize_shift_right(v_h_1783_, v___x_1788_);
v___x_1790_ = lean_nat_add(v_i_1775_, v___x_1785_);
lean_dec(v_i_1775_);
lean_inc(v_v_1780_);
lean_inc(v_k_1779_);
v___x_1791_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_entries_1776_, v_h_1789_, v_depth_1772_, v_k_1779_, v_v_1780_);
v_i_1775_ = v___x_1790_;
v_entries_1776_ = v___x_1791_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_1795_, lean_object* v_keys_1796_, lean_object* v_vals_1797_, lean_object* v_i_1798_, lean_object* v_entries_1799_){
_start:
{
size_t v_depth_boxed_1800_; lean_object* v_res_1801_; 
v_depth_boxed_1800_ = lean_unbox_usize(v_depth_1795_);
lean_dec(v_depth_1795_);
v_res_1801_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_boxed_1800_, v_keys_1796_, v_vals_1797_, v_i_1798_, v_entries_1799_);
lean_dec_ref(v_vals_1797_);
lean_dec_ref(v_keys_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_x_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
size_t v_x_1604__boxed_1807_; size_t v_x_1605__boxed_1808_; lean_object* v_res_1809_; 
v_x_1604__boxed_1807_ = lean_unbox_usize(v_x_1803_);
lean_dec(v_x_1803_);
v_x_1605__boxed_1808_ = lean_unbox_usize(v_x_1804_);
lean_dec(v_x_1804_);
v_res_1809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1802_, v_x_1604__boxed_1807_, v_x_1605__boxed_1808_, v_x_1805_, v_x_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
uint64_t v___y_1814_; 
if (lean_obj_tag(v_x_1811_) == 0)
{
uint64_t v___x_1818_; 
v___x_1818_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1814_ = v___x_1818_;
goto v___jp_1813_;
}
else
{
uint64_t v_hash_1819_; 
v_hash_1819_ = lean_ctor_get_uint64(v_x_1811_, sizeof(void*)*2);
v___y_1814_ = v_hash_1819_;
goto v___jp_1813_;
}
v___jp_1813_:
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_uint64_to_usize(v___y_1814_);
v___x_1816_ = ((size_t)1ULL);
v___x_1817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1810_, v___x_1815_, v___x_1816_, v_x_1811_, v_x_1812_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v_fst_1822_; lean_object* v_snd_1823_; lean_object* v___x_1824_; 
v_fst_1822_ = lean_ctor_get(v_x_1821_, 0);
lean_inc(v_fst_1822_);
v_snd_1823_ = lean_ctor_get(v_x_1821_, 1);
lean_inc(v_snd_1823_);
lean_dec_ref(v_x_1821_);
v___x_1824_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1820_, v_fst_1822_, v_snd_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1858_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1860_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1862_, v_x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
uint8_t v_res_1868_; lean_object* v_r_1869_; 
v_res_1868_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1865_, v_x_1866_, v_x_1867_);
lean_dec(v_x_1867_);
lean_dec_ref(v_x_1866_);
v_r_1869_ = lean_box(v_res_1868_);
return v_r_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1870_, lean_object* v_m_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1873_, lean_object* v_m_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1873_, v_m_1874_);
lean_dec_ref(v_m_1874_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1876_, lean_object* v_as_1877_, lean_object* v_lo_1878_, lean_object* v_hi_1879_, lean_object* v_w_1880_, lean_object* v_hlo_1881_, lean_object* v_hhi_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1876_, v_as_1877_, v_lo_1878_, v_hi_1879_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1884_, lean_object* v_as_1885_, lean_object* v_lo_1886_, lean_object* v_hi_1887_, lean_object* v_w_1888_, lean_object* v_hlo_1889_, lean_object* v_hhi_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1884_, v_as_1885_, v_lo_1886_, v_hi_1887_, v_w_1888_, v_hlo_1889_, v_hhi_1890_);
lean_dec(v_hi_1887_);
lean_dec(v_n_1884_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1893_, v_x_1894_, v_x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1897_, lean_object* v_x_1898_, size_t v_x_1899_, lean_object* v_x_1900_){
_start:
{
uint8_t v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1898_, v_x_1899_, v_x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
size_t v_x_1911__boxed_1906_; uint8_t v_res_1907_; lean_object* v_r_1908_; 
v_x_1911__boxed_1906_ = lean_unbox_usize(v_x_1904_);
lean_dec(v_x_1904_);
v_res_1907_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1902_, v_x_1903_, v_x_1911__boxed_1906_, v_x_1905_);
lean_dec(v_x_1905_);
lean_dec_ref(v_x_1903_);
v_r_1908_ = lean_box(v_res_1907_);
return v_r_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1909_, lean_object* v_00_u03b2_1910_, lean_object* v_map_1911_, lean_object* v_f_1912_, lean_object* v_init_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1911_, v_f_1912_, v_init_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_map_1917_, lean_object* v_f_1918_, lean_object* v_init_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1915_, v_00_u03b2_1916_, v_map_1917_, v_f_1918_, v_init_1919_);
lean_dec_ref(v_map_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_n_1921_, lean_object* v_lo_1922_, lean_object* v_hi_1923_, lean_object* v_hhi_1924_, lean_object* v_pivot_1925_, lean_object* v_as_1926_, lean_object* v_i_1927_, lean_object* v_k_1928_, lean_object* v_ilo_1929_, lean_object* v_ik_1930_, lean_object* v_w_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1923_, v_pivot_1925_, v_as_1926_, v_i_1927_, v_k_1928_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_n_1933_, lean_object* v_lo_1934_, lean_object* v_hi_1935_, lean_object* v_hhi_1936_, lean_object* v_pivot_1937_, lean_object* v_as_1938_, lean_object* v_i_1939_, lean_object* v_k_1940_, lean_object* v_ilo_1941_, lean_object* v_ik_1942_, lean_object* v_w_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(v_n_1933_, v_lo_1934_, v_hi_1935_, v_hhi_1936_, v_pivot_1937_, v_as_1938_, v_i_1939_, v_k_1940_, v_ilo_1941_, v_ik_1942_, v_w_1943_);
lean_dec_ref(v_pivot_1937_);
lean_dec(v_hi_1935_);
lean_dec(v_lo_1934_);
lean_dec(v_n_1933_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1945_, lean_object* v_x_1946_, size_t v_x_1947_, size_t v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1946_, v_x_1947_, v_x_1948_, v_x_1949_, v_x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1952_, lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_){
_start:
{
size_t v_x_1926__boxed_1958_; size_t v_x_1927__boxed_1959_; lean_object* v_res_1960_; 
v_x_1926__boxed_1958_ = lean_unbox_usize(v_x_1954_);
lean_dec(v_x_1954_);
v_x_1927__boxed_1959_ = lean_unbox_usize(v_x_1955_);
lean_dec(v_x_1955_);
v_res_1960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1952_, v_x_1953_, v_x_1926__boxed_1958_, v_x_1927__boxed_1959_, v_x_1956_, v_x_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1961_, lean_object* v_keys_1962_, lean_object* v_vals_1963_, lean_object* v_heq_1964_, lean_object* v_i_1965_, lean_object* v_k_1966_){
_start:
{
uint8_t v___x_1967_; 
v___x_1967_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1962_, v_i_1965_, v_k_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1968_, lean_object* v_keys_1969_, lean_object* v_vals_1970_, lean_object* v_heq_1971_, lean_object* v_i_1972_, lean_object* v_k_1973_){
_start:
{
uint8_t v_res_1974_; lean_object* v_r_1975_; 
v_res_1974_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1968_, v_keys_1969_, v_vals_1970_, v_heq_1971_, v_i_1972_, v_k_1973_);
lean_dec(v_k_1973_);
lean_dec_ref(v_vals_1970_);
lean_dec_ref(v_keys_1969_);
v_r_1975_ = lean_box(v_res_1974_);
return v_r_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1976_, lean_object* v_f_1977_, lean_object* v_init_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1977_, v_map_1976_, v_init_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1980_, lean_object* v_f_1981_, lean_object* v_init_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1980_, v_f_1981_, v_init_1982_);
lean_dec_ref(v_map_1980_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1984_, lean_object* v_00_u03b2_1985_, lean_object* v_map_1986_, lean_object* v_f_1987_, lean_object* v_init_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1987_, v_map_1986_, v_init_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1990_, lean_object* v_00_u03b2_1991_, lean_object* v_map_1992_, lean_object* v_f_1993_, lean_object* v_init_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1990_, v_00_u03b2_1991_, v_map_1992_, v_f_1993_, v_init_1994_);
lean_dec_ref(v_map_1992_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1996_, lean_object* v_n_1997_, lean_object* v_k_1998_, lean_object* v_v_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_n_1997_, v_k_1998_, v_v_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object* v_00_u03b2_2001_, size_t v_depth_2002_, lean_object* v_keys_2003_, lean_object* v_vals_2004_, lean_object* v_heq_2005_, lean_object* v_i_2006_, lean_object* v_entries_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_2002_, v_keys_2003_, v_vals_2004_, v_i_2006_, v_entries_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2009_, lean_object* v_depth_2010_, lean_object* v_keys_2011_, lean_object* v_vals_2012_, lean_object* v_heq_2013_, lean_object* v_i_2014_, lean_object* v_entries_2015_){
_start:
{
size_t v_depth_boxed_2016_; lean_object* v_res_2017_; 
v_depth_boxed_2016_ = lean_unbox_usize(v_depth_2010_);
lean_dec(v_depth_2010_);
v_res_2017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(v_00_u03b2_2009_, v_depth_boxed_2016_, v_keys_2011_, v_vals_2012_, v_heq_2013_, v_i_2014_, v_entries_2015_);
lean_dec_ref(v_vals_2012_);
lean_dec_ref(v_keys_2011_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2018_, lean_object* v_00_u03b1_2019_, lean_object* v_00_u03b2_2020_, lean_object* v_f_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2021_, v_x_2022_, v_x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2025_, lean_object* v_00_u03b1_2026_, lean_object* v_00_u03b2_2027_, lean_object* v_f_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_2025_, v_00_u03b1_2026_, v_00_u03b2_2027_, v_f_2028_, v_x_2029_, v_x_2030_);
lean_dec_ref(v_x_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_x_2033_, v_x_2034_, v_x_2035_, v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_2038_, lean_object* v_00_u03b2_2039_, lean_object* v_00_u03c3_2040_, lean_object* v_f_2041_, lean_object* v_as_2042_, size_t v_i_2043_, size_t v_stop_2044_, lean_object* v_b_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_2041_, v_as_2042_, v_i_2043_, v_stop_2044_, v_b_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_00_u03c3_2049_, lean_object* v_f_2050_, lean_object* v_as_2051_, lean_object* v_i_2052_, lean_object* v_stop_2053_, lean_object* v_b_2054_){
_start:
{
size_t v_i_boxed_2055_; size_t v_stop_boxed_2056_; lean_object* v_res_2057_; 
v_i_boxed_2055_ = lean_unbox_usize(v_i_2052_);
lean_dec(v_i_2052_);
v_stop_boxed_2056_ = lean_unbox_usize(v_stop_2053_);
lean_dec(v_stop_2053_);
v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_2047_, v_00_u03b2_2048_, v_00_u03c3_2049_, v_f_2050_, v_as_2051_, v_i_boxed_2055_, v_stop_boxed_2056_, v_b_2054_);
lean_dec_ref(v_as_2051_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03c3_2058_, lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_f_2061_, lean_object* v_keys_2062_, lean_object* v_vals_2063_, lean_object* v_heq_2064_, lean_object* v_i_2065_, lean_object* v_acc_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_2061_, v_keys_2062_, v_vals_2063_, v_i_2065_, v_acc_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03c3_2068_, lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_f_2071_, lean_object* v_keys_2072_, lean_object* v_vals_2073_, lean_object* v_heq_2074_, lean_object* v_i_2075_, lean_object* v_acc_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(v_00_u03c3_2068_, v_00_u03b1_2069_, v_00_u03b2_2070_, v_f_2071_, v_keys_2072_, v_vals_2073_, v_heq_2074_, v_i_2075_, v_acc_2076_);
lean_dec_ref(v_vals_2073_);
lean_dec_ref(v_keys_2072_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2078_, lean_object* v_fid_2079_, lean_object* v_v_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v_toEnvExtension_2082_; lean_object* v_asyncMode_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2081_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2082_ = lean_ctor_get(v___x_2081_, 0);
v_asyncMode_2083_ = lean_ctor_get(v_toEnvExtension_2082_, 2);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_fid_2079_);
lean_ctor_set(v___x_2084_, 1, v_v_2080_);
v___x_2085_ = lean_box(0);
v___x_2086_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2081_, v_env_2078_, v___x_2084_, v_asyncMode_2083_, v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2087_, lean_object* v_vals_2088_, lean_object* v_i_2089_, lean_object* v_k_2090_){
_start:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = lean_array_get_size(v_keys_2087_);
v___x_2092_ = lean_nat_dec_lt(v_i_2089_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec(v_i_2089_);
v___x_2093_ = lean_box(0);
return v___x_2093_;
}
else
{
lean_object* v_k_x27_2094_; uint8_t v___x_2095_; 
v_k_x27_2094_ = lean_array_fget_borrowed(v_keys_2087_, v_i_2089_);
v___x_2095_ = lean_name_eq(v_k_2090_, v_k_x27_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_unsigned_to_nat(1u);
v___x_2097_ = lean_nat_add(v_i_2089_, v___x_2096_);
lean_dec(v_i_2089_);
v_i_2089_ = v___x_2097_;
goto _start;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_array_fget_borrowed(v_vals_2088_, v_i_2089_);
lean_dec(v_i_2089_);
lean_inc(v___x_2099_);
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2101_, lean_object* v_vals_2102_, lean_object* v_i_2103_, lean_object* v_k_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2101_, v_vals_2102_, v_i_2103_, v_k_2104_);
lean_dec(v_k_2104_);
lean_dec_ref(v_vals_2102_);
lean_dec_ref(v_keys_2101_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2106_, size_t v_x_2107_, lean_object* v_x_2108_){
_start:
{
if (lean_obj_tag(v_x_2106_) == 0)
{
lean_object* v_es_2109_; lean_object* v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v_j_2114_; lean_object* v___x_2115_; 
v_es_2109_ = lean_ctor_get(v_x_2106_, 0);
v___x_2110_ = lean_box(2);
v___x_2111_ = ((size_t)5ULL);
v___x_2112_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_2113_ = lean_usize_land(v_x_2107_, v___x_2112_);
v_j_2114_ = lean_usize_to_nat(v___x_2113_);
v___x_2115_ = lean_array_get_borrowed(v___x_2110_, v_es_2109_, v_j_2114_);
lean_dec(v_j_2114_);
switch(lean_obj_tag(v___x_2115_))
{
case 0:
{
lean_object* v_key_2116_; lean_object* v_val_2117_; uint8_t v___x_2118_; 
v_key_2116_ = lean_ctor_get(v___x_2115_, 0);
v_val_2117_ = lean_ctor_get(v___x_2115_, 1);
v___x_2118_ = lean_name_eq(v_x_2108_, v_key_2116_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_box(0);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; 
lean_inc(v_val_2117_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_val_2117_);
return v___x_2120_;
}
}
case 1:
{
lean_object* v_node_2121_; size_t v___x_2122_; 
v_node_2121_ = lean_ctor_get(v___x_2115_, 0);
v___x_2122_ = lean_usize_shift_right(v_x_2107_, v___x_2111_);
v_x_2106_ = v_node_2121_;
v_x_2107_ = v___x_2122_;
goto _start;
}
default: 
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
}
}
else
{
lean_object* v_ks_2125_; lean_object* v_vs_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_ks_2125_ = lean_ctor_get(v_x_2106_, 0);
v_vs_2126_ = lean_ctor_get(v_x_2106_, 1);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2125_, v_vs_2126_, v___x_2127_, v_x_2108_);
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
size_t v_x_396__boxed_2132_; lean_object* v_res_2133_; 
v_x_396__boxed_2132_ = lean_unbox_usize(v_x_2130_);
lean_dec(v_x_2130_);
v_res_2133_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2129_, v_x_396__boxed_2132_, v_x_2131_);
lean_dec(v_x_2131_);
lean_dec_ref(v_x_2129_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
uint64_t v___y_2137_; 
if (lean_obj_tag(v_x_2135_) == 0)
{
uint64_t v___x_2140_; 
v___x_2140_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_2137_ = v___x_2140_;
goto v___jp_2136_;
}
else
{
uint64_t v_hash_2141_; 
v_hash_2141_ = lean_ctor_get_uint64(v_x_2135_, sizeof(void*)*2);
v___y_2137_ = v_hash_2141_;
goto v___jp_2136_;
}
v___jp_2136_:
{
size_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_uint64_to_usize(v___y_2137_);
v___x_2139_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2134_, v___x_2138_, v_x_2135_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2142_, v_x_2143_);
lean_dec(v_x_2143_);
lean_dec_ref(v_x_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2145_, lean_object* v_k_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_m_2151_; lean_object* v_a_2152_; uint8_t v___x_2153_; 
v___x_2149_ = lean_nat_add(v_x_2147_, v_x_2148_);
v___x_2150_ = lean_unsigned_to_nat(1u);
v_m_2151_ = lean_nat_shiftr(v___x_2149_, v___x_2150_);
lean_dec(v___x_2149_);
v_a_2152_ = lean_array_fget_borrowed(v_as_2145_, v_m_2151_);
v___x_2153_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2152_, v_k_2146_);
if (v___x_2153_ == 0)
{
uint8_t v___x_2154_; 
lean_dec(v_x_2148_);
v___x_2154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2146_, v_a_2152_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_dec(v_m_2151_);
lean_dec(v_x_2147_);
lean_inc(v_a_2152_);
v___x_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_a_2152_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = lean_nat_dec_eq(v_m_2151_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = lean_nat_sub(v_m_2151_, v___x_2150_);
lean_dec(v_m_2151_);
v___x_2159_ = lean_nat_dec_lt(v___x_2158_, v_x_2147_);
if (v___x_2159_ == 0)
{
v_x_2148_ = v___x_2158_;
goto _start;
}
else
{
lean_object* v___x_2161_; 
lean_dec(v___x_2158_);
lean_dec(v_x_2147_);
v___x_2161_ = lean_box(0);
return v___x_2161_;
}
}
else
{
lean_object* v___x_2162_; 
lean_dec(v_m_2151_);
lean_dec(v_x_2147_);
v___x_2162_ = lean_box(0);
return v___x_2162_;
}
}
}
else
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
lean_dec(v_x_2147_);
v___x_2163_ = lean_nat_add(v_m_2151_, v___x_2150_);
lean_dec(v_m_2151_);
v___x_2164_ = lean_nat_dec_le(v___x_2163_, v_x_2148_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_dec(v___x_2163_);
lean_dec(v_x_2148_);
v___x_2165_ = lean_box(0);
return v___x_2165_;
}
else
{
v_x_2147_ = v___x_2163_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2167_, lean_object* v_k_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2167_, v_k_2168_, v_x_2169_, v_x_2170_);
lean_dec_ref(v_k_2168_);
lean_dec_ref(v_as_2167_);
return v_res_2171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2175_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2176_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2180_, lean_object* v_fid_2181_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2191_; 
v___x_2182_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2183_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2191_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2180_, v_fid_2181_);
if (lean_obj_tag(v___x_2191_) == 0)
{
goto v___jp_2184_;
}
else
{
lean_object* v_val_2192_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2214_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_2182_, v___x_2183_, v_env_2180_, v_val_2192_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_array_get_size(v___x_2214_);
v___x_2217_ = lean_nat_dec_lt(v___x_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_dec_ref(v___x_2214_);
goto v___jp_2193_;
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_sub(v___x_2216_, v___x_2218_);
v___x_2220_ = lean_nat_dec_le(v___x_2215_, v___x_2219_);
if (v___x_2220_ == 0)
{
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2214_);
goto v___jp_2193_;
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_box(0);
lean_inc(v_fid_2181_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_fid_2181_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2214_, v___x_2222_, v___x_2215_, v___x_2219_);
lean_dec_ref_known(v___x_2222_, 2);
lean_dec_ref(v___x_2214_);
if (lean_obj_tag(v___x_2223_) == 0)
{
goto v___jp_2193_;
}
else
{
lean_object* v_val_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_val_2192_);
lean_dec(v_fid_2181_);
lean_dec_ref(v_env_2180_);
v_val_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_val_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v_snd_2228_; lean_object* v___x_2230_; 
v_snd_2228_ = lean_ctor_get(v_val_2224_, 1);
lean_inc(v_snd_2228_);
lean_dec(v_val_2224_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v_snd_2228_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_snd_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
v___jp_2193_:
{
uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2194_ = 0;
v___x_2195_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2182_, v___x_2183_, v_env_2180_, v_val_2192_, v___x_2194_);
lean_dec(v_val_2192_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_array_get_size(v___x_2195_);
v___x_2198_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_dec_ref(v___x_2195_);
goto v___jp_2184_;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_sub(v___x_2197_, v___x_2199_);
v___x_2201_ = lean_nat_dec_le(v___x_2196_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_dec(v___x_2200_);
lean_dec_ref(v___x_2195_);
goto v___jp_2184_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_box(0);
lean_inc(v_fid_2181_);
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_fid_2181_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2195_, v___x_2203_, v___x_2196_, v___x_2200_);
lean_dec_ref_known(v___x_2203_, 2);
lean_dec_ref(v___x_2195_);
if (lean_obj_tag(v___x_2204_) == 0)
{
goto v___jp_2184_;
}
else
{
lean_object* v_val_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_fid_2181_);
lean_dec_ref(v_env_2180_);
v_val_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_val_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_snd_2209_; lean_object* v___x_2211_; 
v_snd_2209_ = lean_ctor_get(v_val_2205_, 1);
lean_inc(v_snd_2209_);
lean_dec(v_val_2205_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v_snd_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_snd_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
}
v___jp_2184_:
{
lean_object* v_toEnvExtension_2185_; lean_object* v_asyncMode_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v_snd_2189_; lean_object* v___x_2190_; 
v_toEnvExtension_2185_ = lean_ctor_get(v___x_2183_, 0);
v_asyncMode_2186_ = lean_ctor_get(v_toEnvExtension_2185_, 2);
v___x_2187_ = lean_box(0);
v___x_2188_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2182_, v___x_2183_, v_env_2180_, v_asyncMode_2186_, v___x_2187_);
v_snd_2189_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_snd_2189_);
lean_dec(v___x_2188_);
v___x_2190_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2189_, v_fid_2181_);
lean_dec(v_fid_2181_);
lean_dec(v_snd_2189_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2234_, v_x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2237_, v_x_2238_, v_x_2239_);
lean_dec(v_x_2239_);
lean_dec_ref(v_x_2238_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2241_, lean_object* v_k_2242_, lean_object* v_x_2243_, lean_object* v_x_2244_, lean_object* v_x_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2241_, v_k_2242_, v_x_2243_, v_x_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2247_, lean_object* v_k_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2247_, v_k_2248_, v_x_2249_, v_x_2250_, v_x_2251_);
lean_dec_ref(v_k_2248_);
lean_dec_ref(v_as_2247_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2253_, lean_object* v_x_2254_, size_t v_x_2255_, lean_object* v_x_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2254_, v_x_2255_, v_x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2258_, lean_object* v_x_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
size_t v_x_637__boxed_2262_; lean_object* v_res_2263_; 
v_x_637__boxed_2262_ = lean_unbox_usize(v_x_2260_);
lean_dec(v_x_2260_);
v_res_2263_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2258_, v_x_2259_, v_x_637__boxed_2262_, v_x_2261_);
lean_dec(v_x_2261_);
lean_dec_ref(v_x_2259_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2264_, lean_object* v_keys_2265_, lean_object* v_vals_2266_, lean_object* v_heq_2267_, lean_object* v_i_2268_, lean_object* v_k_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2265_, v_vals_2266_, v_i_2268_, v_k_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2271_, lean_object* v_keys_2272_, lean_object* v_vals_2273_, lean_object* v_heq_2274_, lean_object* v_i_2275_, lean_object* v_k_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2271_, v_keys_2272_, v_vals_2273_, v_heq_2274_, v_i_2275_, v_k_2276_);
lean_dec(v_k_2276_);
lean_dec_ref(v_vals_2273_);
lean_dec_ref(v_keys_2272_);
return v_res_2277_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2281_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2282_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; lean_object* v_assignments_2287_; lean_object* v_currFnIdx_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2286_ = lean_st_ref_get(v_a_2284_);
v_assignments_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc_ref(v_assignments_2287_);
lean_dec(v___x_2286_);
v_currFnIdx_2288_ = lean_ctor_get(v_a_2283_, 1);
v___x_2289_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2290_ = lean_array_get(v___x_2289_, v_assignments_2287_, v_currFnIdx_2288_);
lean_dec_ref(v_assignments_2287_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2296_, v_a_2297_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v_funVals_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = lean_st_ref_get(v_a_2313_);
v_funVals_2316_ = lean_ctor_get(v___x_2315_, 1);
lean_inc_ref(v_funVals_2316_);
lean_dec(v___x_2315_);
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_array_get(v___x_2317_, v_funVals_2316_, v_funIdx_2312_);
lean_dec_ref(v_funVals_2316_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec(v_funIdx_2320_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2324_, v_a_2326_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_funIdx_2333_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2342_, lean_object* v_as_2343_, lean_object* v_j_2344_){
_start:
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = lean_array_get_size(v_as_2343_);
v___x_2346_ = lean_nat_dec_lt(v_j_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; 
lean_dec(v_j_2344_);
v___x_2347_ = lean_box(0);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; lean_object* v_toSignature_2349_; lean_object* v_name_2350_; uint8_t v___x_2351_; 
v___x_2348_ = lean_array_fget_borrowed(v_as_2343_, v_j_2344_);
v_toSignature_2349_ = lean_ctor_get(v___x_2348_, 0);
v_name_2350_ = lean_ctor_get(v_toSignature_2349_, 0);
v___x_2351_ = lean_name_eq(v_name_2350_, v_declName_2342_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_nat_add(v_j_2344_, v___x_2352_);
lean_dec(v_j_2344_);
v_j_2344_ = v___x_2353_;
goto _start;
}
else
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_j_2344_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2356_, lean_object* v_as_2357_, lean_object* v_j_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2356_, v_as_2357_, v_j_2358_);
lean_dec_ref(v_as_2357_);
lean_dec(v_declName_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v_decls_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_decls_2364_ = lean_ctor_get(v_a_2361_, 0);
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2360_, v_decls_2364_, v___x_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_box(0);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
else
{
lean_object* v_val_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2385_; 
v_val_2369_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2371_ = v___x_2366_;
v_isShared_2372_ = v_isSharedCheck_2385_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_val_2369_);
lean_dec(v___x_2366_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2385_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2384_; 
v___x_2373_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2369_, v_a_2362_);
lean_dec(v_val_2369_);
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2384_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2384_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v_a_2374_);
v___x_2379_ = v___x_2371_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2379_);
v___x_2381_ = v___x_2376_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_declName_2386_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2391_, v_a_2392_, v_a_2393_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_declName_2400_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v_currFnIdx_2414_; lean_object* v_assignments_2415_; lean_object* v_funVals_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2434_; 
v___x_2413_ = lean_st_ref_take(v_a_2411_);
v_currFnIdx_2414_ = lean_ctor_get(v_a_2410_, 1);
v_assignments_2415_ = lean_ctor_get(v___x_2413_, 0);
v_funVals_2416_ = lean_ctor_get(v___x_2413_, 1);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2418_ = v___x_2413_;
v_isShared_2419_ = v_isSharedCheck_2434_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_funVals_2416_);
lean_inc(v_assignments_2415_);
lean_dec(v___x_2413_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2434_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___y_2422_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2420_ = lean_box(0);
v___x_2428_ = lean_array_get_size(v_assignments_2415_);
v___x_2429_ = lean_nat_dec_lt(v_currFnIdx_2414_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_dec_ref(v_f_2409_);
v___y_2422_ = v_assignments_2415_;
goto v___jp_2421_;
}
else
{
lean_object* v_v_2430_; lean_object* v_xs_x27_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_v_2430_ = lean_array_fget(v_assignments_2415_, v_currFnIdx_2414_);
v_xs_x27_2431_ = lean_array_fset(v_assignments_2415_, v_currFnIdx_2414_, v___x_2420_);
v___x_2432_ = lean_apply_1(v_f_2409_, v_v_2430_);
v___x_2433_ = lean_array_fset(v_xs_x27_2431_, v_currFnIdx_2414_, v___x_2432_);
v___y_2422_ = v___x_2433_;
goto v___jp_2421_;
}
v___jp_2421_:
{
lean_object* v___x_2424_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___y_2422_);
v___x_2424_ = v___x_2418_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___y_2422_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_funVals_2416_);
v___x_2424_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_st_ref_set(v_a_2411_, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2420_);
return v___x_2426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2440_, v_a_2441_, v_a_2442_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2458_, lean_object* v_fallback_2459_, lean_object* v_x_2460_){
_start:
{
if (lean_obj_tag(v_x_2460_) == 0)
{
lean_inc(v_fallback_2459_);
return v_fallback_2459_;
}
else
{
lean_object* v_key_2461_; lean_object* v_value_2462_; lean_object* v_tail_2463_; uint8_t v___x_2464_; 
v_key_2461_ = lean_ctor_get(v_x_2460_, 0);
v_value_2462_ = lean_ctor_get(v_x_2460_, 1);
v_tail_2463_ = lean_ctor_get(v_x_2460_, 2);
v___x_2464_ = l_Lean_instBEqFVarId_beq(v_key_2461_, v_a_2458_);
if (v___x_2464_ == 0)
{
v_x_2460_ = v_tail_2463_;
goto _start;
}
else
{
lean_inc(v_value_2462_);
return v_value_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2466_, lean_object* v_fallback_2467_, lean_object* v_x_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2466_, v_fallback_2467_, v_x_2468_);
lean_dec(v_x_2468_);
lean_dec(v_fallback_2467_);
lean_dec(v_a_2466_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2470_, lean_object* v_a_2471_, lean_object* v_fallback_2472_){
_start:
{
lean_object* v_buckets_2473_; lean_object* v___x_2474_; uint64_t v___x_2475_; uint64_t v___x_2476_; uint64_t v___x_2477_; uint64_t v_fold_2478_; uint64_t v___x_2479_; uint64_t v___x_2480_; uint64_t v___x_2481_; size_t v___x_2482_; size_t v___x_2483_; size_t v___x_2484_; size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v_buckets_2473_ = lean_ctor_get(v_m_2470_, 1);
v___x_2474_ = lean_array_get_size(v_buckets_2473_);
v___x_2475_ = l_Lean_instHashableFVarId_hash(v_a_2471_);
v___x_2476_ = 32ULL;
v___x_2477_ = lean_uint64_shift_right(v___x_2475_, v___x_2476_);
v_fold_2478_ = lean_uint64_xor(v___x_2475_, v___x_2477_);
v___x_2479_ = 16ULL;
v___x_2480_ = lean_uint64_shift_right(v_fold_2478_, v___x_2479_);
v___x_2481_ = lean_uint64_xor(v_fold_2478_, v___x_2480_);
v___x_2482_ = lean_uint64_to_usize(v___x_2481_);
v___x_2483_ = lean_usize_of_nat(v___x_2474_);
v___x_2484_ = ((size_t)1ULL);
v___x_2485_ = lean_usize_sub(v___x_2483_, v___x_2484_);
v___x_2486_ = lean_usize_land(v___x_2482_, v___x_2485_);
v___x_2487_ = lean_array_uget_borrowed(v_buckets_2473_, v___x_2486_);
v___x_2488_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2471_, v_fallback_2472_, v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2489_, lean_object* v_a_2490_, lean_object* v_fallback_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2489_, v_a_2490_, v_fallback_2491_);
lean_dec(v_fallback_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_m_2489_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2507_; 
v___x_2497_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2494_, v_a_2495_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2502_ = lean_box(0);
v___x_2503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2498_, v_var_2493_, v___x_2502_);
lean_dec(v_a_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2503_);
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_var_2508_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2513_, v_a_2514_, v_a_2515_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_var_2522_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2531_, lean_object* v_m_2532_, lean_object* v_a_2533_, lean_object* v_fallback_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2532_, v_a_2533_, v_fallback_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2536_, lean_object* v_m_2537_, lean_object* v_a_2538_, lean_object* v_fallback_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2536_, v_m_2537_, v_a_2538_, v_fallback_2539_);
lean_dec(v_fallback_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_m_2537_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2541_, lean_object* v_a_2542_, lean_object* v_fallback_2543_, lean_object* v_x_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2542_, v_fallback_2543_, v_x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2546_, lean_object* v_a_2547_, lean_object* v_fallback_2548_, lean_object* v_x_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2546_, v_a_2547_, v_fallback_2548_, v_x_2549_);
lean_dec(v_x_2549_);
lean_dec(v_fallback_2548_);
lean_dec(v_a_2547_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
if (lean_obj_tag(v_arg_2551_) == 1)
{
lean_object* v_fvarId_2555_; lean_object* v___x_2556_; 
v_fvarId_2555_ = lean_ctor_get(v_arg_2551_, 0);
v___x_2556_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2555_, v_a_2552_, v_a_2553_);
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_box(1);
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_arg_2559_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2564_, v_a_2565_, v_a_2566_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_arg_2573_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2582_, lean_object* v_b_2583_, lean_object* v_x_2584_){
_start:
{
if (lean_obj_tag(v_x_2584_) == 0)
{
lean_dec(v_b_2583_);
lean_dec(v_a_2582_);
return v_x_2584_;
}
else
{
lean_object* v_key_2585_; lean_object* v_value_2586_; lean_object* v_tail_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2599_; 
v_key_2585_ = lean_ctor_get(v_x_2584_, 0);
v_value_2586_ = lean_ctor_get(v_x_2584_, 1);
v_tail_2587_ = lean_ctor_get(v_x_2584_, 2);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_x_2584_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2589_ = v_x_2584_;
v_isShared_2590_ = v_isSharedCheck_2599_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_tail_2587_);
lean_inc(v_value_2586_);
lean_inc(v_key_2585_);
lean_dec(v_x_2584_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2599_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
uint8_t v___x_2591_; 
v___x_2591_ = l_Lean_instBEqFVarId_beq(v_key_2585_, v_a_2582_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2582_, v_b_2583_, v_tail_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 2, v___x_2592_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_key_2585_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_value_2586_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
lean_object* v___x_2597_; 
lean_dec(v_value_2586_);
lean_dec(v_key_2585_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v_b_2583_);
lean_ctor_set(v___x_2589_, 0, v_a_2582_);
v___x_2597_ = v___x_2589_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2582_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_b_2583_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_tail_2587_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2600_, lean_object* v_x_2601_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 0)
{
return v_x_2600_;
}
else
{
lean_object* v_key_2602_; lean_object* v_value_2603_; lean_object* v_tail_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2627_; 
v_key_2602_ = lean_ctor_get(v_x_2601_, 0);
v_value_2603_ = lean_ctor_get(v_x_2601_, 1);
v_tail_2604_ = lean_ctor_get(v_x_2601_, 2);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_x_2601_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2606_ = v_x_2601_;
v_isShared_2607_ = v_isSharedCheck_2627_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_tail_2604_);
lean_inc(v_value_2603_);
lean_inc(v_key_2602_);
lean_dec(v_x_2601_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2627_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; uint64_t v___x_2609_; uint64_t v___x_2610_; uint64_t v___x_2611_; uint64_t v_fold_2612_; uint64_t v___x_2613_; uint64_t v___x_2614_; uint64_t v___x_2615_; size_t v___x_2616_; size_t v___x_2617_; size_t v___x_2618_; size_t v___x_2619_; size_t v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2608_ = lean_array_get_size(v_x_2600_);
v___x_2609_ = l_Lean_instHashableFVarId_hash(v_key_2602_);
v___x_2610_ = 32ULL;
v___x_2611_ = lean_uint64_shift_right(v___x_2609_, v___x_2610_);
v_fold_2612_ = lean_uint64_xor(v___x_2609_, v___x_2611_);
v___x_2613_ = 16ULL;
v___x_2614_ = lean_uint64_shift_right(v_fold_2612_, v___x_2613_);
v___x_2615_ = lean_uint64_xor(v_fold_2612_, v___x_2614_);
v___x_2616_ = lean_uint64_to_usize(v___x_2615_);
v___x_2617_ = lean_usize_of_nat(v___x_2608_);
v___x_2618_ = ((size_t)1ULL);
v___x_2619_ = lean_usize_sub(v___x_2617_, v___x_2618_);
v___x_2620_ = lean_usize_land(v___x_2616_, v___x_2619_);
v___x_2621_ = lean_array_uget_borrowed(v_x_2600_, v___x_2620_);
lean_inc(v___x_2621_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 2, v___x_2621_);
v___x_2623_ = v___x_2606_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_key_2602_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_value_2603_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_array_uset(v_x_2600_, v___x_2620_, v___x_2623_);
v_x_2600_ = v___x_2624_;
v_x_2601_ = v_tail_2604_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2628_, lean_object* v_source_2629_, lean_object* v_target_2630_){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = lean_array_get_size(v_source_2629_);
v___x_2632_ = lean_nat_dec_lt(v_i_2628_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_dec_ref(v_source_2629_);
lean_dec(v_i_2628_);
return v_target_2630_;
}
else
{
lean_object* v_es_2633_; lean_object* v___x_2634_; lean_object* v_source_2635_; lean_object* v_target_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_es_2633_ = lean_array_fget(v_source_2629_, v_i_2628_);
v___x_2634_ = lean_box(0);
v_source_2635_ = lean_array_fset(v_source_2629_, v_i_2628_, v___x_2634_);
v_target_2636_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2630_, v_es_2633_);
v___x_2637_ = lean_unsigned_to_nat(1u);
v___x_2638_ = lean_nat_add(v_i_2628_, v___x_2637_);
lean_dec(v_i_2628_);
v_i_2628_ = v___x_2638_;
v_source_2629_ = v_source_2635_;
v_target_2630_ = v_target_2636_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2640_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v_nbuckets_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2641_ = lean_array_get_size(v_data_2640_);
v___x_2642_ = lean_unsigned_to_nat(2u);
v_nbuckets_2643_ = lean_nat_mul(v___x_2641_, v___x_2642_);
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = lean_box(0);
v___x_2646_ = lean_mk_array(v_nbuckets_2643_, v___x_2645_);
v___x_2647_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2644_, v_data_2640_, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2648_, lean_object* v_x_2649_){
_start:
{
if (lean_obj_tag(v_x_2649_) == 0)
{
uint8_t v___x_2650_; 
v___x_2650_ = 0;
return v___x_2650_;
}
else
{
lean_object* v_key_2651_; lean_object* v_tail_2652_; uint8_t v___x_2653_; 
v_key_2651_ = lean_ctor_get(v_x_2649_, 0);
v_tail_2652_ = lean_ctor_get(v_x_2649_, 2);
v___x_2653_ = l_Lean_instBEqFVarId_beq(v_key_2651_, v_a_2648_);
if (v___x_2653_ == 0)
{
v_x_2649_ = v_tail_2652_;
goto _start;
}
else
{
return v___x_2653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2655_, lean_object* v_x_2656_){
_start:
{
uint8_t v_res_2657_; lean_object* v_r_2658_; 
v_res_2657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2655_, v_x_2656_);
lean_dec(v_x_2656_);
lean_dec(v_a_2655_);
v_r_2658_ = lean_box(v_res_2657_);
return v_r_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2659_, lean_object* v_a_2660_, lean_object* v_b_2661_){
_start:
{
lean_object* v_size_2662_; lean_object* v_buckets_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2706_; 
v_size_2662_ = lean_ctor_get(v_m_2659_, 0);
v_buckets_2663_ = lean_ctor_get(v_m_2659_, 1);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_m_2659_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2665_ = v_m_2659_;
v_isShared_2666_ = v_isSharedCheck_2706_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_buckets_2663_);
lean_inc(v_size_2662_);
lean_dec(v_m_2659_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2706_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; uint64_t v___x_2668_; uint64_t v___x_2669_; uint64_t v___x_2670_; uint64_t v_fold_2671_; uint64_t v___x_2672_; uint64_t v___x_2673_; uint64_t v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; size_t v___x_2677_; size_t v___x_2678_; size_t v___x_2679_; lean_object* v_bkt_2680_; uint8_t v___x_2681_; 
v___x_2667_ = lean_array_get_size(v_buckets_2663_);
v___x_2668_ = l_Lean_instHashableFVarId_hash(v_a_2660_);
v___x_2669_ = 32ULL;
v___x_2670_ = lean_uint64_shift_right(v___x_2668_, v___x_2669_);
v_fold_2671_ = lean_uint64_xor(v___x_2668_, v___x_2670_);
v___x_2672_ = 16ULL;
v___x_2673_ = lean_uint64_shift_right(v_fold_2671_, v___x_2672_);
v___x_2674_ = lean_uint64_xor(v_fold_2671_, v___x_2673_);
v___x_2675_ = lean_uint64_to_usize(v___x_2674_);
v___x_2676_ = lean_usize_of_nat(v___x_2667_);
v___x_2677_ = ((size_t)1ULL);
v___x_2678_ = lean_usize_sub(v___x_2676_, v___x_2677_);
v___x_2679_ = lean_usize_land(v___x_2675_, v___x_2678_);
v_bkt_2680_ = lean_array_uget_borrowed(v_buckets_2663_, v___x_2679_);
v___x_2681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2660_, v_bkt_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v_size_x27_2683_; lean_object* v___x_2684_; lean_object* v_buckets_x27_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2682_ = lean_unsigned_to_nat(1u);
v_size_x27_2683_ = lean_nat_add(v_size_2662_, v___x_2682_);
lean_dec(v_size_2662_);
lean_inc(v_bkt_2680_);
v___x_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2684_, 0, v_a_2660_);
lean_ctor_set(v___x_2684_, 1, v_b_2661_);
lean_ctor_set(v___x_2684_, 2, v_bkt_2680_);
v_buckets_x27_2685_ = lean_array_uset(v_buckets_2663_, v___x_2679_, v___x_2684_);
v___x_2686_ = lean_unsigned_to_nat(4u);
v___x_2687_ = lean_nat_mul(v_size_x27_2683_, v___x_2686_);
v___x_2688_ = lean_unsigned_to_nat(3u);
v___x_2689_ = lean_nat_div(v___x_2687_, v___x_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_array_get_size(v_buckets_x27_2685_);
v___x_2691_ = lean_nat_dec_le(v___x_2689_, v___x_2690_);
lean_dec(v___x_2689_);
if (v___x_2691_ == 0)
{
lean_object* v_val_2692_; lean_object* v___x_2694_; 
v_val_2692_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2685_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v_val_2692_);
lean_ctor_set(v___x_2665_, 0, v_size_x27_2683_);
v___x_2694_ = v___x_2665_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_size_x27_2683_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_val_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
else
{
lean_object* v___x_2697_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v_buckets_x27_2685_);
lean_ctor_set(v___x_2665_, 0, v_size_x27_2683_);
v___x_2697_ = v___x_2665_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_size_x27_2683_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_buckets_x27_2685_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v_buckets_x27_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
lean_inc(v_bkt_2680_);
v___x_2699_ = lean_box(0);
v_buckets_x27_2700_ = lean_array_uset(v_buckets_2663_, v___x_2679_, v___x_2699_);
v___x_2701_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2660_, v_b_2661_, v_bkt_2680_);
v___x_2702_ = lean_array_uset(v_buckets_x27_2700_, v___x_2679_, v___x_2701_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v___x_2702_);
v___x_2704_ = v___x_2665_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_size_2662_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2707_, lean_object* v___x_2708_, lean_object* v_x_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2709_, v_var_2707_, v___x_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2711_, lean_object* v_newVal_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_st_ref_get(v_a_2715_);
v___x_2718_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2711_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v_env_2720_; lean_object* v___x_2721_; lean_object* v___f_2722_; lean_object* v___x_2723_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v_env_2720_ = lean_ctor_get(v___x_2717_, 0);
lean_inc_ref(v_env_2720_);
lean_dec(v___x_2717_);
v___x_2721_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2720_, v_a_2719_, v_newVal_2712_);
v___f_2722_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2722_, 0, v_var_2711_);
lean_closure_set(v___f_2722_, 1, v___x_2721_);
v___x_2723_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2722_, v_a_2713_, v_a_2714_);
return v___x_2723_;
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v___x_2717_);
lean_dec(v_newVal_2712_);
lean_dec(v_var_2711_);
v_a_2724_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2718_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2718_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2732_, lean_object* v_newVal_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2732_, v_newVal_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2739_, lean_object* v_newVal_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2739_, v_newVal_2740_, v_a_2741_, v_a_2742_, v_a_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2749_, lean_object* v_newVal_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2749_, v_newVal_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2759_, lean_object* v_m_2760_, lean_object* v_a_2761_, lean_object* v_b_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2760_, v_a_2761_, v_b_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2764_, lean_object* v_a_2765_, lean_object* v_x_2766_){
_start:
{
uint8_t v___x_2767_; 
v___x_2767_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2765_, v_x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2768_, lean_object* v_a_2769_, lean_object* v_x_2770_){
_start:
{
uint8_t v_res_2771_; lean_object* v_r_2772_; 
v_res_2771_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2768_, v_a_2769_, v_x_2770_);
lean_dec(v_x_2770_);
lean_dec(v_a_2769_);
v_r_2772_ = lean_box(v_res_2771_);
return v_r_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2773_, lean_object* v_data_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2776_, lean_object* v_a_2777_, lean_object* v_b_2778_, lean_object* v_x_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2777_, v_b_2778_, v_x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2781_, lean_object* v_i_2782_, lean_object* v_source_2783_, lean_object* v_target_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2782_, v_source_2783_, v_target_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2787_, v_x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2790_, lean_object* v_x_2791_){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = lean_box(0);
v___x_2793_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2791_, v_var_2790_, v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___f_2798_; lean_object* v___x_2799_; 
v___f_2798_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2798_, 0, v_var_2794_);
v___x_2799_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2798_, v_a_2795_, v_a_2796_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2805_, v_a_2806_, v_a_2807_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v_currFnIdx_2835_; lean_object* v_assignments_2836_; lean_object* v_funVals_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2828_ = lean_st_ref_get(v_a_2826_);
v___x_2829_ = lean_st_ref_take(v_a_2825_);
v_currFnIdx_2835_ = lean_ctor_get(v_a_2824_, 1);
v_assignments_2836_ = lean_ctor_get(v___x_2829_, 0);
lean_inc_ref(v_assignments_2836_);
v_funVals_2837_ = lean_ctor_get(v___x_2829_, 1);
lean_inc_ref(v_funVals_2837_);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_array_get_size(v_funVals_2837_);
v___x_2840_ = lean_nat_dec_lt(v_currFnIdx_2835_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_dec_ref(v_funVals_2837_);
lean_dec_ref(v_assignments_2836_);
lean_dec(v___x_2828_);
lean_dec(v_v_2823_);
v_fst_2831_ = v___x_2838_;
v_snd_2832_ = v___x_2829_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2852_; 
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; lean_object* v_unused_2854_; 
v_unused_2853_ = lean_ctor_get(v___x_2829_, 1);
lean_dec(v_unused_2853_);
v_unused_2854_ = lean_ctor_get(v___x_2829_, 0);
lean_dec(v_unused_2854_);
v___x_2842_ = v___x_2829_;
v_isShared_2843_ = v_isSharedCheck_2852_;
goto v_resetjp_2841_;
}
else
{
lean_dec(v___x_2829_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2852_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_env_2844_; lean_object* v_v_2845_; lean_object* v_xs_x27_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v_env_2844_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_env_2844_);
lean_dec(v___x_2828_);
v_v_2845_ = lean_array_fget(v_funVals_2837_, v_currFnIdx_2835_);
v_xs_x27_2846_ = lean_array_fset(v_funVals_2837_, v_currFnIdx_2835_, v___x_2838_);
v___x_2847_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2844_, v_v_2823_, v_v_2845_);
v___x_2848_ = lean_array_fset(v_xs_x27_2846_, v_currFnIdx_2835_, v___x_2847_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 1, v___x_2848_);
v___x_2850_ = v___x_2842_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_assignments_2836_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
v_fst_2831_ = v___x_2838_;
v_snd_2832_ = v___x_2850_;
goto v___jp_2830_;
}
}
}
v___jp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_st_ref_set(v_a_2825_, v_snd_2832_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_fst_2831_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
lean_dec(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2861_, v_a_2862_, v_a_2863_, v_a_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2879_, uint8_t v_b_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_array_2885_; lean_object* v_start_2886_; lean_object* v_stop_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2924_; 
v_array_2885_ = lean_ctor_get(v_a_2879_, 0);
v_start_2886_ = lean_ctor_get(v_a_2879_, 1);
v_stop_2887_ = lean_ctor_get(v_a_2879_, 2);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_a_2879_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2889_ = v_a_2879_;
v_isShared_2890_ = v_isSharedCheck_2924_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_stop_2887_);
lean_inc(v_start_2886_);
lean_inc(v_array_2885_);
lean_dec(v_a_2879_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2924_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_nat_dec_lt(v_start_2886_, v_stop_2887_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_del_object(v___x_2889_);
lean_dec(v_stop_2887_);
lean_dec(v_start_2886_);
lean_dec_ref(v_array_2885_);
v___x_2892_ = lean_box(v_b_2880_);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; lean_object* v_fvarId_2895_; lean_object* v___x_2896_; 
v___x_2894_ = lean_array_fget_borrowed(v_array_2885_, v_start_2886_);
v_fvarId_2895_ = lean_ctor_get(v___x_2894_, 0);
v___x_2896_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2895_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = lean_box(1);
lean_inc(v_fvarId_2895_);
v___x_2899_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2895_, v___x_2898_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_dec_ref_known(v___x_2899_, 1);
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = lean_nat_add(v_start_2886_, v___x_2900_);
lean_dec(v_start_2886_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2901_);
v___x_2903_ = v___x_2889_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_array_2885_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v_stop_2887_);
v___x_2903_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = lean_box(0);
v___x_2905_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2897_, v___x_2904_);
lean_dec(v_a_2897_);
v_a_2879_ = v___x_2903_;
v_b_2880_ = v___x_2905_;
goto _start;
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_a_2897_);
lean_del_object(v___x_2889_);
lean_dec(v_stop_2887_);
lean_dec(v_start_2886_);
lean_dec_ref(v_array_2885_);
v_a_2908_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2899_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2899_);
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
lean_del_object(v___x_2889_);
lean_dec(v_stop_2887_);
lean_dec(v_start_2886_);
lean_dec_ref(v_array_2885_);
v_a_2916_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2896_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2896_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2925_, lean_object* v_b_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
uint8_t v_b_boxed_2931_; lean_object* v_res_2932_; 
v_b_boxed_2931_ = lean_unbox(v_b_2926_);
v_res_2932_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2925_, v_b_boxed_2931_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2933_, lean_object* v___x_2934_, lean_object* v_x_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2935_, v_fvarId_2933_, v___x_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2937_, lean_object* v_as_2938_, size_t v_sz_2939_, size_t v_i_2940_, lean_object* v_b_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_a_2946_; uint8_t v___x_2950_; 
v___x_2950_ = lean_usize_dec_lt(v_i_2940_, v_sz_2939_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec_ref(v___x_2937_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_b_2941_);
return v___x_2951_;
}
else
{
lean_object* v_snd_2952_; lean_object* v_fst_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3019_; 
v_snd_2952_ = lean_ctor_get(v_b_2941_, 1);
v_fst_2953_ = lean_ctor_get(v_b_2941_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_b_2941_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_2955_ = v_b_2941_;
v_isShared_2956_ = v_isSharedCheck_3019_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_snd_2952_);
lean_inc(v_fst_2953_);
lean_dec(v_b_2941_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3019_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_array_2957_; lean_object* v_start_2958_; lean_object* v_stop_2959_; uint8_t v___x_2960_; 
v_array_2957_ = lean_ctor_get(v_snd_2952_, 0);
v_start_2958_ = lean_ctor_get(v_snd_2952_, 1);
v_stop_2959_ = lean_ctor_get(v_snd_2952_, 2);
v___x_2960_ = lean_nat_dec_lt(v_start_2958_, v_stop_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2962_; 
lean_dec_ref(v___x_2937_);
if (v_isShared_2956_ == 0)
{
v___x_2962_ = v___x_2955_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_snd_2952_);
v___x_2962_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
else
{
lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3015_; 
lean_inc(v_stop_2959_);
lean_inc(v_start_2958_);
lean_inc_ref(v_array_2957_);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_snd_2952_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; lean_object* v_unused_3017_; lean_object* v_unused_3018_; 
v_unused_3016_ = lean_ctor_get(v_snd_2952_, 2);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v_snd_2952_, 1);
lean_dec(v_unused_3017_);
v_unused_3018_ = lean_ctor_get(v_snd_2952_, 0);
lean_dec(v_unused_3018_);
v___x_2966_ = v_snd_2952_;
v_isShared_2967_ = v_isSharedCheck_3015_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_snd_2952_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3015_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_a_2968_; lean_object* v_fvarId_2969_; lean_object* v___x_2970_; 
v_a_2968_ = lean_array_uget_borrowed(v_as_2938_, v_i_2940_);
v_fvarId_2969_ = lean_ctor_get(v_a_2968_, 0);
v___x_2970_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2969_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v___x_2972_ = lean_array_fget_borrowed(v_array_2957_, v_start_2958_);
v___x_2973_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2972_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_nat_add(v_start_2958_, v___x_2975_);
lean_dec(v_start_2958_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_2976_);
v___x_2978_ = v___x_2966_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_array_2957_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_stop_2959_);
v___x_2978_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; uint8_t v___x_2980_; 
lean_inc(v_a_2971_);
lean_inc_ref(v___x_2937_);
v___x_2979_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2937_, v_a_2971_, v_a_2974_);
v___x_2980_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2979_, v_a_2971_);
lean_dec(v_a_2971_);
if (v___x_2980_ == 0)
{
lean_object* v___f_2981_; lean_object* v___x_2982_; 
lean_dec(v_fst_2953_);
lean_inc(v_fvarId_2969_);
v___f_2981_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2981_, 0, v_fvarId_2969_);
lean_closure_set(v___f_2981_, 1, v___x_2979_);
v___x_2982_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2981_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
lean_dec_ref_known(v___x_2982_, 1);
v___x_2983_ = lean_box(v___x_2960_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2978_);
lean_ctor_set(v___x_2955_, 0, v___x_2983_);
v___x_2985_ = v___x_2955_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v___x_2978_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
v_a_2946_ = v___x_2985_;
goto v___jp_2945_;
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec_ref(v___x_2978_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2937_);
v_a_2987_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2982_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2982_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v___x_2996_; 
lean_dec(v___x_2979_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2978_);
v___x_2996_ = v___x_2955_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2978_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
v_a_2946_ = v___x_2996_;
goto v___jp_2945_;
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_a_2971_);
lean_del_object(v___x_2966_);
lean_dec(v_stop_2959_);
lean_dec(v_start_2958_);
lean_dec_ref(v_array_2957_);
lean_del_object(v___x_2955_);
lean_dec(v_fst_2953_);
lean_dec_ref(v___x_2937_);
v_a_2999_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2973_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2973_);
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
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2966_);
lean_dec(v_stop_2959_);
lean_dec(v_start_2958_);
lean_dec_ref(v_array_2957_);
lean_del_object(v___x_2955_);
lean_dec(v_fst_2953_);
lean_dec_ref(v___x_2937_);
v_a_3007_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2970_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2970_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
}
}
v___jp_2945_:
{
size_t v___x_2947_; size_t v___x_2948_; 
v___x_2947_ = ((size_t)1ULL);
v___x_2948_ = lean_usize_add(v_i_2940_, v___x_2947_);
v_i_2940_ = v___x_2948_;
v_b_2941_ = v_a_2946_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3020_, lean_object* v_as_3021_, lean_object* v_sz_3022_, lean_object* v_i_3023_, lean_object* v_b_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
size_t v_sz_boxed_3028_; size_t v_i_boxed_3029_; lean_object* v_res_3030_; 
v_sz_boxed_3028_ = lean_unbox_usize(v_sz_3022_);
lean_dec(v_sz_3022_);
v_i_boxed_3029_ = lean_unbox_usize(v_i_3023_);
lean_dec(v_i_3023_);
v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3020_, v_as_3021_, v_sz_boxed_3028_, v_i_boxed_3029_, v_b_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v_as_3021_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3031_, lean_object* v_args_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___x_3040_; lean_object* v_env_3041_; uint8_t v_ret_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; size_t v_sz_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3040_ = lean_st_ref_get(v_a_3038_);
v_env_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc_ref(v_env_3041_);
lean_dec(v___x_3040_);
v_ret_3042_ = 0;
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_array_get_size(v_args_3032_);
v___x_3045_ = l_Array_toSubarray___redArg(v_args_3032_, v___x_3043_, v___x_3044_);
v___x_3046_ = lean_box(v_ret_3042_);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3045_);
v_sz_3048_ = lean_array_size(v_params_3031_);
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3041_, v_params_3031_, v_sz_3048_, v___x_3049_, v___x_3047_, v_a_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3068_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3068_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3068_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v_fst_3055_; lean_object* v_lower_3057_; lean_object* v_upper_3058_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_fst_3055_ = lean_ctor_get(v_a_3051_, 0);
lean_inc(v_fst_3055_);
lean_dec(v_a_3051_);
v___x_3062_ = lean_array_get_size(v_params_3031_);
v___x_3063_ = lean_nat_dec_eq(v___x_3062_, v___x_3044_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
lean_del_object(v___x_3053_);
v___x_3064_ = lean_nat_dec_le(v___x_3044_, v___x_3043_);
if (v___x_3064_ == 0)
{
v_lower_3057_ = v___x_3044_;
v_upper_3058_ = v___x_3062_;
goto v___jp_3056_;
}
else
{
v_lower_3057_ = v___x_3043_;
v_upper_3058_ = v___x_3062_;
goto v___jp_3056_;
}
}
else
{
lean_object* v___x_3066_; 
lean_dec_ref(v_params_3031_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v_fst_3055_);
v___x_3066_ = v___x_3053_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_fst_3055_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
v___jp_3056_:
{
lean_object* v___x_3059_; uint8_t v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = l_Array_toSubarray___redArg(v_params_3031_, v_lower_3057_, v_upper_3058_);
v___x_3060_ = lean_unbox(v_fst_3055_);
lean_dec(v_fst_3055_);
v___x_3061_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3059_, v___x_3060_, v_a_3033_, v_a_3034_, v_a_3038_);
return v___x_3061_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec_ref(v_params_3031_);
v_a_3069_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3050_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3050_);
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
lean_object* v_a_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_box(1);
v___x_3162_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3161_, v_a_3160_);
lean_dec(v_a_3160_);
if (v___x_3162_ == 0)
{
lean_object* v___f_3163_; lean_object* v___x_3164_; 
lean_inc(v_fvarId_3158_);
v___f_3163_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3163_, 0, v_fvarId_3158_);
lean_closure_set(v___f_3163_, 1, v___x_3161_);
v___x_3164_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3163_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_dec_ref_known(v___x_3164_, 1);
v_a_3150_ = v___x_3154_;
goto v___jp_3149_;
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
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
else
{
v_a_3150_ = v_b_3145_;
goto v___jp_3149_;
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_a_3173_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3159_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3159_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3181_, lean_object* v_sz_3182_, lean_object* v_i_3183_, lean_object* v_b_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
size_t v_sz_boxed_3188_; size_t v_i_boxed_3189_; uint8_t v_b_boxed_3190_; lean_object* v_res_3191_; 
v_sz_boxed_3188_ = lean_unbox_usize(v_sz_3182_);
lean_dec(v_sz_3182_);
v_i_boxed_3189_ = lean_unbox_usize(v_i_3183_);
lean_dec(v_i_3183_);
v_b_boxed_3190_ = lean_unbox(v_b_3184_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3181_, v_sz_boxed_3188_, v_i_boxed_3189_, v_b_boxed_3190_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec_ref(v_as_3181_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
uint8_t v_ret_3200_; size_t v_sz_3201_; size_t v___x_3202_; lean_object* v___x_3203_; 
v_ret_3200_ = 0;
v_sz_3201_ = lean_array_size(v_params_3192_);
v___x_3202_ = ((size_t)0ULL);
v___x_3203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3192_, v_sz_3201_, v___x_3202_, v_ret_3200_, v_a_3193_, v_a_3194_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec_ref(v_params_3204_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3213_, size_t v_sz_3214_, size_t v_i_3215_, uint8_t v_b_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3213_, v_sz_3214_, v_i_3215_, v_b_3216_, v___y_3217_, v___y_3218_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3225_, lean_object* v_sz_3226_, lean_object* v_i_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
size_t v_sz_boxed_3236_; size_t v_i_boxed_3237_; uint8_t v_b_boxed_3238_; lean_object* v_res_3239_; 
v_sz_boxed_3236_ = lean_unbox_usize(v_sz_3226_);
lean_dec(v_sz_3226_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3227_);
lean_dec(v_i_3227_);
v_b_boxed_3238_ = lean_unbox(v_b_3228_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3225_, v_sz_boxed_3236_, v_i_boxed_3237_, v_b_boxed_3238_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v_as_3225_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3240_, size_t v_i_3241_, size_t v_stop_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_usize_dec_eq(v_i_3241_, v_stop_3242_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v_fvarId_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_array_uget_borrowed(v_as_3240_, v_i_3241_);
v_fvarId_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_fvarId_3249_);
v___x_3250_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3249_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; size_t v___x_3252_; size_t v___x_3253_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v___x_3252_ = ((size_t)1ULL);
v___x_3253_ = lean_usize_add(v_i_3241_, v___x_3252_);
v_i_3241_ = v___x_3253_;
v_b_3243_ = v_a_3251_;
goto _start;
}
else
{
return v___x_3250_;
}
}
else
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_b_3243_);
return v___x_3255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3256_, lean_object* v_i_3257_, lean_object* v_stop_3258_, lean_object* v_b_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
size_t v_i_boxed_3263_; size_t v_stop_boxed_3264_; lean_object* v_res_3265_; 
v_i_boxed_3263_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_stop_boxed_3264_ = lean_unbox_usize(v_stop_3258_);
lean_dec(v_stop_3258_);
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3256_, v_i_boxed_3263_, v_stop_boxed_3264_, v_b_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v_as_3256_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v_decl_3285_; lean_object* v_k_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; 
switch(lean_obj_tag(v_x_3266_))
{
case 0:
{
lean_object* v_k_3307_; 
v_k_3307_ = lean_ctor_get(v_x_3266_, 1);
lean_inc_ref(v_k_3307_);
lean_dec_ref_known(v_x_3266_, 2);
v_x_3266_ = v_k_3307_;
goto _start;
}
case 3:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec_ref_known(v_x_3266_, 2);
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
case 4:
{
lean_object* v_cases_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3333_; 
v_cases_3311_ = lean_ctor_get(v_x_3266_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_x_3266_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3313_ = v_x_3266_;
v_isShared_3314_ = v_isSharedCheck_3333_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_cases_3311_);
lean_dec(v_x_3266_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3333_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_alts_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; 
v_alts_3315_ = lean_ctor_get(v_cases_3311_, 3);
lean_inc_ref(v_alts_3315_);
lean_dec_ref(v_cases_3311_);
v___x_3316_ = lean_unsigned_to_nat(0u);
v___x_3317_ = lean_array_get_size(v_alts_3315_);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_nat_dec_lt(v___x_3316_, v___x_3317_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3321_; 
lean_dec_ref(v_alts_3315_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3318_);
v___x_3321_ = v___x_3313_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3318_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
else
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_nat_dec_le(v___x_3317_, v___x_3317_);
if (v___x_3323_ == 0)
{
if (v___x_3319_ == 0)
{
lean_object* v___x_3325_; 
lean_dec_ref(v_alts_3315_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3318_);
v___x_3325_ = v___x_3313_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3318_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
else
{
size_t v___x_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
lean_del_object(v___x_3313_);
v___x_3327_ = ((size_t)0ULL);
v___x_3328_ = lean_usize_of_nat(v___x_3317_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3315_, v___x_3327_, v___x_3328_, v___x_3318_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
lean_dec_ref(v_alts_3315_);
return v___x_3329_;
}
}
else
{
size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
lean_del_object(v___x_3313_);
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = lean_usize_of_nat(v___x_3317_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3315_, v___x_3330_, v___x_3331_, v___x_3318_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
lean_dec_ref(v_alts_3315_);
return v___x_3332_;
}
}
}
}
case 5:
{
lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v_x_3266_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v_x_3266_, 0);
lean_dec(v_unused_3342_);
v___x_3335_ = v_x_3266_;
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
else
{
lean_dec(v_x_3266_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3337_ = lean_box(0);
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3337_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
case 6:
{
lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3350_; 
v_isSharedCheck_3350_ = !lean_is_exclusive(v_x_3266_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; 
v_unused_3351_ = lean_ctor_get(v_x_3266_, 0);
lean_dec(v_unused_3351_);
v___x_3344_ = v_x_3266_;
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
else
{
lean_dec(v_x_3266_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_box(0);
if (v_isShared_3345_ == 0)
{
lean_ctor_set_tag(v___x_3344_, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3346_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
default: 
{
lean_object* v_decl_3352_; lean_object* v_k_3353_; 
v_decl_3352_ = lean_ctor_get(v_x_3266_, 0);
lean_inc_ref(v_decl_3352_);
v_k_3353_ = lean_ctor_get(v_x_3266_, 1);
lean_inc_ref(v_k_3353_);
lean_dec_ref(v_x_3266_);
v_decl_3285_ = v_decl_3352_;
v_k_3286_ = v_k_3353_;
v___y_3287_ = v_a_3267_;
v___y_3288_ = v_a_3268_;
v___y_3289_ = v_a_3269_;
v___y_3290_ = v_a_3270_;
v___y_3291_ = v_a_3271_;
v___y_3292_ = v_a_3272_;
goto v___jp_3284_;
}
}
v___jp_3274_:
{
if (lean_obj_tag(v___y_3282_) == 0)
{
lean_dec_ref_known(v___y_3282_, 1);
v_x_3266_ = v___y_3279_;
v_a_3267_ = v___y_3281_;
v_a_3268_ = v___y_3277_;
v_a_3269_ = v___y_3280_;
v_a_3270_ = v___y_3275_;
v_a_3271_ = v___y_3278_;
v_a_3272_ = v___y_3276_;
goto _start;
}
else
{
lean_dec_ref(v___y_3279_);
return v___y_3282_;
}
}
v___jp_3284_:
{
lean_object* v_params_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_params_3293_ = lean_ctor_get(v_decl_3285_, 2);
lean_inc_ref(v_params_3293_);
lean_dec_ref(v_decl_3285_);
v___x_3294_ = lean_unsigned_to_nat(0u);
v___x_3295_ = lean_array_get_size(v_params_3293_);
v___x_3296_ = lean_nat_dec_lt(v___x_3294_, v___x_3295_);
if (v___x_3296_ == 0)
{
lean_dec_ref(v_params_3293_);
v_x_3266_ = v_k_3286_;
v_a_3267_ = v___y_3287_;
v_a_3268_ = v___y_3288_;
v_a_3269_ = v___y_3289_;
v_a_3270_ = v___y_3290_;
v_a_3271_ = v___y_3291_;
v_a_3272_ = v___y_3292_;
goto _start;
}
else
{
lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_nat_dec_le(v___x_3295_, v___x_3295_);
if (v___x_3299_ == 0)
{
if (v___x_3296_ == 0)
{
lean_dec_ref(v_params_3293_);
v_x_3266_ = v_k_3286_;
v_a_3267_ = v___y_3287_;
v_a_3268_ = v___y_3288_;
v_a_3269_ = v___y_3289_;
v_a_3270_ = v___y_3290_;
v_a_3271_ = v___y_3291_;
v_a_3272_ = v___y_3292_;
goto _start;
}
else
{
size_t v___x_3301_; size_t v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = ((size_t)0ULL);
v___x_3302_ = lean_usize_of_nat(v___x_3295_);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3293_, v___x_3301_, v___x_3302_, v___x_3298_, v___y_3287_, v___y_3288_);
lean_dec_ref(v_params_3293_);
v___y_3275_ = v___y_3290_;
v___y_3276_ = v___y_3292_;
v___y_3277_ = v___y_3288_;
v___y_3278_ = v___y_3291_;
v___y_3279_ = v_k_3286_;
v___y_3280_ = v___y_3289_;
v___y_3281_ = v___y_3287_;
v___y_3282_ = v___x_3303_;
goto v___jp_3274_;
}
}
else
{
size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = lean_usize_of_nat(v___x_3295_);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3293_, v___x_3304_, v___x_3305_, v___x_3298_, v___y_3287_, v___y_3288_);
lean_dec_ref(v_params_3293_);
v___y_3275_ = v___y_3290_;
v___y_3276_ = v___y_3292_;
v___y_3277_ = v___y_3288_;
v___y_3278_ = v___y_3291_;
v___y_3279_ = v_k_3286_;
v___y_3280_ = v___y_3289_;
v___y_3281_ = v___y_3287_;
v___y_3282_ = v___x_3306_;
goto v___jp_3274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3354_, size_t v_i_3355_, size_t v_stop_3356_, lean_object* v_b_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___y_3366_; uint8_t v___x_3372_; 
v___x_3372_ = lean_usize_dec_eq(v_i_3355_, v_stop_3356_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_array_uget_borrowed(v_as_3354_, v_i_3355_);
switch(lean_obj_tag(v___x_3373_))
{
case 0:
{
lean_object* v_code_3374_; 
v_code_3374_ = lean_ctor_get(v___x_3373_, 2);
lean_inc_ref(v_code_3374_);
v___y_3366_ = v_code_3374_;
goto v___jp_3365_;
}
case 1:
{
lean_object* v_code_3375_; 
v_code_3375_ = lean_ctor_get(v___x_3373_, 1);
lean_inc_ref(v_code_3375_);
v___y_3366_ = v_code_3375_;
goto v___jp_3365_;
}
default: 
{
lean_object* v_code_3376_; 
v_code_3376_ = lean_ctor_get(v___x_3373_, 0);
lean_inc_ref(v_code_3376_);
v___y_3366_ = v_code_3376_;
goto v___jp_3365_;
}
}
}
else
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v_b_3357_);
return v___x_3377_;
}
v___jp_3365_:
{
lean_object* v___x_3367_; 
v___x_3367_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3366_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; size_t v___x_3369_; size_t v___x_3370_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
v___x_3369_ = ((size_t)1ULL);
v___x_3370_ = lean_usize_add(v_i_3355_, v___x_3369_);
v_i_3355_ = v___x_3370_;
v_b_3357_ = v_a_3368_;
goto _start;
}
else
{
return v___x_3367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3378_, lean_object* v_i_3379_, lean_object* v_stop_3380_, lean_object* v_b_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
size_t v_i_boxed_3389_; size_t v_stop_boxed_3390_; lean_object* v_res_3391_; 
v_i_boxed_3389_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3390_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3378_, v_i_boxed_3389_, v_stop_boxed_3390_, v_b_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v_as_3378_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3401_, size_t v_i_3402_, size_t v_stop_3403_, lean_object* v_b_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3401_, v_i_3402_, v_stop_3403_, v_b_3404_, v___y_3405_, v___y_3406_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3413_, lean_object* v_i_3414_, lean_object* v_stop_3415_, lean_object* v_b_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
size_t v_i_boxed_3424_; size_t v_stop_boxed_3425_; lean_object* v_res_3426_; 
v_i_boxed_3424_ = lean_unbox_usize(v_i_3414_);
lean_dec(v_i_3414_);
v_stop_boxed_3425_ = lean_unbox_usize(v_stop_3415_);
lean_dec(v_stop_3415_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3413_, v_i_boxed_3424_, v_stop_boxed_3425_, v_b_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v_as_3413_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3427_, lean_object* v_b_3428_){
_start:
{
lean_object* v_array_3429_; lean_object* v_start_3430_; lean_object* v_stop_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3444_; 
v_array_3429_ = lean_ctor_get(v_a_3427_, 0);
v_start_3430_ = lean_ctor_get(v_a_3427_, 1);
v_stop_3431_ = lean_ctor_get(v_a_3427_, 2);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3427_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3433_ = v_a_3427_;
v_isShared_3434_ = v_isSharedCheck_3444_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_stop_3431_);
lean_inc(v_start_3430_);
lean_inc(v_array_3429_);
lean_dec(v_a_3427_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3444_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_nat_dec_lt(v_start_3430_, v_stop_3431_);
if (v___x_3435_ == 0)
{
lean_del_object(v___x_3433_);
lean_dec(v_stop_3431_);
lean_dec(v_start_3430_);
lean_dec_ref(v_array_3429_);
return v_b_3428_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3436_ = lean_unsigned_to_nat(1u);
v___x_3437_ = lean_nat_add(v_start_3430_, v___x_3436_);
lean_inc_ref(v_array_3429_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3437_);
v___x_3439_ = v___x_3433_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_array_3429_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3443_, 2, v_stop_3431_);
v___x_3439_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_array_fget(v_array_3429_, v_start_3430_);
lean_dec(v_start_3430_);
lean_dec_ref(v_array_3429_);
v___x_3441_ = lean_array_push(v_b_3428_, v___x_3440_);
v_a_3427_ = v___x_3439_;
v_b_3428_ = v___x_3441_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3445_, size_t v_i_3446_, lean_object* v_bs_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_usize_dec_lt(v_i_3446_, v_sz_3445_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_bs_3447_);
return v___x_3452_;
}
else
{
lean_object* v_v_3453_; lean_object* v___x_3454_; 
v_v_3453_ = lean_array_uget_borrowed(v_bs_3447_, v_i_3446_);
v___x_3454_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3453_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; lean_object* v_bs_x27_3457_; size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = lean_unsigned_to_nat(0u);
v_bs_x27_3457_ = lean_array_uset(v_bs_3447_, v_i_3446_, v___x_3456_);
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3446_, v___x_3458_);
v___x_3460_ = lean_array_uset(v_bs_x27_3457_, v_i_3446_, v_a_3455_);
v_i_3446_ = v___x_3459_;
v_bs_3447_ = v___x_3460_;
goto _start;
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_bs_3447_);
v_a_3462_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3454_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3454_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3470_, lean_object* v_i_3471_, lean_object* v_bs_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
size_t v_sz_boxed_3476_; size_t v_i_boxed_3477_; lean_object* v_res_3478_; 
v_sz_boxed_3476_ = lean_unbox_usize(v_sz_3470_);
lean_dec(v_sz_3470_);
v_i_boxed_3477_ = lean_unbox_usize(v_i_3471_);
lean_dec(v_i_3471_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3476_, v_i_boxed_3477_, v_bs_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3479_, size_t v_i_3480_, size_t v_stop_3481_, lean_object* v_b_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_eq(v_i_3480_, v_stop_3481_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v_fvarId_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3488_ = lean_array_uget_borrowed(v_as_3479_, v_i_3480_);
v_fvarId_3489_ = lean_ctor_get(v___x_3488_, 0);
v___x_3490_ = lean_box(1);
lean_inc(v_fvarId_3489_);
v___x_3491_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3489_, v___x_3490_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; size_t v___x_3493_; size_t v___x_3494_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = ((size_t)1ULL);
v___x_3494_ = lean_usize_add(v_i_3480_, v___x_3493_);
v_i_3480_ = v___x_3494_;
v_b_3482_ = v_a_3492_;
goto _start;
}
else
{
return v___x_3491_;
}
}
else
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_b_3482_);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3497_, lean_object* v_i_3498_, lean_object* v_stop_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
size_t v_i_boxed_3505_; size_t v_stop_boxed_3506_; lean_object* v_res_3507_; 
v_i_boxed_3505_ = lean_unbox_usize(v_i_3498_);
lean_dec(v_i_3498_);
v_stop_boxed_3506_ = lean_unbox_usize(v_stop_3499_);
lean_dec(v_stop_3499_);
v_res_3507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3497_, v_i_boxed_3505_, v_stop_boxed_3506_, v_b_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_as_3497_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3508_, size_t v_i_3509_, size_t v_stop_3510_, lean_object* v_b_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_eq(v_i_3509_, v_stop_3510_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v_fst_3518_; lean_object* v_snd_3519_; lean_object* v_fvarId_3520_; lean_object* v___x_3521_; 
v___x_3517_ = lean_array_uget_borrowed(v_as_3508_, v_i_3509_);
v_fst_3518_ = lean_ctor_get(v___x_3517_, 0);
v_snd_3519_ = lean_ctor_get(v___x_3517_, 1);
v_fvarId_3520_ = lean_ctor_get(v_fst_3518_, 0);
lean_inc(v_snd_3519_);
lean_inc(v_fvarId_3520_);
v___x_3521_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3520_, v_snd_3519_, v___y_3512_, v___y_3513_, v___y_3514_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; size_t v___x_3523_; size_t v___x_3524_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = ((size_t)1ULL);
v___x_3524_ = lean_usize_add(v_i_3509_, v___x_3523_);
v_i_3509_ = v___x_3524_;
v_b_3511_ = v_a_3522_;
goto _start;
}
else
{
return v___x_3521_;
}
}
else
{
lean_object* v___x_3526_; 
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_b_3511_);
return v___x_3526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3527_, lean_object* v_i_3528_, lean_object* v_stop_3529_, lean_object* v_b_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
size_t v_i_boxed_3535_; size_t v_stop_boxed_3536_; lean_object* v_res_3537_; 
v_i_boxed_3535_ = lean_unbox_usize(v_i_3528_);
lean_dec(v_i_3528_);
v_stop_boxed_3536_ = lean_unbox_usize(v_stop_3529_);
lean_dec(v_stop_3529_);
v_res_3537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3527_, v_i_boxed_3535_, v_stop_boxed_3536_, v_b_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v_as_3527_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3540_, size_t v_i_3541_, size_t v_stop_3542_, lean_object* v_b_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
uint8_t v___x_3551_; 
v___x_3551_ = lean_usize_dec_eq(v_i_3541_, v_stop_3542_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_array_uget_borrowed(v_as_3540_, v_i_3541_);
v___x_3553_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3552_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; size_t v___x_3555_; size_t v___x_3556_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = ((size_t)1ULL);
v___x_3556_ = lean_usize_add(v_i_3541_, v___x_3555_);
v_i_3541_ = v___x_3556_;
v_b_3543_ = v_a_3554_;
goto _start;
}
else
{
return v___x_3553_;
}
}
else
{
lean_object* v___x_3558_; 
v___x_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_b_3543_);
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v___y_3574_; 
switch(lean_obj_tag(v_letVal_3559_))
{
case 0:
{
lean_object* v_value_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3591_; 
v_value_3583_ = lean_ctor_get(v_letVal_3559_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_letVal_3559_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3585_ = v_letVal_3559_;
v_isShared_3586_ = v_isSharedCheck_3591_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_value_3583_);
lean_dec(v_letVal_3559_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3591_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3583_);
lean_dec_ref(v_value_3583_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3587_);
v___x_3589_ = v___x_3585_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
case 1:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = lean_box(1);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
case 2:
{
lean_object* v_idx_3594_; lean_object* v_struct_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_idx_3594_ = lean_ctor_get(v_letVal_3559_, 1);
lean_inc(v_idx_3594_);
v_struct_3595_ = lean_ctor_get(v_letVal_3559_, 2);
lean_inc(v_struct_3595_);
lean_dec_ref_known(v_letVal_3559_, 3);
v___x_3596_ = lean_st_ref_get(v_a_3565_);
v___x_3597_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3595_, v_a_3560_, v_a_3561_);
lean_dec(v_struct_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3607_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3607_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3607_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v_env_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v_env_3602_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_ref(v_env_3602_);
lean_dec(v___x_3596_);
v___x_3603_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3602_, v_a_3598_, v_idx_3594_);
lean_dec(v_idx_3594_);
lean_dec(v_a_3598_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3603_);
v___x_3605_ = v___x_3600_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
else
{
lean_dec(v___x_3596_);
lean_dec(v_idx_3594_);
return v___x_3597_;
}
}
case 3:
{
lean_object* v_declName_3608_; lean_object* v_args_3609_; lean_object* v___x_3610_; lean_object* v_env_3611_; lean_object* v___x_3612_; lean_object* v_numFields_3614_; lean_object* v_lower_3615_; lean_object* v_upper_3616_; lean_object* v___x_3644_; lean_object* v___y_3713_; uint8_t v___x_3722_; 
v_declName_3608_ = lean_ctor_get(v_letVal_3559_, 0);
lean_inc(v_declName_3608_);
v_args_3609_ = lean_ctor_get(v_letVal_3559_, 2);
lean_inc_ref(v_args_3609_);
lean_dec_ref_known(v_letVal_3559_, 3);
v___x_3610_ = lean_st_ref_get(v_a_3565_);
v_env_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc_ref(v_env_3611_);
lean_dec(v___x_3610_);
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3644_ = lean_array_get_size(v_args_3609_);
v___x_3722_ = lean_nat_dec_lt(v___x_3612_, v___x_3644_);
if (v___x_3722_ == 0)
{
goto v___jp_3645_;
}
else
{
lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_nat_dec_le(v___x_3644_, v___x_3644_);
if (v___x_3724_ == 0)
{
if (v___x_3722_ == 0)
{
goto v___jp_3645_;
}
else
{
size_t v___x_3725_; size_t v___x_3726_; lean_object* v___x_3727_; 
v___x_3725_ = ((size_t)0ULL);
v___x_3726_ = lean_usize_of_nat(v___x_3644_);
v___x_3727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3609_, v___x_3725_, v___x_3726_, v___x_3723_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
v___y_3713_ = v___x_3727_;
goto v___jp_3712_;
}
}
else
{
size_t v___x_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = lean_usize_of_nat(v___x_3644_);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3609_, v___x_3728_, v___x_3729_, v___x_3723_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
v___y_3713_ = v___x_3730_;
goto v___jp_3712_;
}
}
v___jp_3613_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; 
v___x_3617_ = l_Array_toSubarray___redArg(v_args_3609_, v_lower_3615_, v_upper_3616_);
v___x_3618_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3619_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3617_, v___x_3618_);
v___x_3620_ = lean_array_get_size(v___x_3619_);
v___x_3621_ = lean_nat_dec_eq(v_numFields_3614_, v___x_3620_);
lean_dec(v_numFields_3614_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
lean_dec_ref(v___x_3619_);
lean_dec(v_declName_3608_);
v___x_3622_ = lean_box(1);
v___x_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
return v___x_3623_;
}
else
{
size_t v_sz_3624_; size_t v___x_3625_; lean_object* v___x_3626_; 
v_sz_3624_ = lean_array_size(v___x_3619_);
v___x_3625_ = ((size_t)0ULL);
v___x_3626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3624_, v___x_3625_, v___x_3619_, v_a_3560_, v_a_3561_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3635_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3635_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3635_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_declName_3608_);
lean_ctor_set(v___x_3631_, 1, v_a_3627_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3631_);
v___x_3633_ = v___x_3629_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec(v_declName_3608_);
v_a_3636_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3626_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3626_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
v___jp_3645_:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3562_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; uint8_t v___x_3648_; lean_object* v___x_3649_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
v___x_3648_ = lean_unbox(v_a_3647_);
lean_dec(v_a_3647_);
lean_inc(v_declName_3608_);
v___x_3649_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3608_, v___x_3648_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3695_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3695_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3695_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
if (lean_obj_tag(v_a_3650_) == 1)
{
lean_object* v_val_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
lean_dec_ref(v_args_3609_);
v_val_3654_ = lean_ctor_get(v_a_3650_, 0);
lean_inc(v_val_3654_);
lean_dec_ref_known(v_a_3650_, 1);
v___x_3655_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3654_);
lean_dec(v_val_3654_);
v___x_3656_ = lean_nat_dec_eq(v___x_3655_, v___x_3644_);
lean_dec(v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
lean_dec_ref(v_env_3611_);
lean_dec(v_declName_3608_);
v___x_3657_ = lean_box(1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3657_);
v___x_3659_ = v___x_3652_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
else
{
lean_object* v___x_3661_; 
lean_inc(v_declName_3608_);
v___x_3661_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3611_, v_declName_3608_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v___x_3662_; 
lean_del_object(v___x_3652_);
v___x_3662_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3608_, v_a_3560_, v_a_3561_);
lean_dec(v_declName_3608_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3675_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3675_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3675_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
if (lean_obj_tag(v_a_3663_) == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_box(1);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3667_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
else
{
lean_object* v_val_3671_; lean_object* v___x_3673_; 
v_val_3671_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_val_3671_);
lean_dec_ref_known(v_a_3663_, 1);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v_val_3671_);
v___x_3673_ = v___x_3665_;
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
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
v_a_3676_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3662_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3662_);
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
else
{
lean_object* v_val_3684_; lean_object* v___x_3686_; 
lean_dec(v_declName_3608_);
v_val_3684_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_val_3684_);
lean_dec_ref_known(v___x_3661_, 1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_val_3684_);
v___x_3686_ = v___x_3652_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_val_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
uint8_t v___x_3688_; lean_object* v___x_3689_; 
lean_del_object(v___x_3652_);
lean_dec(v_a_3650_);
v___x_3688_ = 0;
lean_inc(v_declName_3608_);
v___x_3689_ = l_Lean_Environment_find_x3f(v_env_3611_, v_declName_3608_, v___x_3688_);
if (lean_obj_tag(v___x_3689_) == 1)
{
lean_object* v_val_3690_; 
v_val_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_val_3690_);
lean_dec_ref_known(v___x_3689_, 1);
if (lean_obj_tag(v_val_3690_) == 6)
{
lean_object* v_val_3691_; lean_object* v_numParams_3692_; lean_object* v_numFields_3693_; uint8_t v___x_3694_; 
v_val_3691_ = lean_ctor_get(v_val_3690_, 0);
lean_inc_ref(v_val_3691_);
lean_dec_ref_known(v_val_3690_, 1);
v_numParams_3692_ = lean_ctor_get(v_val_3691_, 3);
lean_inc(v_numParams_3692_);
v_numFields_3693_ = lean_ctor_get(v_val_3691_, 4);
lean_inc(v_numFields_3693_);
lean_dec_ref(v_val_3691_);
v___x_3694_ = lean_nat_dec_le(v_numParams_3692_, v___x_3612_);
if (v___x_3694_ == 0)
{
v_numFields_3614_ = v_numFields_3693_;
v_lower_3615_ = v_numParams_3692_;
v_upper_3616_ = v___x_3644_;
goto v___jp_3613_;
}
else
{
lean_dec(v_numParams_3692_);
v_numFields_3614_ = v_numFields_3693_;
v_lower_3615_ = v___x_3612_;
v_upper_3616_ = v___x_3644_;
goto v___jp_3613_;
}
}
else
{
lean_dec(v_val_3690_);
lean_dec_ref(v_args_3609_);
lean_dec(v_declName_3608_);
goto v___jp_3567_;
}
}
else
{
lean_dec(v___x_3689_);
lean_dec_ref(v_args_3609_);
lean_dec(v_declName_3608_);
goto v___jp_3567_;
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v_env_3611_);
lean_dec_ref(v_args_3609_);
lean_dec(v_declName_3608_);
v_a_3696_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3649_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3649_);
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
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_env_3611_);
lean_dec_ref(v_args_3609_);
lean_dec(v_declName_3608_);
v_a_3704_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3646_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3646_);
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
v___jp_3712_:
{
if (lean_obj_tag(v___y_3713_) == 0)
{
lean_dec_ref_known(v___y_3713_, 1);
goto v___jp_3645_;
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec_ref(v_env_3611_);
lean_dec_ref(v_args_3609_);
lean_dec(v_declName_3608_);
v_a_3714_ = lean_ctor_get(v___y_3713_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___y_3713_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___y_3713_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___y_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
default: 
{
lean_object* v_args_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v_args_3731_ = lean_ctor_get(v_letVal_3559_, 1);
lean_inc_ref(v_args_3731_);
lean_dec_ref_known(v_letVal_3559_, 2);
v___x_3732_ = lean_unsigned_to_nat(0u);
v___x_3733_ = lean_array_get_size(v_args_3731_);
v___x_3734_ = lean_nat_dec_lt(v___x_3732_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_dec_ref(v_args_3731_);
goto v___jp_3570_;
}
else
{
lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3735_ = lean_box(0);
v___x_3736_ = lean_nat_dec_le(v___x_3733_, v___x_3733_);
if (v___x_3736_ == 0)
{
if (v___x_3734_ == 0)
{
lean_dec_ref(v_args_3731_);
goto v___jp_3570_;
}
else
{
size_t v___x_3737_; size_t v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = ((size_t)0ULL);
v___x_3738_ = lean_usize_of_nat(v___x_3733_);
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3731_, v___x_3737_, v___x_3738_, v___x_3735_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
lean_dec_ref(v_args_3731_);
v___y_3574_ = v___x_3739_;
goto v___jp_3573_;
}
}
else
{
size_t v___x_3740_; size_t v___x_3741_; lean_object* v___x_3742_; 
v___x_3740_ = ((size_t)0ULL);
v___x_3741_ = lean_usize_of_nat(v___x_3733_);
v___x_3742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3731_, v___x_3740_, v___x_3741_, v___x_3735_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
lean_dec_ref(v_args_3731_);
v___y_3574_ = v___x_3742_;
goto v___jp_3573_;
}
}
}
}
v___jp_3567_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_box(1);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
v___jp_3570_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_box(1);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
return v___x_3572_;
}
v___jp_3573_:
{
if (lean_obj_tag(v___y_3574_) == 0)
{
lean_dec_ref_known(v___y_3574_, 1);
goto v___jp_3570_;
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
v_a_3575_ = lean_ctor_get(v___y_3574_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___y_3574_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___y_3574_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___y_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3743_, lean_object* v_args_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v_params_3752_; lean_object* v_value_3753_; lean_object* v___x_3754_; 
v_params_3752_ = lean_ctor_get(v_funDecl_3743_, 2);
lean_inc_ref(v_params_3752_);
v_value_3753_ = lean_ctor_get(v_funDecl_3743_, 4);
lean_inc_ref(v_value_3753_);
lean_dec_ref(v_funDecl_3743_);
v___x_3754_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3752_, v_args_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3766_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3766_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3766_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_unbox(v_a_3755_);
lean_dec(v_a_3755_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3762_; 
lean_dec_ref(v_value_3753_);
v___x_3760_ = lean_box(0);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v___x_3760_);
v___x_3762_ = v___x_3757_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
else
{
lean_object* v___x_3764_; 
lean_del_object(v___x_3757_);
lean_inc_ref(v_value_3753_);
v___x_3764_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3753_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v___x_3765_; 
lean_dec_ref_known(v___x_3764_, 1);
v___x_3765_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3753_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
return v___x_3765_;
}
else
{
lean_dec_ref(v_value_3753_);
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref(v_value_3753_);
v_a_3767_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3754_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3754_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3775_, lean_object* v_as_3776_, size_t v_sz_3777_, size_t v_i_3778_, lean_object* v_b_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_a_3788_; uint8_t v___x_3792_; 
v___x_3792_ = lean_usize_dec_lt(v_i_3778_, v_sz_3777_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_b_3779_);
return v___x_3793_;
}
else
{
lean_object* v___x_3794_; lean_object* v_a_3795_; 
v___x_3794_ = lean_box(0);
v_a_3795_ = lean_array_uget_borrowed(v_as_3776_, v_i_3778_);
if (lean_obj_tag(v_a_3795_) == 0)
{
lean_object* v_ctorName_3796_; lean_object* v_params_3797_; lean_object* v_code_3798_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3808_; lean_object* v___y_3810_; lean_object* v___x_3811_; 
v_ctorName_3796_ = lean_ctor_get(v_a_3795_, 0);
v_params_3797_ = lean_ctor_get(v_a_3795_, 1);
v_code_3798_ = lean_ctor_get(v_a_3795_, 2);
v___x_3811_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3775_, v_ctorName_3796_);
if (lean_obj_tag(v___x_3811_) == 1)
{
lean_object* v_val_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_val_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_val_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = l_Array_zip___redArg(v_params_3797_, v_val_3812_);
lean_dec(v_val_3812_);
v___x_3814_ = lean_unsigned_to_nat(0u);
v___x_3815_ = lean_array_get_size(v___x_3813_);
v___x_3816_ = lean_nat_dec_lt(v___x_3814_, v___x_3815_);
if (v___x_3816_ == 0)
{
lean_dec_ref(v___x_3813_);
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
goto v___jp_3799_;
}
else
{
uint8_t v___x_3817_; 
v___x_3817_ = lean_nat_dec_le(v___x_3815_, v___x_3815_);
if (v___x_3817_ == 0)
{
if (v___x_3816_ == 0)
{
lean_dec_ref(v___x_3813_);
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
goto v___jp_3799_;
}
else
{
size_t v___x_3818_; size_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = lean_usize_of_nat(v___x_3815_);
v___x_3820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3813_, v___x_3818_, v___x_3819_, v___x_3794_, v___y_3780_, v___y_3781_, v___y_3785_);
lean_dec_ref(v___x_3813_);
v___y_3808_ = v___x_3820_;
goto v___jp_3807_;
}
}
else
{
size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; 
v___x_3821_ = ((size_t)0ULL);
v___x_3822_ = lean_usize_of_nat(v___x_3815_);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3813_, v___x_3821_, v___x_3822_, v___x_3794_, v___y_3780_, v___y_3781_, v___y_3785_);
lean_dec_ref(v___x_3813_);
v___y_3808_ = v___x_3823_;
goto v___jp_3807_;
}
}
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
lean_dec(v___x_3811_);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = lean_array_get_size(v_params_3797_);
v___x_3826_ = lean_nat_dec_lt(v___x_3824_, v___x_3825_);
if (v___x_3826_ == 0)
{
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
goto v___jp_3799_;
}
else
{
uint8_t v___x_3827_; 
v___x_3827_ = lean_nat_dec_le(v___x_3825_, v___x_3825_);
if (v___x_3827_ == 0)
{
if (v___x_3826_ == 0)
{
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
goto v___jp_3799_;
}
else
{
size_t v___x_3828_; size_t v___x_3829_; lean_object* v___x_3830_; 
v___x_3828_ = ((size_t)0ULL);
v___x_3829_ = lean_usize_of_nat(v___x_3825_);
v___x_3830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3797_, v___x_3828_, v___x_3829_, v___x_3794_, v___y_3780_, v___y_3781_, v___y_3785_);
v___y_3810_ = v___x_3830_;
goto v___jp_3809_;
}
}
else
{
size_t v___x_3831_; size_t v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = ((size_t)0ULL);
v___x_3832_ = lean_usize_of_nat(v___x_3825_);
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3797_, v___x_3831_, v___x_3832_, v___x_3794_, v___y_3780_, v___y_3781_, v___y_3785_);
v___y_3810_ = v___x_3833_;
goto v___jp_3809_;
}
}
}
v___jp_3799_:
{
lean_object* v___x_3806_; 
lean_inc_ref(v_code_3798_);
v___x_3806_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3798_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec_ref_known(v___x_3806_, 1);
v_a_3788_ = v___x_3794_;
goto v___jp_3787_;
}
else
{
return v___x_3806_;
}
}
v___jp_3807_:
{
if (lean_obj_tag(v___y_3808_) == 0)
{
lean_dec_ref_known(v___y_3808_, 1);
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
goto v___jp_3799_;
}
else
{
return v___y_3808_;
}
}
v___jp_3809_:
{
if (lean_obj_tag(v___y_3810_) == 0)
{
lean_dec_ref_known(v___y_3810_, 1);
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
v___y_3803_ = v___y_3783_;
v___y_3804_ = v___y_3784_;
v___y_3805_ = v___y_3785_;
goto v___jp_3799_;
}
else
{
return v___y_3810_;
}
}
}
else
{
lean_object* v_code_3834_; lean_object* v___x_3835_; 
v_code_3834_ = lean_ctor_get(v_a_3795_, 0);
lean_inc_ref(v_code_3834_);
v___x_3835_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3834_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_dec_ref_known(v___x_3835_, 1);
v_a_3788_ = v___x_3794_;
goto v___jp_3787_;
}
else
{
return v___x_3835_;
}
}
}
v___jp_3787_:
{
size_t v___x_3789_; size_t v___x_3790_; 
v___x_3789_ = ((size_t)1ULL);
v___x_3790_ = lean_usize_add(v_i_3778_, v___x_3789_);
v_i_3778_ = v___x_3790_;
v_b_3779_ = v_a_3788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_decl_3845_; lean_object* v_k_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; 
switch(lean_obj_tag(v_x_3836_))
{
case 0:
{
lean_object* v_decl_3856_; lean_object* v_k_3857_; lean_object* v_fvarId_3858_; lean_object* v_value_3859_; lean_object* v___x_3860_; 
v_decl_3856_ = lean_ctor_get(v_x_3836_, 0);
lean_inc_ref(v_decl_3856_);
v_k_3857_ = lean_ctor_get(v_x_3836_, 1);
lean_inc_ref(v_k_3857_);
lean_dec_ref_known(v_x_3836_, 2);
v_fvarId_3858_ = lean_ctor_get(v_decl_3856_, 0);
lean_inc(v_fvarId_3858_);
v_value_3859_ = lean_ctor_get(v_decl_3856_, 3);
lean_inc_n(v_value_3859_, 2);
lean_dec_ref(v_decl_3856_);
v___x_3860_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3859_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3858_, v_a_3861_, v_a_3837_, v_a_3838_, v_a_3842_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_dec_ref_known(v___x_3862_, 1);
if (lean_obj_tag(v_value_3859_) == 4)
{
lean_object* v_fvarId_3863_; lean_object* v_args_3864_; uint8_t v___x_3865_; lean_object* v___x_3866_; 
v_fvarId_3863_ = lean_ctor_get(v_value_3859_, 0);
lean_inc(v_fvarId_3863_);
v_args_3864_ = lean_ctor_get(v_value_3859_, 1);
lean_inc_ref(v_args_3864_);
lean_dec_ref_known(v_value_3859_, 2);
v___x_3865_ = 0;
v___x_3866_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3865_, v_fvarId_3863_, v_a_3840_);
lean_dec(v_fvarId_3863_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
if (lean_obj_tag(v_a_3867_) == 1)
{
lean_object* v_val_3868_; lean_object* v___x_3869_; 
v_val_3868_ = lean_ctor_get(v_a_3867_, 0);
lean_inc(v_val_3868_);
lean_dec_ref_known(v_a_3867_, 1);
v___x_3869_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3868_, v_args_3864_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_dec_ref_known(v___x_3869_, 1);
v_x_3836_ = v_k_3857_;
goto _start;
}
else
{
lean_dec_ref(v_k_3857_);
return v___x_3869_;
}
}
else
{
lean_dec(v_a_3867_);
lean_dec_ref(v_args_3864_);
v_x_3836_ = v_k_3857_;
goto _start;
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v_args_3864_);
lean_dec_ref(v_k_3857_);
v_a_3872_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3866_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3866_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_dec(v_value_3859_);
v_x_3836_ = v_k_3857_;
goto _start;
}
}
else
{
lean_dec(v_value_3859_);
lean_dec_ref(v_k_3857_);
return v___x_3862_;
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_value_3859_);
lean_dec(v_fvarId_3858_);
lean_dec_ref(v_k_3857_);
v_a_3881_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3860_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3860_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3889_; lean_object* v_args_3890_; uint8_t v___x_3891_; lean_object* v___x_3892_; 
v_fvarId_3889_ = lean_ctor_get(v_x_3836_, 0);
lean_inc(v_fvarId_3889_);
v_args_3890_ = lean_ctor_get(v_x_3836_, 1);
lean_inc_ref(v_args_3890_);
lean_dec_ref_known(v_x_3836_, 2);
v___x_3891_ = 0;
v___x_3892_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3891_, v_fvarId_3889_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___y_3895_; lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3897_ = lean_unsigned_to_nat(0u);
v___x_3898_ = lean_array_get_size(v_args_3890_);
v___x_3899_ = lean_nat_dec_lt(v___x_3897_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
v___x_3900_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3893_, v_args_3890_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
return v___x_3900_;
}
else
{
lean_object* v___x_3901_; uint8_t v___x_3902_; 
v___x_3901_ = lean_box(0);
v___x_3902_ = lean_nat_dec_le(v___x_3898_, v___x_3898_);
if (v___x_3902_ == 0)
{
if (v___x_3899_ == 0)
{
lean_object* v___x_3903_; 
v___x_3903_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3893_, v_args_3890_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
return v___x_3903_;
}
else
{
size_t v___x_3904_; size_t v___x_3905_; lean_object* v___x_3906_; 
v___x_3904_ = ((size_t)0ULL);
v___x_3905_ = lean_usize_of_nat(v___x_3898_);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3890_, v___x_3904_, v___x_3905_, v___x_3901_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
v___y_3895_ = v___x_3906_;
goto v___jp_3894_;
}
}
else
{
size_t v___x_3907_; size_t v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = ((size_t)0ULL);
v___x_3908_ = lean_usize_of_nat(v___x_3898_);
v___x_3909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3890_, v___x_3907_, v___x_3908_, v___x_3901_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
v___y_3895_ = v___x_3909_;
goto v___jp_3894_;
}
}
v___jp_3894_:
{
if (lean_obj_tag(v___y_3895_) == 0)
{
lean_object* v___x_3896_; 
lean_dec_ref_known(v___y_3895_, 1);
v___x_3896_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3893_, v_args_3890_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
return v___x_3896_;
}
else
{
lean_dec(v_a_3893_);
lean_dec_ref(v_args_3890_);
return v___y_3895_;
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec_ref(v_args_3890_);
v_a_3910_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3892_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3892_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
case 4:
{
lean_object* v_cases_3918_; lean_object* v_discr_3919_; lean_object* v_alts_3920_; lean_object* v___x_3921_; 
v_cases_3918_ = lean_ctor_get(v_x_3836_, 0);
lean_inc_ref(v_cases_3918_);
lean_dec_ref_known(v_x_3836_, 1);
v_discr_3919_ = lean_ctor_get(v_cases_3918_, 2);
lean_inc(v_discr_3919_);
v_alts_3920_ = lean_ctor_get(v_cases_3918_, 3);
lean_inc_ref(v_alts_3920_);
lean_dec_ref(v_cases_3918_);
v___x_3921_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3919_, v_a_3837_, v_a_3838_);
lean_dec(v_discr_3919_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; size_t v_sz_3924_; size_t v___x_3925_; lean_object* v___x_3926_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = lean_box(0);
v_sz_3924_ = lean_array_size(v_alts_3920_);
v___x_3925_ = ((size_t)0ULL);
v___x_3926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3922_, v_alts_3920_, v_sz_3924_, v___x_3925_, v___x_3923_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
lean_dec_ref(v_alts_3920_);
lean_dec(v_a_3922_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v___x_3926_, 0);
lean_dec(v_unused_3934_);
v___x_3928_ = v___x_3926_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_dec(v___x_3926_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v___x_3923_);
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3923_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
else
{
return v___x_3926_;
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v_alts_3920_);
v_a_3935_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3921_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3921_);
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
case 5:
{
lean_object* v_fvarId_3943_; lean_object* v___x_3944_; 
v_fvarId_3943_ = lean_ctor_get(v_x_3836_, 0);
lean_inc(v_fvarId_3943_);
lean_dec_ref_known(v_x_3836_, 1);
v___x_3944_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3943_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v___x_3945_; 
lean_dec_ref_known(v___x_3944_, 1);
v___x_3945_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3943_, v_a_3837_, v_a_3838_);
lean_dec(v_fvarId_3943_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3947_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v___x_3947_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3946_, v_a_3837_, v_a_3838_, v_a_3842_);
return v___x_3947_;
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
v_a_3948_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3945_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3945_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_dec(v_fvarId_3943_);
return v___x_3944_;
}
}
case 6:
{
lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3963_; 
v_isSharedCheck_3963_ = !lean_is_exclusive(v_x_3836_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v_x_3836_, 0);
lean_dec(v_unused_3964_);
v___x_3957_ = v_x_3836_;
v_isShared_3958_ = v_isSharedCheck_3963_;
goto v_resetjp_3956_;
}
else
{
lean_dec(v_x_3836_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3963_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3959_ = lean_box(0);
if (v_isShared_3958_ == 0)
{
lean_ctor_set_tag(v___x_3957_, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3959_);
v___x_3961_ = v___x_3957_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3959_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
default: 
{
lean_object* v_decl_3965_; lean_object* v_k_3966_; 
v_decl_3965_ = lean_ctor_get(v_x_3836_, 0);
lean_inc_ref(v_decl_3965_);
v_k_3966_ = lean_ctor_get(v_x_3836_, 1);
lean_inc_ref(v_k_3966_);
lean_dec_ref(v_x_3836_);
v_decl_3845_ = v_decl_3965_;
v_k_3846_ = v_k_3966_;
v___y_3847_ = v_a_3837_;
v___y_3848_ = v_a_3838_;
v___y_3849_ = v_a_3839_;
v___y_3850_ = v_a_3840_;
v___y_3851_ = v_a_3841_;
v___y_3852_ = v_a_3842_;
goto v___jp_3844_;
}
}
v___jp_3844_:
{
lean_object* v_value_3853_; lean_object* v___x_3854_; 
v_value_3853_ = lean_ctor_get(v_decl_3845_, 4);
lean_inc_ref(v_value_3853_);
lean_dec_ref(v_decl_3845_);
v___x_3854_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3853_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_dec_ref_known(v___x_3854_, 1);
v_x_3836_ = v_k_3846_;
v_a_3837_ = v___y_3847_;
v_a_3838_ = v___y_3848_;
v_a_3839_ = v___y_3849_;
v_a_3840_ = v___y_3850_;
v_a_3841_ = v___y_3851_;
v_a_3842_ = v___y_3852_;
goto _start;
}
else
{
lean_dec_ref(v_k_3846_);
return v___x_3854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
uint8_t v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = 0;
v___x_3976_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3975_, v_var_3967_, v_a_3971_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4009_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_4009_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4009_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
if (lean_obj_tag(v_a_3977_) == 1)
{
lean_object* v_val_3981_; lean_object* v_params_3982_; lean_object* v_value_3983_; lean_object* v___x_3984_; 
lean_del_object(v___x_3979_);
v_val_3981_ = lean_ctor_get(v_a_3977_, 0);
lean_inc(v_val_3981_);
lean_dec_ref_known(v_a_3977_, 1);
v_params_3982_ = lean_ctor_get(v_val_3981_, 2);
lean_inc_ref(v_params_3982_);
v_value_3983_ = lean_ctor_get(v_val_3981_, 4);
lean_inc_ref(v_value_3983_);
lean_dec(v_val_3981_);
v___x_3984_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3982_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec_ref(v_params_3982_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3996_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3987_ = v___x_3984_;
v_isShared_3988_ = v_isSharedCheck_3996_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3996_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
uint8_t v___x_3989_; 
v___x_3989_ = lean_unbox(v_a_3985_);
lean_dec(v_a_3985_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
lean_dec_ref(v_value_3983_);
v___x_3990_ = lean_box(0);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3990_);
v___x_3992_ = v___x_3987_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
else
{
lean_object* v___x_3994_; 
lean_del_object(v___x_3987_);
lean_inc_ref(v_value_3983_);
v___x_3994_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3983_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v___x_3995_; 
lean_dec_ref_known(v___x_3994_, 1);
v___x_3995_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3983_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_3995_;
}
else
{
lean_dec_ref(v_value_3983_);
return v___x_3994_;
}
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_dec_ref(v_value_3983_);
v_a_3997_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3984_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3984_);
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
else
{
lean_object* v___x_4005_; lean_object* v___x_4007_; 
lean_dec(v_a_3977_);
v___x_4005_ = lean_box(0);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_4005_);
v___x_4007_ = v___x_3979_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
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
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
v_a_4010_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3976_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3976_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
if (lean_obj_tag(v_arg_4018_) == 1)
{
lean_object* v_fvarId_4026_; lean_object* v___x_4027_; 
v_fvarId_4026_ = lean_ctor_get(v_arg_4018_, 0);
v___x_4027_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4026_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
return v___x_4027_;
}
else
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = lean_box(0);
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
return v___x_4029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_arg_4030_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_4039_, lean_object* v_i_4040_, lean_object* v_stop_4041_, lean_object* v_b_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
size_t v_i_boxed_4050_; size_t v_stop_boxed_4051_; lean_object* v_res_4052_; 
v_i_boxed_4050_ = lean_unbox_usize(v_i_4040_);
lean_dec(v_i_4040_);
v_stop_boxed_4051_ = lean_unbox_usize(v_stop_4041_);
lean_dec(v_stop_4041_);
v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_4039_, v_i_boxed_4050_, v_stop_boxed_4051_, v_b_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec_ref(v_as_4039_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_4053_, lean_object* v_args_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_4053_, v_args_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_var_4063_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4072_, lean_object* v_as_4073_, lean_object* v_sz_4074_, lean_object* v_i_4075_, lean_object* v_b_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
size_t v_sz_boxed_4084_; size_t v_i_boxed_4085_; lean_object* v_res_4086_; 
v_sz_boxed_4084_ = lean_unbox_usize(v_sz_4074_);
lean_dec(v_sz_4074_);
v_i_boxed_4085_ = lean_unbox_usize(v_i_4075_);
lean_dec(v_i_4075_);
v_res_4086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4072_, v_as_4073_, v_sz_boxed_4084_, v_i_boxed_4085_, v_b_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec_ref(v_as_4073_);
lean_dec(v_a_4072_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4105_, lean_object* v_R_4106_, lean_object* v_a_4107_, lean_object* v_b_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4107_, v_b_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4110_, size_t v_i_4111_, lean_object* v_bs_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4110_, v_i_4111_, v_bs_4112_, v___y_4113_, v___y_4114_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4121_, lean_object* v_i_4122_, lean_object* v_bs_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
size_t v_sz_boxed_4131_; size_t v_i_boxed_4132_; lean_object* v_res_4133_; 
v_sz_boxed_4131_ = lean_unbox_usize(v_sz_4121_);
lean_dec(v_sz_4121_);
v_i_boxed_4132_ = lean_unbox_usize(v_i_4122_);
lean_dec(v_i_4122_);
v_res_4133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4131_, v_i_boxed_4132_, v_bs_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4134_, size_t v_i_4135_, size_t v_stop_4136_, lean_object* v_b_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4134_, v_i_4135_, v_stop_4136_, v_b_4137_, v___y_4138_, v___y_4139_, v___y_4143_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4146_, lean_object* v_i_4147_, lean_object* v_stop_4148_, lean_object* v_b_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
size_t v_i_boxed_4157_; size_t v_stop_boxed_4158_; lean_object* v_res_4159_; 
v_i_boxed_4157_ = lean_unbox_usize(v_i_4147_);
lean_dec(v_i_4147_);
v_stop_boxed_4158_ = lean_unbox_usize(v_stop_4148_);
lean_dec(v_stop_4148_);
v_res_4159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4146_, v_i_boxed_4157_, v_stop_boxed_4158_, v_b_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v_as_4146_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4160_, size_t v_i_4161_, size_t v_stop_4162_, lean_object* v_b_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4160_, v_i_4161_, v_stop_4162_, v_b_4163_, v___y_4164_, v___y_4165_, v___y_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4172_, lean_object* v_i_4173_, lean_object* v_stop_4174_, lean_object* v_b_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
size_t v_i_boxed_4183_; size_t v_stop_boxed_4184_; lean_object* v_res_4185_; 
v_i_boxed_4183_ = lean_unbox_usize(v_i_4173_);
lean_dec(v_i_4173_);
v_stop_boxed_4184_ = lean_unbox_usize(v_stop_4174_);
lean_dec(v_stop_4174_);
v_res_4185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4172_, v_i_boxed_4183_, v_stop_boxed_4184_, v_b_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec_ref(v_as_4172_);
return v_res_4185_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4186_ = lean_unsigned_to_nat(32u);
v___x_4187_ = lean_mk_empty_array_with_capacity(v___x_4186_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4189_ = ((size_t)5ULL);
v___x_4190_ = lean_unsigned_to_nat(0u);
v___x_4191_ = lean_unsigned_to_nat(32u);
v___x_4192_ = lean_mk_empty_array_with_capacity(v___x_4191_);
v___x_4193_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4194_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
lean_ctor_set(v___x_4194_, 1, v___x_4192_);
lean_ctor_set(v___x_4194_, 2, v___x_4190_);
lean_ctor_set(v___x_4194_, 3, v___x_4190_);
lean_ctor_set_usize(v___x_4194_, 4, v___x_4189_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; lean_object* v_traceState_4198_; lean_object* v_traces_4199_; lean_object* v___x_4200_; lean_object* v_traceState_4201_; lean_object* v_env_4202_; lean_object* v_nextMacroScope_4203_; lean_object* v_ngen_4204_; lean_object* v_auxDeclNGen_4205_; lean_object* v_cache_4206_; lean_object* v_messages_4207_; lean_object* v_infoState_4208_; lean_object* v_snapshotTasks_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4228_; 
v___x_4197_ = lean_st_ref_get(v___y_4195_);
v_traceState_4198_ = lean_ctor_get(v___x_4197_, 4);
lean_inc_ref(v_traceState_4198_);
lean_dec(v___x_4197_);
v_traces_4199_ = lean_ctor_get(v_traceState_4198_, 0);
lean_inc_ref(v_traces_4199_);
lean_dec_ref(v_traceState_4198_);
v___x_4200_ = lean_st_ref_take(v___y_4195_);
v_traceState_4201_ = lean_ctor_get(v___x_4200_, 4);
v_env_4202_ = lean_ctor_get(v___x_4200_, 0);
v_nextMacroScope_4203_ = lean_ctor_get(v___x_4200_, 1);
v_ngen_4204_ = lean_ctor_get(v___x_4200_, 2);
v_auxDeclNGen_4205_ = lean_ctor_get(v___x_4200_, 3);
v_cache_4206_ = lean_ctor_get(v___x_4200_, 5);
v_messages_4207_ = lean_ctor_get(v___x_4200_, 6);
v_infoState_4208_ = lean_ctor_get(v___x_4200_, 7);
v_snapshotTasks_4209_ = lean_ctor_get(v___x_4200_, 8);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4211_ = v___x_4200_;
v_isShared_4212_ = v_isSharedCheck_4228_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_snapshotTasks_4209_);
lean_inc(v_infoState_4208_);
lean_inc(v_messages_4207_);
lean_inc(v_cache_4206_);
lean_inc(v_traceState_4201_);
lean_inc(v_auxDeclNGen_4205_);
lean_inc(v_ngen_4204_);
lean_inc(v_nextMacroScope_4203_);
lean_inc(v_env_4202_);
lean_dec(v___x_4200_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4228_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
uint64_t v_tid_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4226_; 
v_tid_4213_ = lean_ctor_get_uint64(v_traceState_4201_, sizeof(void*)*1);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_traceState_4201_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; 
v_unused_4227_ = lean_ctor_get(v_traceState_4201_, 0);
lean_dec(v_unused_4227_);
v___x_4215_ = v_traceState_4201_;
v_isShared_4216_ = v_isSharedCheck_4226_;
goto v_resetjp_4214_;
}
else
{
lean_dec(v_traceState_4201_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4226_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4217_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4217_);
v___x_4219_ = v___x_4215_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4217_);
lean_ctor_set_uint64(v_reuseFailAlloc_4225_, sizeof(void*)*1, v_tid_4213_);
v___x_4219_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4221_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 4, v___x_4219_);
v___x_4221_ = v___x_4211_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_env_4202_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_nextMacroScope_4203_);
lean_ctor_set(v_reuseFailAlloc_4224_, 2, v_ngen_4204_);
lean_ctor_set(v_reuseFailAlloc_4224_, 3, v_auxDeclNGen_4205_);
lean_ctor_set(v_reuseFailAlloc_4224_, 4, v___x_4219_);
lean_ctor_set(v_reuseFailAlloc_4224_, 5, v_cache_4206_);
lean_ctor_set(v_reuseFailAlloc_4224_, 6, v_messages_4207_);
lean_ctor_set(v_reuseFailAlloc_4224_, 7, v_infoState_4208_);
lean_ctor_set(v_reuseFailAlloc_4224_, 8, v_snapshotTasks_4209_);
v___x_4221_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = lean_st_ref_set(v___y_4195_, v___x_4221_);
v___x_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4223_, 0, v_traces_4199_);
return v___x_4223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4229_);
lean_dec(v___y_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4237_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
return v_res_4247_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4248_, lean_object* v_opt_4249_){
_start:
{
lean_object* v_name_4250_; lean_object* v_defValue_4251_; lean_object* v_map_4252_; lean_object* v___x_4253_; 
v_name_4250_ = lean_ctor_get(v_opt_4249_, 0);
v_defValue_4251_ = lean_ctor_get(v_opt_4249_, 1);
v_map_4252_ = lean_ctor_get(v_opts_4248_, 0);
v___x_4253_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4252_, v_name_4250_);
if (lean_obj_tag(v___x_4253_) == 0)
{
uint8_t v___x_4254_; 
v___x_4254_ = lean_unbox(v_defValue_4251_);
return v___x_4254_;
}
else
{
lean_object* v_val_4255_; 
v_val_4255_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_val_4255_);
lean_dec_ref_known(v___x_4253_, 1);
if (lean_obj_tag(v_val_4255_) == 1)
{
uint8_t v_v_4256_; 
v_v_4256_ = lean_ctor_get_uint8(v_val_4255_, 0);
lean_dec_ref_known(v_val_4255_, 0);
return v_v_4256_;
}
else
{
uint8_t v___x_4257_; 
lean_dec(v_val_4255_);
v___x_4257_ = lean_unbox(v_defValue_4251_);
return v___x_4257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4258_, lean_object* v_opt_4259_){
_start:
{
uint8_t v_res_4260_; lean_object* v_r_4261_; 
v_res_4260_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4258_, v_opt_4259_);
lean_dec_ref(v_opt_4259_);
lean_dec_ref(v_opts_4258_);
v_r_4261_ = lean_box(v_res_4260_);
return v_r_4261_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4264_ = l_Lean_stringToMessageData(v___x_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4265_, lean_object* v_x_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4274_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4275_ = l_Lean_MessageData_ofName(v_name_4265_);
v___x_4276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4274_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4278_, lean_object* v_x_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4278_, v_x_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec_ref(v_x_4279_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4288_, lean_object* v_opt_4289_){
_start:
{
lean_object* v_name_4290_; lean_object* v_defValue_4291_; lean_object* v_map_4292_; lean_object* v___x_4293_; 
v_name_4290_ = lean_ctor_get(v_opt_4289_, 0);
v_defValue_4291_ = lean_ctor_get(v_opt_4289_, 1);
v_map_4292_ = lean_ctor_get(v_opts_4288_, 0);
v___x_4293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4292_, v_name_4290_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_inc(v_defValue_4291_);
return v_defValue_4291_;
}
else
{
lean_object* v_val_4294_; 
v_val_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_val_4294_);
lean_dec_ref_known(v___x_4293_, 1);
if (lean_obj_tag(v_val_4294_) == 3)
{
lean_object* v_v_4295_; 
v_v_4295_ = lean_ctor_get(v_val_4294_, 0);
lean_inc(v_v_4295_);
lean_dec_ref_known(v_val_4294_, 1);
return v_v_4295_;
}
else
{
lean_dec(v_val_4294_);
lean_inc(v_defValue_4291_);
return v_defValue_4291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4296_, lean_object* v_opt_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4296_, v_opt_4297_);
lean_dec_ref(v_opt_4297_);
lean_dec_ref(v_opts_4296_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4299_){
_start:
{
if (lean_obj_tag(v_x_4299_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
v_a_4301_ = lean_ctor_get(v_x_4299_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_x_4299_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v_x_4299_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v_x_4299_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
lean_ctor_set_tag(v___x_4303_, 1);
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
v_a_4309_ = lean_ctor_get(v_x_4299_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_x_4299_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v_x_4299_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v_x_4299_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set_tag(v___x_4311_, 0);
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4317_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4320_, size_t v_i_4321_, lean_object* v_bs_4322_){
_start:
{
uint8_t v___x_4323_; 
v___x_4323_ = lean_usize_dec_lt(v_i_4321_, v_sz_4320_);
if (v___x_4323_ == 0)
{
return v_bs_4322_;
}
else
{
lean_object* v_v_4324_; lean_object* v_msg_4325_; lean_object* v___x_4326_; lean_object* v_bs_x27_4327_; size_t v___x_4328_; size_t v___x_4329_; lean_object* v___x_4330_; 
v_v_4324_ = lean_array_uget_borrowed(v_bs_4322_, v_i_4321_);
v_msg_4325_ = lean_ctor_get(v_v_4324_, 1);
lean_inc_ref(v_msg_4325_);
v___x_4326_ = lean_unsigned_to_nat(0u);
v_bs_x27_4327_ = lean_array_uset(v_bs_4322_, v_i_4321_, v___x_4326_);
v___x_4328_ = ((size_t)1ULL);
v___x_4329_ = lean_usize_add(v_i_4321_, v___x_4328_);
v___x_4330_ = lean_array_uset(v_bs_x27_4327_, v_i_4321_, v_msg_4325_);
v_i_4321_ = v___x_4329_;
v_bs_4322_ = v___x_4330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4332_, lean_object* v_i_4333_, lean_object* v_bs_4334_){
_start:
{
size_t v_sz_boxed_4335_; size_t v_i_boxed_4336_; lean_object* v_res_4337_; 
v_sz_boxed_4335_ = lean_unbox_usize(v_sz_4332_);
lean_dec(v_sz_4332_);
v_i_boxed_4336_ = lean_unbox_usize(v_i_4333_);
lean_dec(v_i_4333_);
v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4335_, v_i_boxed_4336_, v_bs_4334_);
return v_res_4337_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4338_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
return v___x_4340_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4342_ = lean_unsigned_to_nat(0u);
v___x_4343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
lean_ctor_set(v___x_4343_, 2, v___x_4342_);
lean_ctor_set(v___x_4343_, 3, v___x_4342_);
lean_ctor_set(v___x_4343_, 4, v___x_4341_);
lean_ctor_set(v___x_4343_, 5, v___x_4341_);
lean_ctor_set(v___x_4343_, 6, v___x_4341_);
lean_ctor_set(v___x_4343_, 7, v___x_4341_);
lean_ctor_set(v___x_4343_, 8, v___x_4341_);
lean_ctor_set(v___x_4343_, 9, v___x_4341_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4344_, lean_object* v_data_4345_, lean_object* v_ref_4346_, lean_object* v_msg_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_options_4353_; lean_object* v___x_4354_; lean_object* v_traceState_4355_; lean_object* v_traces_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v_options_4353_ = lean_ctor_get(v___y_4350_, 2);
v___x_4354_ = lean_st_ref_get(v___y_4351_);
v_traceState_4355_ = lean_ctor_get(v___x_4354_, 4);
lean_inc_ref(v_traceState_4355_);
lean_dec(v___x_4354_);
v_traces_4356_ = lean_ctor_get(v_traceState_4355_, 0);
lean_inc_ref(v_traces_4356_);
lean_dec_ref(v_traceState_4355_);
v___x_4357_ = lean_st_ref_get(v___y_4351_);
v___x_4358_ = lean_st_ref_get(v___y_4349_);
v___x_4359_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4348_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4416_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4362_ = v___x_4359_;
v_isShared_4363_ = v_isSharedCheck_4416_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4359_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4416_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v_env_4364_; lean_object* v_lctx_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4414_; 
v_env_4364_ = lean_ctor_get(v___x_4357_, 0);
lean_inc_ref(v_env_4364_);
lean_dec(v___x_4357_);
v_lctx_4365_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; 
v_unused_4415_ = lean_ctor_get(v___x_4358_, 1);
lean_dec(v_unused_4415_);
v___x_4367_ = v___x_4358_;
v_isShared_4368_ = v_isSharedCheck_4414_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_lctx_4365_);
lean_dec(v___x_4358_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4414_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v_traceState_4371_; lean_object* v_env_4372_; lean_object* v_nextMacroScope_4373_; lean_object* v_ngen_4374_; lean_object* v_auxDeclNGen_4375_; lean_object* v_cache_4376_; lean_object* v_messages_4377_; lean_object* v_infoState_4378_; lean_object* v_snapshotTasks_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4413_; 
v___x_4369_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4370_ = lean_st_ref_take(v___y_4351_);
v_traceState_4371_ = lean_ctor_get(v___x_4370_, 4);
v_env_4372_ = lean_ctor_get(v___x_4370_, 0);
v_nextMacroScope_4373_ = lean_ctor_get(v___x_4370_, 1);
v_ngen_4374_ = lean_ctor_get(v___x_4370_, 2);
v_auxDeclNGen_4375_ = lean_ctor_get(v___x_4370_, 3);
v_cache_4376_ = lean_ctor_get(v___x_4370_, 5);
v_messages_4377_ = lean_ctor_get(v___x_4370_, 6);
v_infoState_4378_ = lean_ctor_get(v___x_4370_, 7);
v_snapshotTasks_4379_ = lean_ctor_get(v___x_4370_, 8);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4381_ = v___x_4370_;
v_isShared_4382_ = v_isSharedCheck_4413_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_snapshotTasks_4379_);
lean_inc(v_infoState_4378_);
lean_inc(v_messages_4377_);
lean_inc(v_cache_4376_);
lean_inc(v_traceState_4371_);
lean_inc(v_auxDeclNGen_4375_);
lean_inc(v_ngen_4374_);
lean_inc(v_nextMacroScope_4373_);
lean_inc(v_env_4372_);
lean_dec(v___x_4370_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4413_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
uint64_t v_tid_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4411_; 
v_tid_4383_ = lean_ctor_get_uint64(v_traceState_4371_, sizeof(void*)*1);
v_isSharedCheck_4411_ = !lean_is_exclusive(v_traceState_4371_);
if (v_isSharedCheck_4411_ == 0)
{
lean_object* v_unused_4412_; 
v_unused_4412_ = lean_ctor_get(v_traceState_4371_, 0);
lean_dec(v_unused_4412_);
v___x_4385_ = v_traceState_4371_;
v_isShared_4386_ = v_isSharedCheck_4411_;
goto v_resetjp_4384_;
}
else
{
lean_dec(v_traceState_4371_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4411_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; size_t v_sz_4388_; size_t v___x_4389_; lean_object* v___x_4390_; lean_object* v_msg_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4387_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4356_);
lean_dec_ref(v_traces_4356_);
v_sz_4388_ = lean_array_size(v___x_4387_);
v___x_4389_ = ((size_t)0ULL);
v___x_4390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4388_, v___x_4389_, v___x_4387_);
v_msg_4391_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4391_, 0, v_data_4345_);
lean_ctor_set(v_msg_4391_, 1, v_msg_4347_);
lean_ctor_set(v_msg_4391_, 2, v___x_4390_);
v___x_4392_ = lean_unbox(v_a_4360_);
lean_dec(v_a_4360_);
v___x_4393_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4365_, v___x_4392_);
lean_dec_ref(v_lctx_4365_);
lean_inc_ref(v_options_4353_);
v___x_4394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4394_, 0, v_env_4364_);
lean_ctor_set(v___x_4394_, 1, v___x_4369_);
lean_ctor_set(v___x_4394_, 2, v___x_4393_);
lean_ctor_set(v___x_4394_, 3, v_options_4353_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set_tag(v___x_4367_, 3);
lean_ctor_set(v___x_4367_, 1, v_msg_4391_);
lean_ctor_set(v___x_4367_, 0, v___x_4394_);
v___x_4396_ = v___x_4367_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4394_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_msg_4391_);
v___x_4396_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4397_, 0, v_ref_4346_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4344_, v___x_4397_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v___x_4398_);
v___x_4400_ = v___x_4385_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4398_);
lean_ctor_set_uint64(v_reuseFailAlloc_4409_, sizeof(void*)*1, v_tid_4383_);
v___x_4400_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4402_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 4, v___x_4400_);
v___x_4402_ = v___x_4381_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_env_4372_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_nextMacroScope_4373_);
lean_ctor_set(v_reuseFailAlloc_4408_, 2, v_ngen_4374_);
lean_ctor_set(v_reuseFailAlloc_4408_, 3, v_auxDeclNGen_4375_);
lean_ctor_set(v_reuseFailAlloc_4408_, 4, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4408_, 5, v_cache_4376_);
lean_ctor_set(v_reuseFailAlloc_4408_, 6, v_messages_4377_);
lean_ctor_set(v_reuseFailAlloc_4408_, 7, v_infoState_4378_);
lean_ctor_set(v_reuseFailAlloc_4408_, 8, v_snapshotTasks_4379_);
v___x_4402_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4403_ = lean_st_ref_set(v___y_4351_, v___x_4402_);
v___x_4404_ = lean_box(0);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v___x_4404_);
v___x_4406_ = v___x_4362_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
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
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec(v___x_4358_);
lean_dec(v___x_4357_);
lean_dec_ref(v_traces_4356_);
lean_dec_ref(v_msg_4347_);
lean_dec(v_ref_4346_);
lean_dec_ref(v_data_4345_);
lean_dec_ref(v_oldTraces_4344_);
v_a_4417_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4359_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4359_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4425_, lean_object* v_data_4426_, lean_object* v_ref_4427_, lean_object* v_msg_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4425_, v_data_4426_, v_ref_4427_, v_msg_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
return v_res_4434_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4435_){
_start:
{
if (lean_obj_tag(v_e_4435_) == 0)
{
uint8_t v___x_4436_; 
v___x_4436_ = 2;
return v___x_4436_;
}
else
{
uint8_t v___x_4437_; 
v___x_4437_ = 0;
return v___x_4437_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4438_){
_start:
{
uint8_t v_res_4439_; lean_object* v_r_4440_; 
v_res_4439_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4438_);
lean_dec_ref(v_e_4438_);
v_r_4440_ = lean_box(v_res_4439_);
return v_r_4440_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4441_; double v___x_4442_; 
v___x_4441_ = lean_unsigned_to_nat(0u);
v___x_4442_ = lean_float_of_nat(v___x_4441_);
return v___x_4442_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4445_ = l_Lean_stringToMessageData(v___x_4444_);
return v___x_4445_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4446_; double v___x_4447_; 
v___x_4446_ = lean_unsigned_to_nat(1000u);
v___x_4447_ = lean_float_of_nat(v___x_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4448_, uint8_t v_collapsed_4449_, lean_object* v_tag_4450_, lean_object* v_opts_4451_, uint8_t v_clsEnabled_4452_, lean_object* v_oldTraces_4453_, lean_object* v_msg_4454_, lean_object* v_resStartStop_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_fst_4463_; lean_object* v_snd_4464_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v_data_4468_; lean_object* v_fst_4471_; lean_object* v_snd_4472_; lean_object* v___x_4473_; uint8_t v___x_4474_; lean_object* v___y_4476_; lean_object* v_a_4477_; uint8_t v___y_4492_; double v___y_4523_; 
v_fst_4463_ = lean_ctor_get(v_resStartStop_4455_, 0);
lean_inc(v_fst_4463_);
v_snd_4464_ = lean_ctor_get(v_resStartStop_4455_, 1);
lean_inc(v_snd_4464_);
lean_dec_ref(v_resStartStop_4455_);
v_fst_4471_ = lean_ctor_get(v_snd_4464_, 0);
lean_inc(v_fst_4471_);
v_snd_4472_ = lean_ctor_get(v_snd_4464_, 1);
lean_inc(v_snd_4472_);
lean_dec(v_snd_4464_);
v___x_4473_ = l_Lean_trace_profiler;
v___x_4474_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4451_, v___x_4473_);
if (v___x_4474_ == 0)
{
v___y_4492_ = v___x_4474_;
goto v___jp_4491_;
}
else
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4529_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4451_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; double v___x_4532_; double v___x_4533_; double v___x_4534_; 
v___x_4530_ = l_Lean_trace_profiler_threshold;
v___x_4531_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4451_, v___x_4530_);
v___x_4532_ = lean_float_of_nat(v___x_4531_);
v___x_4533_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4534_ = lean_float_div(v___x_4532_, v___x_4533_);
v___y_4523_ = v___x_4534_;
goto v___jp_4522_;
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; double v___x_4537_; 
v___x_4535_ = l_Lean_trace_profiler_threshold;
v___x_4536_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4451_, v___x_4535_);
v___x_4537_ = lean_float_of_nat(v___x_4536_);
v___y_4523_ = v___x_4537_;
goto v___jp_4522_;
}
}
v___jp_4465_:
{
lean_object* v___x_4469_; 
lean_inc(v___y_4466_);
v___x_4469_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4453_, v_data_4468_, v___y_4466_, v___y_4467_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v___x_4470_; 
lean_dec_ref_known(v___x_4469_, 1);
v___x_4470_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4463_);
return v___x_4470_;
}
else
{
lean_dec(v_fst_4463_);
return v___x_4469_;
}
}
v___jp_4475_:
{
uint8_t v_result_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; double v___x_4481_; lean_object* v_data_4482_; 
v_result_4478_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4463_);
v___x_4479_ = lean_box(v_result_4478_);
v___x_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
v___x_4481_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4450_);
lean_inc_ref(v___x_4480_);
lean_inc(v_cls_4448_);
v_data_4482_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4482_, 0, v_cls_4448_);
lean_ctor_set(v_data_4482_, 1, v___x_4480_);
lean_ctor_set(v_data_4482_, 2, v_tag_4450_);
lean_ctor_set_float(v_data_4482_, sizeof(void*)*3, v___x_4481_);
lean_ctor_set_float(v_data_4482_, sizeof(void*)*3 + 8, v___x_4481_);
lean_ctor_set_uint8(v_data_4482_, sizeof(void*)*3 + 16, v_collapsed_4449_);
if (v___x_4474_ == 0)
{
lean_dec_ref_known(v___x_4480_, 1);
lean_dec(v_snd_4472_);
lean_dec(v_fst_4471_);
lean_dec_ref(v_tag_4450_);
lean_dec(v_cls_4448_);
v___y_4466_ = v___y_4476_;
v___y_4467_ = v_a_4477_;
v_data_4468_ = v_data_4482_;
goto v___jp_4465_;
}
else
{
lean_object* v_data_4483_; double v___x_4484_; double v___x_4485_; 
lean_dec_ref_known(v_data_4482_, 3);
v_data_4483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4483_, 0, v_cls_4448_);
lean_ctor_set(v_data_4483_, 1, v___x_4480_);
lean_ctor_set(v_data_4483_, 2, v_tag_4450_);
v___x_4484_ = lean_unbox_float(v_fst_4471_);
lean_dec(v_fst_4471_);
lean_ctor_set_float(v_data_4483_, sizeof(void*)*3, v___x_4484_);
v___x_4485_ = lean_unbox_float(v_snd_4472_);
lean_dec(v_snd_4472_);
lean_ctor_set_float(v_data_4483_, sizeof(void*)*3 + 8, v___x_4485_);
lean_ctor_set_uint8(v_data_4483_, sizeof(void*)*3 + 16, v_collapsed_4449_);
v___y_4466_ = v___y_4476_;
v___y_4467_ = v_a_4477_;
v_data_4468_ = v_data_4483_;
goto v___jp_4465_;
}
}
v___jp_4486_:
{
lean_object* v_ref_4487_; lean_object* v___x_4488_; 
v_ref_4487_ = lean_ctor_get(v___y_4460_, 5);
lean_inc(v___y_4461_);
lean_inc_ref(v___y_4460_);
lean_inc(v___y_4459_);
lean_inc_ref(v___y_4458_);
lean_inc(v___y_4457_);
lean_inc_ref(v___y_4456_);
lean_inc(v_fst_4463_);
v___x_4488_ = lean_apply_8(v_msg_4454_, v_fst_4463_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, lean_box(0));
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v___y_4476_ = v_ref_4487_;
v_a_4477_ = v_a_4489_;
goto v___jp_4475_;
}
else
{
lean_object* v___x_4490_; 
lean_dec_ref_known(v___x_4488_, 1);
v___x_4490_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4476_ = v_ref_4487_;
v_a_4477_ = v___x_4490_;
goto v___jp_4475_;
}
}
v___jp_4491_:
{
if (v_clsEnabled_4452_ == 0)
{
if (v___y_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v_traceState_4494_; lean_object* v_env_4495_; lean_object* v_nextMacroScope_4496_; lean_object* v_ngen_4497_; lean_object* v_auxDeclNGen_4498_; lean_object* v_cache_4499_; lean_object* v_messages_4500_; lean_object* v_infoState_4501_; lean_object* v_snapshotTasks_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4521_; 
lean_dec(v_snd_4472_);
lean_dec(v_fst_4471_);
lean_dec_ref(v_msg_4454_);
lean_dec_ref(v_tag_4450_);
lean_dec(v_cls_4448_);
v___x_4493_ = lean_st_ref_take(v___y_4461_);
v_traceState_4494_ = lean_ctor_get(v___x_4493_, 4);
v_env_4495_ = lean_ctor_get(v___x_4493_, 0);
v_nextMacroScope_4496_ = lean_ctor_get(v___x_4493_, 1);
v_ngen_4497_ = lean_ctor_get(v___x_4493_, 2);
v_auxDeclNGen_4498_ = lean_ctor_get(v___x_4493_, 3);
v_cache_4499_ = lean_ctor_get(v___x_4493_, 5);
v_messages_4500_ = lean_ctor_get(v___x_4493_, 6);
v_infoState_4501_ = lean_ctor_get(v___x_4493_, 7);
v_snapshotTasks_4502_ = lean_ctor_get(v___x_4493_, 8);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4504_ = v___x_4493_;
v_isShared_4505_ = v_isSharedCheck_4521_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_snapshotTasks_4502_);
lean_inc(v_infoState_4501_);
lean_inc(v_messages_4500_);
lean_inc(v_cache_4499_);
lean_inc(v_traceState_4494_);
lean_inc(v_auxDeclNGen_4498_);
lean_inc(v_ngen_4497_);
lean_inc(v_nextMacroScope_4496_);
lean_inc(v_env_4495_);
lean_dec(v___x_4493_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4521_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
uint64_t v_tid_4506_; lean_object* v_traces_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4520_; 
v_tid_4506_ = lean_ctor_get_uint64(v_traceState_4494_, sizeof(void*)*1);
v_traces_4507_ = lean_ctor_get(v_traceState_4494_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_traceState_4494_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4509_ = v_traceState_4494_;
v_isShared_4510_ = v_isSharedCheck_4520_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_traces_4507_);
lean_dec(v_traceState_4494_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4520_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4511_; lean_object* v___x_4513_; 
v___x_4511_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4453_, v_traces_4507_);
lean_dec_ref(v_traces_4507_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 0, v___x_4511_);
v___x_4513_ = v___x_4509_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4511_);
lean_ctor_set_uint64(v_reuseFailAlloc_4519_, sizeof(void*)*1, v_tid_4506_);
v___x_4513_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
lean_object* v___x_4515_; 
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 4, v___x_4513_);
v___x_4515_ = v___x_4504_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_env_4495_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_nextMacroScope_4496_);
lean_ctor_set(v_reuseFailAlloc_4518_, 2, v_ngen_4497_);
lean_ctor_set(v_reuseFailAlloc_4518_, 3, v_auxDeclNGen_4498_);
lean_ctor_set(v_reuseFailAlloc_4518_, 4, v___x_4513_);
lean_ctor_set(v_reuseFailAlloc_4518_, 5, v_cache_4499_);
lean_ctor_set(v_reuseFailAlloc_4518_, 6, v_messages_4500_);
lean_ctor_set(v_reuseFailAlloc_4518_, 7, v_infoState_4501_);
lean_ctor_set(v_reuseFailAlloc_4518_, 8, v_snapshotTasks_4502_);
v___x_4515_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = lean_st_ref_set(v___y_4461_, v___x_4515_);
v___x_4517_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4463_);
return v___x_4517_;
}
}
}
}
}
else
{
goto v___jp_4486_;
}
}
else
{
goto v___jp_4486_;
}
}
v___jp_4522_:
{
double v___x_4524_; double v___x_4525_; double v___x_4526_; uint8_t v___x_4527_; 
v___x_4524_ = lean_unbox_float(v_snd_4472_);
v___x_4525_ = lean_unbox_float(v_fst_4471_);
v___x_4526_ = lean_float_sub(v___x_4524_, v___x_4525_);
v___x_4527_ = lean_float_decLt(v___y_4523_, v___x_4526_);
v___y_4492_ = v___x_4527_;
goto v___jp_4491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4538_, lean_object* v_collapsed_4539_, lean_object* v_tag_4540_, lean_object* v_opts_4541_, lean_object* v_clsEnabled_4542_, lean_object* v_oldTraces_4543_, lean_object* v_msg_4544_, lean_object* v_resStartStop_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
uint8_t v_collapsed_boxed_4553_; uint8_t v_clsEnabled_boxed_4554_; lean_object* v_res_4555_; 
v_collapsed_boxed_4553_ = lean_unbox(v_collapsed_4539_);
v_clsEnabled_boxed_4554_ = lean_unbox(v_clsEnabled_4542_);
v_res_4555_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4538_, v_collapsed_boxed_4553_, v_tag_4540_, v_opts_4541_, v_clsEnabled_boxed_4554_, v_oldTraces_4543_, v_msg_4544_, v_resStartStop_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v_opts_4541_);
return v_res_4555_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4559_; double v___x_4560_; 
v___x_4559_ = lean_unsigned_to_nat(1000000000u);
v___x_4560_ = lean_float_of_nat(v___x_4559_);
return v___x_4560_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4569_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4570_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4571_ = l_Lean_Name_append(v___x_4570_, v___x_4569_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4572_, lean_object* v___x_4573_, lean_object* v_a_4574_, lean_object* v_b_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_a_4584_; uint8_t v___x_4588_; 
v___x_4588_ = lean_nat_dec_lt(v_a_4574_, v_upperBound_4572_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; 
lean_dec(v_a_4574_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v_b_4575_);
return v___x_4589_;
}
else
{
lean_object* v___x_4590_; lean_object* v_toSignature_4591_; lean_object* v_value_4592_; lean_object* v_name_4593_; lean_object* v_params_4594_; uint8_t v_safe_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
lean_dec_ref(v_b_4575_);
v___x_4590_ = lean_array_fget_borrowed(v___x_4573_, v_a_4574_);
v_toSignature_4591_ = lean_ctor_get(v___x_4590_, 0);
v_value_4592_ = lean_ctor_get(v___x_4590_, 1);
v_name_4593_ = lean_ctor_get(v_toSignature_4591_, 0);
v_params_4594_ = lean_ctor_get(v_toSignature_4591_, 3);
v_safe_4595_ = lean_ctor_get_uint8(v_toSignature_4591_, sizeof(void*)*4);
v___x_4596_ = lean_box(0);
v___x_4597_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4595_ == 0)
{
v_a_4584_ = v___x_4597_;
goto v___jp_4583_;
}
else
{
lean_object* v___x_4598_; 
v___x_4598_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4574_, v___y_4577_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___y_4601_; lean_object* v_decls_4631_; lean_object* v___f_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; uint8_t v___y_4642_; lean_object* v_a_4643_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; uint8_t v___y_4661_; lean_object* v_a_4662_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; uint8_t v___y_4676_; lean_object* v___y_4742_; uint8_t v___x_4751_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
v_decls_4631_ = lean_ctor_get(v___y_4576_, 0);
lean_inc(v_name_4593_);
v___f_4632_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4632_, 0, v_name_4593_);
v___x_4633_ = lean_unsigned_to_nat(0u);
v___x_4634_ = lean_array_get_size(v_params_4594_);
lean_inc(v_a_4574_);
lean_inc_ref(v_decls_4631_);
v___x_4635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4635_, 0, v_decls_4631_);
lean_ctor_set(v___x_4635_, 1, v_a_4574_);
v___x_4751_ = lean_nat_dec_lt(v___x_4633_, v___x_4634_);
if (v___x_4751_ == 0)
{
goto v___jp_4725_;
}
else
{
uint8_t v___x_4752_; 
v___x_4752_ = lean_nat_dec_le(v___x_4634_, v___x_4634_);
if (v___x_4752_ == 0)
{
if (v___x_4751_ == 0)
{
goto v___jp_4725_;
}
else
{
size_t v___x_4753_; size_t v___x_4754_; lean_object* v___x_4755_; 
v___x_4753_ = ((size_t)0ULL);
v___x_4754_ = lean_usize_of_nat(v___x_4634_);
v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4594_, v___x_4753_, v___x_4754_, v___x_4596_, v___x_4635_, v___y_4577_, v___y_4581_);
v___y_4742_ = v___x_4755_;
goto v___jp_4741_;
}
}
else
{
size_t v___x_4756_; size_t v___x_4757_; lean_object* v___x_4758_; 
v___x_4756_ = ((size_t)0ULL);
v___x_4757_ = lean_usize_of_nat(v___x_4634_);
v___x_4758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4594_, v___x_4756_, v___x_4757_, v___x_4596_, v___x_4635_, v___y_4577_, v___y_4581_);
v___y_4742_ = v___x_4758_;
goto v___jp_4741_;
}
}
v___jp_4600_:
{
if (lean_obj_tag(v___y_4601_) == 0)
{
lean_object* v___x_4602_; 
lean_dec_ref_known(v___y_4601_, 1);
v___x_4602_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4574_, v___y_4577_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4614_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
uint8_t v___x_4607_; 
v___x_4607_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4599_, v_a_4603_);
lean_dec(v_a_4603_);
lean_dec(v_a_4599_);
if (v___x_4607_ == 0)
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_dec(v_a_4574_);
v___x_4608_ = lean_box(v_safe_4595_);
v___x_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
v___x_4610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
lean_ctor_set(v___x_4610_, 1, v___x_4596_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4610_);
v___x_4612_ = v___x_4605_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
else
{
lean_del_object(v___x_4605_);
v_a_4584_ = v___x_4597_;
goto v___jp_4583_;
}
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec(v_a_4599_);
lean_dec(v_a_4574_);
v_a_4615_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4602_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4602_);
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
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec(v_a_4599_);
lean_dec(v_a_4574_);
v_a_4623_ = lean_ctor_get(v___y_4601_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___y_4601_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___y_4601_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___y_4601_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
v___jp_4636_:
{
lean_object* v___x_4644_; double v___x_4645_; double v___x_4646_; double v___x_4647_; double v___x_4648_; double v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4644_ = lean_io_mono_nanos_now();
v___x_4645_ = lean_float_of_nat(v___y_4637_);
v___x_4646_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4647_ = lean_float_div(v___x_4645_, v___x_4646_);
v___x_4648_ = lean_float_of_nat(v___x_4644_);
v___x_4649_ = lean_float_div(v___x_4648_, v___x_4646_);
v___x_4650_ = lean_box_float(v___x_4647_);
v___x_4651_ = lean_box_float(v___x_4649_);
v___x_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4650_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
v___x_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4653_, 0, v_a_4643_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
lean_inc_ref(v___y_4638_);
lean_inc(v___y_4641_);
v___x_4654_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4641_, v_safe_4595_, v___y_4638_, v___y_4639_, v___y_4642_, v___y_4640_, v___f_4632_, v___x_4653_, v___x_4635_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec_ref_known(v___x_4635_, 2);
v___y_4601_ = v___x_4654_;
goto v___jp_4600_;
}
v___jp_4655_:
{
lean_object* v___x_4663_; double v___x_4664_; double v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4663_ = lean_io_get_num_heartbeats();
v___x_4664_ = lean_float_of_nat(v___y_4658_);
v___x_4665_ = lean_float_of_nat(v___x_4663_);
v___x_4666_ = lean_box_float(v___x_4664_);
v___x_4667_ = lean_box_float(v___x_4665_);
v___x_4668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4666_);
lean_ctor_set(v___x_4668_, 1, v___x_4667_);
v___x_4669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4669_, 0, v_a_4662_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
lean_inc_ref(v___y_4656_);
lean_inc(v___y_4660_);
v___x_4670_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4660_, v_safe_4595_, v___y_4656_, v___y_4657_, v___y_4661_, v___y_4659_, v___f_4632_, v___x_4669_, v___x_4635_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec_ref_known(v___x_4635_, 2);
v___y_4601_ = v___x_4670_;
goto v___jp_4600_;
}
v___jp_4671_:
{
lean_object* v___x_4677_; 
v___x_4677_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4581_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___x_4677_, 1);
v___x_4679_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4680_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4674_, v___x_4679_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = lean_io_mono_nanos_now();
v___x_4682_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4672_, v___x_4635_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
lean_ctor_set_tag(v___x_4685_, 1);
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
v___y_4637_ = v___x_4681_;
v___y_4638_ = v___y_4673_;
v___y_4639_ = v___y_4674_;
v___y_4640_ = v_a_4678_;
v___y_4641_ = v___y_4675_;
v___y_4642_ = v___y_4676_;
v_a_4643_ = v___x_4688_;
goto v___jp_4636_;
}
}
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
v_a_4691_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4682_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4682_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
lean_ctor_set_tag(v___x_4693_, 0);
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
v___y_4637_ = v___x_4681_;
v___y_4638_ = v___y_4673_;
v___y_4639_ = v___y_4674_;
v___y_4640_ = v_a_4678_;
v___y_4641_ = v___y_4675_;
v___y_4642_ = v___y_4676_;
v_a_4643_ = v___x_4696_;
goto v___jp_4636_;
}
}
}
}
else
{
lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4699_ = lean_io_get_num_heartbeats();
v___x_4700_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4672_, v___x_4635_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4700_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4700_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
lean_ctor_set_tag(v___x_4703_, 1);
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
v___y_4656_ = v___y_4673_;
v___y_4657_ = v___y_4674_;
v___y_4658_ = v___x_4699_;
v___y_4659_ = v_a_4678_;
v___y_4660_ = v___y_4675_;
v___y_4661_ = v___y_4676_;
v_a_4662_ = v___x_4706_;
goto v___jp_4655_;
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
v_a_4709_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4700_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4700_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
lean_ctor_set_tag(v___x_4711_, 0);
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
v___y_4656_ = v___y_4673_;
v___y_4657_ = v___y_4674_;
v___y_4658_ = v___x_4699_;
v___y_4659_ = v_a_4678_;
v___y_4660_ = v___y_4675_;
v___y_4661_ = v___y_4676_;
v_a_4662_ = v___x_4714_;
goto v___jp_4655_;
}
}
}
}
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
lean_dec_ref(v___y_4672_);
lean_dec_ref_known(v___x_4635_, 2);
lean_dec_ref(v___f_4632_);
lean_dec(v_a_4599_);
lean_dec(v_a_4574_);
v_a_4717_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4677_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4677_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
v___jp_4725_:
{
if (lean_obj_tag(v_value_4592_) == 0)
{
lean_object* v_options_4726_; uint8_t v_hasTrace_4727_; 
v_options_4726_ = lean_ctor_get(v___y_4580_, 2);
v_hasTrace_4727_ = lean_ctor_get_uint8(v_options_4726_, sizeof(void*)*1);
if (v_hasTrace_4727_ == 0)
{
lean_object* v_code_4728_; lean_object* v___x_4729_; 
lean_dec_ref(v___f_4632_);
v_code_4728_ = lean_ctor_get(v_value_4592_, 0);
lean_inc_ref(v_code_4728_);
v___x_4729_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4728_, v___x_4635_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec_ref_known(v___x_4635_, 2);
v___y_4601_ = v___x_4729_;
goto v___jp_4600_;
}
else
{
lean_object* v_code_4730_; lean_object* v_inheritedTraceOptions_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v_code_4730_ = lean_ctor_get(v_value_4592_, 0);
v_inheritedTraceOptions_4731_ = lean_ctor_get(v___y_4580_, 13);
v___x_4732_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4733_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4731_, v_options_4726_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; uint8_t v___x_4737_; 
v___x_4736_ = l_Lean_trace_profiler;
v___x_4737_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4726_, v___x_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; 
lean_dec_ref(v___f_4632_);
lean_inc_ref(v_code_4730_);
v___x_4738_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4730_, v___x_4635_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec_ref_known(v___x_4635_, 2);
v___y_4601_ = v___x_4738_;
goto v___jp_4600_;
}
else
{
lean_inc_ref(v_code_4730_);
v___y_4672_ = v_code_4730_;
v___y_4673_ = v___x_4733_;
v___y_4674_ = v_options_4726_;
v___y_4675_ = v___x_4732_;
v___y_4676_ = v___x_4735_;
goto v___jp_4671_;
}
}
else
{
lean_inc_ref(v_code_4730_);
v___y_4672_ = v_code_4730_;
v___y_4673_ = v___x_4733_;
v___y_4674_ = v_options_4726_;
v___y_4675_ = v___x_4732_;
v___y_4676_ = v___x_4735_;
goto v___jp_4671_;
}
}
}
else
{
lean_object* v___x_4739_; lean_object* v___x_4740_; 
lean_dec_ref(v___f_4632_);
v___x_4739_ = lean_box(1);
v___x_4740_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4739_, v___x_4635_, v___y_4577_, v___y_4581_);
lean_dec_ref_known(v___x_4635_, 2);
v___y_4601_ = v___x_4740_;
goto v___jp_4600_;
}
}
v___jp_4741_:
{
if (lean_obj_tag(v___y_4742_) == 0)
{
lean_dec_ref_known(v___y_4742_, 1);
goto v___jp_4725_;
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
lean_dec_ref_known(v___x_4635_, 2);
lean_dec_ref(v___f_4632_);
lean_dec(v_a_4599_);
lean_dec(v_a_4574_);
v_a_4743_ = lean_ctor_get(v___y_4742_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___y_4742_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___y_4742_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___y_4742_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec(v_a_4574_);
v_a_4759_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4598_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4598_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
}
v___jp_4583_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = lean_unsigned_to_nat(1u);
v___x_4586_ = lean_nat_add(v_a_4574_, v___x_4585_);
lean_dec(v_a_4574_);
lean_inc_ref(v_a_4584_);
v_a_4574_ = v___x_4586_;
v_b_4575_ = v_a_4584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4767_, lean_object* v___x_4768_, lean_object* v_a_4769_, lean_object* v_b_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4767_, v___x_4768_, v_a_4769_, v_b_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec_ref(v___x_4768_);
lean_dec(v_upperBound_4767_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_){
_start:
{
lean_object* v_decls_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v_decls_4786_ = lean_ctor_get(v_a_4779_, 0);
v___x_4787_ = lean_array_get_size(v_decls_4786_);
v___x_4788_ = lean_unsigned_to_nat(0u);
v___x_4789_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4787_, v_decls_4786_, v___x_4788_, v___x_4789_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4805_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_4805_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4805_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v_fst_4795_; 
v_fst_4795_ = lean_ctor_get(v_a_4791_, 0);
lean_inc(v_fst_4795_);
lean_dec(v_a_4791_);
if (lean_obj_tag(v_fst_4795_) == 0)
{
uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v___x_4796_ = 0;
v___x_4797_ = lean_box(v___x_4796_);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v___x_4797_);
v___x_4799_ = v___x_4793_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
else
{
lean_object* v_val_4801_; lean_object* v___x_4803_; 
v_val_4801_ = lean_ctor_get(v_fst_4795_, 0);
lean_inc(v_val_4801_);
lean_dec_ref_known(v_fst_4795_, 1);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v_val_4801_);
v___x_4803_ = v___x_4793_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_val_4801_);
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
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
v_a_4806_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4790_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4790_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
lean_dec(v_a_4819_);
lean_dec_ref(v_a_4818_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4822_, lean_object* v_x_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4823_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4832_, lean_object* v_x_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4832_, v_x_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4842_, lean_object* v___x_4843_, lean_object* v_inst_4844_, lean_object* v_R_4845_, lean_object* v_a_4846_, lean_object* v_b_4847_, lean_object* v_c_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v___x_4856_; 
v___x_4856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4842_, v___x_4843_, v_a_4846_, v_b_4847_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4857_, lean_object* v___x_4858_, lean_object* v_inst_4859_, lean_object* v_R_4860_, lean_object* v_a_4861_, lean_object* v_b_4862_, lean_object* v_c_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4857_, v___x_4858_, v_inst_4859_, v_R_4860_, v_a_4861_, v_b_4862_, v_c_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec_ref(v___x_4858_);
lean_dec(v_upperBound_4857_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4872_, lean_object* v_data_4873_, lean_object* v_ref_4874_, lean_object* v_msg_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v___x_4883_; 
v___x_4883_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4872_, v_data_4873_, v_ref_4874_, v_msg_4875_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_);
return v___x_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4884_, lean_object* v_data_4885_, lean_object* v_ref_4886_, lean_object* v_msg_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4884_, v_data_4885_, v_ref_4886_, v_msg_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec(v___y_4889_);
lean_dec_ref(v___y_4888_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4898_, lean_object* v_msg_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v_options_4905_; lean_object* v_ref_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v_options_4905_ = lean_ctor_get(v___y_4902_, 2);
v_ref_4906_ = lean_ctor_get(v___y_4902_, 5);
v___x_4907_ = lean_st_ref_get(v___y_4903_);
v___x_4908_ = lean_st_ref_get(v___y_4901_);
v___x_4909_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4900_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4968_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4968_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4968_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v_env_4914_; lean_object* v_lctx_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4966_; 
v_env_4914_ = lean_ctor_get(v___x_4907_, 0);
lean_inc_ref(v_env_4914_);
lean_dec(v___x_4907_);
v_lctx_4915_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4966_ == 0)
{
lean_object* v_unused_4967_; 
v_unused_4967_ = lean_ctor_get(v___x_4908_, 1);
lean_dec(v_unused_4967_);
v___x_4917_ = v___x_4908_;
v_isShared_4918_ = v_isSharedCheck_4966_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_lctx_4915_);
lean_dec(v___x_4908_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4966_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v_traceState_4921_; lean_object* v_env_4922_; lean_object* v_nextMacroScope_4923_; lean_object* v_ngen_4924_; lean_object* v_auxDeclNGen_4925_; lean_object* v_cache_4926_; lean_object* v_messages_4927_; lean_object* v_infoState_4928_; lean_object* v_snapshotTasks_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4965_; 
v___x_4919_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_4920_ = lean_st_ref_take(v___y_4903_);
v_traceState_4921_ = lean_ctor_get(v___x_4920_, 4);
v_env_4922_ = lean_ctor_get(v___x_4920_, 0);
v_nextMacroScope_4923_ = lean_ctor_get(v___x_4920_, 1);
v_ngen_4924_ = lean_ctor_get(v___x_4920_, 2);
v_auxDeclNGen_4925_ = lean_ctor_get(v___x_4920_, 3);
v_cache_4926_ = lean_ctor_get(v___x_4920_, 5);
v_messages_4927_ = lean_ctor_get(v___x_4920_, 6);
v_infoState_4928_ = lean_ctor_get(v___x_4920_, 7);
v_snapshotTasks_4929_ = lean_ctor_get(v___x_4920_, 8);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4931_ = v___x_4920_;
v_isShared_4932_ = v_isSharedCheck_4965_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_snapshotTasks_4929_);
lean_inc(v_infoState_4928_);
lean_inc(v_messages_4927_);
lean_inc(v_cache_4926_);
lean_inc(v_traceState_4921_);
lean_inc(v_auxDeclNGen_4925_);
lean_inc(v_ngen_4924_);
lean_inc(v_nextMacroScope_4923_);
lean_inc(v_env_4922_);
lean_dec(v___x_4920_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4965_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
uint64_t v_tid_4933_; lean_object* v_traces_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4964_; 
v_tid_4933_ = lean_ctor_get_uint64(v_traceState_4921_, sizeof(void*)*1);
v_traces_4934_ = lean_ctor_get(v_traceState_4921_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_traceState_4921_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4936_ = v_traceState_4921_;
v_isShared_4937_ = v_isSharedCheck_4964_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_traces_4934_);
lean_dec(v_traceState_4921_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4964_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
uint8_t v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4938_ = lean_unbox(v_a_4910_);
lean_dec(v_a_4910_);
v___x_4939_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4915_, v___x_4938_);
lean_dec_ref(v_lctx_4915_);
lean_inc_ref(v_options_4905_);
v___x_4940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4940_, 0, v_env_4914_);
lean_ctor_set(v___x_4940_, 1, v___x_4919_);
lean_ctor_set(v___x_4940_, 2, v___x_4939_);
lean_ctor_set(v___x_4940_, 3, v_options_4905_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set_tag(v___x_4917_, 3);
lean_ctor_set(v___x_4917_, 1, v_msg_4899_);
lean_ctor_set(v___x_4917_, 0, v___x_4940_);
v___x_4942_ = v___x_4917_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4940_);
lean_ctor_set(v_reuseFailAlloc_4963_, 1, v_msg_4899_);
v___x_4942_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4943_; double v___x_4944_; uint8_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4953_; 
v___x_4943_ = lean_box(0);
v___x_4944_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4945_ = 0;
v___x_4946_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4947_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4947_, 0, v_cls_4898_);
lean_ctor_set(v___x_4947_, 1, v___x_4943_);
lean_ctor_set(v___x_4947_, 2, v___x_4946_);
lean_ctor_set_float(v___x_4947_, sizeof(void*)*3, v___x_4944_);
lean_ctor_set_float(v___x_4947_, sizeof(void*)*3 + 8, v___x_4944_);
lean_ctor_set_uint8(v___x_4947_, sizeof(void*)*3 + 16, v___x_4945_);
v___x_4948_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4949_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4947_);
lean_ctor_set(v___x_4949_, 1, v___x_4942_);
lean_ctor_set(v___x_4949_, 2, v___x_4948_);
lean_inc(v_ref_4906_);
v___x_4950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4950_, 0, v_ref_4906_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = l_Lean_PersistentArray_push___redArg(v_traces_4934_, v___x_4950_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v___x_4951_);
v___x_4953_ = v___x_4936_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4951_);
lean_ctor_set_uint64(v_reuseFailAlloc_4962_, sizeof(void*)*1, v_tid_4933_);
v___x_4953_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
lean_object* v___x_4955_; 
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 4, v___x_4953_);
v___x_4955_ = v___x_4931_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_env_4922_);
lean_ctor_set(v_reuseFailAlloc_4961_, 1, v_nextMacroScope_4923_);
lean_ctor_set(v_reuseFailAlloc_4961_, 2, v_ngen_4924_);
lean_ctor_set(v_reuseFailAlloc_4961_, 3, v_auxDeclNGen_4925_);
lean_ctor_set(v_reuseFailAlloc_4961_, 4, v___x_4953_);
lean_ctor_set(v_reuseFailAlloc_4961_, 5, v_cache_4926_);
lean_ctor_set(v_reuseFailAlloc_4961_, 6, v_messages_4927_);
lean_ctor_set(v_reuseFailAlloc_4961_, 7, v_infoState_4928_);
lean_ctor_set(v_reuseFailAlloc_4961_, 8, v_snapshotTasks_4929_);
v___x_4955_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4959_; 
v___x_4956_ = lean_st_ref_set(v___y_4903_, v___x_4955_);
v___x_4957_ = lean_box(0);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4957_);
v___x_4959_ = v___x_4912_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
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
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec(v___x_4908_);
lean_dec(v___x_4907_);
lean_dec_ref(v_msg_4899_);
lean_dec(v_cls_4898_);
v_a_4969_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4909_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4909_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4977_, lean_object* v_msg_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4977_, v_msg_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4985_, lean_object* v_msg_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; 
v___x_4994_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4985_, v_msg_4986_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4995_, lean_object* v_msg_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4995_, v_msg_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___y_5002_);
lean_dec_ref(v___y_5001_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
return v_res_5004_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5005_ = lean_box(0);
v___x_5006_ = lean_unsigned_to_nat(16u);
v___x_5007_ = lean_mk_array(v___x_5006_, v___x_5005_);
return v___x_5007_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5008_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_5009_ = lean_unsigned_to_nat(0u);
v___x_5010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
lean_ctor_set(v___x_5010_, 1, v___x_5008_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_5011_, size_t v_i_5012_, lean_object* v_bs_5013_){
_start:
{
uint8_t v___x_5014_; 
v___x_5014_ = lean_usize_dec_lt(v_i_5012_, v_sz_5011_);
if (v___x_5014_ == 0)
{
return v_bs_5013_;
}
else
{
lean_object* v___x_5015_; lean_object* v_bs_x27_5016_; lean_object* v___x_5017_; size_t v___x_5018_; size_t v___x_5019_; lean_object* v___x_5020_; 
v___x_5015_ = lean_unsigned_to_nat(0u);
v_bs_x27_5016_ = lean_array_uset(v_bs_5013_, v_i_5012_, v___x_5015_);
v___x_5017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5018_ = ((size_t)1ULL);
v___x_5019_ = lean_usize_add(v_i_5012_, v___x_5018_);
v___x_5020_ = lean_array_uset(v_bs_x27_5016_, v_i_5012_, v___x_5017_);
v_i_5012_ = v___x_5019_;
v_bs_5013_ = v___x_5020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_5022_, lean_object* v_i_5023_, lean_object* v_bs_5024_){
_start:
{
size_t v_sz_boxed_5025_; size_t v_i_boxed_5026_; lean_object* v_res_5027_; 
v_sz_boxed_5025_ = lean_unbox_usize(v_sz_5022_);
lean_dec(v_sz_5022_);
v_i_boxed_5026_ = lean_unbox_usize(v_i_5023_);
lean_dec(v_i_5023_);
v_res_5027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_5025_, v_i_boxed_5026_, v_bs_5024_);
return v_res_5027_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5029_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5030_ = l_Lean_stringToMessageData(v___x_5029_);
return v___x_5030_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5033_ = l_Lean_stringToMessageData(v___x_5032_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_){
_start:
{
lean_object* v___x_5045_; lean_object* v_decls_5046_; lean_object* v_funVals_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5086_; 
v___x_5045_ = lean_st_ref_take(v_a_5036_);
v_decls_5046_ = lean_ctor_get(v_a_5035_, 0);
v_funVals_5047_ = lean_ctor_get(v___x_5045_, 1);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5086_ == 0)
{
lean_object* v_unused_5087_; 
v_unused_5087_ = lean_ctor_get(v___x_5045_, 0);
lean_dec(v_unused_5087_);
v___x_5049_ = v___x_5045_;
v_isShared_5050_ = v_isSharedCheck_5086_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_funVals_5047_);
lean_dec(v___x_5045_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5086_;
goto v_resetjp_5048_;
}
v___jp_5042_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = lean_box(0);
v___x_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
return v___x_5044_;
}
v_resetjp_5048_:
{
size_t v_sz_5051_; size_t v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5055_; 
v_sz_5051_ = lean_array_size(v_decls_5046_);
v___x_5052_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5046_);
v___x_5053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5051_, v___x_5052_, v_decls_5046_);
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 0, v___x_5053_);
v___x_5055_ = v___x_5049_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5053_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v_funVals_5047_);
v___x_5055_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5056_ = lean_st_ref_set(v_a_5036_, v___x_5055_);
v___x_5057_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; uint8_t v___x_5059_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v___x_5059_ = lean_unbox(v_a_5058_);
lean_dec(v_a_5058_);
if (v___x_5059_ == 0)
{
lean_object* v_options_5060_; uint8_t v_hasTrace_5061_; 
v_options_5060_ = lean_ctor_get(v_a_5039_, 2);
v_hasTrace_5061_ = lean_ctor_get_uint8(v_options_5060_, sizeof(void*)*1);
if (v_hasTrace_5061_ == 0)
{
lean_dec(v_n_5034_);
goto v___jp_5042_;
}
else
{
lean_object* v_inheritedTraceOptions_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v_inheritedTraceOptions_5062_ = lean_ctor_get(v_a_5039_, 13);
v___x_5063_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5064_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5062_, v_options_5060_, v___x_5064_);
if (v___x_5065_ == 0)
{
lean_dec(v_n_5034_);
goto v___jp_5042_;
}
else
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5066_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5067_ = l_Nat_reprFast(v_n_5034_);
v___x_5068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
v___x_5069_ = l_Lean_MessageData_ofFormat(v___x_5068_);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5066_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5070_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5063_, v___x_5072_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_dec_ref_known(v___x_5073_, 1);
goto v___jp_5042_;
}
else
{
return v___x_5073_;
}
}
}
}
else
{
lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5074_ = lean_unsigned_to_nat(1u);
v___x_5075_ = lean_nat_add(v_n_5034_, v___x_5074_);
lean_dec(v_n_5034_);
v_n_5034_ = v___x_5075_;
goto _start;
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_dec(v_n_5034_);
v_a_5077_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5057_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5057_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_){
_start:
{
lean_object* v_res_5096_; 
v_res_5096_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
lean_dec(v_a_5094_);
lean_dec_ref(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_a_5091_);
lean_dec(v_a_5090_);
lean_dec_ref(v_a_5089_);
return v_res_5096_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = 0;
v___x_5098_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5099_){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5100_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5101_ = lean_panic_fn_borrowed(v___x_5100_, v_msg_5099_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5102_, lean_object* v_msg_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v_options_5109_; lean_object* v_ref_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v_options_5109_ = lean_ctor_get(v___y_5106_, 2);
v_ref_5110_ = lean_ctor_get(v___y_5106_, 5);
v___x_5111_ = lean_st_ref_get(v___y_5107_);
v___x_5112_ = lean_st_ref_get(v___y_5105_);
v___x_5113_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5104_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5172_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5172_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5172_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v_env_5118_; lean_object* v_lctx_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5170_; 
v_env_5118_ = lean_ctor_get(v___x_5111_, 0);
lean_inc_ref(v_env_5118_);
lean_dec(v___x_5111_);
v_lctx_5119_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5170_ == 0)
{
lean_object* v_unused_5171_; 
v_unused_5171_ = lean_ctor_get(v___x_5112_, 1);
lean_dec(v_unused_5171_);
v___x_5121_ = v___x_5112_;
v_isShared_5122_ = v_isSharedCheck_5170_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_lctx_5119_);
lean_dec(v___x_5112_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5170_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v_traceState_5125_; lean_object* v_env_5126_; lean_object* v_nextMacroScope_5127_; lean_object* v_ngen_5128_; lean_object* v_auxDeclNGen_5129_; lean_object* v_cache_5130_; lean_object* v_messages_5131_; lean_object* v_infoState_5132_; lean_object* v_snapshotTasks_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5169_; 
v___x_5123_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__2);
v___x_5124_ = lean_st_ref_take(v___y_5107_);
v_traceState_5125_ = lean_ctor_get(v___x_5124_, 4);
v_env_5126_ = lean_ctor_get(v___x_5124_, 0);
v_nextMacroScope_5127_ = lean_ctor_get(v___x_5124_, 1);
v_ngen_5128_ = lean_ctor_get(v___x_5124_, 2);
v_auxDeclNGen_5129_ = lean_ctor_get(v___x_5124_, 3);
v_cache_5130_ = lean_ctor_get(v___x_5124_, 5);
v_messages_5131_ = lean_ctor_get(v___x_5124_, 6);
v_infoState_5132_ = lean_ctor_get(v___x_5124_, 7);
v_snapshotTasks_5133_ = lean_ctor_get(v___x_5124_, 8);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5135_ = v___x_5124_;
v_isShared_5136_ = v_isSharedCheck_5169_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_snapshotTasks_5133_);
lean_inc(v_infoState_5132_);
lean_inc(v_messages_5131_);
lean_inc(v_cache_5130_);
lean_inc(v_traceState_5125_);
lean_inc(v_auxDeclNGen_5129_);
lean_inc(v_ngen_5128_);
lean_inc(v_nextMacroScope_5127_);
lean_inc(v_env_5126_);
lean_dec(v___x_5124_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5169_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
uint64_t v_tid_5137_; lean_object* v_traces_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5168_; 
v_tid_5137_ = lean_ctor_get_uint64(v_traceState_5125_, sizeof(void*)*1);
v_traces_5138_ = lean_ctor_get(v_traceState_5125_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v_traceState_5125_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5140_ = v_traceState_5125_;
v_isShared_5141_ = v_isSharedCheck_5168_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_traces_5138_);
lean_dec(v_traceState_5125_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5168_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
uint8_t v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5146_; 
v___x_5142_ = lean_unbox(v_a_5114_);
lean_dec(v_a_5114_);
v___x_5143_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5119_, v___x_5142_);
lean_dec_ref(v_lctx_5119_);
lean_inc_ref(v_options_5109_);
v___x_5144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5144_, 0, v_env_5118_);
lean_ctor_set(v___x_5144_, 1, v___x_5123_);
lean_ctor_set(v___x_5144_, 2, v___x_5143_);
lean_ctor_set(v___x_5144_, 3, v_options_5109_);
if (v_isShared_5122_ == 0)
{
lean_ctor_set_tag(v___x_5121_, 3);
lean_ctor_set(v___x_5121_, 1, v_msg_5103_);
lean_ctor_set(v___x_5121_, 0, v___x_5144_);
v___x_5146_ = v___x_5121_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5144_);
lean_ctor_set(v_reuseFailAlloc_5167_, 1, v_msg_5103_);
v___x_5146_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
lean_object* v___x_5147_; double v___x_5148_; uint8_t v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5157_; 
v___x_5147_ = lean_box(0);
v___x_5148_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5149_ = 0;
v___x_5150_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5151_, 0, v_cls_5102_);
lean_ctor_set(v___x_5151_, 1, v___x_5147_);
lean_ctor_set(v___x_5151_, 2, v___x_5150_);
lean_ctor_set_float(v___x_5151_, sizeof(void*)*3, v___x_5148_);
lean_ctor_set_float(v___x_5151_, sizeof(void*)*3 + 8, v___x_5148_);
lean_ctor_set_uint8(v___x_5151_, sizeof(void*)*3 + 16, v___x_5149_);
v___x_5152_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5153_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5151_);
lean_ctor_set(v___x_5153_, 1, v___x_5146_);
lean_ctor_set(v___x_5153_, 2, v___x_5152_);
lean_inc(v_ref_5110_);
v___x_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5154_, 0, v_ref_5110_);
lean_ctor_set(v___x_5154_, 1, v___x_5153_);
v___x_5155_ = l_Lean_PersistentArray_push___redArg(v_traces_5138_, v___x_5154_);
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 0, v___x_5155_);
v___x_5157_ = v___x_5140_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5155_);
lean_ctor_set_uint64(v_reuseFailAlloc_5166_, sizeof(void*)*1, v_tid_5137_);
v___x_5157_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
lean_object* v___x_5159_; 
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 4, v___x_5157_);
v___x_5159_ = v___x_5135_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_env_5126_);
lean_ctor_set(v_reuseFailAlloc_5165_, 1, v_nextMacroScope_5127_);
lean_ctor_set(v_reuseFailAlloc_5165_, 2, v_ngen_5128_);
lean_ctor_set(v_reuseFailAlloc_5165_, 3, v_auxDeclNGen_5129_);
lean_ctor_set(v_reuseFailAlloc_5165_, 4, v___x_5157_);
lean_ctor_set(v_reuseFailAlloc_5165_, 5, v_cache_5130_);
lean_ctor_set(v_reuseFailAlloc_5165_, 6, v_messages_5131_);
lean_ctor_set(v_reuseFailAlloc_5165_, 7, v_infoState_5132_);
lean_ctor_set(v_reuseFailAlloc_5165_, 8, v_snapshotTasks_5133_);
v___x_5159_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5163_; 
v___x_5160_ = lean_st_ref_set(v___y_5107_, v___x_5159_);
v___x_5161_ = lean_box(0);
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 0, v___x_5161_);
v___x_5163_ = v___x_5116_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v___x_5161_);
v___x_5163_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
return v___x_5163_;
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
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec(v___x_5112_);
lean_dec(v___x_5111_);
lean_dec_ref(v_msg_5103_);
lean_dec(v_cls_5102_);
v_a_5173_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5113_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5113_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5181_, lean_object* v_msg_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5181_, v_msg_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5189_, size_t v_i_5190_, size_t v_stop_5191_, lean_object* v_b_5192_){
_start:
{
uint8_t v___x_5194_; 
v___x_5194_ = lean_usize_dec_eq(v_i_5190_, v_stop_5191_);
if (v___x_5194_ == 0)
{
lean_object* v_fst_5195_; lean_object* v_snd_5196_; lean_object* v___x_5197_; lean_object* v_snd_5198_; lean_object* v_fst_5199_; lean_object* v_fst_5200_; lean_object* v_snd_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5216_; 
v_fst_5195_ = lean_ctor_get(v_b_5192_, 0);
lean_inc(v_fst_5195_);
v_snd_5196_ = lean_ctor_get(v_b_5192_, 1);
lean_inc(v_snd_5196_);
lean_dec_ref(v_b_5192_);
v___x_5197_ = lean_array_uget_borrowed(v_as_5189_, v_i_5190_);
v_snd_5198_ = lean_ctor_get(v___x_5197_, 1);
lean_inc(v_snd_5198_);
v_fst_5199_ = lean_ctor_get(v___x_5197_, 0);
v_fst_5200_ = lean_ctor_get(v_snd_5198_, 0);
v_snd_5201_ = lean_ctor_get(v_snd_5198_, 1);
v_isSharedCheck_5216_ = !lean_is_exclusive(v_snd_5198_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5203_ = v_snd_5198_;
v_isShared_5204_ = v_isSharedCheck_5216_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_snd_5201_);
lean_inc(v_fst_5200_);
lean_dec(v_snd_5198_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5216_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v_fvarId_5205_; uint8_t v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5211_; 
v_fvarId_5205_ = lean_ctor_get(v_fst_5199_, 0);
v___x_5206_ = 0;
v___x_5207_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5206_, v_fst_5200_, v_fst_5195_);
lean_dec(v_fst_5200_);
v___x_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5208_, 0, v_snd_5201_);
lean_inc(v_fvarId_5205_);
v___x_5209_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5196_, v_fvarId_5205_, v___x_5208_);
if (v_isShared_5204_ == 0)
{
lean_ctor_set(v___x_5203_, 1, v___x_5209_);
lean_ctor_set(v___x_5203_, 0, v___x_5207_);
v___x_5211_ = v___x_5203_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5207_);
lean_ctor_set(v_reuseFailAlloc_5215_, 1, v___x_5209_);
v___x_5211_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
size_t v___x_5212_; size_t v___x_5213_; 
v___x_5212_ = ((size_t)1ULL);
v___x_5213_ = lean_usize_add(v_i_5190_, v___x_5212_);
v_i_5190_ = v___x_5213_;
v_b_5192_ = v___x_5211_;
goto _start;
}
}
}
else
{
lean_object* v___x_5217_; 
v___x_5217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5217_, 0, v_b_5192_);
return v___x_5217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5218_, lean_object* v_i_5219_, lean_object* v_stop_5220_, lean_object* v_b_5221_, lean_object* v___y_5222_){
_start:
{
size_t v_i_boxed_5223_; size_t v_stop_boxed_5224_; lean_object* v_res_5225_; 
v_i_boxed_5223_ = lean_unbox_usize(v_i_5219_);
lean_dec(v_i_5219_);
v_stop_boxed_5224_ = lean_unbox_usize(v_stop_5220_);
lean_dec(v_stop_5220_);
v_res_5225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5218_, v_i_boxed_5223_, v_stop_boxed_5224_, v_b_5221_);
lean_dec_ref(v_as_5218_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5226_, lean_object* v_x_5227_){
_start:
{
if (lean_obj_tag(v_x_5227_) == 0)
{
lean_object* v___x_5228_; 
v___x_5228_ = lean_box(0);
return v___x_5228_;
}
else
{
lean_object* v_key_5229_; lean_object* v_value_5230_; lean_object* v_tail_5231_; uint8_t v___x_5232_; 
v_key_5229_ = lean_ctor_get(v_x_5227_, 0);
v_value_5230_ = lean_ctor_get(v_x_5227_, 1);
v_tail_5231_ = lean_ctor_get(v_x_5227_, 2);
v___x_5232_ = l_Lean_instBEqFVarId_beq(v_key_5229_, v_a_5226_);
if (v___x_5232_ == 0)
{
v_x_5227_ = v_tail_5231_;
goto _start;
}
else
{
lean_object* v___x_5234_; 
lean_inc(v_value_5230_);
v___x_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5234_, 0, v_value_5230_);
return v___x_5234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5235_, lean_object* v_x_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5235_, v_x_5236_);
lean_dec(v_x_5236_);
lean_dec(v_a_5235_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_buckets_5240_; lean_object* v___x_5241_; uint64_t v___x_5242_; uint64_t v___x_5243_; uint64_t v___x_5244_; uint64_t v_fold_5245_; uint64_t v___x_5246_; uint64_t v___x_5247_; uint64_t v___x_5248_; size_t v___x_5249_; size_t v___x_5250_; size_t v___x_5251_; size_t v___x_5252_; size_t v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v_buckets_5240_ = lean_ctor_get(v_m_5238_, 1);
v___x_5241_ = lean_array_get_size(v_buckets_5240_);
v___x_5242_ = l_Lean_instHashableFVarId_hash(v_a_5239_);
v___x_5243_ = 32ULL;
v___x_5244_ = lean_uint64_shift_right(v___x_5242_, v___x_5243_);
v_fold_5245_ = lean_uint64_xor(v___x_5242_, v___x_5244_);
v___x_5246_ = 16ULL;
v___x_5247_ = lean_uint64_shift_right(v_fold_5245_, v___x_5246_);
v___x_5248_ = lean_uint64_xor(v_fold_5245_, v___x_5247_);
v___x_5249_ = lean_uint64_to_usize(v___x_5248_);
v___x_5250_ = lean_usize_of_nat(v___x_5241_);
v___x_5251_ = ((size_t)1ULL);
v___x_5252_ = lean_usize_sub(v___x_5250_, v___x_5251_);
v___x_5253_ = lean_usize_land(v___x_5249_, v___x_5252_);
v___x_5254_ = lean_array_uget_borrowed(v_buckets_5240_, v___x_5253_);
v___x_5255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5239_, v___x_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5256_, lean_object* v_a_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5256_, v_a_5257_);
lean_dec(v_a_5257_);
lean_dec_ref(v_m_5256_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5259_, lean_object* v_as_5260_, size_t v_i_5261_, size_t v_stop_5262_, lean_object* v_b_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
lean_object* v_a_5270_; uint8_t v___x_5274_; 
v___x_5274_ = lean_usize_dec_eq(v_i_5261_, v_stop_5262_);
if (v___x_5274_ == 0)
{
lean_object* v___x_5275_; lean_object* v_fvarId_5276_; lean_object* v___x_5277_; 
v___x_5275_ = lean_array_uget_borrowed(v_as_5260_, v_i_5261_);
v_fvarId_5276_ = lean_ctor_get(v___x_5275_, 0);
v___x_5277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5259_, v_fvarId_5276_);
if (lean_obj_tag(v___x_5277_) == 1)
{
lean_object* v_val_5278_; lean_object* v___x_5279_; 
v_val_5278_ = lean_ctor_get(v___x_5277_, 0);
lean_inc(v_val_5278_);
lean_dec_ref_known(v___x_5277_, 1);
v___x_5279_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5278_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref_known(v___x_5279_, 1);
if (lean_obj_tag(v_a_5280_) == 1)
{
lean_object* v_val_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v_val_5281_ = lean_ctor_get(v_a_5280_, 0);
lean_inc(v_val_5281_);
lean_dec_ref_known(v_a_5280_, 1);
lean_inc(v___x_5275_);
v___x_5282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5275_);
lean_ctor_set(v___x_5282_, 1, v_val_5281_);
v___x_5283_ = lean_array_push(v_b_5263_, v___x_5282_);
v_a_5270_ = v___x_5283_;
goto v___jp_5269_;
}
else
{
lean_dec(v_a_5280_);
v_a_5270_ = v_b_5263_;
goto v___jp_5269_;
}
}
else
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
lean_dec_ref(v_b_5263_);
v_a_5284_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5279_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5279_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
else
{
lean_dec(v___x_5277_);
v_a_5270_ = v_b_5263_;
goto v___jp_5269_;
}
}
else
{
lean_object* v___x_5292_; 
v___x_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5292_, 0, v_b_5263_);
return v___x_5292_;
}
v___jp_5269_:
{
size_t v___x_5271_; size_t v___x_5272_; 
v___x_5271_ = ((size_t)1ULL);
v___x_5272_ = lean_usize_add(v_i_5261_, v___x_5271_);
v_i_5261_ = v___x_5272_;
v_b_5263_ = v_a_5270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5293_, lean_object* v_as_5294_, lean_object* v_i_5295_, lean_object* v_stop_5296_, lean_object* v_b_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
size_t v_i_boxed_5303_; size_t v_stop_boxed_5304_; lean_object* v_res_5305_; 
v_i_boxed_5303_ = lean_unbox_usize(v_i_5295_);
lean_dec(v_i_5295_);
v_stop_boxed_5304_ = lean_unbox_usize(v_stop_5296_);
lean_dec(v_stop_5296_);
v_res_5305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5293_, v_as_5294_, v_i_boxed_5303_, v_stop_boxed_5304_, v_b_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec_ref(v_as_5294_);
lean_dec_ref(v_assignment_5293_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5308_, lean_object* v_as_5309_, lean_object* v_start_5310_, lean_object* v_stop_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v___x_5317_; uint8_t v___x_5318_; 
v___x_5317_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5318_ = lean_nat_dec_lt(v_start_5310_, v_stop_5311_);
if (v___x_5318_ == 0)
{
lean_object* v___x_5319_; 
v___x_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5317_);
return v___x_5319_;
}
else
{
lean_object* v___x_5320_; uint8_t v___x_5321_; 
v___x_5320_ = lean_array_get_size(v_as_5309_);
v___x_5321_ = lean_nat_dec_le(v_stop_5311_, v___x_5320_);
if (v___x_5321_ == 0)
{
uint8_t v___x_5322_; 
v___x_5322_ = lean_nat_dec_lt(v_start_5310_, v___x_5320_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
v___x_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5323_, 0, v___x_5317_);
return v___x_5323_;
}
else
{
size_t v___x_5324_; size_t v___x_5325_; lean_object* v___x_5326_; 
v___x_5324_ = lean_usize_of_nat(v_start_5310_);
v___x_5325_ = lean_usize_of_nat(v___x_5320_);
v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5308_, v_as_5309_, v___x_5324_, v___x_5325_, v___x_5317_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
return v___x_5326_;
}
}
else
{
size_t v___x_5327_; size_t v___x_5328_; lean_object* v___x_5329_; 
v___x_5327_ = lean_usize_of_nat(v_start_5310_);
v___x_5328_ = lean_usize_of_nat(v_stop_5311_);
v___x_5329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5308_, v_as_5309_, v___x_5327_, v___x_5328_, v___x_5317_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
return v___x_5329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5330_, lean_object* v_as_5331_, lean_object* v_start_5332_, lean_object* v_stop_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
lean_object* v_res_5339_; 
v_res_5339_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5330_, v_as_5331_, v_start_5332_, v_stop_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v_stop_5333_);
lean_dec(v_start_5332_);
lean_dec_ref(v_as_5331_);
lean_dec_ref(v_assignment_5330_);
return v_res_5339_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5342_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5343_ = lean_unsigned_to_nat(9u);
v___x_5344_ = lean_unsigned_to_nat(641u);
v___x_5345_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5346_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5347_ = l_mkPanicMessageWithDecl(v___x_5346_, v___x_5345_, v___x_5344_, v___x_5343_, v___x_5342_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5350_, lean_object* v_discrVal_5351_, lean_object* v_discr_5352_, lean_object* v_assignment_5353_, lean_object* v_i_5354_, lean_object* v_as_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v___x_5361_; uint8_t v___x_5362_; 
v___x_5361_ = lean_array_get_size(v_as_5355_);
v___x_5362_ = lean_nat_dec_lt(v_i_5354_, v___x_5361_);
if (v___x_5362_ == 0)
{
lean_object* v___x_5363_; 
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v___x_5363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5363_, 0, v_as_5355_);
return v___x_5363_;
}
else
{
lean_object* v_a_5364_; lean_object* v_a_5366_; 
v_a_5364_ = lean_array_fget_borrowed(v_as_5355_, v_i_5354_);
if (lean_obj_tag(v_a_5364_) == 0)
{
lean_object* v_ctorName_5377_; lean_object* v_params_5378_; lean_object* v_code_5379_; uint8_t v___x_5380_; lean_object* v___y_5382_; lean_object* v___y_5383_; lean_object* v___y_5396_; uint8_t v___x_5400_; 
v_ctorName_5377_ = lean_ctor_get(v_a_5364_, 0);
v_params_5378_ = lean_ctor_get(v_a_5364_, 1);
v_code_5379_ = lean_ctor_get(v_a_5364_, 2);
v___x_5380_ = 0;
v___x_5400_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5351_, v_ctorName_5377_);
if (v___x_5400_ == 0)
{
lean_object* v_options_5401_; uint8_t v_hasTrace_5402_; 
v_options_5401_ = lean_ctor_get(v___y_5358_, 2);
v_hasTrace_5402_ = lean_ctor_get_uint8(v_options_5401_, sizeof(void*)*1);
if (v_hasTrace_5402_ == 0)
{
v___y_5396_ = v___y_5357_;
goto v___jp_5395_;
}
else
{
lean_object* v_inheritedTraceOptions_5403_; lean_object* v_cls_5404_; lean_object* v___x_5405_; uint8_t v___x_5406_; 
v_inheritedTraceOptions_5403_ = lean_ctor_get(v___y_5358_, 13);
v_cls_5404_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5405_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5406_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5403_, v_options_5401_, v___x_5405_);
if (v___x_5406_ == 0)
{
v___y_5396_ = v___y_5357_;
goto v___jp_5395_;
}
else
{
lean_object* v___x_5407_; 
lean_inc(v_discr_5352_);
v___x_5407_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5352_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5407_) == 0)
{
lean_object* v_a_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
lean_inc(v_a_5408_);
lean_dec_ref_known(v___x_5407_, 1);
v___x_5409_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5408_, v___x_5406_);
v___x_5411_ = lean_string_append(v___x_5409_, v___x_5410_);
lean_dec_ref(v___x_5410_);
v___x_5412_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5413_ = lean_string_append(v___x_5411_, v___x_5412_);
lean_inc(v_ctorName_5377_);
v___x_5414_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5377_, v___x_5406_);
v___x_5415_ = lean_string_append(v___x_5413_, v___x_5414_);
lean_dec_ref(v___x_5414_);
v___x_5416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5416_, 0, v___x_5415_);
v___x_5417_ = l_Lean_MessageData_ofFormat(v___x_5416_);
v___x_5418_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5404_, v___x_5417_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5418_) == 0)
{
lean_dec_ref_known(v___x_5418_, 1);
v___y_5396_ = v___y_5357_;
goto v___jp_5395_;
}
else
{
lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5421_ = v___x_5418_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_dec(v___x_5418_);
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
else
{
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5434_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5427_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5429_ = v___x_5407_;
v_isShared_5430_ = v_isSharedCheck_5434_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v___x_5407_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5434_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v___x_5432_; 
if (v_isShared_5430_ == 0)
{
v___x_5432_ = v___x_5429_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_a_5427_);
v___x_5432_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
return v___x_5432_;
}
}
}
}
}
}
else
{
lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5435_ = lean_unsigned_to_nat(0u);
v___x_5436_ = lean_array_get_size(v_params_5378_);
v___x_5437_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5353_, v_params_5378_, v___x_5435_, v___x_5436_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5437_) == 0)
{
lean_object* v_a_5438_; lean_object* v___x_5451_; uint8_t v___x_5452_; lean_object* v_fst_5454_; lean_object* v_snd_5455_; lean_object* v___y_5468_; 
v_a_5438_ = lean_ctor_get(v___x_5437_, 0);
lean_inc(v_a_5438_);
lean_dec_ref_known(v___x_5437_, 1);
v___x_5451_ = lean_array_get_size(v_a_5438_);
v___x_5452_ = lean_nat_dec_eq(v___x_5451_, v___x_5435_);
if (v___x_5452_ == 0)
{
if (v___x_5400_ == 0)
{
lean_dec(v_a_5438_);
goto v___jp_5439_;
}
else
{
lean_object* v___x_5480_; 
lean_inc_ref(v_code_5379_);
v___x_5480_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5353_, v_code_5379_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5480_) == 0)
{
lean_object* v_a_5481_; lean_object* v___x_5482_; uint8_t v___x_5483_; 
v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
lean_inc(v_a_5481_);
lean_dec_ref_known(v___x_5480_, 1);
v___x_5482_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5483_ = lean_nat_dec_lt(v___x_5435_, v___x_5451_);
if (v___x_5483_ == 0)
{
lean_dec(v_a_5438_);
v_fst_5454_ = v_a_5481_;
v_snd_5455_ = v___x_5482_;
goto v___jp_5453_;
}
else
{
lean_object* v___x_5484_; uint8_t v___x_5485_; 
lean_inc(v_a_5481_);
v___x_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5484_, 0, v_a_5481_);
lean_ctor_set(v___x_5484_, 1, v___x_5482_);
v___x_5485_ = lean_nat_dec_le(v___x_5451_, v___x_5451_);
if (v___x_5485_ == 0)
{
if (v___x_5483_ == 0)
{
lean_dec_ref_known(v___x_5484_, 2);
lean_dec(v_a_5438_);
v_fst_5454_ = v_a_5481_;
v_snd_5455_ = v___x_5482_;
goto v___jp_5453_;
}
else
{
size_t v___x_5486_; size_t v___x_5487_; lean_object* v___x_5488_; 
lean_dec(v_a_5481_);
v___x_5486_ = ((size_t)0ULL);
v___x_5487_ = lean_usize_of_nat(v___x_5451_);
v___x_5488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5438_, v___x_5486_, v___x_5487_, v___x_5484_);
lean_dec(v_a_5438_);
v___y_5468_ = v___x_5488_;
goto v___jp_5467_;
}
}
else
{
size_t v___x_5489_; size_t v___x_5490_; lean_object* v___x_5491_; 
lean_dec(v_a_5481_);
v___x_5489_ = ((size_t)0ULL);
v___x_5490_ = lean_usize_of_nat(v___x_5451_);
v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5438_, v___x_5489_, v___x_5490_, v___x_5484_);
lean_dec(v_a_5438_);
v___y_5468_ = v___x_5491_;
goto v___jp_5467_;
}
}
}
else
{
lean_object* v_a_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5499_; 
lean_dec(v_a_5438_);
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5492_ = lean_ctor_get(v___x_5480_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5480_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5494_ = v___x_5480_;
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_a_5492_);
lean_dec(v___x_5480_);
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
}
else
{
lean_dec(v_a_5438_);
goto v___jp_5439_;
}
v___jp_5439_:
{
lean_object* v___x_5440_; 
lean_inc_ref(v_code_5379_);
v___x_5440_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5353_, v_code_5379_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v___x_5442_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v___x_5440_, 1);
lean_inc_ref(v_a_5364_);
v___x_5442_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5364_, v_a_5441_);
v_a_5366_ = v___x_5442_;
goto v___jp_5365_;
}
else
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5450_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5443_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5450_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5445_ = v___x_5440_;
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5440_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5448_; 
if (v_isShared_5446_ == 0)
{
v___x_5448_ = v___x_5445_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_a_5443_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
}
v___jp_5453_:
{
lean_object* v___x_5456_; 
v___x_5456_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5380_, v_fst_5454_, v_snd_5455_, v___x_5452_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
lean_dec_ref(v_snd_5455_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; lean_object* v___x_5458_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5456_, 1);
lean_inc_ref(v_a_5364_);
v___x_5458_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5364_, v_a_5457_);
v_a_5366_ = v___x_5458_;
goto v___jp_5365_;
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5459_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5456_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5456_);
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
v___jp_5467_:
{
if (lean_obj_tag(v___y_5468_) == 0)
{
lean_object* v_a_5469_; lean_object* v_fst_5470_; lean_object* v_snd_5471_; 
v_a_5469_ = lean_ctor_get(v___y_5468_, 0);
lean_inc(v_a_5469_);
lean_dec_ref_known(v___y_5468_, 1);
v_fst_5470_ = lean_ctor_get(v_a_5469_, 0);
lean_inc(v_fst_5470_);
v_snd_5471_ = lean_ctor_get(v_a_5469_, 1);
lean_inc(v_snd_5471_);
lean_dec(v_a_5469_);
v_fst_5454_ = v_fst_5470_;
v_snd_5455_ = v_snd_5471_;
goto v___jp_5453_;
}
else
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5479_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5472_ = lean_ctor_get(v___y_5468_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___y_5468_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5474_ = v___y_5468_;
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___y_5468_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5477_; 
if (v_isShared_5475_ == 0)
{
v___x_5477_ = v___x_5474_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
return v___x_5477_;
}
}
}
}
}
else
{
lean_object* v_a_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5507_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5500_ = lean_ctor_get(v___x_5437_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5437_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5502_ = v___x_5437_;
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_a_5500_);
lean_dec(v___x_5437_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5505_; 
if (v_isShared_5503_ == 0)
{
v___x_5505_ = v___x_5502_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5500_);
v___x_5505_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
return v___x_5505_;
}
}
}
}
v___jp_5381_:
{
lean_object* v___x_5384_; 
v___x_5384_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5380_, v___y_5383_, v___y_5382_);
lean_dec_ref(v___y_5383_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
lean_dec_ref_known(v___x_5384_, 1);
lean_inc_ref(v_resultType_5350_);
v___x_5385_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5385_, 0, v_resultType_5350_);
lean_inc_ref(v_a_5364_);
v___x_5386_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5364_, v___x_5385_);
v_a_5366_ = v___x_5386_;
goto v___jp_5365_;
}
else
{
lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5387_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5384_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5384_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5392_; 
if (v_isShared_5390_ == 0)
{
v___x_5392_ = v___x_5389_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
v___jp_5395_:
{
switch(lean_obj_tag(v_a_5364_))
{
case 0:
{
lean_object* v_code_5397_; 
v_code_5397_ = lean_ctor_get(v_a_5364_, 2);
lean_inc_ref(v_code_5397_);
v___y_5382_ = v___y_5396_;
v___y_5383_ = v_code_5397_;
goto v___jp_5381_;
}
case 1:
{
lean_object* v_code_5398_; 
v_code_5398_ = lean_ctor_get(v_a_5364_, 1);
lean_inc_ref(v_code_5398_);
v___y_5382_ = v___y_5396_;
v___y_5383_ = v_code_5398_;
goto v___jp_5381_;
}
default: 
{
lean_object* v_code_5399_; 
v_code_5399_ = lean_ctor_get(v_a_5364_, 0);
lean_inc_ref(v_code_5399_);
v___y_5382_ = v___y_5396_;
v___y_5383_ = v_code_5399_;
goto v___jp_5381_;
}
}
}
}
else
{
lean_object* v_code_5508_; lean_object* v___x_5509_; 
v_code_5508_ = lean_ctor_get(v_a_5364_, 0);
lean_inc_ref(v_code_5508_);
v___x_5509_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5353_, v_code_5508_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5509_) == 0)
{
lean_object* v_a_5510_; lean_object* v___x_5511_; 
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
lean_inc(v_a_5510_);
lean_dec_ref_known(v___x_5509_, 1);
lean_inc_ref(v_a_5364_);
v___x_5511_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5364_, v_a_5510_);
v_a_5366_ = v___x_5511_;
goto v___jp_5365_;
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
lean_dec_ref(v_as_5355_);
lean_dec(v_i_5354_);
lean_dec(v_discr_5352_);
lean_dec_ref(v_resultType_5350_);
v_a_5512_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5514_ = v___x_5509_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_dec(v___x_5509_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
v___jp_5365_:
{
size_t v___x_5367_; size_t v___x_5368_; uint8_t v___x_5369_; 
v___x_5367_ = lean_ptr_addr(v_a_5364_);
v___x_5368_ = lean_ptr_addr(v_a_5366_);
v___x_5369_ = lean_usize_dec_eq(v___x_5367_, v___x_5368_);
if (v___x_5369_ == 0)
{
lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; 
v___x_5370_ = lean_unsigned_to_nat(1u);
v___x_5371_ = lean_nat_add(v_i_5354_, v___x_5370_);
v___x_5372_ = lean_array_fset(v_as_5355_, v_i_5354_, v_a_5366_);
lean_dec(v_i_5354_);
v_i_5354_ = v___x_5371_;
v_as_5355_ = v___x_5372_;
goto _start;
}
else
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
lean_dec_ref(v_a_5366_);
v___x_5374_ = lean_unsigned_to_nat(1u);
v___x_5375_ = lean_nat_add(v_i_5354_, v___x_5374_);
lean_dec(v_i_5354_);
v_i_5354_ = v___x_5375_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5520_, lean_object* v_code_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_){
_start:
{
lean_object* v___y_5528_; lean_object* v___y_5529_; uint8_t v___y_5530_; lean_object* v___y_5535_; lean_object* v___y_5536_; uint8_t v___y_5537_; lean_object* v_decl_5542_; lean_object* v_k_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5547_; 
switch(lean_obj_tag(v_code_5521_))
{
case 0:
{
lean_object* v_decl_5593_; lean_object* v_k_5594_; lean_object* v___x_5595_; 
v_decl_5593_ = lean_ctor_get(v_code_5521_, 0);
v_k_5594_ = lean_ctor_get(v_code_5521_, 1);
lean_inc_ref(v_k_5594_);
v___x_5595_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5520_, v_k_5594_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_);
if (lean_obj_tag(v___x_5595_) == 0)
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5622_; 
v_a_5596_ = lean_ctor_get(v___x_5595_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5595_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5598_ = v___x_5595_;
v_isShared_5599_ = v_isSharedCheck_5622_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v___x_5595_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5622_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
uint8_t v___y_5601_; size_t v___x_5617_; size_t v___x_5618_; uint8_t v___x_5619_; 
v___x_5617_ = lean_ptr_addr(v_k_5594_);
v___x_5618_ = lean_ptr_addr(v_a_5596_);
v___x_5619_ = lean_usize_dec_eq(v___x_5617_, v___x_5618_);
if (v___x_5619_ == 0)
{
v___y_5601_ = v___x_5619_;
goto v___jp_5600_;
}
else
{
size_t v___x_5620_; uint8_t v___x_5621_; 
v___x_5620_ = lean_ptr_addr(v_decl_5593_);
v___x_5621_ = lean_usize_dec_eq(v___x_5620_, v___x_5620_);
v___y_5601_ = v___x_5621_;
goto v___jp_5600_;
}
v___jp_5600_:
{
if (v___y_5601_ == 0)
{
lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5611_; 
lean_inc_ref(v_decl_5593_);
v_isSharedCheck_5611_ = !lean_is_exclusive(v_code_5521_);
if (v_isSharedCheck_5611_ == 0)
{
lean_object* v_unused_5612_; lean_object* v_unused_5613_; 
v_unused_5612_ = lean_ctor_get(v_code_5521_, 1);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_code_5521_, 0);
lean_dec(v_unused_5613_);
v___x_5603_ = v_code_5521_;
v_isShared_5604_ = v_isSharedCheck_5611_;
goto v_resetjp_5602_;
}
else
{
lean_dec(v_code_5521_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5611_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 1, v_a_5596_);
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_decl_5593_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_a_5596_);
v___x_5606_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
lean_object* v___x_5608_; 
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 0, v___x_5606_);
v___x_5608_ = v___x_5598_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v___x_5606_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
}
else
{
lean_object* v___x_5615_; 
lean_dec(v_a_5596_);
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 0, v_code_5521_);
v___x_5615_ = v___x_5598_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_code_5521_);
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
else
{
lean_dec_ref_known(v_code_5521_, 2);
return v___x_5595_;
}
}
case 1:
{
lean_object* v_decl_5623_; lean_object* v_k_5624_; 
v_decl_5623_ = lean_ctor_get(v_code_5521_, 0);
v_k_5624_ = lean_ctor_get(v_code_5521_, 1);
lean_inc_ref(v_k_5624_);
lean_inc_ref(v_decl_5623_);
v_decl_5542_ = v_decl_5623_;
v_k_5543_ = v_k_5624_;
v___y_5544_ = v_a_5522_;
v___y_5545_ = v_a_5523_;
v___y_5546_ = v_a_5524_;
v___y_5547_ = v_a_5525_;
goto v___jp_5541_;
}
case 2:
{
lean_object* v_decl_5625_; lean_object* v_k_5626_; 
v_decl_5625_ = lean_ctor_get(v_code_5521_, 0);
v_k_5626_ = lean_ctor_get(v_code_5521_, 1);
lean_inc_ref(v_k_5626_);
lean_inc_ref(v_decl_5625_);
v_decl_5542_ = v_decl_5625_;
v_k_5543_ = v_k_5626_;
v___y_5544_ = v_a_5522_;
v___y_5545_ = v_a_5523_;
v___y_5546_ = v_a_5524_;
v___y_5547_ = v_a_5525_;
goto v___jp_5541_;
}
case 4:
{
lean_object* v_cases_5627_; lean_object* v_typeName_5628_; lean_object* v_resultType_5629_; lean_object* v_discr_5630_; lean_object* v_alts_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5672_; 
v_cases_5627_ = lean_ctor_get(v_code_5521_, 0);
lean_inc_ref(v_cases_5627_);
v_typeName_5628_ = lean_ctor_get(v_cases_5627_, 0);
v_resultType_5629_ = lean_ctor_get(v_cases_5627_, 1);
v_discr_5630_ = lean_ctor_get(v_cases_5627_, 2);
v_alts_5631_ = lean_ctor_get(v_cases_5627_, 3);
v_isSharedCheck_5672_ = !lean_is_exclusive(v_cases_5627_);
if (v_isSharedCheck_5672_ == 0)
{
v___x_5633_ = v_cases_5627_;
v_isShared_5634_ = v_isSharedCheck_5672_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_alts_5631_);
lean_inc(v_discr_5630_);
lean_inc(v_resultType_5629_);
lean_inc(v_typeName_5628_);
lean_dec(v_cases_5627_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5672_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v___x_5635_; lean_object* v_discrVal_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; 
v___x_5635_ = lean_box(0);
v_discrVal_5636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5520_, v_discr_5630_, v___x_5635_);
v___x_5637_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5631_);
lean_inc(v_discr_5630_);
lean_inc_ref(v_resultType_5629_);
v___x_5638_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5629_, v_discrVal_5636_, v_discr_5630_, v_assignment_5520_, v___x_5637_, v_alts_5631_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_);
lean_dec(v_discrVal_5636_);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_object* v_a_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5663_; 
v_a_5639_ = lean_ctor_get(v___x_5638_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5638_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5641_ = v___x_5638_;
v_isShared_5642_ = v_isSharedCheck_5663_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_a_5639_);
lean_dec(v___x_5638_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5663_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
size_t v___x_5643_; size_t v___x_5644_; uint8_t v___x_5645_; 
v___x_5643_ = lean_ptr_addr(v_alts_5631_);
lean_dec_ref(v_alts_5631_);
v___x_5644_ = lean_ptr_addr(v_a_5639_);
v___x_5645_ = lean_usize_dec_eq(v___x_5643_, v___x_5644_);
if (v___x_5645_ == 0)
{
lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5658_; 
v_isSharedCheck_5658_ = !lean_is_exclusive(v_code_5521_);
if (v_isSharedCheck_5658_ == 0)
{
lean_object* v_unused_5659_; 
v_unused_5659_ = lean_ctor_get(v_code_5521_, 0);
lean_dec(v_unused_5659_);
v___x_5647_ = v_code_5521_;
v_isShared_5648_ = v_isSharedCheck_5658_;
goto v_resetjp_5646_;
}
else
{
lean_dec(v_code_5521_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5658_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
lean_object* v___x_5650_; 
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 3, v_a_5639_);
v___x_5650_ = v___x_5633_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_typeName_5628_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_resultType_5629_);
lean_ctor_set(v_reuseFailAlloc_5657_, 2, v_discr_5630_);
lean_ctor_set(v_reuseFailAlloc_5657_, 3, v_a_5639_);
v___x_5650_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
lean_object* v___x_5652_; 
if (v_isShared_5648_ == 0)
{
lean_ctor_set(v___x_5647_, 0, v___x_5650_);
v___x_5652_ = v___x_5647_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v___x_5650_);
v___x_5652_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
lean_object* v___x_5654_; 
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 0, v___x_5652_);
v___x_5654_ = v___x_5641_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v___x_5652_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
}
}
else
{
lean_object* v___x_5661_; 
lean_dec(v_a_5639_);
lean_del_object(v___x_5633_);
lean_dec(v_discr_5630_);
lean_dec_ref(v_resultType_5629_);
lean_dec(v_typeName_5628_);
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 0, v_code_5521_);
v___x_5661_ = v___x_5641_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_code_5521_);
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
else
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5671_; 
lean_del_object(v___x_5633_);
lean_dec_ref(v_alts_5631_);
lean_dec(v_discr_5630_);
lean_dec_ref(v_resultType_5629_);
lean_dec(v_typeName_5628_);
lean_dec_ref_known(v_code_5521_, 1);
v_a_5664_ = lean_ctor_get(v___x_5638_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5638_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5666_ = v___x_5638_;
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5638_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
}
default: 
{
lean_object* v___x_5673_; 
v___x_5673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5673_, 0, v_code_5521_);
return v___x_5673_;
}
}
v___jp_5527_:
{
if (v___y_5530_ == 0)
{
lean_object* v___x_5531_; lean_object* v___x_5532_; 
lean_dec_ref(v_code_5521_);
v___x_5531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5531_, 0, v___y_5529_);
lean_ctor_set(v___x_5531_, 1, v___y_5528_);
v___x_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5531_);
return v___x_5532_;
}
else
{
lean_object* v___x_5533_; 
lean_dec_ref(v___y_5529_);
lean_dec_ref(v___y_5528_);
v___x_5533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5533_, 0, v_code_5521_);
return v___x_5533_;
}
}
v___jp_5534_:
{
if (v___y_5537_ == 0)
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
lean_dec_ref(v_code_5521_);
v___x_5538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5538_, 0, v___y_5536_);
lean_ctor_set(v___x_5538_, 1, v___y_5535_);
v___x_5539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5538_);
return v___x_5539_;
}
else
{
lean_object* v___x_5540_; 
lean_dec_ref(v___y_5536_);
lean_dec_ref(v___y_5535_);
v___x_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5540_, 0, v_code_5521_);
return v___x_5540_;
}
}
v___jp_5541_:
{
lean_object* v_params_5548_; lean_object* v_type_5549_; lean_object* v_value_5550_; lean_object* v___x_5551_; 
v_params_5548_ = lean_ctor_get(v_decl_5542_, 2);
lean_inc_ref(v_params_5548_);
v_type_5549_ = lean_ctor_get(v_decl_5542_, 3);
lean_inc_ref(v_type_5549_);
v_value_5550_ = lean_ctor_get(v_decl_5542_, 4);
lean_inc_ref(v_value_5550_);
v___x_5551_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5520_, v_value_5550_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_);
if (lean_obj_tag(v___x_5551_) == 0)
{
lean_object* v_a_5552_; uint8_t v___x_5553_; lean_object* v___x_5554_; 
v_a_5552_ = lean_ctor_get(v___x_5551_, 0);
lean_inc(v_a_5552_);
lean_dec_ref_known(v___x_5551_, 1);
v___x_5553_ = 0;
v___x_5554_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5553_, v_decl_5542_, v_type_5549_, v_params_5548_, v_a_5552_, v___y_5545_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v_a_5555_; lean_object* v___x_5556_; 
v_a_5555_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_a_5555_);
lean_dec_ref_known(v___x_5554_, 1);
v___x_5556_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5520_, v_k_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_);
if (lean_obj_tag(v___x_5556_) == 0)
{
switch(lean_obj_tag(v_code_5521_))
{
case 1:
{
lean_object* v_a_5557_; lean_object* v_decl_5558_; lean_object* v_k_5559_; size_t v___x_5560_; size_t v___x_5561_; uint8_t v___x_5562_; 
v_a_5557_ = lean_ctor_get(v___x_5556_, 0);
lean_inc(v_a_5557_);
lean_dec_ref_known(v___x_5556_, 1);
v_decl_5558_ = lean_ctor_get(v_code_5521_, 0);
v_k_5559_ = lean_ctor_get(v_code_5521_, 1);
v___x_5560_ = lean_ptr_addr(v_k_5559_);
v___x_5561_ = lean_ptr_addr(v_a_5557_);
v___x_5562_ = lean_usize_dec_eq(v___x_5560_, v___x_5561_);
if (v___x_5562_ == 0)
{
v___y_5528_ = v_a_5557_;
v___y_5529_ = v_a_5555_;
v___y_5530_ = v___x_5562_;
goto v___jp_5527_;
}
else
{
size_t v___x_5563_; size_t v___x_5564_; uint8_t v___x_5565_; 
v___x_5563_ = lean_ptr_addr(v_decl_5558_);
v___x_5564_ = lean_ptr_addr(v_a_5555_);
v___x_5565_ = lean_usize_dec_eq(v___x_5563_, v___x_5564_);
v___y_5528_ = v_a_5557_;
v___y_5529_ = v_a_5555_;
v___y_5530_ = v___x_5565_;
goto v___jp_5527_;
}
}
case 2:
{
lean_object* v_a_5566_; lean_object* v_decl_5567_; lean_object* v_k_5568_; size_t v___x_5569_; size_t v___x_5570_; uint8_t v___x_5571_; 
v_a_5566_ = lean_ctor_get(v___x_5556_, 0);
lean_inc(v_a_5566_);
lean_dec_ref_known(v___x_5556_, 1);
v_decl_5567_ = lean_ctor_get(v_code_5521_, 0);
v_k_5568_ = lean_ctor_get(v_code_5521_, 1);
v___x_5569_ = lean_ptr_addr(v_k_5568_);
v___x_5570_ = lean_ptr_addr(v_a_5566_);
v___x_5571_ = lean_usize_dec_eq(v___x_5569_, v___x_5570_);
if (v___x_5571_ == 0)
{
v___y_5535_ = v_a_5566_;
v___y_5536_ = v_a_5555_;
v___y_5537_ = v___x_5571_;
goto v___jp_5534_;
}
else
{
size_t v___x_5572_; size_t v___x_5573_; uint8_t v___x_5574_; 
v___x_5572_ = lean_ptr_addr(v_decl_5567_);
v___x_5573_ = lean_ptr_addr(v_a_5555_);
v___x_5574_ = lean_usize_dec_eq(v___x_5572_, v___x_5573_);
v___y_5535_ = v_a_5566_;
v___y_5536_ = v_a_5555_;
v___y_5537_ = v___x_5574_;
goto v___jp_5534_;
}
}
default: 
{
lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5583_; 
lean_dec(v_a_5555_);
lean_dec_ref(v_code_5521_);
v_isSharedCheck_5583_ = !lean_is_exclusive(v___x_5556_);
if (v_isSharedCheck_5583_ == 0)
{
lean_object* v_unused_5584_; 
v_unused_5584_ = lean_ctor_get(v___x_5556_, 0);
lean_dec(v_unused_5584_);
v___x_5576_ = v___x_5556_;
v_isShared_5577_ = v_isSharedCheck_5583_;
goto v_resetjp_5575_;
}
else
{
lean_dec(v___x_5556_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5583_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5581_; 
v___x_5578_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5579_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5578_);
if (v_isShared_5577_ == 0)
{
lean_ctor_set(v___x_5576_, 0, v___x_5579_);
v___x_5581_ = v___x_5576_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v___x_5579_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
}
}
}
else
{
lean_dec(v_a_5555_);
lean_dec_ref(v_code_5521_);
return v___x_5556_;
}
}
else
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
lean_dec_ref(v_k_5543_);
lean_dec_ref(v_code_5521_);
v_a_5585_ = lean_ctor_get(v___x_5554_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5554_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___x_5554_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
else
{
lean_dec_ref(v_type_5549_);
lean_dec_ref(v_params_5548_);
lean_dec_ref(v_k_5543_);
lean_dec_ref(v_decl_5542_);
lean_dec_ref(v_code_5521_);
return v___x_5551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5674_, lean_object* v_code_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_){
_start:
{
lean_object* v_res_5681_; 
v_res_5681_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5674_, v_code_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
lean_dec_ref(v_assignment_5674_);
return v_res_5681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5682_, lean_object* v_discrVal_5683_, lean_object* v_discr_5684_, lean_object* v_assignment_5685_, lean_object* v_i_5686_, lean_object* v_as_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v_res_5693_; 
v_res_5693_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5682_, v_discrVal_5683_, v_discr_5684_, v_assignment_5685_, v_i_5686_, v_as_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
lean_dec(v___y_5691_);
lean_dec_ref(v___y_5690_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
lean_dec_ref(v_assignment_5685_);
lean_dec(v_discrVal_5683_);
return v_res_5693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5694_, lean_object* v_m_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v___x_5697_; 
v___x_5697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5695_, v_a_5696_);
return v___x_5697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5698_, lean_object* v_m_5699_, lean_object* v_a_5700_){
_start:
{
lean_object* v_res_5701_; 
v_res_5701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5698_, v_m_5699_, v_a_5700_);
lean_dec(v_a_5700_);
lean_dec_ref(v_m_5699_);
return v_res_5701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5702_, size_t v_i_5703_, size_t v_stop_5704_, lean_object* v_b_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
lean_object* v___x_5711_; 
v___x_5711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5702_, v_i_5703_, v_stop_5704_, v_b_5705_);
return v___x_5711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5712_, lean_object* v_i_5713_, lean_object* v_stop_5714_, lean_object* v_b_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_){
_start:
{
size_t v_i_boxed_5721_; size_t v_stop_boxed_5722_; lean_object* v_res_5723_; 
v_i_boxed_5721_ = lean_unbox_usize(v_i_5713_);
lean_dec(v_i_5713_);
v_stop_boxed_5722_ = lean_unbox_usize(v_stop_5714_);
lean_dec(v_stop_5714_);
v_res_5723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5712_, v_i_boxed_5721_, v_stop_boxed_5722_, v_b_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
lean_dec(v___y_5719_);
lean_dec_ref(v___y_5718_);
lean_dec(v___y_5717_);
lean_dec_ref(v___y_5716_);
lean_dec_ref(v_as_5712_);
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5724_, lean_object* v_a_5725_, lean_object* v_x_5726_){
_start:
{
lean_object* v___x_5727_; 
v___x_5727_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5725_, v_x_5726_);
return v___x_5727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5728_, lean_object* v_a_5729_, lean_object* v_x_5730_){
_start:
{
lean_object* v_res_5731_; 
v_res_5731_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5728_, v_a_5729_, v_x_5730_);
lean_dec(v_x_5730_);
lean_dec(v_a_5729_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5732_, lean_object* v_v_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_){
_start:
{
if (lean_obj_tag(v_v_5733_) == 0)
{
lean_object* v_code_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5763_; 
v_code_5739_ = lean_ctor_get(v_v_5733_, 0);
v_isSharedCheck_5763_ = !lean_is_exclusive(v_v_5733_);
if (v_isSharedCheck_5763_ == 0)
{
v___x_5741_ = v_v_5733_;
v_isShared_5742_ = v_isSharedCheck_5763_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_code_5739_);
lean_dec(v_v_5733_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5763_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v___x_5743_; 
lean_inc(v___y_5737_);
lean_inc_ref(v___y_5736_);
lean_inc(v___y_5735_);
lean_inc_ref(v___y_5734_);
v___x_5743_ = lean_apply_6(v_f_5732_, v_code_5739_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, lean_box(0));
if (lean_obj_tag(v___x_5743_) == 0)
{
lean_object* v_a_5744_; lean_object* v___x_5746_; uint8_t v_isShared_5747_; uint8_t v_isSharedCheck_5754_; 
v_a_5744_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5754_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5754_ == 0)
{
v___x_5746_ = v___x_5743_;
v_isShared_5747_ = v_isSharedCheck_5754_;
goto v_resetjp_5745_;
}
else
{
lean_inc(v_a_5744_);
lean_dec(v___x_5743_);
v___x_5746_ = lean_box(0);
v_isShared_5747_ = v_isSharedCheck_5754_;
goto v_resetjp_5745_;
}
v_resetjp_5745_:
{
lean_object* v___x_5749_; 
if (v_isShared_5742_ == 0)
{
lean_ctor_set(v___x_5741_, 0, v_a_5744_);
v___x_5749_ = v___x_5741_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_a_5744_);
v___x_5749_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
lean_object* v___x_5751_; 
if (v_isShared_5747_ == 0)
{
lean_ctor_set(v___x_5746_, 0, v___x_5749_);
v___x_5751_ = v___x_5746_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5749_);
v___x_5751_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
return v___x_5751_;
}
}
}
}
else
{
lean_object* v_a_5755_; lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5762_; 
lean_del_object(v___x_5741_);
v_a_5755_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5757_ = v___x_5743_;
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
else
{
lean_inc(v_a_5755_);
lean_dec(v___x_5743_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5760_; 
if (v_isShared_5758_ == 0)
{
v___x_5760_ = v___x_5757_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_a_5755_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
}
}
else
{
lean_object* v___x_5764_; 
lean_dec_ref(v_f_5732_);
v___x_5764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5764_, 0, v_v_5733_);
return v___x_5764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5765_, lean_object* v_v_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_){
_start:
{
lean_object* v_res_5772_; 
v_res_5772_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5765_, v_v_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5773_, lean_object* v_f_5774_, lean_object* v_v_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_){
_start:
{
lean_object* v___x_5781_; 
v___x_5781_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5774_, v_v_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5782_, lean_object* v_f_5783_, lean_object* v_v_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_){
_start:
{
uint8_t v_pu_boxed_5790_; lean_object* v_res_5791_; 
v_pu_boxed_5790_ = lean_unbox(v_pu_5782_);
v_res_5791_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5790_, v_f_5783_, v_v_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
lean_dec(v___y_5788_);
lean_dec_ref(v___y_5787_);
lean_dec(v___y_5786_);
lean_dec_ref(v___y_5785_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5792_, lean_object* v_x_5793_){
_start:
{
if (lean_obj_tag(v_x_5793_) == 0)
{
return v_x_5792_;
}
else
{
lean_object* v_key_5794_; lean_object* v_value_5795_; lean_object* v_tail_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; 
v_key_5794_ = lean_ctor_get(v_x_5793_, 0);
v_value_5795_ = lean_ctor_get(v_x_5793_, 1);
v_tail_5796_ = lean_ctor_get(v_x_5793_, 2);
lean_inc(v_value_5795_);
lean_inc(v_key_5794_);
v___x_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5797_, 0, v_key_5794_);
lean_ctor_set(v___x_5797_, 1, v_value_5795_);
v___x_5798_ = lean_array_push(v_x_5792_, v___x_5797_);
v_x_5792_ = v___x_5798_;
v_x_5793_ = v_tail_5796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5800_, lean_object* v_x_5801_){
_start:
{
lean_object* v_res_5802_; 
v_res_5802_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5800_, v_x_5801_);
lean_dec(v_x_5801_);
return v_res_5802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5803_, size_t v_i_5804_, size_t v_stop_5805_, lean_object* v_b_5806_){
_start:
{
uint8_t v___x_5807_; 
v___x_5807_ = lean_usize_dec_eq(v_i_5804_, v_stop_5805_);
if (v___x_5807_ == 0)
{
lean_object* v___x_5808_; lean_object* v___x_5809_; size_t v___x_5810_; size_t v___x_5811_; 
v___x_5808_ = lean_array_uget_borrowed(v_as_5803_, v_i_5804_);
v___x_5809_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5806_, v___x_5808_);
v___x_5810_ = ((size_t)1ULL);
v___x_5811_ = lean_usize_add(v_i_5804_, v___x_5810_);
v_i_5804_ = v___x_5811_;
v_b_5806_ = v___x_5809_;
goto _start;
}
else
{
return v_b_5806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5813_, lean_object* v_i_5814_, lean_object* v_stop_5815_, lean_object* v_b_5816_){
_start:
{
size_t v_i_boxed_5817_; size_t v_stop_boxed_5818_; lean_object* v_res_5819_; 
v_i_boxed_5817_ = lean_unbox_usize(v_i_5814_);
lean_dec(v_i_5814_);
v_stop_boxed_5818_ = lean_unbox_usize(v_stop_5815_);
lean_dec(v_stop_5815_);
v_res_5819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5813_, v_i_boxed_5817_, v_stop_boxed_5818_, v_b_5816_);
lean_dec_ref(v_as_5813_);
return v_res_5819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5820_, size_t v_sz_5821_, size_t v_i_5822_, lean_object* v_bs_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_){
_start:
{
uint8_t v___x_5829_; 
v___x_5829_ = lean_usize_dec_lt(v_i_5822_, v_sz_5821_);
if (v___x_5829_ == 0)
{
lean_object* v___x_5830_; 
v___x_5830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5830_, 0, v_bs_5823_);
return v___x_5830_;
}
else
{
lean_object* v_v_5831_; lean_object* v_fst_5832_; lean_object* v_snd_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5857_; 
v_v_5831_ = lean_array_uget(v_bs_5823_, v_i_5822_);
v_fst_5832_ = lean_ctor_get(v_v_5831_, 0);
v_snd_5833_ = lean_ctor_get(v_v_5831_, 1);
v_isSharedCheck_5857_ = !lean_is_exclusive(v_v_5831_);
if (v_isSharedCheck_5857_ == 0)
{
v___x_5835_ = v_v_5831_;
v_isShared_5836_ = v_isSharedCheck_5857_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_snd_5833_);
lean_inc(v_fst_5832_);
lean_dec(v_v_5831_);
v___x_5835_ = lean_box(0);
v_isShared_5836_ = v_isSharedCheck_5857_;
goto v_resetjp_5834_;
}
v_resetjp_5834_:
{
lean_object* v___x_5837_; 
v___x_5837_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5832_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; lean_object* v___x_5839_; lean_object* v_bs_x27_5840_; lean_object* v___x_5841_; lean_object* v___x_5843_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5838_);
lean_dec_ref_known(v___x_5837_, 1);
v___x_5839_ = lean_unsigned_to_nat(0u);
v_bs_x27_5840_ = lean_array_uset(v_bs_5823_, v_i_5822_, v___x_5839_);
v___x_5841_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5838_, v_a_5820_);
if (v_isShared_5836_ == 0)
{
lean_ctor_set(v___x_5835_, 0, v___x_5841_);
v___x_5843_ = v___x_5835_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v___x_5841_);
lean_ctor_set(v_reuseFailAlloc_5848_, 1, v_snd_5833_);
v___x_5843_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
size_t v___x_5844_; size_t v___x_5845_; lean_object* v___x_5846_; 
v___x_5844_ = ((size_t)1ULL);
v___x_5845_ = lean_usize_add(v_i_5822_, v___x_5844_);
v___x_5846_ = lean_array_uset(v_bs_x27_5840_, v_i_5822_, v___x_5843_);
v_i_5822_ = v___x_5845_;
v_bs_5823_ = v___x_5846_;
goto _start;
}
}
else
{
lean_object* v_a_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5856_; 
lean_del_object(v___x_5835_);
lean_dec(v_snd_5833_);
lean_dec_ref(v_bs_5823_);
v_a_5849_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5851_ = v___x_5837_;
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_a_5849_);
lean_dec(v___x_5837_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5852_ == 0)
{
v___x_5854_ = v___x_5851_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_a_5849_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5858_, lean_object* v_sz_5859_, lean_object* v_i_5860_, lean_object* v_bs_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_){
_start:
{
uint8_t v_a_2702__boxed_5867_; size_t v_sz_boxed_5868_; size_t v_i_boxed_5869_; lean_object* v_res_5870_; 
v_a_2702__boxed_5867_ = lean_unbox(v_a_5858_);
v_sz_boxed_5868_ = lean_unbox_usize(v_sz_5859_);
lean_dec(v_sz_5859_);
v_i_boxed_5869_ = lean_unbox_usize(v_i_5860_);
lean_dec(v_i_5860_);
v_res_5870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2702__boxed_5867_, v_sz_boxed_5868_, v_i_boxed_5869_, v_bs_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec(v___y_5863_);
lean_dec_ref(v___y_5862_);
return v_res_5870_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5871_){
_start:
{
lean_object* v_fst_5872_; lean_object* v_snd_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5896_; 
v_fst_5872_ = lean_ctor_get(v_x_5871_, 0);
v_snd_5873_ = lean_ctor_get(v_x_5871_, 1);
v_isSharedCheck_5896_ = !lean_is_exclusive(v_x_5871_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5875_ = v_x_5871_;
v_isShared_5876_ = v_isSharedCheck_5896_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_snd_5873_);
lean_inc(v_fst_5872_);
lean_dec(v_x_5871_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5896_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5881_; 
v___x_5877_ = l_String_quote(v_fst_5872_);
v___x_5878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5877_);
v___x_5879_ = lean_box(0);
if (v_isShared_5876_ == 0)
{
lean_ctor_set_tag(v___x_5875_, 1);
lean_ctor_set(v___x_5875_, 1, v___x_5879_);
lean_ctor_set(v___x_5875_, 0, v___x_5878_);
v___x_5881_ = v___x_5875_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v___x_5878_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v___x_5879_);
v___x_5881_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; uint8_t v___x_5893_; lean_object* v___x_5894_; 
v___x_5882_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5873_);
v___x_5883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5882_);
lean_ctor_set(v___x_5883_, 1, v___x_5881_);
v___x_5884_ = l_List_reverse___redArg(v___x_5883_);
v___x_5885_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5886_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5884_, v___x_5885_);
v___x_5887_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5888_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5888_);
lean_ctor_set(v___x_5889_, 1, v___x_5886_);
v___x_5890_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5891_, 0, v___x_5889_);
lean_ctor_set(v___x_5891_, 1, v___x_5890_);
v___x_5892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5887_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = 0;
v___x_5894_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5894_, 0, v___x_5892_);
lean_ctor_set_uint8(v___x_5894_, sizeof(void*)*1, v___x_5893_);
return v___x_5894_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5897_, lean_object* v_x_5898_, lean_object* v_x_5899_){
_start:
{
if (lean_obj_tag(v_x_5899_) == 0)
{
lean_dec(v_x_5897_);
return v_x_5898_;
}
else
{
lean_object* v_head_5900_; lean_object* v_tail_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5911_; 
v_head_5900_ = lean_ctor_get(v_x_5899_, 0);
v_tail_5901_ = lean_ctor_get(v_x_5899_, 1);
v_isSharedCheck_5911_ = !lean_is_exclusive(v_x_5899_);
if (v_isSharedCheck_5911_ == 0)
{
v___x_5903_ = v_x_5899_;
v_isShared_5904_ = v_isSharedCheck_5911_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_tail_5901_);
lean_inc(v_head_5900_);
lean_dec(v_x_5899_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5911_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5906_; 
lean_inc(v_x_5897_);
if (v_isShared_5904_ == 0)
{
lean_ctor_set_tag(v___x_5903_, 5);
lean_ctor_set(v___x_5903_, 1, v_x_5897_);
lean_ctor_set(v___x_5903_, 0, v_x_5898_);
v___x_5906_ = v___x_5903_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_x_5898_);
lean_ctor_set(v_reuseFailAlloc_5910_, 1, v_x_5897_);
v___x_5906_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5907_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5900_);
v___x_5908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5906_);
lean_ctor_set(v___x_5908_, 1, v___x_5907_);
v_x_5898_ = v___x_5908_;
v_x_5899_ = v_tail_5901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5912_, lean_object* v_x_5913_, lean_object* v_x_5914_){
_start:
{
if (lean_obj_tag(v_x_5914_) == 0)
{
lean_dec(v_x_5912_);
return v_x_5913_;
}
else
{
lean_object* v_head_5915_; lean_object* v_tail_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5926_; 
v_head_5915_ = lean_ctor_get(v_x_5914_, 0);
v_tail_5916_ = lean_ctor_get(v_x_5914_, 1);
v_isSharedCheck_5926_ = !lean_is_exclusive(v_x_5914_);
if (v_isSharedCheck_5926_ == 0)
{
v___x_5918_ = v_x_5914_;
v_isShared_5919_ = v_isSharedCheck_5926_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_tail_5916_);
lean_inc(v_head_5915_);
lean_dec(v_x_5914_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5926_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5921_; 
lean_inc(v_x_5912_);
if (v_isShared_5919_ == 0)
{
lean_ctor_set_tag(v___x_5918_, 5);
lean_ctor_set(v___x_5918_, 1, v_x_5912_);
lean_ctor_set(v___x_5918_, 0, v_x_5913_);
v___x_5921_ = v___x_5918_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5925_; 
v_reuseFailAlloc_5925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_x_5913_);
lean_ctor_set(v_reuseFailAlloc_5925_, 1, v_x_5912_);
v___x_5921_ = v_reuseFailAlloc_5925_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; 
v___x_5922_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5915_);
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5921_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5912_, v___x_5923_, v_tail_5916_);
return v___x_5924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5927_, lean_object* v_x_5928_){
_start:
{
if (lean_obj_tag(v_x_5927_) == 0)
{
lean_object* v___x_5929_; 
lean_dec(v_x_5928_);
v___x_5929_ = lean_box(0);
return v___x_5929_;
}
else
{
lean_object* v_tail_5930_; 
v_tail_5930_ = lean_ctor_get(v_x_5927_, 1);
if (lean_obj_tag(v_tail_5930_) == 0)
{
lean_object* v_head_5931_; lean_object* v___x_5932_; 
lean_dec(v_x_5928_);
v_head_5931_ = lean_ctor_get(v_x_5927_, 0);
lean_inc(v_head_5931_);
lean_dec_ref_known(v_x_5927_, 2);
v___x_5932_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5931_);
return v___x_5932_;
}
else
{
lean_object* v_head_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
lean_inc(v_tail_5930_);
v_head_5933_ = lean_ctor_get(v_x_5927_, 0);
lean_inc(v_head_5933_);
lean_dec_ref_known(v_x_5927_, 2);
v___x_5934_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5933_);
v___x_5935_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5928_, v___x_5934_, v_tail_5930_);
return v___x_5935_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; 
v___x_5937_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5938_ = lean_string_length(v___x_5937_);
return v___x_5938_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5939_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5940_ = lean_nat_to_int(v___x_5939_);
return v___x_5940_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5946_){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; uint8_t v___x_5949_; 
v___x_5947_ = lean_array_get_size(v_xs_5946_);
v___x_5948_ = lean_unsigned_to_nat(0u);
v___x_5949_ = lean_nat_dec_eq(v___x_5947_, v___x_5948_);
if (v___x_5949_ == 0)
{
lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; 
v___x_5950_ = lean_array_to_list(v_xs_5946_);
v___x_5951_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5952_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5950_, v___x_5951_);
v___x_5953_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5954_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5954_);
lean_ctor_set(v___x_5955_, 1, v___x_5952_);
v___x_5956_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5955_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5953_);
lean_ctor_set(v___x_5958_, 1, v___x_5957_);
v___x_5959_ = l_Std_Format_fill(v___x_5958_);
return v___x_5959_;
}
else
{
lean_object* v___x_5960_; 
lean_dec_ref(v_xs_5946_);
v___x_5960_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_5960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_5963_, lean_object* v_decl_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_){
_start:
{
lean_object* v___y_5971_; lean_object* v___y_5972_; lean_object* v___y_5973_; lean_object* v___y_5974_; lean_object* v_options_6004_; uint8_t v_hasTrace_6005_; 
v_options_6004_ = lean_ctor_get(v_a_5967_, 2);
v_hasTrace_6005_ = lean_ctor_get_uint8(v_options_6004_, sizeof(void*)*1);
if (v_hasTrace_6005_ == 0)
{
v___y_5971_ = v_a_5965_;
v___y_5972_ = v_a_5966_;
v___y_5973_ = v_a_5967_;
v___y_5974_ = v_a_5968_;
goto v___jp_5970_;
}
else
{
lean_object* v_inheritedTraceOptions_6006_; lean_object* v_cls_6007_; uint8_t v___y_6009_; lean_object* v___y_6010_; lean_object* v___x_6046_; uint8_t v___x_6047_; 
v_inheritedTraceOptions_6006_ = lean_ctor_get(v_a_5967_, 13);
v_cls_6007_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6046_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6047_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6006_, v_options_6004_, v___x_6046_);
if (v___x_6047_ == 0)
{
v___y_5971_ = v_a_5965_;
v___y_5972_ = v_a_5966_;
v___y_5973_ = v_a_5967_;
v___y_5974_ = v_a_5968_;
goto v___jp_5970_;
}
else
{
lean_object* v_size_6048_; lean_object* v_buckets_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; uint8_t v___x_6053_; 
v_size_6048_ = lean_ctor_get(v_assignment_5963_, 0);
v_buckets_6049_ = lean_ctor_get(v_assignment_5963_, 1);
v___x_6050_ = lean_mk_empty_array_with_capacity(v_size_6048_);
v___x_6051_ = lean_unsigned_to_nat(0u);
v___x_6052_ = lean_array_get_size(v_buckets_6049_);
v___x_6053_ = lean_nat_dec_lt(v___x_6051_, v___x_6052_);
if (v___x_6053_ == 0)
{
v___y_6009_ = v___x_6047_;
v___y_6010_ = v___x_6050_;
goto v___jp_6008_;
}
else
{
uint8_t v___x_6054_; 
v___x_6054_ = lean_nat_dec_le(v___x_6052_, v___x_6052_);
if (v___x_6054_ == 0)
{
if (v___x_6053_ == 0)
{
v___y_6009_ = v___x_6047_;
v___y_6010_ = v___x_6050_;
goto v___jp_6008_;
}
else
{
size_t v___x_6055_; size_t v___x_6056_; lean_object* v___x_6057_; 
v___x_6055_ = ((size_t)0ULL);
v___x_6056_ = lean_usize_of_nat(v___x_6052_);
v___x_6057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6049_, v___x_6055_, v___x_6056_, v___x_6050_);
v___y_6009_ = v___x_6047_;
v___y_6010_ = v___x_6057_;
goto v___jp_6008_;
}
}
else
{
size_t v___x_6058_; size_t v___x_6059_; lean_object* v___x_6060_; 
v___x_6058_ = ((size_t)0ULL);
v___x_6059_ = lean_usize_of_nat(v___x_6052_);
v___x_6060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6049_, v___x_6058_, v___x_6059_, v___x_6050_);
v___y_6009_ = v___x_6047_;
v___y_6010_ = v___x_6060_;
goto v___jp_6008_;
}
}
}
v___jp_6008_:
{
size_t v_sz_6011_; size_t v___x_6012_; lean_object* v___x_6013_; 
v_sz_6011_ = lean_array_size(v___y_6010_);
v___x_6012_ = ((size_t)0ULL);
v___x_6013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6009_, v_sz_6011_, v___x_6012_, v___y_6010_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
if (lean_obj_tag(v___x_6013_) == 0)
{
lean_object* v_toSignature_6014_; lean_object* v_a_6015_; lean_object* v_name_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; 
v_toSignature_6014_ = lean_ctor_get(v_decl_5964_, 0);
v_a_6015_ = lean_ctor_get(v___x_6013_, 0);
lean_inc(v_a_6015_);
lean_dec_ref_known(v___x_6013_, 1);
v_name_6016_ = lean_ctor_get(v_toSignature_6014_, 0);
v___x_6017_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6016_);
v___x_6018_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6016_, v___y_6009_);
v___x_6019_ = lean_string_append(v___x_6017_, v___x_6018_);
lean_dec_ref(v___x_6018_);
v___x_6020_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6021_ = lean_string_append(v___x_6019_, v___x_6020_);
v___x_6022_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6015_);
v___x_6023_ = l_Std_Format_defWidth;
v___x_6024_ = lean_unsigned_to_nat(0u);
v___x_6025_ = l_Std_Format_pretty(v___x_6022_, v___x_6023_, v___x_6024_, v___x_6024_);
v___x_6026_ = lean_string_append(v___x_6021_, v___x_6025_);
lean_dec_ref(v___x_6025_);
v___x_6027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
v___x_6028_ = l_Lean_MessageData_ofFormat(v___x_6027_);
v___x_6029_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_6007_, v___x_6028_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
if (lean_obj_tag(v___x_6029_) == 0)
{
lean_dec_ref_known(v___x_6029_, 1);
v___y_5971_ = v_a_5965_;
v___y_5972_ = v_a_5966_;
v___y_5973_ = v_a_5967_;
v___y_5974_ = v_a_5968_;
goto v___jp_5970_;
}
else
{
lean_object* v_a_6030_; lean_object* v___x_6032_; uint8_t v_isShared_6033_; uint8_t v_isSharedCheck_6037_; 
lean_dec_ref(v_decl_5964_);
lean_dec_ref(v_assignment_5963_);
v_a_6030_ = lean_ctor_get(v___x_6029_, 0);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_6029_);
if (v_isSharedCheck_6037_ == 0)
{
v___x_6032_ = v___x_6029_;
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
else
{
lean_inc(v_a_6030_);
lean_dec(v___x_6029_);
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
else
{
lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6045_; 
lean_dec_ref(v_decl_5964_);
lean_dec_ref(v_assignment_5963_);
v_a_6038_ = lean_ctor_get(v___x_6013_, 0);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_6013_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6040_ = v___x_6013_;
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_6013_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
lean_object* v___x_6043_; 
if (v_isShared_6041_ == 0)
{
v___x_6043_ = v___x_6040_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_a_6038_);
v___x_6043_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
return v___x_6043_;
}
}
}
}
}
v___jp_5970_:
{
lean_object* v_toSignature_5975_; lean_object* v_value_5976_; uint8_t v_recursive_5977_; lean_object* v_inlineAttr_x3f_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_6003_; 
v_toSignature_5975_ = lean_ctor_get(v_decl_5964_, 0);
v_value_5976_ = lean_ctor_get(v_decl_5964_, 1);
v_recursive_5977_ = lean_ctor_get_uint8(v_decl_5964_, sizeof(void*)*3);
v_inlineAttr_x3f_5978_ = lean_ctor_get(v_decl_5964_, 2);
v_isSharedCheck_6003_ = !lean_is_exclusive(v_decl_5964_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5980_ = v_decl_5964_;
v_isShared_5981_ = v_isSharedCheck_6003_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_inlineAttr_x3f_5978_);
lean_inc(v_value_5976_);
lean_inc(v_toSignature_5975_);
lean_dec(v_decl_5964_);
v___x_5980_ = lean_box(0);
v_isShared_5981_ = v_isSharedCheck_6003_;
goto v_resetjp_5979_;
}
v_resetjp_5979_:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_5982_, 0, v_assignment_5963_);
v___x_5983_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_5982_, v_value_5976_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_);
if (lean_obj_tag(v___x_5983_) == 0)
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5994_; 
v_a_5984_ = lean_ctor_get(v___x_5983_, 0);
v_isSharedCheck_5994_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_5994_ == 0)
{
v___x_5986_ = v___x_5983_;
v_isShared_5987_ = v_isSharedCheck_5994_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v___x_5983_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5994_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5989_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 1, v_a_5984_);
v___x_5989_ = v___x_5980_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_toSignature_5975_);
lean_ctor_set(v_reuseFailAlloc_5993_, 1, v_a_5984_);
lean_ctor_set(v_reuseFailAlloc_5993_, 2, v_inlineAttr_x3f_5978_);
lean_ctor_set_uint8(v_reuseFailAlloc_5993_, sizeof(void*)*3, v_recursive_5977_);
v___x_5989_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
lean_object* v___x_5991_; 
if (v_isShared_5987_ == 0)
{
lean_ctor_set(v___x_5986_, 0, v___x_5989_);
v___x_5991_ = v___x_5986_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5989_);
v___x_5991_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
return v___x_5991_;
}
}
}
}
else
{
lean_object* v_a_5995_; lean_object* v___x_5997_; uint8_t v_isShared_5998_; uint8_t v_isSharedCheck_6002_; 
lean_del_object(v___x_5980_);
lean_dec(v_inlineAttr_x3f_5978_);
lean_dec_ref(v_toSignature_5975_);
v_a_5995_ = lean_ctor_get(v___x_5983_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_6002_ == 0)
{
v___x_5997_ = v___x_5983_;
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
else
{
lean_inc(v_a_5995_);
lean_dec(v___x_5983_);
v___x_5997_ = lean_box(0);
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
v_resetjp_5996_:
{
lean_object* v___x_6000_; 
if (v_isShared_5998_ == 0)
{
v___x_6000_ = v___x_5997_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v_a_5995_);
v___x_6000_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
return v___x_6000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6061_, lean_object* v_decl_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_){
_start:
{
lean_object* v_res_6068_; 
v_res_6068_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6061_, v_decl_6062_, v_a_6063_, v_a_6064_, v_a_6065_, v_a_6066_);
lean_dec(v_a_6066_);
lean_dec_ref(v_a_6065_);
lean_dec(v_a_6064_);
lean_dec_ref(v_a_6063_);
return v_res_6068_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6069_, lean_object* v_x_6070_){
_start:
{
lean_object* v___x_6071_; 
v___x_6071_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6069_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6072_, lean_object* v_x_6073_){
_start:
{
lean_object* v_res_6074_; 
v_res_6074_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6072_, v_x_6073_);
lean_dec(v_x_6073_);
return v_res_6074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6075_, size_t v_i_6076_, lean_object* v_bs_6077_){
_start:
{
uint8_t v___x_6078_; 
v___x_6078_ = lean_usize_dec_lt(v_i_6076_, v_sz_6075_);
if (v___x_6078_ == 0)
{
return v_bs_6077_;
}
else
{
lean_object* v_v_6079_; lean_object* v_toSignature_6080_; lean_object* v_name_6081_; lean_object* v___x_6082_; lean_object* v_bs_x27_6083_; size_t v___x_6084_; size_t v___x_6085_; lean_object* v___x_6086_; 
v_v_6079_ = lean_array_uget_borrowed(v_bs_6077_, v_i_6076_);
v_toSignature_6080_ = lean_ctor_get(v_v_6079_, 0);
v_name_6081_ = lean_ctor_get(v_toSignature_6080_, 0);
lean_inc(v_name_6081_);
v___x_6082_ = lean_unsigned_to_nat(0u);
v_bs_x27_6083_ = lean_array_uset(v_bs_6077_, v_i_6076_, v___x_6082_);
v___x_6084_ = ((size_t)1ULL);
v___x_6085_ = lean_usize_add(v_i_6076_, v___x_6084_);
v___x_6086_ = lean_array_uset(v_bs_x27_6083_, v_i_6076_, v_name_6081_);
v_i_6076_ = v___x_6085_;
v_bs_6077_ = v___x_6086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6088_, lean_object* v_i_6089_, lean_object* v_bs_6090_){
_start:
{
size_t v_sz_boxed_6091_; size_t v_i_boxed_6092_; lean_object* v_res_6093_; 
v_sz_boxed_6091_ = lean_unbox_usize(v_sz_6088_);
lean_dec(v_sz_6088_);
v_i_boxed_6092_ = lean_unbox_usize(v_i_6089_);
lean_dec(v_i_6089_);
v_res_6093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6091_, v_i_boxed_6092_, v_bs_6090_);
return v_res_6093_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6094_, lean_object* v_a_6095_){
_start:
{
if (lean_obj_tag(v_a_6094_) == 0)
{
lean_object* v___x_6096_; 
v___x_6096_ = l_List_reverse___redArg(v_a_6095_);
return v___x_6096_;
}
else
{
lean_object* v_head_6097_; lean_object* v_tail_6098_; lean_object* v___x_6100_; uint8_t v_isShared_6101_; uint8_t v_isSharedCheck_6107_; 
v_head_6097_ = lean_ctor_get(v_a_6094_, 0);
v_tail_6098_ = lean_ctor_get(v_a_6094_, 1);
v_isSharedCheck_6107_ = !lean_is_exclusive(v_a_6094_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6100_ = v_a_6094_;
v_isShared_6101_ = v_isSharedCheck_6107_;
goto v_resetjp_6099_;
}
else
{
lean_inc(v_tail_6098_);
lean_inc(v_head_6097_);
lean_dec(v_a_6094_);
v___x_6100_ = lean_box(0);
v_isShared_6101_ = v_isSharedCheck_6107_;
goto v_resetjp_6099_;
}
v_resetjp_6099_:
{
lean_object* v___x_6102_; lean_object* v___x_6104_; 
v___x_6102_ = l_Lean_MessageData_ofName(v_head_6097_);
if (v_isShared_6101_ == 0)
{
lean_ctor_set(v___x_6100_, 1, v_a_6095_);
lean_ctor_set(v___x_6100_, 0, v___x_6102_);
v___x_6104_ = v___x_6100_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6106_; 
v_reuseFailAlloc_6106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6106_, 0, v___x_6102_);
lean_ctor_set(v_reuseFailAlloc_6106_, 1, v_a_6095_);
v___x_6104_ = v_reuseFailAlloc_6106_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
v_a_6094_ = v_tail_6098_;
v_a_6095_ = v___x_6104_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6109_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6110_ = l_Lean_stringToMessageData(v___x_6109_);
return v___x_6110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6111_, lean_object* v_x_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_){
_start:
{
lean_object* v___x_6120_; size_t v_sz_6121_; size_t v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___x_6120_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6121_ = lean_array_size(v___y_6111_);
v___x_6122_ = ((size_t)0ULL);
v___x_6123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6121_, v___x_6122_, v___y_6111_);
v___x_6124_ = lean_array_to_list(v___x_6123_);
v___x_6125_ = lean_box(0);
v___x_6126_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6124_, v___x_6125_);
v___x_6127_ = l_Lean_MessageData_ofList(v___x_6126_);
v___x_6128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6120_);
lean_ctor_set(v___x_6128_, 1, v___x_6127_);
v___x_6129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6130_, lean_object* v_x_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6130_, v_x_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_);
lean_dec(v___y_6137_);
lean_dec_ref(v___y_6136_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
lean_dec_ref(v_x_6131_);
return v_res_6139_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6140_; lean_object* v___x_6141_; 
v___x_6140_ = 0;
v___x_6141_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6140_);
return v___x_6141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6142_, lean_object* v_n_6143_, lean_object* v_j_6144_, lean_object* v_a_6145_){
_start:
{
lean_object* v_zero_6146_; uint8_t v_isZero_6147_; 
v_zero_6146_ = lean_unsigned_to_nat(0u);
v_isZero_6147_ = lean_nat_dec_eq(v_j_6144_, v_zero_6146_);
if (v_isZero_6147_ == 1)
{
lean_dec(v_j_6144_);
return v_a_6145_;
}
else
{
lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v_toSignature_6151_; uint8_t v_safe_6152_; lean_object* v_one_6153_; lean_object* v_n_6154_; 
v___x_6148_ = lean_nat_sub(v_n_6143_, v_j_6144_);
v___x_6149_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6150_ = lean_array_get_borrowed(v___x_6149_, v___y_6142_, v___x_6148_);
lean_dec(v___x_6148_);
v_toSignature_6151_ = lean_ctor_get(v___x_6150_, 0);
v_safe_6152_ = lean_ctor_get_uint8(v_toSignature_6151_, sizeof(void*)*4);
v_one_6153_ = lean_unsigned_to_nat(1u);
v_n_6154_ = lean_nat_sub(v_j_6144_, v_one_6153_);
lean_dec(v_j_6144_);
if (v_safe_6152_ == 0)
{
lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6155_ = lean_box(1);
v___x_6156_ = lean_array_push(v_a_6145_, v___x_6155_);
v_j_6144_ = v_n_6154_;
v_a_6145_ = v___x_6156_;
goto _start;
}
else
{
lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6158_ = lean_box(0);
v___x_6159_ = lean_array_push(v_a_6145_, v___x_6158_);
v_j_6144_ = v_n_6154_;
v_a_6145_ = v___x_6159_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6161_, lean_object* v_n_6162_, lean_object* v_j_6163_, lean_object* v_a_6164_){
_start:
{
lean_object* v_res_6165_; 
v_res_6165_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6161_, v_n_6162_, v_j_6163_, v_a_6164_);
lean_dec(v_n_6162_);
lean_dec_ref(v___y_6161_);
return v_res_6165_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6166_, lean_object* v_as_6167_, lean_object* v_i_6168_, lean_object* v_j_6169_, lean_object* v_bs_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_){
_start:
{
lean_object* v_zero_6176_; uint8_t v_isZero_6177_; 
v_zero_6176_ = lean_unsigned_to_nat(0u);
v_isZero_6177_ = lean_nat_dec_eq(v_i_6168_, v_zero_6176_);
if (v_isZero_6177_ == 1)
{
lean_object* v___x_6178_; 
lean_dec(v_j_6169_);
lean_dec(v_i_6168_);
v___x_6178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6178_, 0, v_bs_6170_);
return v___x_6178_;
}
else
{
lean_object* v___x_6179_; lean_object* v_toSignature_6180_; uint8_t v_safe_6181_; lean_object* v_one_6182_; lean_object* v_n_6183_; lean_object* v_a_6185_; 
v___x_6179_ = lean_array_fget_borrowed(v_as_6167_, v_j_6169_);
v_toSignature_6180_ = lean_ctor_get(v___x_6179_, 0);
v_safe_6181_ = lean_ctor_get_uint8(v_toSignature_6180_, sizeof(void*)*4);
v_one_6182_ = lean_unsigned_to_nat(1u);
v_n_6183_ = lean_nat_sub(v_i_6168_, v_one_6182_);
lean_dec(v_i_6168_);
if (v_safe_6181_ == 0)
{
lean_inc(v___x_6179_);
v_a_6185_ = v___x_6179_;
goto v___jp_6184_;
}
else
{
lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; 
v___x_6189_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6190_ = lean_array_get_borrowed(v___x_6189_, v___x_6166_, v_j_6169_);
lean_inc(v___x_6179_);
lean_inc(v___x_6190_);
v___x_6191_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6190_, v___x_6179_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_);
if (lean_obj_tag(v___x_6191_) == 0)
{
lean_object* v_a_6192_; 
v_a_6192_ = lean_ctor_get(v___x_6191_, 0);
lean_inc(v_a_6192_);
lean_dec_ref_known(v___x_6191_, 1);
v_a_6185_ = v_a_6192_;
goto v___jp_6184_;
}
else
{
lean_object* v_a_6193_; lean_object* v___x_6195_; uint8_t v_isShared_6196_; uint8_t v_isSharedCheck_6200_; 
lean_dec(v_n_6183_);
lean_dec_ref(v_bs_6170_);
lean_dec(v_j_6169_);
v_a_6193_ = lean_ctor_get(v___x_6191_, 0);
v_isSharedCheck_6200_ = !lean_is_exclusive(v___x_6191_);
if (v_isSharedCheck_6200_ == 0)
{
v___x_6195_ = v___x_6191_;
v_isShared_6196_ = v_isSharedCheck_6200_;
goto v_resetjp_6194_;
}
else
{
lean_inc(v_a_6193_);
lean_dec(v___x_6191_);
v___x_6195_ = lean_box(0);
v_isShared_6196_ = v_isSharedCheck_6200_;
goto v_resetjp_6194_;
}
v_resetjp_6194_:
{
lean_object* v___x_6198_; 
if (v_isShared_6196_ == 0)
{
v___x_6198_ = v___x_6195_;
goto v_reusejp_6197_;
}
else
{
lean_object* v_reuseFailAlloc_6199_; 
v_reuseFailAlloc_6199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6199_, 0, v_a_6193_);
v___x_6198_ = v_reuseFailAlloc_6199_;
goto v_reusejp_6197_;
}
v_reusejp_6197_:
{
return v___x_6198_;
}
}
}
}
v___jp_6184_:
{
lean_object* v___x_6186_; lean_object* v___x_6187_; 
v___x_6186_ = lean_nat_add(v_j_6169_, v_one_6182_);
lean_dec(v_j_6169_);
v___x_6187_ = lean_array_push(v_bs_6170_, v_a_6185_);
v_i_6168_ = v_n_6183_;
v_j_6169_ = v___x_6186_;
v_bs_6170_ = v___x_6187_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6201_, lean_object* v_as_6202_, lean_object* v_i_6203_, lean_object* v_j_6204_, lean_object* v_bs_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_){
_start:
{
lean_object* v_res_6211_; 
v_res_6211_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6201_, v_as_6202_, v_i_6203_, v_j_6204_, v_bs_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
lean_dec(v___y_6209_);
lean_dec_ref(v___y_6208_);
lean_dec(v___y_6207_);
lean_dec_ref(v___y_6206_);
lean_dec_ref(v_as_6202_);
lean_dec_ref(v___x_6201_);
return v_res_6211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6214_, lean_object* v_pivot_6215_, lean_object* v_as_6216_, lean_object* v_i_6217_, lean_object* v_k_6218_){
_start:
{
uint8_t v___x_6219_; 
v___x_6219_ = lean_nat_dec_lt(v_k_6218_, v_hi_6214_);
if (v___x_6219_ == 0)
{
lean_object* v___x_6220_; lean_object* v___x_6221_; 
lean_dec(v_k_6218_);
lean_dec_ref(v_pivot_6215_);
v___x_6220_ = lean_array_fswap(v_as_6216_, v_i_6217_, v_hi_6214_);
v___x_6221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6221_, 0, v_i_6217_);
lean_ctor_set(v___x_6221_, 1, v___x_6220_);
return v___x_6221_;
}
else
{
lean_object* v___x_6222_; lean_object* v_toSignature_6223_; lean_object* v_toSignature_6224_; lean_object* v_name_6225_; lean_object* v_name_6226_; uint8_t v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; uint8_t v___x_6237_; 
v___x_6222_ = lean_array_fget_borrowed(v_as_6216_, v_k_6218_);
v_toSignature_6223_ = lean_ctor_get(v___x_6222_, 0);
v_toSignature_6224_ = lean_ctor_get(v_pivot_6215_, 0);
v_name_6225_ = lean_ctor_get(v_toSignature_6223_, 0);
v_name_6226_ = lean_ctor_get(v_toSignature_6224_, 0);
v___x_6227_ = 0;
v___x_6228_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6227_, v___x_6222_);
v___x_6229_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6230_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6231_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6225_);
v___x_6232_ = l_Lean_Name_toString(v_name_6225_, v___x_6219_);
v___x_6233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6233_, 0, v___x_6228_);
lean_ctor_set(v___x_6233_, 1, v___x_6232_);
v___x_6234_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6227_, v_pivot_6215_);
lean_inc(v_name_6226_);
v___x_6235_ = l_Lean_Name_toString(v_name_6226_, v___x_6219_);
v___x_6236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6236_, 0, v___x_6234_);
lean_ctor_set(v___x_6236_, 1, v___x_6235_);
v___x_6237_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6229_, v___x_6230_, v___x_6231_, v___x_6233_, v___x_6236_);
if (v___x_6237_ == 0)
{
lean_object* v___x_6238_; lean_object* v___x_6239_; 
v___x_6238_ = lean_unsigned_to_nat(1u);
v___x_6239_ = lean_nat_add(v_k_6218_, v___x_6238_);
lean_dec(v_k_6218_);
v_k_6218_ = v___x_6239_;
goto _start;
}
else
{
lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; 
v___x_6241_ = lean_array_fswap(v_as_6216_, v_i_6217_, v_k_6218_);
v___x_6242_ = lean_unsigned_to_nat(1u);
v___x_6243_ = lean_nat_add(v_i_6217_, v___x_6242_);
lean_dec(v_i_6217_);
v___x_6244_ = lean_nat_add(v_k_6218_, v___x_6242_);
lean_dec(v_k_6218_);
v_as_6216_ = v___x_6241_;
v_i_6217_ = v___x_6243_;
v_k_6218_ = v___x_6244_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6246_, lean_object* v_pivot_6247_, lean_object* v_as_6248_, lean_object* v_i_6249_, lean_object* v_k_6250_){
_start:
{
lean_object* v_res_6251_; 
v_res_6251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6246_, v_pivot_6247_, v_as_6248_, v_i_6249_, v_k_6250_);
lean_dec(v_hi_6246_);
return v_res_6251_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6252_, lean_object* v_l_6253_, lean_object* v_r_6254_){
_start:
{
lean_object* v_toSignature_6255_; lean_object* v_toSignature_6256_; lean_object* v_name_6257_; lean_object* v_name_6258_; uint8_t v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; uint8_t v___x_6269_; 
v_toSignature_6255_ = lean_ctor_get(v_l_6253_, 0);
v_toSignature_6256_ = lean_ctor_get(v_r_6254_, 0);
v_name_6257_ = lean_ctor_get(v_toSignature_6255_, 0);
lean_inc(v_name_6257_);
v_name_6258_ = lean_ctor_get(v_toSignature_6256_, 0);
lean_inc(v_name_6258_);
v___x_6259_ = 0;
v___x_6260_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6259_, v_l_6253_);
lean_dec_ref(v_l_6253_);
v___x_6261_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6262_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6263_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6264_ = l_Lean_Name_toString(v_name_6257_, v___x_6252_);
v___x_6265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6265_, 0, v___x_6260_);
lean_ctor_set(v___x_6265_, 1, v___x_6264_);
v___x_6266_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6259_, v_r_6254_);
lean_dec_ref(v_r_6254_);
v___x_6267_ = l_Lean_Name_toString(v_name_6258_, v___x_6252_);
v___x_6268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6268_, 0, v___x_6266_);
lean_ctor_set(v___x_6268_, 1, v___x_6267_);
v___x_6269_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6261_, v___x_6262_, v___x_6263_, v___x_6265_, v___x_6268_);
return v___x_6269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6270_, lean_object* v_l_6271_, lean_object* v_r_6272_){
_start:
{
uint8_t v___x_13130__boxed_6273_; uint8_t v_res_6274_; lean_object* v_r_6275_; 
v___x_13130__boxed_6273_ = lean_unbox(v___x_6270_);
v_res_6274_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13130__boxed_6273_, v_l_6271_, v_r_6272_);
v_r_6275_ = lean_box(v_res_6274_);
return v_r_6275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6276_, lean_object* v_as_6277_, lean_object* v_lo_6278_, lean_object* v_hi_6279_){
_start:
{
lean_object* v___y_6281_; uint8_t v___x_6291_; 
v___x_6291_ = lean_nat_dec_lt(v_lo_6278_, v_hi_6279_);
if (v___x_6291_ == 0)
{
lean_dec(v_lo_6278_);
return v_as_6277_;
}
else
{
lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v_mid_6294_; lean_object* v___y_6296_; lean_object* v___y_6302_; lean_object* v___x_6307_; lean_object* v___x_6308_; uint8_t v___x_6309_; 
v___x_6292_ = lean_nat_add(v_lo_6278_, v_hi_6279_);
v___x_6293_ = lean_unsigned_to_nat(1u);
v_mid_6294_ = lean_nat_shiftr(v___x_6292_, v___x_6293_);
lean_dec(v___x_6292_);
v___x_6307_ = lean_array_fget_borrowed(v_as_6277_, v_mid_6294_);
v___x_6308_ = lean_array_fget_borrowed(v_as_6277_, v_lo_6278_);
lean_inc(v___x_6308_);
lean_inc(v___x_6307_);
v___x_6309_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6291_, v___x_6307_, v___x_6308_);
if (v___x_6309_ == 0)
{
v___y_6302_ = v_as_6277_;
goto v___jp_6301_;
}
else
{
lean_object* v___x_6310_; 
v___x_6310_ = lean_array_fswap(v_as_6277_, v_lo_6278_, v_mid_6294_);
v___y_6302_ = v___x_6310_;
goto v___jp_6301_;
}
v___jp_6295_:
{
lean_object* v___x_6297_; lean_object* v___x_6298_; uint8_t v___x_6299_; 
v___x_6297_ = lean_array_fget_borrowed(v___y_6296_, v_mid_6294_);
v___x_6298_ = lean_array_fget_borrowed(v___y_6296_, v_hi_6279_);
lean_inc(v___x_6298_);
lean_inc(v___x_6297_);
v___x_6299_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6291_, v___x_6297_, v___x_6298_);
if (v___x_6299_ == 0)
{
lean_dec(v_mid_6294_);
v___y_6281_ = v___y_6296_;
goto v___jp_6280_;
}
else
{
lean_object* v___x_6300_; 
v___x_6300_ = lean_array_fswap(v___y_6296_, v_mid_6294_, v_hi_6279_);
lean_dec(v_mid_6294_);
v___y_6281_ = v___x_6300_;
goto v___jp_6280_;
}
}
v___jp_6301_:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; uint8_t v___x_6305_; 
v___x_6303_ = lean_array_fget_borrowed(v___y_6302_, v_hi_6279_);
v___x_6304_ = lean_array_fget_borrowed(v___y_6302_, v_lo_6278_);
lean_inc(v___x_6304_);
lean_inc(v___x_6303_);
v___x_6305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6291_, v___x_6303_, v___x_6304_);
if (v___x_6305_ == 0)
{
v___y_6296_ = v___y_6302_;
goto v___jp_6295_;
}
else
{
lean_object* v___x_6306_; 
v___x_6306_ = lean_array_fswap(v___y_6302_, v_lo_6278_, v_hi_6279_);
v___y_6296_ = v___x_6306_;
goto v___jp_6295_;
}
}
}
v___jp_6280_:
{
lean_object* v_pivot_6282_; lean_object* v___x_6283_; lean_object* v_fst_6284_; lean_object* v_snd_6285_; uint8_t v___x_6286_; 
v_pivot_6282_ = lean_array_fget(v___y_6281_, v_hi_6279_);
lean_inc_n(v_lo_6278_, 2);
v___x_6283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6279_, v_pivot_6282_, v___y_6281_, v_lo_6278_, v_lo_6278_);
v_fst_6284_ = lean_ctor_get(v___x_6283_, 0);
lean_inc(v_fst_6284_);
v_snd_6285_ = lean_ctor_get(v___x_6283_, 1);
lean_inc(v_snd_6285_);
lean_dec_ref(v___x_6283_);
v___x_6286_ = lean_nat_dec_le(v_hi_6279_, v_fst_6284_);
if (v___x_6286_ == 0)
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; 
v___x_6287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6276_, v_snd_6285_, v_lo_6278_, v_fst_6284_);
v___x_6288_ = lean_unsigned_to_nat(1u);
v___x_6289_ = lean_nat_add(v_fst_6284_, v___x_6288_);
lean_dec(v_fst_6284_);
v_as_6277_ = v___x_6287_;
v_lo_6278_ = v___x_6289_;
goto _start;
}
else
{
lean_dec(v_fst_6284_);
lean_dec(v_lo_6278_);
return v_snd_6285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6311_, lean_object* v_as_6312_, lean_object* v_lo_6313_, lean_object* v_hi_6314_){
_start:
{
lean_object* v_res_6315_; 
v_res_6315_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6311_, v_as_6312_, v_lo_6313_, v_hi_6314_);
lean_dec(v_hi_6314_);
lean_dec(v_n_6311_);
return v_res_6315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6316_, lean_object* v___x_6317_, lean_object* v_n_6318_, lean_object* v_j_6319_, lean_object* v_a_6320_){
_start:
{
lean_object* v_zero_6321_; uint8_t v_isZero_6322_; 
v_zero_6321_ = lean_unsigned_to_nat(0u);
v_isZero_6322_ = lean_nat_dec_eq(v_j_6319_, v_zero_6321_);
if (v_isZero_6322_ == 1)
{
lean_dec(v_j_6319_);
return v_a_6320_;
}
else
{
lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v_toSignature_6325_; lean_object* v_name_6326_; lean_object* v___x_6327_; lean_object* v_one_6328_; lean_object* v_n_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6323_ = lean_nat_sub(v_n_6318_, v_j_6319_);
v___x_6324_ = lean_array_fget_borrowed(v___y_6316_, v___x_6323_);
v_toSignature_6325_ = lean_ctor_get(v___x_6324_, 0);
v_name_6326_ = lean_ctor_get(v_toSignature_6325_, 0);
v___x_6327_ = lean_box(0);
v_one_6328_ = lean_unsigned_to_nat(1u);
v_n_6329_ = lean_nat_sub(v_j_6319_, v_one_6328_);
lean_dec(v_j_6319_);
v___x_6330_ = lean_array_get_borrowed(v___x_6327_, v___x_6317_, v___x_6323_);
lean_dec(v___x_6323_);
lean_inc(v___x_6330_);
lean_inc(v_name_6326_);
v___x_6331_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6320_, v_name_6326_, v___x_6330_);
v_j_6319_ = v_n_6329_;
v_a_6320_ = v___x_6331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6333_, lean_object* v___x_6334_, lean_object* v_n_6335_, lean_object* v_j_6336_, lean_object* v_a_6337_){
_start:
{
lean_object* v_res_6338_; 
v_res_6338_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6333_, v___x_6334_, v_n_6335_, v_j_6336_, v_a_6337_);
lean_dec(v_n_6335_);
lean_dec_ref(v___x_6334_);
lean_dec_ref(v___y_6333_);
return v_res_6338_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6339_; 
v___x_6339_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6339_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6340_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6341_, 0, v___x_6340_);
return v___x_6341_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6342_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6343_, 0, v___x_6342_);
lean_ctor_set(v___x_6343_, 1, v___x_6342_);
return v___x_6343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_, lean_object* v_a_6349_, lean_object* v_a_6350_){
_start:
{
lean_object* v___x_6352_; lean_object* v___y_6354_; lean_object* v___y_6355_; lean_object* v___y_6356_; lean_object* v___y_6357_; lean_object* v___y_6392_; lean_object* v___y_6393_; lean_object* v___y_6394_; lean_object* v___y_6395_; uint8_t v___y_6396_; lean_object* v___y_6397_; lean_object* v___y_6398_; uint8_t v___y_6399_; lean_object* v___y_6400_; lean_object* v___y_6401_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v_a_6404_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; lean_object* v___y_6417_; uint8_t v___y_6418_; lean_object* v___y_6419_; lean_object* v___y_6420_; uint8_t v___y_6421_; lean_object* v___y_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v_a_6426_; lean_object* v___y_6439_; lean_object* v___y_6440_; lean_object* v___y_6441_; uint8_t v___y_6442_; lean_object* v___y_6443_; lean_object* v___y_6444_; uint8_t v___y_6445_; lean_object* v___y_6446_; lean_object* v___y_6447_; lean_object* v___y_6448_; lean_object* v___y_6490_; lean_object* v___x_6512_; lean_object* v___y_6514_; lean_object* v___y_6515_; uint8_t v___x_6517_; 
v___x_6352_ = lean_unsigned_to_nat(0u);
v___x_6512_ = lean_array_get_size(v_decls_6346_);
v___x_6517_ = lean_nat_dec_eq(v___x_6512_, v___x_6352_);
if (v___x_6517_ == 0)
{
lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___y_6521_; uint8_t v___x_6523_; 
v___x_6518_ = lean_unsigned_to_nat(1u);
v___x_6519_ = lean_nat_sub(v___x_6512_, v___x_6518_);
v___x_6523_ = lean_nat_dec_le(v___x_6352_, v___x_6519_);
if (v___x_6523_ == 0)
{
lean_inc(v___x_6519_);
v___y_6521_ = v___x_6519_;
goto v___jp_6520_;
}
else
{
v___y_6521_ = v___x_6352_;
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
v___y_6490_ = v_decls_6346_;
goto v___jp_6489_;
}
v___jp_6353_:
{
if (lean_obj_tag(v___y_6357_) == 0)
{
lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v_assignments_6360_; lean_object* v_funVals_6361_; lean_object* v_env_6362_; lean_object* v_nextMacroScope_6363_; lean_object* v_ngen_6364_; lean_object* v_auxDeclNGen_6365_; lean_object* v_traceState_6366_; lean_object* v_messages_6367_; lean_object* v_infoState_6368_; lean_object* v_snapshotTasks_6369_; lean_object* v___x_6371_; uint8_t v_isShared_6372_; uint8_t v_isSharedCheck_6381_; 
lean_dec_ref_known(v___y_6357_, 1);
v___x_6358_ = lean_st_ref_get(v___y_6355_);
lean_dec(v___y_6355_);
v___x_6359_ = lean_st_ref_take(v_a_6350_);
v_assignments_6360_ = lean_ctor_get(v___x_6358_, 0);
lean_inc_ref(v_assignments_6360_);
v_funVals_6361_ = lean_ctor_get(v___x_6358_, 1);
lean_inc_ref(v_funVals_6361_);
lean_dec(v___x_6358_);
v_env_6362_ = lean_ctor_get(v___x_6359_, 0);
v_nextMacroScope_6363_ = lean_ctor_get(v___x_6359_, 1);
v_ngen_6364_ = lean_ctor_get(v___x_6359_, 2);
v_auxDeclNGen_6365_ = lean_ctor_get(v___x_6359_, 3);
v_traceState_6366_ = lean_ctor_get(v___x_6359_, 4);
v_messages_6367_ = lean_ctor_get(v___x_6359_, 6);
v_infoState_6368_ = lean_ctor_get(v___x_6359_, 7);
v_snapshotTasks_6369_ = lean_ctor_get(v___x_6359_, 8);
v_isSharedCheck_6381_ = !lean_is_exclusive(v___x_6359_);
if (v_isSharedCheck_6381_ == 0)
{
lean_object* v_unused_6382_; 
v_unused_6382_ = lean_ctor_get(v___x_6359_, 5);
lean_dec(v_unused_6382_);
v___x_6371_ = v___x_6359_;
v_isShared_6372_ = v_isSharedCheck_6381_;
goto v_resetjp_6370_;
}
else
{
lean_inc(v_snapshotTasks_6369_);
lean_inc(v_infoState_6368_);
lean_inc(v_messages_6367_);
lean_inc(v_traceState_6366_);
lean_inc(v_auxDeclNGen_6365_);
lean_inc(v_ngen_6364_);
lean_inc(v_nextMacroScope_6363_);
lean_inc(v_env_6362_);
lean_dec(v___x_6359_);
v___x_6371_ = lean_box(0);
v_isShared_6372_ = v_isSharedCheck_6381_;
goto v_resetjp_6370_;
}
v_resetjp_6370_:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6376_; 
lean_inc(v___y_6356_);
v___x_6373_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6354_, v_funVals_6361_, v___y_6356_, v___y_6356_, v_env_6362_);
lean_dec_ref(v_funVals_6361_);
v___x_6374_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6372_ == 0)
{
lean_ctor_set(v___x_6371_, 5, v___x_6374_);
lean_ctor_set(v___x_6371_, 0, v___x_6373_);
v___x_6376_ = v___x_6371_;
goto v_reusejp_6375_;
}
else
{
lean_object* v_reuseFailAlloc_6380_; 
v_reuseFailAlloc_6380_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6380_, 0, v___x_6373_);
lean_ctor_set(v_reuseFailAlloc_6380_, 1, v_nextMacroScope_6363_);
lean_ctor_set(v_reuseFailAlloc_6380_, 2, v_ngen_6364_);
lean_ctor_set(v_reuseFailAlloc_6380_, 3, v_auxDeclNGen_6365_);
lean_ctor_set(v_reuseFailAlloc_6380_, 4, v_traceState_6366_);
lean_ctor_set(v_reuseFailAlloc_6380_, 5, v___x_6374_);
lean_ctor_set(v_reuseFailAlloc_6380_, 6, v_messages_6367_);
lean_ctor_set(v_reuseFailAlloc_6380_, 7, v_infoState_6368_);
lean_ctor_set(v_reuseFailAlloc_6380_, 8, v_snapshotTasks_6369_);
v___x_6376_ = v_reuseFailAlloc_6380_;
goto v_reusejp_6375_;
}
v_reusejp_6375_:
{
lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; 
v___x_6377_ = lean_st_ref_set(v_a_6350_, v___x_6376_);
v___x_6378_ = lean_mk_empty_array_with_capacity(v___y_6356_);
v___x_6379_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6360_, v___y_6354_, v___y_6356_, v___x_6352_, v___x_6378_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_);
lean_dec_ref(v___y_6354_);
lean_dec_ref(v_assignments_6360_);
return v___x_6379_;
}
}
}
else
{
lean_object* v_a_6383_; lean_object* v___x_6385_; uint8_t v_isShared_6386_; uint8_t v_isSharedCheck_6390_; 
lean_dec(v___y_6356_);
lean_dec(v___y_6355_);
lean_dec_ref(v___y_6354_);
v_a_6383_ = lean_ctor_get(v___y_6357_, 0);
v_isSharedCheck_6390_ = !lean_is_exclusive(v___y_6357_);
if (v_isSharedCheck_6390_ == 0)
{
v___x_6385_ = v___y_6357_;
v_isShared_6386_ = v_isSharedCheck_6390_;
goto v_resetjp_6384_;
}
else
{
lean_inc(v_a_6383_);
lean_dec(v___y_6357_);
v___x_6385_ = lean_box(0);
v_isShared_6386_ = v_isSharedCheck_6390_;
goto v_resetjp_6384_;
}
v_resetjp_6384_:
{
lean_object* v___x_6388_; 
if (v_isShared_6386_ == 0)
{
v___x_6388_ = v___x_6385_;
goto v_reusejp_6387_;
}
else
{
lean_object* v_reuseFailAlloc_6389_; 
v_reuseFailAlloc_6389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6389_, 0, v_a_6383_);
v___x_6388_ = v_reuseFailAlloc_6389_;
goto v_reusejp_6387_;
}
v_reusejp_6387_:
{
return v___x_6388_;
}
}
}
}
v___jp_6391_:
{
lean_object* v___x_6405_; double v___x_6406_; double v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; 
v___x_6405_ = lean_io_get_num_heartbeats();
v___x_6406_ = lean_float_of_nat(v___y_6403_);
v___x_6407_ = lean_float_of_nat(v___x_6405_);
v___x_6408_ = lean_box_float(v___x_6406_);
v___x_6409_ = lean_box_float(v___x_6407_);
v___x_6410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6410_, 0, v___x_6408_);
lean_ctor_set(v___x_6410_, 1, v___x_6409_);
v___x_6411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6411_, 0, v_a_6404_);
lean_ctor_set(v___x_6411_, 1, v___x_6410_);
lean_inc_ref(v___y_6397_);
lean_inc(v___y_6400_);
v___x_6412_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6400_, v___y_6396_, v___y_6397_, v___y_6394_, v___y_6399_, v___y_6395_, v___y_6393_, v___x_6411_, v___y_6402_, v___y_6398_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_);
lean_dec_ref(v___y_6402_);
v___y_6354_ = v___y_6392_;
v___y_6355_ = v___y_6398_;
v___y_6356_ = v___y_6401_;
v___y_6357_ = v___x_6412_;
goto v___jp_6353_;
}
v___jp_6413_:
{
lean_object* v___x_6427_; double v___x_6428_; double v___x_6429_; double v___x_6430_; double v___x_6431_; double v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; 
v___x_6427_ = lean_io_mono_nanos_now();
v___x_6428_ = lean_float_of_nat(v___y_6425_);
v___x_6429_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6430_ = lean_float_div(v___x_6428_, v___x_6429_);
v___x_6431_ = lean_float_of_nat(v___x_6427_);
v___x_6432_ = lean_float_div(v___x_6431_, v___x_6429_);
v___x_6433_ = lean_box_float(v___x_6430_);
v___x_6434_ = lean_box_float(v___x_6432_);
v___x_6435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6435_, 0, v___x_6433_);
lean_ctor_set(v___x_6435_, 1, v___x_6434_);
v___x_6436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6436_, 0, v_a_6426_);
lean_ctor_set(v___x_6436_, 1, v___x_6435_);
lean_inc_ref(v___y_6419_);
lean_inc(v___y_6422_);
v___x_6437_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6422_, v___y_6418_, v___y_6419_, v___y_6416_, v___y_6421_, v___y_6417_, v___y_6415_, v___x_6436_, v___y_6424_, v___y_6420_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_);
lean_dec_ref(v___y_6424_);
v___y_6354_ = v___y_6414_;
v___y_6355_ = v___y_6420_;
v___y_6356_ = v___y_6423_;
v___y_6357_ = v___x_6437_;
goto v___jp_6353_;
}
v___jp_6438_:
{
lean_object* v___x_6449_; lean_object* v_a_6450_; lean_object* v___x_6451_; uint8_t v___x_6452_; 
v___x_6449_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6350_);
v_a_6450_ = lean_ctor_get(v___x_6449_, 0);
lean_inc(v_a_6450_);
lean_dec_ref(v___x_6449_);
v___x_6451_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6452_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6441_, v___x_6451_);
if (v___x_6452_ == 0)
{
lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6453_ = lean_io_mono_nanos_now();
v___x_6454_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6352_, v___y_6447_, v___y_6446_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_);
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
v___y_6414_ = v___y_6439_;
v___y_6415_ = v___y_6440_;
v___y_6416_ = v___y_6441_;
v___y_6417_ = v_a_6450_;
v___y_6418_ = v___y_6442_;
v___y_6419_ = v___y_6443_;
v___y_6420_ = v___y_6446_;
v___y_6421_ = v___y_6445_;
v___y_6422_ = v___y_6444_;
v___y_6423_ = v___y_6448_;
v___y_6424_ = v___y_6447_;
v___y_6425_ = v___x_6453_;
v_a_6426_ = v___x_6460_;
goto v___jp_6413_;
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
v___y_6414_ = v___y_6439_;
v___y_6415_ = v___y_6440_;
v___y_6416_ = v___y_6441_;
v___y_6417_ = v_a_6450_;
v___y_6418_ = v___y_6442_;
v___y_6419_ = v___y_6443_;
v___y_6420_ = v___y_6446_;
v___y_6421_ = v___y_6445_;
v___y_6422_ = v___y_6444_;
v___y_6423_ = v___y_6448_;
v___y_6424_ = v___y_6447_;
v___y_6425_ = v___x_6453_;
v_a_6426_ = v___x_6468_;
goto v___jp_6413_;
}
}
}
}
else
{
lean_object* v___x_6471_; lean_object* v___x_6472_; 
v___x_6471_ = lean_io_get_num_heartbeats();
v___x_6472_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6352_, v___y_6447_, v___y_6446_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_);
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
v___y_6392_ = v___y_6439_;
v___y_6393_ = v___y_6440_;
v___y_6394_ = v___y_6441_;
v___y_6395_ = v_a_6450_;
v___y_6396_ = v___y_6442_;
v___y_6397_ = v___y_6443_;
v___y_6398_ = v___y_6446_;
v___y_6399_ = v___y_6445_;
v___y_6400_ = v___y_6444_;
v___y_6401_ = v___y_6448_;
v___y_6402_ = v___y_6447_;
v___y_6403_ = v___x_6471_;
v_a_6404_ = v___x_6478_;
goto v___jp_6391_;
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
v___y_6392_ = v___y_6439_;
v___y_6393_ = v___y_6440_;
v___y_6394_ = v___y_6441_;
v___y_6395_ = v_a_6450_;
v___y_6396_ = v___y_6442_;
v___y_6397_ = v___y_6443_;
v___y_6398_ = v___y_6446_;
v___y_6399_ = v___y_6445_;
v___y_6400_ = v___y_6444_;
v___y_6401_ = v___y_6448_;
v___y_6402_ = v___y_6447_;
v___y_6403_ = v___x_6471_;
v_a_6404_ = v___x_6486_;
goto v___jp_6391_;
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
v_options_6499_ = lean_ctor_get(v_a_6349_, 2);
v_inheritedTraceOptions_6500_ = lean_ctor_get(v_a_6349_, 13);
v_hasTrace_6501_ = lean_ctor_get_uint8(v_options_6499_, sizeof(void*)*1);
v_ctx_6502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6502_, 0, v___y_6490_);
lean_ctor_set(v_ctx_6502_, 1, v___x_6352_);
if (v_hasTrace_6501_ == 0)
{
lean_object* v___x_6503_; 
v___x_6503_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6352_, v_ctx_6502_, v___x_6498_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_);
lean_dec_ref_known(v_ctx_6502_, 2);
v___y_6354_ = v___y_6490_;
v___y_6355_ = v___x_6498_;
v___y_6356_ = v___x_6494_;
v___y_6357_ = v___x_6503_;
goto v___jp_6353_;
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
v___x_6511_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6352_, v_ctx_6502_, v___x_6498_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_);
lean_dec_ref_known(v_ctx_6502_, 2);
v___y_6354_ = v___y_6490_;
v___y_6355_ = v___x_6498_;
v___y_6356_ = v___x_6494_;
v___y_6357_ = v___x_6511_;
goto v___jp_6353_;
}
else
{
v___y_6439_ = v___y_6490_;
v___y_6440_ = v___f_6504_;
v___y_6441_ = v_options_6499_;
v___y_6442_ = v_hasTrace_6501_;
v___y_6443_ = v___x_6506_;
v___y_6444_ = v___x_6505_;
v___y_6445_ = v___x_6508_;
v___y_6446_ = v___x_6498_;
v___y_6447_ = v_ctx_6502_;
v___y_6448_ = v___x_6494_;
goto v___jp_6438_;
}
}
else
{
v___y_6439_ = v___y_6490_;
v___y_6440_ = v___f_6504_;
v___y_6441_ = v_options_6499_;
v___y_6442_ = v_hasTrace_6501_;
v___y_6443_ = v___x_6506_;
v___y_6444_ = v___x_6505_;
v___y_6445_ = v___x_6508_;
v___y_6446_ = v___x_6498_;
v___y_6447_ = v_ctx_6502_;
v___y_6448_ = v___x_6494_;
goto v___jp_6438_;
}
}
}
v___jp_6513_:
{
lean_object* v___x_6516_; 
v___x_6516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6512_, v_decls_6346_, v___y_6514_, v___y_6515_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6557_, lean_object* v_as_6558_, lean_object* v_i_6559_, lean_object* v_j_6560_, lean_object* v_inv_6561_, lean_object* v_bs_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_, lean_object* v___y_6566_){
_start:
{
lean_object* v___x_6568_; 
v___x_6568_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6557_, v_as_6558_, v_i_6559_, v_j_6560_, v_bs_6562_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_);
return v___x_6568_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6569_, lean_object* v_as_6570_, lean_object* v_i_6571_, lean_object* v_j_6572_, lean_object* v_inv_6573_, lean_object* v_bs_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_){
_start:
{
lean_object* v_res_6580_; 
v_res_6580_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6569_, v_as_6570_, v_i_6571_, v_j_6572_, v_inv_6573_, v_bs_6574_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_);
lean_dec(v___y_6578_);
lean_dec_ref(v___y_6577_);
lean_dec(v___y_6576_);
lean_dec_ref(v___y_6575_);
lean_dec_ref(v_as_6570_);
lean_dec_ref(v___x_6569_);
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
