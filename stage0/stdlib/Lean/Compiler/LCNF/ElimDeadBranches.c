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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Std_HashMap_instInhabited___redArg();
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
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(uint8_t, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
uint8_t l_Prod_lexLtDec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default___redArg();
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0;
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
static const lean_array_object l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 2:
{
lean_object* v_i_7_; lean_object* v_vs_8_; lean_object* v___x_9_; 
v_i_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_i_7_);
v_vs_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_vs_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_i_7_, v_vs_8_);
return v___x_9_;
}
case 3:
{
lean_object* v_vs_10_; lean_object* v___x_11_; 
v_vs_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_vs_10_);
lean_dec_ref_known(v_t_5_, 1);
v___x_11_ = lean_apply_1(v_k_6_, v_vs_10_);
return v___x_11_;
}
default: 
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim(lean_object* v_motive__1_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___boxed(lean_object* v_motive__1_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim(v_motive__1_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_bot_elim___redArg(lean_object* v_t_24_, lean_object* v_bot_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_24_, v_bot_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_bot_elim(lean_object* v_motive__1_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_bot_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_28_, v_bot_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_top_elim___redArg(lean_object* v_t_32_, lean_object* v_top_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_32_, v_top_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_top_elim(lean_object* v_motive__1_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_top_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_36_, v_top_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctor_elim___redArg(lean_object* v_t_40_, lean_object* v_ctor_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_40_, v_ctor_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctor_elim(lean_object* v_motive__1_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_ctor_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_44_, v_ctor_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_choice_elim___redArg(lean_object* v_t_48_, lean_object* v_choice_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_48_, v_choice_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_choice_elim(lean_object* v_motive__1_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_choice_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ctorElim___redArg(v_t_52_, v_choice_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue_default(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_instInhabitedValue(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_maxValueDepth(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_unsigned_to_nat(8u);
return v___x_58_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(lean_object* v_xs_59_, lean_object* v_ys_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_zero_62_; uint8_t v_isZero_63_; 
v_zero_62_ = lean_unsigned_to_nat(0u);
v_isZero_63_ = lean_nat_dec_eq(v_x_61_, v_zero_62_);
if (v_isZero_63_ == 1)
{
lean_dec(v_x_61_);
return v_isZero_63_;
}
else
{
lean_object* v_one_64_; lean_object* v_n_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_one_64_ = lean_unsigned_to_nat(1u);
v_n_65_ = lean_nat_sub(v_x_61_, v_one_64_);
lean_dec(v_x_61_);
v___x_66_ = lean_array_fget_borrowed(v_xs_59_, v_n_65_);
v___x_67_ = lean_array_fget_borrowed(v_ys_60_, v_n_65_);
v___x_68_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec(v_n_65_);
return v___x_68_;
}
else
{
v_x_61_ = v_n_65_;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
switch(lean_obj_tag(v_x_70_))
{
case 0:
{
if (lean_obj_tag(v_x_71_) == 0)
{
uint8_t v___x_72_; 
v___x_72_ = 1;
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
case 1:
{
if (lean_obj_tag(v_x_71_) == 1)
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
case 2:
{
if (lean_obj_tag(v_x_71_) == 2)
{
lean_object* v_i_76_; lean_object* v_vs_77_; lean_object* v_i_78_; lean_object* v_vs_79_; uint8_t v___x_80_; 
v_i_76_ = lean_ctor_get(v_x_70_, 0);
v_vs_77_ = lean_ctor_get(v_x_70_, 1);
v_i_78_ = lean_ctor_get(v_x_71_, 0);
v_vs_79_ = lean_ctor_get(v_x_71_, 1);
v___x_80_ = lean_name_eq(v_i_76_, v_i_78_);
if (v___x_80_ == 0)
{
return v___x_80_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_array_get_size(v_vs_77_);
v___x_82_ = lean_array_get_size(v_vs_79_);
v___x_83_ = lean_nat_dec_eq(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(v_vs_77_, v_vs_79_, v___x_81_);
return v___x_84_;
}
}
}
else
{
uint8_t v___x_85_; 
v___x_85_ = 0;
return v___x_85_;
}
}
default: 
{
if (lean_obj_tag(v_x_71_) == 3)
{
lean_object* v_vs_86_; lean_object* v_vs_87_; uint8_t v___x_88_; 
v_vs_86_ = lean_ctor_get(v_x_70_, 0);
v_vs_87_ = lean_ctor_get(v_x_71_, 0);
v___x_88_ = l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(v_vs_87_, v_vs_86_);
if (v___x_88_ == 0)
{
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(v_vs_86_, v_vs_87_);
return v___x_89_;
}
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(lean_object* v_a_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
else
{
lean_object* v_head_94_; lean_object* v_tail_95_; uint8_t v___x_96_; 
v_head_94_ = lean_ctor_get(v_x_92_, 0);
v_tail_95_ = lean_ctor_get(v_x_92_, 1);
v___x_96_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_91_, v_head_94_);
if (v___x_96_ == 0)
{
v_x_92_ = v_tail_95_;
goto _start;
}
else
{
return v___x_96_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(lean_object* v_bs_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
uint8_t v___x_100_; 
v___x_100_ = 1;
return v___x_100_;
}
else
{
lean_object* v_head_101_; lean_object* v_tail_102_; uint8_t v___x_103_; 
v_head_101_ = lean_ctor_get(v_x_99_, 0);
v_tail_102_ = lean_ctor_get(v_x_99_, 1);
v___x_103_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(v_head_101_, v_bs_98_);
if (v___x_103_ == 0)
{
return v___x_103_;
}
else
{
v_x_99_ = v_tail_102_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1___boxed(lean_object* v_bs_105_, lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_List_all___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__1(v_bs_105_, v_x_106_);
lean_dec(v_x_106_);
lean_dec(v_bs_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0___boxed(lean_object* v_a_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__0(v_a_109_, v_x_110_);
lean_dec(v_x_110_);
lean_dec(v_a_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg___boxed(lean_object* v_xs_113_, lean_object* v_ys_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(v_xs_113_, v_ys_114_, v_x_115_);
lean_dec_ref(v_ys_114_);
lean_dec_ref(v_xs_113_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq___boxed(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_x_118_, v_x_119_);
lean_dec(v_x_119_);
lean_dec(v_x_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2(lean_object* v_xs_122_, lean_object* v_ys_123_, lean_object* v_hsz_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___redArg(v_xs_122_, v_ys_123_, v_x_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2___boxed(lean_object* v_xs_128_, lean_object* v_ys_129_, lean_object* v_hsz_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_beq_spec__2(v_xs_128_, v_ys_129_, v_hsz_130_, v_x_131_, v_x_132_);
lean_dec_ref(v_ys_129_);
lean_dec_ref(v_xs_128_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__1(lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_nat_to_int(v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3_spec__3(lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_dec(v_x_139_);
return v_x_140_;
}
else
{
lean_object* v_head_142_; lean_object* v_tail_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_152_; 
v_head_142_ = lean_ctor_get(v_x_141_, 0);
v_tail_143_ = lean_ctor_get(v_x_141_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_141_);
if (v_isSharedCheck_152_ == 0)
{
v___x_145_ = v_x_141_;
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_tail_143_);
lean_inc(v_head_142_);
lean_dec(v_x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
lean_inc(v_x_139_);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 5);
lean_ctor_set(v___x_145_, 1, v_x_139_);
lean_ctor_set(v___x_145_, 0, v_x_140_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_x_140_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_x_139_);
v___x_148_ = v_reuseFailAlloc_151_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_head_142_);
v_x_140_ = v___x_149_;
v_x_141_ = v_tail_143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v___x_155_; 
lean_dec(v_x_154_);
v___x_155_ = lean_box(0);
return v___x_155_;
}
else
{
lean_object* v_tail_156_; 
v_tail_156_ = lean_ctor_get(v_x_153_, 1);
if (lean_obj_tag(v_tail_156_) == 0)
{
lean_object* v_head_157_; 
lean_dec(v_x_154_);
v_head_157_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_head_157_);
lean_dec_ref_known(v_x_153_, 2);
return v_head_157_;
}
else
{
lean_object* v_head_158_; lean_object* v___x_159_; 
lean_inc(v_tail_156_);
v_head_158_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_head_158_);
lean_dec_ref_known(v_x_153_, 2);
v___x_159_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3_spec__3(v_x_154_, v_head_158_, v_tail_156_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0(lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
if (lean_obj_tag(v_a_169_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = l_List_reverse___redArg(v_a_170_);
return v___x_171_;
}
else
{
lean_object* v_head_172_; lean_object* v_tail_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_184_; 
v_head_172_ = lean_ctor_get(v_a_169_, 0);
v_tail_173_ = lean_ctor_get(v_a_169_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_169_);
if (v_isSharedCheck_184_ == 0)
{
v___x_175_ = v_a_169_;
v_isShared_176_ = v_isSharedCheck_184_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_tail_173_);
lean_inc(v_head_172_);
lean_dec(v_a_169_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_184_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_177_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__1));
v___x_178_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_172_);
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v_a_170_);
lean_ctor_set(v___x_175_, 0, v___x_179_);
v___x_181_ = v___x_175_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_a_170_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v_a_169_ = v_tail_173_;
v_a_170_ = v___x_181_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__4));
v___x_187_ = lean_string_length(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__6);
v___x_189_ = lean_nat_to_int(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(lean_object* v_x_198_){
_start:
{
switch(lean_obj_tag(v_x_198_))
{
case 0:
{
lean_object* v___x_199_; 
v___x_199_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__1));
return v___x_199_;
}
case 1:
{
lean_object* v___x_200_; 
v___x_200_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__3));
return v___x_200_;
}
case 2:
{
lean_object* v_i_201_; lean_object* v_vs_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_229_; 
v_i_201_ = lean_ctor_get(v_x_198_, 0);
v_vs_202_ = lean_ctor_get(v_x_198_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_229_ == 0)
{
v___x_204_ = v_x_198_;
v_isShared_205_ = v_isSharedCheck_229_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_vs_202_);
lean_inc(v_i_201_);
lean_dec(v_x_198_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_229_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_array_get_size(v_vs_202_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_209_ = 1;
v___x_210_ = l_Lean_Name_toString(v_i_201_, v___x_209_);
v___x_211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = lean_array_to_list(v_vs_202_);
v___x_213_ = lean_box(0);
v___x_214_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0(v___x_212_, v___x_213_);
v___x_215_ = l_Std_Format_join(v___x_214_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 5);
lean_ctor_set(v___x_204_, 1, v___x_215_);
lean_ctor_set(v___x_204_, 0, v___x_211_);
v___x_217_ = v___x_204_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_226_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; 
v___x_218_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_219_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_217_);
v___x_221_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_218_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
return v___x_225_;
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_del_object(v___x_204_);
lean_dec_ref(v_vs_202_);
v___x_227_ = l_Lean_Name_toString(v_i_201_, v___x_208_);
v___x_228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
}
default: 
{
lean_object* v_vs_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; 
v_vs_230_ = lean_ctor_get(v_x_198_, 0);
lean_inc(v_vs_230_);
lean_dec_ref_known(v_x_198_, 1);
v___x_231_ = lean_box(0);
v___x_232_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__2(v_vs_230_, v___x_231_);
v___x_233_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__11));
v___x_234_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_232_, v___x_233_);
v___x_235_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_236_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_234_);
v___x_238_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_235_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_241_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__2(lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
if (lean_obj_tag(v_a_243_) == 0)
{
lean_object* v___x_245_; 
v___x_245_ = l_List_reverse___redArg(v_a_244_);
return v___x_245_;
}
else
{
lean_object* v_head_246_; lean_object* v_tail_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_256_; 
v_head_246_ = lean_ctor_get(v_a_243_, 0);
v_tail_247_ = lean_ctor_get(v_a_243_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_256_ == 0)
{
v___x_249_ = v_a_243_;
v_isShared_250_ = v_isSharedCheck_256_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_tail_247_);
lean_inc(v_head_246_);
lean_dec(v_a_243_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_256_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_246_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v_a_244_);
lean_ctor_set(v___x_249_, 0, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_a_244_);
v___x_253_ = v_reuseFailAlloc_255_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v_a_243_ = v_tail_247_;
v_a_244_ = v___x_253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0(lean_object* v_v_257_, lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0___boxed(lean_object* v_v_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_instRepr___lam__0(v_v_260_, v_x_261_);
lean_dec(v_x_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(lean_object* v_msg_272_){
_start:
{
lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___f_273_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_274_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_275_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_276_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_277_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_278_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_279_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___f_273_);
lean_ctor_set(v___x_280_, 1, v___f_274_);
v___x_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___f_275_);
lean_ctor_set(v___x_281_, 2, v___f_276_);
lean_ctor_set(v___x_281_, 3, v___f_277_);
lean_ctor_set(v___x_281_, 4, v___f_278_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___f_279_);
v___x_283_ = l_Lean_instInhabitedInductiveVal_default;
v___x_284_ = l_instInhabitedOfMonad___redArg(v___x_282_, v___x_283_);
v___x_285_ = lean_panic_fn_borrowed(v___x_284_, v_msg_272_);
lean_dec(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_289_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_290_ = lean_unsigned_to_nat(51u);
v___x_291_ = lean_unsigned_to_nat(72u);
v___x_292_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1));
v___x_293_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_294_ = l_mkPanicMessageWithDecl(v___x_293_, v___x_292_, v___x_291_, v___x_290_, v___x_289_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_296_ = lean_unsigned_to_nat(56u);
v___x_297_ = lean_unsigned_to_nat(73u);
v___x_298_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__1));
v___x_299_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_300_ = l_mkPanicMessageWithDecl(v___x_299_, v___x_298_, v___x_297_, v___x_296_, v___x_295_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(lean_object* v_ctorName_301_, lean_object* v_env_302_){
_start:
{
uint8_t v___x_309_; lean_object* v___x_310_; 
v___x_309_ = 0;
lean_inc_ref(v_env_302_);
v___x_310_ = l_Lean_Environment_find_x3f(v_env_302_, v_ctorName_301_, v___x_309_);
if (lean_obj_tag(v___x_310_) == 1)
{
lean_object* v_val_311_; 
v_val_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_val_311_);
lean_dec_ref_known(v___x_310_, 1);
if (lean_obj_tag(v_val_311_) == 6)
{
lean_object* v_val_312_; lean_object* v_induct_313_; lean_object* v___x_314_; 
v_val_312_ = lean_ctor_get(v_val_311_, 0);
lean_inc_ref(v_val_312_);
lean_dec_ref_known(v_val_311_, 1);
v_induct_313_ = lean_ctor_get(v_val_312_, 1);
lean_inc(v_induct_313_);
lean_dec_ref(v_val_312_);
v___x_314_ = l_Lean_Environment_find_x3f(v_env_302_, v_induct_313_, v___x_309_);
if (lean_obj_tag(v___x_314_) == 1)
{
lean_object* v_val_315_; 
v_val_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___x_314_, 1);
if (lean_obj_tag(v_val_315_) == 5)
{
lean_object* v_val_316_; 
v_val_316_ = lean_ctor_get(v_val_315_, 0);
lean_inc_ref(v_val_316_);
lean_dec_ref_known(v_val_315_, 1);
return v_val_316_;
}
else
{
lean_dec(v_val_315_);
goto v___jp_306_;
}
}
else
{
lean_dec(v___x_314_);
goto v___jp_306_;
}
}
else
{
lean_dec(v_val_311_);
lean_dec_ref(v_env_302_);
goto v___jp_303_;
}
}
else
{
lean_dec(v___x_310_);
lean_dec_ref(v_env_302_);
goto v___jp_303_;
}
v___jp_303_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__3);
v___x_305_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(v___x_304_);
return v___x_305_;
}
v___jp_306_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__4);
v___x_308_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0(v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(lean_object* v_ctorName_317_, lean_object* v_env_318_, lean_object* v_n_319_){
_start:
{
lean_object* v_induct_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_induct_320_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_ctorName_317_, v_env_318_);
v___x_321_ = l_Lean_InductiveVal_numCtors(v_induct_320_);
lean_dec_ref(v_induct_320_);
v___x_322_ = lean_nat_dec_eq(v_n_319_, v___x_321_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors___boxed(lean_object* v_ctorName_323_, lean_object* v_env_324_, lean_object* v_n_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_ctorName_323_, v_env_324_, v_n_325_);
lean_dec(v_n_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(uint8_t v___x_328_, lean_object* v_v_329_){
_start:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_box(1);
v___x_331_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_v_329_, v___x_330_);
if (v___x_331_ == 0)
{
return v___x_328_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed(lean_object* v___x_333_, lean_object* v_v_334_){
_start:
{
uint8_t v___x_150__boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v___x_150__boxed_335_ = lean_unbox(v___x_333_);
v_res_336_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0(v___x_150__boxed_335_, v_v_334_);
lean_dec(v_v_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(lean_object* v_value_338_){
_start:
{
if (lean_obj_tag(v_value_338_) == 2)
{
lean_object* v_vs_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_366_; 
v_vs_339_ = lean_ctor_get(v_value_338_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_value_338_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_value_338_, 0);
lean_dec(v_unused_367_);
v___x_341_ = v_value_338_;
v_isShared_342_ = v_isSharedCheck_366_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_vs_339_);
lean_dec(v_value_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_366_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___f_351_; lean_object* v___x_353_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_get_size(v_vs_339_);
v___f_345_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_346_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_347_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_348_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_349_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_350_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_351_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 0);
lean_ctor_set(v___x_341_, 1, v___f_346_);
lean_ctor_set(v___x_341_, 0, v___f_345_);
v___x_353_ = v___x_341_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___f_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___f_346_);
v___x_353_ = v_reuseFailAlloc_365_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___f_347_);
lean_ctor_set(v___x_354_, 2, v___f_348_);
lean_ctor_set(v___x_354_, 3, v___f_349_);
lean_ctor_set(v___x_354_, 4, v___f_350_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___f_351_);
v___x_356_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
lean_dec_ref_known(v___x_355_, 2);
lean_dec_ref(v_vs_339_);
v___x_357_ = 1;
return v___x_357_;
}
else
{
if (v___x_356_ == 0)
{
lean_dec_ref_known(v___x_355_, 2);
lean_dec_ref(v_vs_339_);
return v___x_356_;
}
else
{
lean_object* v___x_358_; lean_object* v___f_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_358_ = lean_box(v___x_356_);
v___f_359_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___lam__0___boxed), 2, 1);
lean_closure_set(v___f_359_, 0, v___x_358_);
v___x_360_ = ((size_t)0ULL);
v___x_361_ = lean_usize_of_nat(v___x_344_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_355_, v___f_359_, v_vs_339_, v___x_360_, v___x_361_);
v___x_363_ = lean_unbox(v___x_362_);
lean_dec(v___x_362_);
if (v___x_363_ == 0)
{
return v___x_356_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
}
}
}
}
}
else
{
uint8_t v___x_368_; 
lean_dec(v_value_338_);
v___x_368_ = 0;
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible___boxed(lean_object* v_value_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_eligible(v_value_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(lean_object* v_msg_372_){
_start:
{
lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___f_373_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__0));
v___f_374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__1));
v___f_375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__2));
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__3));
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__4));
v___f_378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__5));
v___f_379_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor_spec__0___closed__6));
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___f_373_);
lean_ctor_set(v___x_380_, 1, v___f_374_);
v___x_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___f_375_);
lean_ctor_set(v___x_381_, 2, v___f_376_);
lean_ctor_set(v___x_381_, 3, v___f_377_);
lean_ctor_set(v___x_381_, 4, v___f_378_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___f_379_);
v___x_383_ = lean_box(0);
v___x_384_ = l_instInhabitedOfMonad___redArg(v___x_382_, v___x_383_);
v___x_385_ = lean_panic_fn_borrowed(v___x_384_, v_msg_372_);
lean_dec(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(lean_object* v_as_386_, size_t v_i_387_, size_t v_stop_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_usize_dec_eq(v_i_387_, v_stop_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_array_uget_borrowed(v_as_386_, v_i_387_);
v___x_391_ = lean_box(1);
v___x_392_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = 1;
return v___x_393_;
}
else
{
size_t v___x_394_; size_t v___x_395_; 
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_add(v_i_387_, v___x_394_);
v_i_387_ = v___x_395_;
goto _start;
}
}
else
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0___boxed(lean_object* v_as_398_, lean_object* v_i_399_, lean_object* v_stop_400_){
_start:
{
size_t v_i_boxed_401_; size_t v_stop_boxed_402_; uint8_t v_res_403_; lean_object* v_r_404_; 
v_i_boxed_401_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_stop_boxed_402_ = lean_unbox_usize(v_stop_400_);
lean_dec(v_stop_400_);
v_res_403_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_as_398_, v_i_boxed_401_, v_stop_boxed_402_);
lean_dec_ref(v_as_398_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
uint8_t v___x_406_; 
v___x_406_ = 1;
return v___x_406_;
}
else
{
lean_object* v_head_407_; 
v_head_407_ = lean_ctor_get(v_x_405_, 0);
if (lean_obj_tag(v_head_407_) == 2)
{
lean_object* v_tail_408_; lean_object* v_vs_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_tail_408_ = lean_ctor_get(v_x_405_, 1);
v_vs_409_ = lean_ctor_get(v_head_407_, 1);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_array_get_size(v_vs_409_);
v___x_412_ = lean_nat_dec_lt(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
v_x_405_ = v_tail_408_;
goto _start;
}
else
{
if (v___x_412_ == 0)
{
v_x_405_ = v_tail_408_;
goto _start;
}
else
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = ((size_t)0ULL);
v___x_416_ = lean_usize_of_nat(v___x_411_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_409_, v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
v_x_405_ = v_tail_408_;
goto _start;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
}
}
}
else
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1___boxed(lean_object* v_x_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_x_421_);
lean_dec(v_x_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_425_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_426_ = lean_unsigned_to_nat(42u);
v___x_427_ = lean_unsigned_to_nat(122u);
v___x_428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0));
v___x_429_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_430_ = l_mkPanicMessageWithDecl(v___x_429_, v___x_428_, v___x_427_, v___x_426_, v___x_425_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(lean_object* v_env_431_, lean_object* v_vs_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_vs_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_dec_ref(v_env_431_);
v___x_434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_434_, 0, v_vs_432_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(0);
v___x_436_ = l_List_head_x21___redArg(v___x_435_, v_vs_432_);
if (lean_obj_tag(v___x_436_) == 2)
{
lean_object* v_i_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_i_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_i_437_);
lean_dec_ref_known(v___x_436_, 2);
v___x_438_ = l_List_lengthTR___redArg(v_vs_432_);
v___x_439_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_i_437_, v_env_431_, v___x_438_);
lean_dec(v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_440_, 0, v_vs_432_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
lean_dec(v_vs_432_);
v___x_441_ = lean_box(1);
return v___x_441_;
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v___x_436_);
lean_dec(v_vs_432_);
lean_dec_ref(v_env_431_);
v___x_442_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1);
v___x_443_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(v___x_442_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(lean_object* v_msg_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_box(0);
v___x_446_ = lean_panic_fn_borrowed(v___x_445_, v_msg_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
lean_dec(v_x_447_);
return v_x_448_;
}
else
{
lean_object* v_head_450_; lean_object* v_tail_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_461_; 
v_head_450_ = lean_ctor_get(v_x_449_, 0);
v_tail_451_ = lean_ctor_get(v_x_449_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_x_449_);
if (v_isSharedCheck_461_ == 0)
{
v___x_453_ = v_x_449_;
v_isShared_454_ = v_isSharedCheck_461_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_tail_451_);
lean_inc(v_head_450_);
lean_dec(v_x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_461_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
lean_inc(v_x_447_);
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 5);
lean_ctor_set(v___x_453_, 1, v_x_447_);
lean_ctor_set(v___x_453_, 0, v_x_448_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_x_448_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_x_447_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_450_);
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v_x_448_ = v___x_458_;
v_x_449_ = v_tail_451_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_464_; 
lean_dec(v_x_463_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
else
{
lean_object* v_tail_465_; 
v_tail_465_ = lean_ctor_get(v_x_462_, 1);
if (lean_obj_tag(v_tail_465_) == 0)
{
lean_object* v_head_466_; lean_object* v___x_467_; 
lean_dec(v_x_463_);
v_head_466_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_head_466_);
lean_dec_ref_known(v_x_462_, 2);
v___x_467_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_466_);
return v___x_467_;
}
else
{
lean_object* v_head_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_inc(v_tail_465_);
v_head_468_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_head_468_);
lean_dec_ref_known(v_x_462_, 2);
v___x_469_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_468_);
v___x_470_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(v_x_463_, v___x_469_, v_tail_465_);
return v___x_470_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2));
v___x_483_ = lean_string_length(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7);
v___x_485_ = lean_nat_to_int(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(lean_object* v_a_490_){
_start:
{
if (lean_obj_tag(v_a_490_) == 0)
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1));
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; 
v___x_492_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_493_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(v_a_490_, v___x_492_);
v___x_494_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8);
v___x_495_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9));
v___x_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_493_);
v___x_497_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_494_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = 0;
v___x_501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(lean_object* v_env_507_, lean_object* v_v1_508_, lean_object* v_v2_509_){
_start:
{
lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_517_; lean_object* v_i_518_; lean_object* v_vs_519_; 
switch(lean_obj_tag(v_v1_508_))
{
case 0:
{
switch(lean_obj_tag(v_v2_509_))
{
case 2:
{
lean_object* v_i_526_; lean_object* v_vs_527_; 
v_i_526_ = lean_ctor_get(v_v2_509_, 0);
lean_inc(v_i_526_);
v_vs_527_ = lean_ctor_get(v_v2_509_, 1);
lean_inc_ref(v_vs_527_);
v___y_517_ = v_v2_509_;
v_i_518_ = v_i_526_;
v_vs_519_ = v_vs_527_;
goto v___jp_516_;
}
case 3:
{
lean_object* v_vs_528_; lean_object* v___x_529_; 
v_vs_528_ = lean_ctor_get(v_v2_509_, 0);
lean_inc(v_vs_528_);
lean_dec_ref_known(v_v2_509_, 1);
v___x_529_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_507_, v_vs_528_);
return v___x_529_;
}
default: 
{
lean_dec_ref(v_env_507_);
return v_v2_509_;
}
}
}
case 1:
{
lean_dec(v_v2_509_);
lean_dec_ref(v_env_507_);
return v_v1_508_;
}
case 2:
{
switch(lean_obj_tag(v_v2_509_))
{
case 0:
{
lean_object* v_i_530_; lean_object* v_vs_531_; 
v_i_530_ = lean_ctor_get(v_v1_508_, 0);
lean_inc(v_i_530_);
v_vs_531_ = lean_ctor_get(v_v1_508_, 1);
lean_inc_ref(v_vs_531_);
v___y_517_ = v_v1_508_;
v_i_518_ = v_i_530_;
v_vs_519_ = v_vs_531_;
goto v___jp_516_;
}
case 1:
{
lean_dec_ref_known(v_v1_508_, 2);
lean_dec_ref(v_env_507_);
return v_v2_509_;
}
case 2:
{
lean_object* v_i_532_; lean_object* v_vs_533_; lean_object* v_i_534_; lean_object* v_vs_535_; uint8_t v___x_536_; 
v_i_532_ = lean_ctor_get(v_v1_508_, 0);
v_vs_533_ = lean_ctor_get(v_v1_508_, 1);
v_i_534_ = lean_ctor_get(v_v2_509_, 0);
v_vs_535_ = lean_ctor_get(v_v2_509_, 1);
v___x_536_ = lean_name_eq(v_i_532_, v_i_534_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_538_, 0, v_v2_509_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v_v1_508_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_507_, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_550_; 
lean_inc_ref(v_vs_535_);
lean_inc_ref(v_vs_533_);
lean_inc(v_i_532_);
lean_dec_ref_known(v_v1_508_, 2);
v_isSharedCheck_550_ = !lean_is_exclusive(v_v2_509_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; lean_object* v_unused_552_; 
v_unused_551_ = lean_ctor_get(v_v2_509_, 1);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_v2_509_, 0);
lean_dec(v_unused_552_);
v___x_542_ = v_v2_509_;
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_v2_509_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
lean_inc_ref(v_env_507_);
v___x_546_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_507_, v_vs_533_, v_vs_535_, v___x_544_, v___x_545_);
lean_dec_ref(v_vs_535_);
lean_dec_ref(v_vs_533_);
lean_inc_ref(v___x_546_);
lean_inc(v_i_532_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_546_);
lean_ctor_set(v___x_542_, 0, v_i_532_);
v___x_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_i_532_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v___y_517_ = v___x_548_;
v_i_518_ = v_i_532_;
v_vs_519_ = v___x_546_;
goto v___jp_516_;
}
}
}
}
default: 
{
lean_object* v_vs_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_vs_553_ = lean_ctor_get(v_v2_509_, 0);
lean_inc(v_vs_553_);
lean_dec_ref_known(v_v2_509_, 1);
lean_inc_ref(v_env_507_);
v___x_554_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_507_, v_vs_553_, v_v1_508_);
v___x_555_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_507_, v___x_554_);
return v___x_555_;
}
}
}
default: 
{
switch(lean_obj_tag(v_v2_509_))
{
case 0:
{
lean_object* v_vs_556_; lean_object* v___x_557_; 
v_vs_556_ = lean_ctor_get(v_v1_508_, 0);
lean_inc(v_vs_556_);
lean_dec_ref_known(v_v1_508_, 1);
v___x_557_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_507_, v_vs_556_);
return v___x_557_;
}
case 1:
{
lean_dec_ref_known(v_v1_508_, 1);
lean_dec_ref(v_env_507_);
return v_v2_509_;
}
case 3:
{
lean_object* v_vs_558_; lean_object* v_vs_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_vs_558_ = lean_ctor_get(v_v1_508_, 0);
lean_inc(v_vs_558_);
lean_dec_ref_known(v_v1_508_, 1);
v_vs_559_ = lean_ctor_get(v_v2_509_, 0);
lean_inc(v_vs_559_);
lean_dec_ref_known(v_v2_509_, 1);
lean_inc_ref(v_env_507_);
v___x_560_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(v_env_507_, v_vs_559_, v_vs_558_);
v___x_561_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_507_, v___x_560_);
return v___x_561_;
}
default: 
{
lean_object* v_vs_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_vs_562_ = lean_ctor_get(v_v1_508_, 0);
lean_inc(v_vs_562_);
lean_dec_ref_known(v_v1_508_, 1);
lean_inc_ref(v_env_507_);
v___x_563_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_507_, v_vs_562_, v_v2_509_);
v___x_564_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_507_, v___x_563_);
return v___x_564_;
}
}
}
}
v___jp_510_:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v___y_511_, v_env_507_, v___x_513_);
if (v___x_514_ == 0)
{
return v___y_512_;
}
else
{
lean_object* v___x_515_; 
lean_dec(v___y_512_);
v___x_515_ = lean_box(1);
return v___x_515_;
}
}
v___jp_516_:
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_array_get_size(v_vs_519_);
v___x_522_ = lean_nat_dec_lt(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_vs_519_);
v___y_511_ = v_i_518_;
v___y_512_ = v___y_517_;
goto v___jp_510_;
}
else
{
if (v___x_522_ == 0)
{
lean_dec_ref(v_vs_519_);
v___y_511_ = v_i_518_;
v___y_512_ = v___y_517_;
goto v___jp_510_;
}
else
{
size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_521_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_519_, v___x_523_, v___x_524_);
lean_dec_ref(v_vs_519_);
if (v___x_525_ == 0)
{
v___y_511_ = v_i_518_;
v___y_512_ = v___y_517_;
goto v___jp_510_;
}
else
{
lean_dec(v_i_518_);
lean_dec_ref(v_env_507_);
return v___y_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(lean_object* v_env_565_, lean_object* v_as_566_, lean_object* v_bs_567_, lean_object* v_i_568_, lean_object* v_cs_569_){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_array_get_size(v_as_566_);
v___x_571_ = lean_nat_dec_lt(v_i_568_, v___x_570_);
if (v___x_571_ == 0)
{
lean_dec(v_i_568_);
lean_dec_ref(v_env_565_);
return v_cs_569_;
}
else
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_array_get_size(v_bs_567_);
v___x_573_ = lean_nat_dec_lt(v_i_568_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec(v_i_568_);
lean_dec_ref(v_env_565_);
return v_cs_569_;
}
else
{
lean_object* v_a_574_; lean_object* v_b_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_a_574_ = lean_array_fget_borrowed(v_as_566_, v_i_568_);
v_b_575_ = lean_array_fget_borrowed(v_bs_567_, v_i_568_);
lean_inc(v_b_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_env_565_);
v___x_576_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_565_, v_a_574_, v_b_575_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_i_568_, v___x_577_);
lean_dec(v_i_568_);
v___x_579_ = lean_array_push(v_cs_569_, v___x_576_);
v_i_568_ = v___x_578_;
v_cs_569_ = v___x_579_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(lean_object* v_env_581_, lean_object* v_vs_582_, lean_object* v_v_583_){
_start:
{
if (lean_obj_tag(v_vs_582_) == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_env_581_);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v_v_583_);
lean_ctor_set(v___x_602_, 1, v_vs_582_);
return v___x_602_;
}
else
{
lean_object* v_head_603_; 
v_head_603_ = lean_ctor_get(v_vs_582_, 0);
if (lean_obj_tag(v_head_603_) == 2)
{
if (lean_obj_tag(v_v_583_) == 2)
{
lean_object* v_tail_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_632_; 
lean_inc_ref(v_head_603_);
v_tail_604_ = lean_ctor_get(v_vs_582_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_vs_582_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_vs_582_, 0);
lean_dec(v_unused_633_);
v___x_606_ = v_vs_582_;
v_isShared_607_ = v_isSharedCheck_632_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_tail_604_);
lean_dec(v_vs_582_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_632_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_i_608_; lean_object* v_vs_609_; lean_object* v_i_610_; lean_object* v_vs_611_; uint8_t v___x_612_; 
v_i_608_ = lean_ctor_get(v_head_603_, 0);
v_vs_609_ = lean_ctor_get(v_head_603_, 1);
v_i_610_ = lean_ctor_get(v_v_583_, 0);
v_vs_611_ = lean_ctor_get(v_v_583_, 1);
v___x_612_ = lean_name_eq(v_i_608_, v_i_610_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_581_, v_tail_604_, v_v_583_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_613_);
v___x_615_ = v___x_606_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_head_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_629_; 
lean_inc_ref(v_vs_611_);
lean_inc_ref(v_vs_609_);
lean_inc(v_i_608_);
lean_dec_ref_known(v_head_603_, 2);
v_isSharedCheck_629_ = !lean_is_exclusive(v_v_583_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; lean_object* v_unused_631_; 
v_unused_630_ = lean_ctor_get(v_v_583_, 1);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_v_583_, 0);
lean_dec(v_unused_631_);
v___x_618_ = v_v_583_;
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
else
{
lean_dec(v_v_583_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
v___x_622_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_581_, v_vs_609_, v_vs_611_, v___x_620_, v___x_621_);
lean_dec_ref(v_vs_611_);
lean_dec_ref(v_vs_609_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_622_);
lean_ctor_set(v___x_618_, 0, v_i_608_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_i_608_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_622_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_624_);
v___x_626_ = v___x_606_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_tail_604_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_581_);
goto v___jp_584_;
}
}
else
{
lean_dec_ref(v_env_581_);
goto v___jp_584_;
}
}
v___jp_584_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_585_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_586_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0));
v___x_587_ = lean_unsigned_to_nat(92u);
v___x_588_ = lean_unsigned_to_nat(12u);
v___x_589_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1));
v___x_590_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_583_);
v___x_591_ = l_Std_Format_defWidth;
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = l_Std_Format_pretty(v___x_590_, v___x_591_, v___x_592_, v___x_592_);
v___x_594_ = lean_string_append(v___x_589_, v___x_593_);
lean_dec_ref(v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2));
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
v___x_597_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_vs_582_);
v___x_598_ = l_Std_Format_pretty(v___x_597_, v___x_591_, v___x_592_, v___x_592_);
v___x_599_ = lean_string_append(v___x_596_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = l_mkPanicMessageWithDecl(v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(v___x_600_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(lean_object* v_env_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_dec_ref(v_env_634_);
return v_x_635_;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v___x_639_; 
v_head_637_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_head_637_);
v_tail_638_ = lean_ctor_get(v_x_636_, 1);
lean_inc(v_tail_638_);
lean_dec_ref_known(v_x_636_, 2);
lean_inc_ref(v_env_634_);
v___x_639_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_634_, v_x_635_, v_head_637_);
v_x_635_ = v___x_639_;
v_x_636_ = v_tail_638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2___boxed(lean_object* v_env_641_, lean_object* v_as_642_, lean_object* v_bs_643_, lean_object* v_i_644_, lean_object* v_cs_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_641_, v_as_642_, v_bs_643_, v_i_644_, v_cs_645_);
lean_dec_ref(v_bs_643_);
lean_dec_ref(v_as_642_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(lean_object* v_a_647_, lean_object* v_n_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_a_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___boxed(lean_object* v_a_650_, lean_object* v_n_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(v_a_650_, v_n_651_);
lean_dec(v_n_651_);
return v_res_652_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(lean_object* v_a_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
else
{
lean_object* v_head_656_; lean_object* v_tail_657_; uint8_t v___x_658_; 
v_head_656_ = lean_ctor_get(v_x_654_, 0);
v_tail_657_ = lean_ctor_get(v_x_654_, 1);
v___x_658_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_653_, v_head_656_);
if (v___x_658_ == 0)
{
v_x_654_ = v_tail_657_;
goto _start;
}
else
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object* v_a_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v_a_660_, v_x_661_);
lean_dec(v_x_661_);
lean_dec(v_a_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(lean_object* v_env_664_, lean_object* v_forbiddenTypes_x27_665_, lean_object* v_n_666_, size_t v_sz_667_, size_t v_i_668_, lean_object* v_bs_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_lt(v_i_668_, v_sz_667_);
if (v___x_670_ == 0)
{
lean_dec(v_forbiddenTypes_x27_665_);
lean_dec_ref(v_env_664_);
return v_bs_669_;
}
else
{
lean_object* v_v_671_; lean_object* v___x_672_; lean_object* v_bs_x27_673_; lean_object* v___x_674_; size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v_v_671_ = lean_array_uget(v_bs_669_, v_i_668_);
v___x_672_ = lean_unsigned_to_nat(0u);
v_bs_x27_673_ = lean_array_uset(v_bs_669_, v_i_668_, v___x_672_);
lean_inc(v_forbiddenTypes_x27_665_);
lean_inc_ref(v_env_664_);
v___x_674_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_664_, v_v_671_, v_forbiddenTypes_x27_665_, v_n_666_);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_add(v_i_668_, v___x_675_);
v___x_677_ = lean_array_uset(v_bs_x27_673_, v_i_668_, v___x_674_);
v_i_668_ = v___x_676_;
v_bs_669_ = v___x_677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(lean_object* v_env_679_, lean_object* v_v_680_, lean_object* v_forbiddenTypes_681_, lean_object* v_remainingDepth_682_){
_start:
{
lean_object* v_zero_683_; uint8_t v_isZero_684_; 
v_zero_683_ = lean_unsigned_to_nat(0u);
v_isZero_684_ = lean_nat_dec_eq(v_remainingDepth_682_, v_zero_683_);
if (v_isZero_684_ == 1)
{
lean_object* v___x_685_; 
lean_dec(v_forbiddenTypes_681_);
lean_dec(v_v_680_);
lean_dec_ref(v_env_679_);
v___x_685_ = lean_box(1);
return v___x_685_;
}
else
{
lean_object* v_one_686_; lean_object* v_n_687_; 
v_one_686_ = lean_unsigned_to_nat(1u);
v_n_687_ = lean_nat_sub(v_remainingDepth_682_, v_one_686_);
switch(lean_obj_tag(v_v_680_))
{
case 2:
{
lean_object* v_i_688_; lean_object* v_vs_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_708_; 
v_i_688_ = lean_ctor_get(v_v_680_, 0);
v_vs_689_ = lean_ctor_get(v_v_680_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_v_680_);
if (v_isSharedCheck_708_ == 0)
{
v___x_691_ = v_v_680_;
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_vs_689_);
lean_inc(v_i_688_);
lean_dec(v_v_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_forbiddenTypes_x27_694_; lean_object* v_induct_701_; lean_object* v_toConstantVal_702_; uint8_t v_isRec_703_; lean_object* v_name_704_; uint8_t v___x_705_; 
lean_inc_ref(v_env_679_);
lean_inc(v_i_688_);
v_induct_701_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_i_688_, v_env_679_);
v_toConstantVal_702_ = lean_ctor_get(v_induct_701_, 0);
lean_inc_ref(v_toConstantVal_702_);
v_isRec_703_ = lean_ctor_get_uint8(v_induct_701_, sizeof(void*)*6);
lean_dec_ref(v_induct_701_);
v_name_704_ = lean_ctor_get(v_toConstantVal_702_, 0);
lean_inc(v_name_704_);
lean_dec_ref(v_toConstantVal_702_);
v___x_705_ = l_Lean_NameSet_contains(v_forbiddenTypes_681_, v_name_704_);
if (v___x_705_ == 0)
{
if (v_isRec_703_ == 0)
{
lean_dec(v_name_704_);
v_forbiddenTypes_x27_694_ = v_forbiddenTypes_681_;
goto v___jp_693_;
}
else
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_NameSet_insert(v_forbiddenTypes_681_, v_name_704_);
v_forbiddenTypes_x27_694_ = v___x_706_;
goto v___jp_693_;
}
}
else
{
lean_object* v___x_707_; 
lean_dec(v_name_704_);
lean_del_object(v___x_691_);
lean_dec_ref(v_vs_689_);
lean_dec(v_i_688_);
lean_dec(v_n_687_);
lean_dec(v_forbiddenTypes_681_);
lean_dec_ref(v_env_679_);
v___x_707_ = lean_box(1);
return v___x_707_;
}
v___jp_693_:
{
size_t v_sz_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_sz_695_ = lean_array_size(v_vs_689_);
v___x_696_ = ((size_t)0ULL);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_679_, v_forbiddenTypes_x27_694_, v_n_687_, v_sz_695_, v___x_696_, v_vs_689_);
lean_dec(v_n_687_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_697_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_i_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
case 3:
{
lean_object* v_vs_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_720_; 
v_vs_709_ = lean_ctor_get(v_v_680_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_v_680_);
if (v_isSharedCheck_720_ == 0)
{
v___x_711_ = v_v_680_;
v_isShared_712_ = v_isSharedCheck_720_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_vs_709_);
lean_dec(v_v_680_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_720_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v_vs_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_713_ = lean_box(0);
v_vs_714_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_679_, v_forbiddenTypes_681_, v_n_687_, v_vs_709_, v___x_713_);
lean_dec(v_n_687_);
v___x_715_ = lean_box(1);
v___x_716_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v___x_715_, v_vs_714_);
if (v___x_716_ == 0)
{
lean_object* v___x_718_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_vs_714_);
v___x_718_ = v___x_711_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_vs_714_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_dec(v_vs_714_);
lean_del_object(v___x_711_);
return v___x_715_;
}
}
}
default: 
{
lean_dec(v_n_687_);
lean_dec(v_forbiddenTypes_681_);
lean_dec_ref(v_env_679_);
return v_v_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(lean_object* v_env_721_, lean_object* v_forbiddenTypes_722_, lean_object* v_n_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
if (lean_obj_tag(v_a_724_) == 0)
{
lean_object* v___x_726_; 
lean_dec(v_forbiddenTypes_722_);
lean_dec_ref(v_env_721_);
v___x_726_ = l_List_reverse___redArg(v_a_725_);
return v___x_726_;
}
else
{
lean_object* v_head_727_; lean_object* v_tail_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_737_; 
v_head_727_ = lean_ctor_get(v_a_724_, 0);
v_tail_728_ = lean_ctor_get(v_a_724_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_737_ == 0)
{
v___x_730_ = v_a_724_;
v_isShared_731_ = v_isSharedCheck_737_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_tail_728_);
lean_inc(v_head_727_);
lean_dec(v_a_724_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_737_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
lean_inc(v_forbiddenTypes_722_);
lean_inc_ref(v_env_721_);
v___x_732_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_721_, v_head_727_, v_forbiddenTypes_722_, v_n_723_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_a_725_);
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_a_725_);
v___x_734_ = v_reuseFailAlloc_736_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
v_a_724_ = v_tail_728_;
v_a_725_ = v___x_734_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object* v_env_738_, lean_object* v_forbiddenTypes_739_, lean_object* v_n_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_738_, v_forbiddenTypes_739_, v_n_740_, v_a_741_, v_a_742_);
lean_dec(v_n_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object* v_env_744_, lean_object* v_forbiddenTypes_x27_745_, lean_object* v_n_746_, lean_object* v_sz_747_, lean_object* v_i_748_, lean_object* v_bs_749_){
_start:
{
size_t v_sz_boxed_750_; size_t v_i_boxed_751_; lean_object* v_res_752_; 
v_sz_boxed_750_ = lean_unbox_usize(v_sz_747_);
lean_dec(v_sz_747_);
v_i_boxed_751_ = lean_unbox_usize(v_i_748_);
lean_dec(v_i_748_);
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_744_, v_forbiddenTypes_x27_745_, v_n_746_, v_sz_boxed_750_, v_i_boxed_751_, v_bs_749_);
lean_dec(v_n_746_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___boxed(lean_object* v_env_753_, lean_object* v_v_754_, lean_object* v_forbiddenTypes_755_, lean_object* v_remainingDepth_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_753_, v_v_754_, v_forbiddenTypes_755_, v_remainingDepth_756_);
lean_dec(v_remainingDepth_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(lean_object* v_env_758_, lean_object* v_v_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = l_Lean_NameSet_empty;
v___x_761_ = lean_unsigned_to_nat(8u);
v___x_762_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_758_, v_v_759_, v___x_760_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(lean_object* v_env_763_, lean_object* v_v1_764_, lean_object* v_v2_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_inc_ref(v_env_763_);
v___x_766_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_763_, v_v1_764_, v_v2_765_);
v___x_767_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(v_env_763_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
uint8_t v___x_770_; 
v___x_770_ = 0;
return v___x_770_;
}
else
{
lean_object* v_head_771_; lean_object* v_tail_772_; uint8_t v___x_773_; 
v_head_771_ = lean_ctor_get(v_x_769_, 0);
v_tail_772_ = lean_ctor_get(v_x_769_, 1);
v___x_773_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_head_771_, v_x_768_);
if (v___x_773_ == 0)
{
v_x_769_ = v_tail_772_;
goto _start;
}
else
{
return v___x_773_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
switch(lean_obj_tag(v_x_775_))
{
case 2:
{
lean_object* v_i_777_; uint8_t v___x_778_; 
v_i_777_ = lean_ctor_get(v_x_775_, 0);
v___x_778_ = lean_name_eq(v_i_777_, v_x_776_);
return v___x_778_;
}
case 3:
{
lean_object* v_vs_779_; uint8_t v___x_780_; 
v_vs_779_ = lean_ctor_get(v_x_775_, 0);
v___x_780_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_776_, v_vs_779_);
return v___x_780_;
}
default: 
{
uint8_t v___x_781_; 
v___x_781_ = 1;
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_x_782_, v_x_783_);
lean_dec(v_x_783_);
lean_dec(v_x_782_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0___boxed(lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_786_, v_x_787_);
lean_dec(v_x_787_);
lean_dec(v_x_786_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(lean_object* v_x_793_, lean_object* v_as_x27_794_, lean_object* v_b_795_){
_start:
{
if (lean_obj_tag(v_as_x27_794_) == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_b_795_);
return v___x_796_;
}
else
{
lean_object* v_head_797_; lean_object* v_tail_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v_b_795_);
v_head_797_ = lean_ctor_get(v_as_x27_794_, 0);
v_tail_798_ = lean_ctor_get(v_as_x27_794_, 1);
v___x_799_ = lean_box(0);
v___x_800_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_797_) == 2)
{
lean_object* v_i_801_; lean_object* v_vs_802_; uint8_t v___x_803_; 
v_i_801_ = lean_ctor_get(v_head_797_, 0);
v_vs_802_ = lean_ctor_get(v_head_797_, 1);
v___x_803_ = lean_name_eq(v_i_801_, v_x_793_);
if (v___x_803_ == 0)
{
v_as_x27_794_ = v_tail_798_;
v_b_795_ = v___x_800_;
goto _start;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_inc_ref(v_vs_802_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_vs_802_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_799_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
else
{
v_as_x27_794_ = v_tail_798_;
v_b_795_ = v___x_800_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___boxed(lean_object* v_x_809_, lean_object* v_as_x27_810_, lean_object* v_b_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_809_, v_as_x27_810_, v_b_811_);
lean_dec(v_as_x27_810_);
lean_dec(v_x_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
switch(lean_obj_tag(v_x_813_))
{
case 2:
{
lean_object* v_i_815_; lean_object* v_vs_816_; uint8_t v___x_817_; 
v_i_815_ = lean_ctor_get(v_x_813_, 0);
v_vs_816_ = lean_ctor_get(v_x_813_, 1);
v___x_817_ = lean_name_eq(v_i_815_, v_x_814_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_box(0);
return v___x_818_;
}
else
{
lean_object* v___x_819_; 
lean_inc_ref(v_vs_816_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v_vs_816_);
return v___x_819_;
}
}
case 3:
{
lean_object* v_vs_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_val_824_; lean_object* v_fst_825_; 
v_vs_820_ = lean_ctor_get(v_x_813_, 0);
v___x_821_ = lean_box(0);
v___x_822_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
v___x_823_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_814_, v_vs_820_, v___x_822_);
v_val_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_824_);
lean_dec(v___x_823_);
v_fst_825_ = lean_ctor_get(v_val_824_, 0);
lean_inc(v_fst_825_);
lean_dec(v_val_824_);
if (lean_obj_tag(v_fst_825_) == 0)
{
return v___x_821_;
}
else
{
return v_fst_825_;
}
}
default: 
{
lean_object* v___x_826_; 
v___x_826_ = lean_box(0);
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs___boxed(lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_x_827_, v_x_828_);
lean_dec(v_x_828_);
lean_dec(v_x_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(lean_object* v_x_830_, lean_object* v_as_831_, lean_object* v_as_x27_832_, lean_object* v_b_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_830_, v_as_x27_832_, v_b_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___boxed(lean_object* v_x_836_, lean_object* v_as_837_, lean_object* v_as_x27_838_, lean_object* v_b_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(v_x_836_, v_as_837_, v_as_x27_838_, v_b_839_, v_a_840_);
lean_dec(v_as_x27_838_);
lean_dec(v_as_837_);
lean_dec(v_x_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(lean_object* v_a_854_){
_start:
{
lean_object* v_zero_855_; uint8_t v_isZero_856_; 
v_zero_855_ = lean_unsigned_to_nat(0u);
v_isZero_856_ = lean_nat_dec_eq(v_a_854_, v_zero_855_);
if (v_isZero_856_ == 1)
{
lean_object* v___x_857_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3));
return v___x_857_;
}
else
{
lean_object* v_one_858_; lean_object* v_n_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_one_858_ = lean_unsigned_to_nat(1u);
v_n_859_ = lean_nat_sub(v_a_854_, v_one_858_);
v___x_860_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5));
v___x_861_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_859_);
lean_dec(v_n_859_);
v___x_862_ = lean_mk_empty_array_with_capacity(v_one_858_);
v___x_863_ = lean_array_push(v___x_862_, v___x_861_);
v___x_864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_860_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___boxed(lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_a_865_);
lean_dec(v_a_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(lean_object* v_n_867_){
_start:
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = lean_unsigned_to_nat(8u);
v___x_869_ = lean_nat_dec_lt(v___x_868_, v_n_867_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_867_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = lean_box(1);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat___boxed(lean_object* v_n_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_n_872_);
lean_dec(v_n_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v_val_875_; lean_object* v___x_876_; 
v_val_875_ = lean_ctor_get(v_x_874_, 0);
v___x_876_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_val_875_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; 
v___x_877_ = lean_box(1);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit___boxed(lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_x_878_);
lean_dec_ref(v_x_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(lean_object* v_env_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
switch(lean_obj_tag(v_x_881_))
{
case 2:
{
lean_object* v_vs_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
lean_dec_ref(v_env_880_);
v_vs_883_ = lean_ctor_get(v_x_881_, 1);
v___x_884_ = lean_array_get_size(v_vs_883_);
v___x_885_ = lean_nat_dec_lt(v_x_882_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
v___x_886_ = lean_box(0);
return v___x_886_;
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_array_fget_borrowed(v_vs_883_, v_x_882_);
lean_inc(v___x_887_);
return v___x_887_;
}
}
case 3:
{
lean_object* v_vs_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_vs_888_ = lean_ctor_get(v_x_881_, 0);
v___x_889_ = lean_box(0);
v___x_890_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_880_, v_x_882_, v___x_889_, v_vs_888_);
return v___x_890_;
}
default: 
{
lean_dec_ref(v_env_880_);
lean_inc(v_x_881_);
return v_x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(lean_object* v_env_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_dec_ref(v_env_891_);
return v_x_893_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_head_895_ = lean_ctor_get(v_x_894_, 0);
v_tail_896_ = lean_ctor_get(v_x_894_, 1);
lean_inc_ref_n(v_env_891_, 2);
v___x_897_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_891_, v_head_895_, v_x_892_);
v___x_898_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_891_, v_x_893_, v___x_897_);
v_x_893_ = v___x_898_;
v_x_894_ = v_tail_896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0___boxed(lean_object* v_env_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_900_, v_x_901_, v_x_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec(v_x_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj___boxed(lean_object* v_env_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_905_, v_x_906_, v_x_907_);
lean_dec(v_x_907_);
lean_dec(v_x_906_);
return v_res_908_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_909_) == 2)
{
lean_object* v_vs_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_vs_910_ = lean_ctor_get(v_x_909_, 1);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_array_get_size(v_vs_910_);
v___x_913_ = lean_nat_dec_lt(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
v___x_914_ = 1;
return v___x_914_;
}
else
{
if (v___x_913_ == 0)
{
return v___x_913_;
}
else
{
size_t v___x_915_; size_t v___x_916_; uint8_t v___x_917_; 
v___x_915_ = ((size_t)0ULL);
v___x_916_ = lean_usize_of_nat(v___x_912_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_vs_910_, v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
return v___x_913_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = 0;
return v___x_918_;
}
}
}
}
else
{
uint8_t v___x_919_; 
v___x_919_ = 0;
return v___x_919_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(lean_object* v_as_920_, size_t v_i_921_, size_t v_stop_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_eq(v_i_921_, v_stop_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_array_uget_borrowed(v_as_920_, v_i_921_);
v___x_925_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v___x_924_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; 
v___x_926_ = 1;
return v___x_926_;
}
else
{
size_t v___x_927_; size_t v___x_928_; 
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_i_921_, v___x_927_);
v_i_921_ = v___x_928_;
goto _start;
}
}
else
{
uint8_t v___x_930_; 
v___x_930_ = 0;
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0___boxed(lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_stop_933_){
_start:
{
size_t v_i_boxed_934_; size_t v_stop_boxed_935_; uint8_t v_res_936_; lean_object* v_r_937_; 
v_i_boxed_934_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_stop_boxed_935_ = lean_unbox_usize(v_stop_933_);
lean_dec(v_stop_933_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_as_931_, v_i_boxed_934_, v_stop_boxed_935_);
lean_dec_ref(v_as_931_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral___boxed(lean_object* v_x_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_x_938_);
lean_dec(v_x_938_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(lean_object* v_msg_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_panic_fn_borrowed(v___x_942_, v_msg_941_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1));
v___x_947_ = lean_unsigned_to_nat(9u);
v___x_948_ = lean_unsigned_to_nat(271u);
v___x_949_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0));
v___x_950_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_951_ = l_mkPanicMessageWithDecl(v___x_950_, v___x_949_, v___x_948_, v___x_947_, v___x_946_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(lean_object* v_a_952_){
_start:
{
if (lean_obj_tag(v_a_952_) == 2)
{
lean_object* v_i_956_; 
v_i_956_ = lean_ctor_get(v_a_952_, 0);
if (lean_obj_tag(v_i_956_) == 1)
{
lean_object* v_pre_957_; 
v_pre_957_ = lean_ctor_get(v_i_956_, 0);
if (lean_obj_tag(v_pre_957_) == 1)
{
lean_object* v_pre_958_; 
v_pre_958_ = lean_ctor_get(v_pre_957_, 0);
if (lean_obj_tag(v_pre_958_) == 0)
{
lean_object* v_vs_959_; lean_object* v_str_960_; lean_object* v_str_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_vs_959_ = lean_ctor_get(v_a_952_, 1);
v_str_960_ = lean_ctor_get(v_i_956_, 1);
v_str_961_ = lean_ctor_get(v_pre_957_, 1);
v___x_962_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_963_ = lean_string_dec_eq(v_str_961_, v___x_962_);
if (v___x_963_ == 0)
{
goto v___jp_953_;
}
else
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_965_ = lean_string_dec_eq(v_str_960_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_967_ = lean_string_dec_eq(v_str_960_, v___x_966_);
if (v___x_967_ == 0)
{
goto v___jp_953_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_968_ = lean_array_get_size(v_vs_959_);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = lean_nat_dec_eq(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
goto v___jp_953_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = lean_array_fget_borrowed(v_vs_959_, v___x_971_);
v___x_973_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_972_);
v___x_974_ = lean_nat_add(v___x_973_, v___x_969_);
lean_dec(v___x_973_);
return v___x_974_;
}
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_array_get_size(v_vs_959_);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_nat_dec_eq(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
goto v___jp_953_;
}
else
{
return v___x_976_;
}
}
}
}
else
{
goto v___jp_953_;
}
}
else
{
goto v___jp_953_;
}
}
else
{
goto v___jp_953_;
}
}
else
{
goto v___jp_953_;
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2);
v___x_955_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(v___x_954_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___boxed(lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v_a_978_);
lean_dec(v_a_978_);
return v_res_979_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_instMonadEIO___redArg();
return v___x_980_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Array_instInhabited___redArg();
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_toApplicative_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1027_; 
v___x_990_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0);
v___x_991_ = l_StateRefT_x27_instMonad___redArg(v___x_990_);
v_toApplicative_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v___x_991_, 1);
lean_dec(v_unused_1028_);
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1027_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_toApplicative_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1027_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_toFunctor_996_; lean_object* v_toSeq_997_; lean_object* v_toSeqLeft_998_; lean_object* v_toSeqRight_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1025_; 
v_toFunctor_996_ = lean_ctor_get(v_toApplicative_992_, 0);
v_toSeq_997_ = lean_ctor_get(v_toApplicative_992_, 2);
v_toSeqLeft_998_ = lean_ctor_get(v_toApplicative_992_, 3);
v_toSeqRight_999_ = lean_ctor_get(v_toApplicative_992_, 4);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_toApplicative_992_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_toApplicative_992_, 1);
lean_dec(v_unused_1026_);
v___x_1001_ = v_toApplicative_992_;
v_isShared_1002_ = v_isSharedCheck_1025_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_toSeqRight_999_);
lean_inc(v_toSeqLeft_998_);
lean_inc(v_toSeq_997_);
lean_inc(v_toFunctor_996_);
lean_dec(v_toApplicative_992_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1025_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1012_; 
v___f_1003_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1));
v___f_1004_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2));
lean_inc_ref(v_toFunctor_996_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toFunctor_996_);
v___f_1006_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1006_, 0, v_toFunctor_996_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___f_1005_);
lean_ctor_set(v___x_1007_, 1, v___f_1006_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toSeqRight_999_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toSeqLeft_998_);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toSeq_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v___f_1008_);
lean_ctor_set(v___x_1001_, 3, v___f_1009_);
lean_ctor_set(v___x_1001_, 2, v___f_1010_);
lean_ctor_set(v___x_1001_, 1, v___f_1003_);
lean_ctor_set(v___x_1001_, 0, v___x_1007_);
v___x_1012_ = v___x_1001_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___f_1003_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v___f_1010_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v___f_1009_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v___f_1008_);
v___x_1012_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___f_1004_);
lean_ctor_set(v___x_994_, 0, v___x_1012_);
v___x_1014_ = v___x_994_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___f_1004_);
v___x_1014_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___x_1803__overap_1021_; lean_object* v___x_1022_; 
v___x_1015_ = l_StateRefT_x27_instMonad___redArg(v___x_1014_);
v___x_1016_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1017_ = lean_box(0);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_instInhabitedOfMonad___redArg(v___x_1015_, v___x_1018_);
v___f_1020_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1020_, 0, v___x_1019_);
v___x_1803__overap_1021_ = lean_panic_fn_borrowed(v___f_1020_, v_msg_984_);
lean_dec_ref(v___f_1020_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
lean_inc(v___y_986_);
lean_inc_ref(v___y_985_);
v___x_1022_ = lean_apply_5(v___x_1803__overap_1021_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, lean_box(0));
return v___x_1022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v_msg_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object* v_as_1036_, size_t v_i_1037_, size_t v_stop_1038_, lean_object* v_b_1039_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_usize_dec_eq(v_i_1037_, v_stop_1038_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1058_; 
v___x_1041_ = lean_array_uget_borrowed(v_as_1036_, v_i_1037_);
v_fst_1042_ = lean_ctor_get(v___x_1041_, 0);
v_snd_1043_ = lean_ctor_get(v___x_1041_, 1);
v_fst_1044_ = lean_ctor_get(v_b_1039_, 0);
v_snd_1045_ = lean_ctor_get(v_b_1039_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_b_1039_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1047_ = v_b_1039_;
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v_b_1039_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1049_ = l_Array_append___redArg(v_fst_1044_, v_fst_1042_);
lean_inc(v_snd_1043_);
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_snd_1043_);
v___x_1051_ = lean_array_push(v_snd_1045_, v___x_1050_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1051_);
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1053_ = v___x_1047_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
size_t v___x_1054_; size_t v___x_1055_; 
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_add(v_i_1037_, v___x_1054_);
v_i_1037_ = v___x_1055_;
v_b_1039_ = v___x_1053_;
goto _start;
}
}
}
else
{
return v_b_1039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object* v_as_1059_, lean_object* v_i_1060_, lean_object* v_stop_1061_, lean_object* v_b_1062_){
_start:
{
size_t v_i_boxed_1063_; size_t v_stop_boxed_1064_; lean_object* v_res_1065_; 
v_i_boxed_1063_ = lean_unbox_usize(v_i_1060_);
lean_dec(v_i_1060_);
v_stop_boxed_1064_ = lean_unbox_usize(v_stop_1061_);
lean_dec(v_stop_1061_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_as_1059_, v_i_boxed_1063_, v_stop_boxed_1064_, v_b_1062_);
lean_dec_ref(v_as_1059_);
return v_res_1065_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1070_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1071_ = lean_unsigned_to_nat(65u);
v___x_1072_ = lean_unsigned_to_nat(258u);
v___x_1073_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1074_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1075_ = l_mkPanicMessageWithDecl(v___x_1074_, v___x_1073_, v___x_1072_, v___x_1071_, v___x_1070_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1083_ = lean_unsigned_to_nat(9u);
v___x_1084_ = lean_unsigned_to_nat(266u);
v___x_1085_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1086_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1087_ = l_mkPanicMessageWithDecl(v___x_1086_, v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; 
if (lean_obj_tag(v_a_1088_) == 2)
{
lean_object* v_i_1143_; lean_object* v_vs_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1265_; 
v_i_1143_ = lean_ctor_get(v_a_1088_, 0);
v_vs_1144_ = lean_ctor_get(v_a_1088_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_a_1088_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1146_ = v_a_1088_;
v_isShared_1147_ = v_isSharedCheck_1265_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_vs_1144_);
lean_inc(v_i_1143_);
lean_dec(v_a_1088_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1265_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_ctorName_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; 
if (lean_obj_tag(v_i_1143_) == 1)
{
lean_object* v_pre_1187_; 
v_pre_1187_ = lean_ctor_get(v_i_1143_, 0);
if (lean_obj_tag(v_pre_1187_) == 1)
{
lean_object* v_pre_1188_; 
v_pre_1188_ = lean_ctor_get(v_pre_1187_, 0);
if (lean_obj_tag(v_pre_1188_) == 0)
{
lean_object* v_str_1189_; lean_object* v_str_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_str_1189_ = lean_ctor_get(v_i_1143_, 1);
v_str_1190_ = lean_ctor_get(v_pre_1187_, 1);
v___x_1191_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_1192_ = lean_string_dec_eq(v_str_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
v_ctorName_1149_ = v_i_1143_;
v___y_1150_ = v_a_1089_;
v___y_1151_ = v_a_1090_;
v___y_1152_ = v_a_1091_;
v___y_1153_ = v_a_1092_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
lean_inc_ref(v_str_1189_);
lean_inc(v_pre_1188_);
lean_dec_ref_known(v_i_1143_, 2);
v___x_1193_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_1194_ = lean_string_dec_eq(v_str_1189_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_1196_ = lean_string_dec_eq(v_str_1189_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = l_Lean_Name_str___override(v_pre_1188_, v___x_1191_);
v___x_1198_ = l_Lean_Name_str___override(v___x_1197_, v_str_1189_);
v_ctorName_1149_ = v___x_1198_;
v___y_1150_ = v_a_1089_;
v___y_1151_ = v_a_1090_;
v___y_1152_ = v_a_1091_;
v___y_1153_ = v_a_1092_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
lean_dec_ref(v_str_1189_);
v___x_1199_ = lean_array_get_size(v_vs_1144_);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_nat_dec_eq(v___x_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Lean_Name_str___override(v_pre_1188_, v___x_1191_);
v___x_1203_ = l_Lean_Name_str___override(v___x_1202_, v___x_1195_);
v_ctorName_1149_ = v___x_1203_;
v___y_1150_ = v_a_1089_;
v___y_1151_ = v_a_1090_;
v___y_1152_ = v_a_1091_;
v___y_1153_ = v_a_1092_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_val_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_del_object(v___x_1146_);
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_array_fget(v_vs_1144_, v___x_1204_);
lean_dec_ref(v_vs_1144_);
v___x_1206_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_1205_);
lean_dec(v___x_1205_);
v_val_1207_ = lean_nat_add(v___x_1206_, v___x_1200_);
lean_dec(v___x_1206_);
v___x_1208_ = 0;
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_val_1207_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
v___x_1211_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1212_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1208_, v___x_1210_, v___x_1211_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1225_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_fvarId_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v_fvarId_1217_ = lean_ctor_get(v_a_1213_, 0);
lean_inc(v_fvarId_1217_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_a_1213_);
v___x_1219_ = lean_mk_empty_array_with_capacity(v___x_1200_);
v___x_1220_ = lean_array_push(v___x_1219_, v___x_1218_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v_fvarId_1217_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1221_);
v___x_1223_ = v___x_1215_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1212_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1212_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
lean_dec_ref(v_str_1189_);
v___x_1234_ = lean_array_get_size(v_vs_1144_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_nat_dec_eq(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = l_Lean_Name_str___override(v_pre_1188_, v___x_1191_);
v___x_1238_ = l_Lean_Name_str___override(v___x_1237_, v___x_1193_);
v_ctorName_1149_ = v___x_1238_;
v___y_1150_ = v_a_1089_;
v___y_1151_ = v_a_1090_;
v___y_1152_ = v_a_1091_;
v___y_1153_ = v_a_1092_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_del_object(v___x_1146_);
lean_dec_ref(v_vs_1144_);
v___x_1239_ = 0;
v___x_1240_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6));
v___x_1241_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1242_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1239_, v___x_1240_, v___x_1241_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1256_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1256_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1256_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_fvarId_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v_fvarId_1247_ = lean_ctor_get(v_a_1243_, 0);
lean_inc(v_fvarId_1247_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1243_);
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_mk_empty_array_with_capacity(v___x_1249_);
v___x_1251_ = lean_array_push(v___x_1250_, v___x_1248_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_fvarId_1247_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1252_);
v___x_1254_ = v___x_1245_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1242_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1242_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
}
else
{
v_ctorName_1149_ = v_i_1143_;
v___y_1150_ = v_a_1089_;
v___y_1151_ = v_a_1090_;
v___y_1152_ = v_a_1091_;
v___y_1153_ = v_a_1092_;
goto v___jp_1148_;
}
}
else
{
v_ctorName_1149_ = v_i_1143_;
v___y_1150_ = v_a_1089_;
v___y_1151_ = v_a_1090_;
v___y_1152_ = v_a_1091_;
v___y_1153_ = v_a_1092_;
goto v___jp_1148_;
}
}
else
{
v_ctorName_1149_ = v_i_1143_;
v___y_1150_ = v_a_1089_;
v___y_1151_ = v_a_1090_;
v___y_1152_ = v_a_1091_;
v___y_1153_ = v_a_1092_;
goto v___jp_1148_;
}
v___jp_1148_:
{
lean_object* v___x_1154_; lean_object* v_env_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = lean_st_ref_get(v___y_1153_);
v_env_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc_ref(v_env_1155_);
lean_dec(v___x_1154_);
v___x_1156_ = 0;
lean_inc(v_ctorName_1149_);
v___x_1157_ = l_Lean_Environment_find_x3f(v_env_1155_, v_ctorName_1149_, v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 1)
{
lean_object* v_val_1158_; 
v_val_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v___x_1157_, 1);
if (lean_obj_tag(v_val_1158_) == 6)
{
lean_object* v_val_1159_; size_t v_sz_1160_; size_t v___x_1161_; lean_object* v___x_1162_; 
v_val_1159_ = lean_ctor_get(v_val_1158_, 0);
lean_inc_ref(v_val_1159_);
lean_dec_ref_known(v_val_1158_, 1);
v_sz_1160_ = lean_array_size(v_vs_1144_);
v___x_1161_ = ((size_t)0ULL);
v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_1160_, v___x_1161_, v_vs_1144_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_numParams_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_numParams_1164_ = lean_ctor_get(v_val_1159_, 3);
lean_inc(v_numParams_1164_);
lean_dec_ref(v_val_1159_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4));
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_mk_array(v_numParams_1164_, v___x_1167_);
v___x_1169_ = lean_array_get_size(v_a_1163_);
v___x_1170_ = lean_nat_dec_lt(v___x_1165_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_dec(v_a_1163_);
lean_del_object(v___x_1146_);
v___y_1095_ = v___y_1152_;
v___y_1096_ = v___y_1150_;
v___y_1097_ = v___y_1151_;
v___y_1098_ = v_ctorName_1149_;
v___y_1099_ = v___y_1153_;
v_fst_1100_ = v___x_1166_;
v_snd_1101_ = v___x_1168_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1172_; 
lean_inc_ref(v___x_1168_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set_tag(v___x_1146_, 0);
lean_ctor_set(v___x_1146_, 1, v___x_1168_);
lean_ctor_set(v___x_1146_, 0, v___x_1166_);
v___x_1172_ = v___x_1146_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1168_);
v___x_1172_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_le(v___x_1169_, v___x_1169_);
if (v___x_1173_ == 0)
{
if (v___x_1170_ == 0)
{
lean_dec_ref(v___x_1172_);
lean_dec(v_a_1163_);
v___y_1095_ = v___y_1152_;
v___y_1096_ = v___y_1150_;
v___y_1097_ = v___y_1151_;
v___y_1098_ = v_ctorName_1149_;
v___y_1099_ = v___y_1153_;
v_fst_1100_ = v___x_1166_;
v_snd_1101_ = v___x_1168_;
goto v___jp_1094_;
}
else
{
size_t v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref(v___x_1168_);
v___x_1174_ = lean_usize_of_nat(v___x_1169_);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1163_, v___x_1161_, v___x_1174_, v___x_1172_);
lean_dec(v_a_1163_);
v___y_1128_ = v___y_1152_;
v___y_1129_ = v___y_1150_;
v___y_1130_ = v_ctorName_1149_;
v___y_1131_ = v___y_1151_;
v___y_1132_ = v___y_1153_;
v___y_1133_ = v___x_1175_;
goto v___jp_1127_;
}
}
else
{
size_t v___x_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v___x_1168_);
v___x_1176_ = lean_usize_of_nat(v___x_1169_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1163_, v___x_1161_, v___x_1176_, v___x_1172_);
lean_dec(v_a_1163_);
v___y_1128_ = v___y_1152_;
v___y_1129_ = v___y_1150_;
v___y_1130_ = v_ctorName_1149_;
v___y_1131_ = v___y_1151_;
v___y_1132_ = v___y_1153_;
v___y_1133_ = v___x_1177_;
goto v___jp_1127_;
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_val_1159_);
lean_dec(v_ctorName_1149_);
lean_del_object(v___x_1146_);
v_a_1179_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1162_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1162_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_dec(v_val_1158_);
lean_dec(v_ctorName_1149_);
lean_del_object(v___x_1146_);
lean_dec_ref(v_vs_1144_);
v___y_1137_ = v___y_1150_;
v___y_1138_ = v___y_1151_;
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___y_1153_;
goto v___jp_1136_;
}
}
else
{
lean_dec(v___x_1157_);
lean_dec(v_ctorName_1149_);
lean_del_object(v___x_1146_);
lean_dec_ref(v_vs_1144_);
v___y_1137_ = v___y_1150_;
v___y_1138_ = v___y_1151_;
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___y_1153_;
goto v___jp_1136_;
}
}
}
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v_a_1088_);
v___x_1266_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7);
v___x_1267_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1266_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1267_;
}
v___jp_1094_:
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1102_ = 0;
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1104_, 0, v___y_1098_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
lean_ctor_set(v___x_1104_, 2, v_snd_1101_);
v___x_1105_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1106_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1102_, v___x_1104_, v___x_1105_, v___y_1096_, v___y_1097_, v___y_1095_, v___y_1099_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_fvarId_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v_fvarId_1111_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_fvarId_1111_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1107_);
v___x_1113_ = lean_array_push(v_fst_1100_, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_fvarId_1111_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1114_);
v___x_1116_ = v___x_1109_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_fst_1100_);
v_a_1119_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1106_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1106_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
v___jp_1127_:
{
lean_object* v_fst_1134_; lean_object* v_snd_1135_; 
v_fst_1134_ = lean_ctor_get(v___y_1133_, 0);
lean_inc(v_fst_1134_);
v_snd_1135_ = lean_ctor_get(v___y_1133_, 1);
lean_inc(v_snd_1135_);
lean_dec_ref(v___y_1133_);
v___y_1095_ = v___y_1128_;
v___y_1096_ = v___y_1129_;
v___y_1097_ = v___y_1131_;
v___y_1098_ = v___y_1130_;
v___y_1099_ = v___y_1132_;
v_fst_1100_ = v_fst_1134_;
v_snd_1101_ = v_snd_1135_;
goto v___jp_1094_;
}
v___jp_1136_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3);
v___x_1142_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1141_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(size_t v_sz_1268_, size_t v_i_1269_, lean_object* v_bs_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_usize_dec_lt(v_i_1269_, v_sz_1268_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_bs_1270_);
return v___x_1277_;
}
else
{
lean_object* v_v_1278_; lean_object* v___x_1279_; lean_object* v_bs_x27_1280_; lean_object* v___x_1281_; 
v_v_1278_ = lean_array_uget(v_bs_1270_, v_i_1269_);
v___x_1279_ = lean_unsigned_to_nat(0u);
v_bs_x27_1280_ = lean_array_uset(v_bs_1270_, v_i_1269_, v___x_1279_);
v___x_1281_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1278_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_add(v_i_1269_, v___x_1283_);
v___x_1285_ = lean_array_uset(v_bs_x27_1280_, v_i_1269_, v_a_1282_);
v_i_1269_ = v___x_1284_;
v_bs_1270_ = v___x_1285_;
goto _start;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_bs_x27_1280_);
v_a_1287_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1281_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1281_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object* v_sz_1295_, lean_object* v_i_1296_, lean_object* v_bs_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
size_t v_sz_boxed_1303_; size_t v_i_boxed_1304_; lean_object* v_res_1305_; 
v_sz_boxed_1303_ = lean_unbox_usize(v_sz_1295_);
lean_dec(v_sz_1295_);
v_i_boxed_1304_ = lean_unbox_usize(v_i_1296_);
lean_dec(v_i_1296_);
v_res_1305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_boxed_1303_, v_i_boxed_1304_, v_bs_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(lean_object* v_v_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_v_1313_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec(v_v_1313_);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_a_1323_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1327_);
v___x_1329_ = v___x_1325_;
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
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1322_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1322_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral___boxed(lean_object* v_v_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_v_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
return v_res_1346_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(lean_object* v_a_1347_, lean_object* v_b_1348_){
_start:
{
lean_object* v_fst_1349_; lean_object* v_fst_1350_; uint8_t v___x_1351_; 
v_fst_1349_ = lean_ctor_get(v_a_1347_, 0);
v_fst_1350_ = lean_ctor_get(v_b_1348_, 0);
v___x_1351_ = l_Lean_Name_quickLt(v_fst_1349_, v_fst_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed(lean_object* v_a_1352_, lean_object* v_b_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(v_a_1352_, v_b_1353_);
lean_dec_ref(v_b_1353_);
lean_dec_ref(v_a_1352_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(lean_object* v_entries_1358_, lean_object* v_fid_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_array_get_size(v_entries_1358_);
v___x_1362_ = lean_nat_dec_lt(v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec(v_fid_1359_);
v___x_1363_ = lean_box(0);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = lean_nat_sub(v___x_1361_, v___x_1364_);
v___x_1366_ = lean_nat_dec_le(v___x_1360_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec(v___x_1365_);
lean_dec(v_fid_1359_);
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_fid_1359_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0));
v___x_1371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1));
v___x_1372_ = l_Array_binSearchAux___redArg(v___x_1370_, v___x_1371_, v_entries_1358_, v___x_1369_, v___x_1360_, v___x_1365_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_box(0);
return v___x_1373_;
}
else
{
lean_object* v_val_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1382_; 
v_val_1374_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1376_ = v___x_1372_;
v_isShared_1377_ = v_isSharedCheck_1382_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_val_1374_);
lean_dec(v___x_1372_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1382_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_snd_1378_; lean_object* v___x_1380_; 
v_snd_1378_ = lean_ctor_get(v_val_1374_, 1);
lean_inc(v_snd_1378_);
lean_dec(v_val_1374_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v_snd_1378_);
v___x_1380_ = v___x_1376_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_snd_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___boxed(lean_object* v_entries_1383_, lean_object* v_fid_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(v_entries_1383_, v_fid_1384_);
lean_dec_ref(v_entries_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_es_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_array_mk(v_es_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1388_, lean_object* v_i_1389_, lean_object* v_k_1390_){
_start:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_array_get_size(v_keys_1388_);
v___x_1392_ = lean_nat_dec_lt(v_i_1389_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_dec(v_i_1389_);
return v___x_1392_;
}
else
{
lean_object* v_k_x27_1393_; uint8_t v___x_1394_; 
v_k_x27_1393_ = lean_array_fget_borrowed(v_keys_1388_, v_i_1389_);
v___x_1394_ = lean_name_eq(v_k_1390_, v_k_x27_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_add(v_i_1389_, v___x_1395_);
lean_dec(v_i_1389_);
v_i_1389_ = v___x_1396_;
goto _start;
}
else
{
lean_dec(v_i_1389_);
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1398_, lean_object* v_i_1399_, lean_object* v_k_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1398_, v_i_1399_, v_k_1400_);
lean_dec(v_k_1400_);
lean_dec_ref(v_keys_1398_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1403_, size_t v_x_1404_, lean_object* v_x_1405_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 0)
{
lean_object* v_es_1406_; lean_object* v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; lean_object* v_j_1410_; lean_object* v___x_1411_; 
v_es_1406_ = lean_ctor_get(v_x_1403_, 0);
v___x_1407_ = lean_box(2);
v___x_1408_ = ((size_t)31ULL);
v___x_1409_ = lean_usize_land(v_x_1404_, v___x_1408_);
v_j_1410_ = lean_usize_to_nat(v___x_1409_);
v___x_1411_ = lean_array_get_borrowed(v___x_1407_, v_es_1406_, v_j_1410_);
lean_dec(v_j_1410_);
switch(lean_obj_tag(v___x_1411_))
{
case 0:
{
lean_object* v_key_1412_; uint8_t v___x_1413_; 
v_key_1412_ = lean_ctor_get(v___x_1411_, 0);
v___x_1413_ = lean_name_eq(v_x_1405_, v_key_1412_);
return v___x_1413_;
}
case 1:
{
lean_object* v_node_1414_; size_t v___x_1415_; size_t v___x_1416_; 
v_node_1414_ = lean_ctor_get(v___x_1411_, 0);
v___x_1415_ = ((size_t)5ULL);
v___x_1416_ = lean_usize_shift_right(v_x_1404_, v___x_1415_);
v_x_1403_ = v_node_1414_;
v_x_1404_ = v___x_1416_;
goto _start;
}
default: 
{
uint8_t v___x_1418_; 
v___x_1418_ = 0;
return v___x_1418_;
}
}
}
else
{
lean_object* v_ks_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_ks_1419_ = lean_ctor_get(v_x_1403_, 0);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1419_, v___x_1420_, v_x_1405_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
size_t v_x_1145__boxed_1425_; uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_x_1145__boxed_1425_ = lean_unbox_usize(v_x_1423_);
lean_dec(v_x_1423_);
v_res_1426_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1422_, v_x_1145__boxed_1425_, v_x_1424_);
lean_dec(v_x_1424_);
lean_dec_ref(v_x_1422_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
uint64_t v___y_1431_; 
if (lean_obj_tag(v_x_1429_) == 0)
{
uint64_t v___x_1434_; 
v___x_1434_ = 1723ULL;
v___y_1431_ = v___x_1434_;
goto v___jp_1430_;
}
else
{
uint64_t v_hash_1435_; 
v_hash_1435_ = lean_ctor_get_uint64(v_x_1429_, sizeof(void*)*2);
v___y_1431_ = v_hash_1435_;
goto v___jp_1430_;
}
v___jp_1430_:
{
size_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = lean_uint64_to_usize(v___y_1431_);
v___x_1433_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1428_, v___x_1432_, v_x_1429_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1436_, v_x_1437_);
lean_dec(v_x_1437_);
lean_dec_ref(v_x_1436_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x1_1440_, lean_object* v_x2_1441_){
_start:
{
lean_object* v_fst_1442_; uint8_t v___x_1443_; 
v_fst_1442_ = lean_ctor_get(v_x2_1441_, 0);
v___x_1443_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x1_1440_, v_fst_1442_);
if (v___x_1443_ == 0)
{
uint8_t v___x_1444_; 
v___x_1444_ = 1;
return v___x_1444_;
}
else
{
uint8_t v___x_1445_; 
v___x_1445_ = 0;
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x1_1446_, lean_object* v_x2_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x1_1446_, v_x2_1447_);
lean_dec_ref(v_x2_1447_);
lean_dec_ref(v_x1_1446_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_f_1450_, lean_object* v_keys_1451_, lean_object* v_vals_1452_, lean_object* v_i_1453_, lean_object* v_acc_1454_){
_start:
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = lean_array_get_size(v_keys_1451_);
v___x_1456_ = lean_nat_dec_lt(v_i_1453_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_dec(v_i_1453_);
lean_dec(v_f_1450_);
return v_acc_1454_;
}
else
{
lean_object* v_k_1457_; lean_object* v_v_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_k_1457_ = lean_array_fget_borrowed(v_keys_1451_, v_i_1453_);
v_v_1458_ = lean_array_fget_borrowed(v_vals_1452_, v_i_1453_);
lean_inc(v_f_1450_);
lean_inc(v_v_1458_);
lean_inc(v_k_1457_);
v___x_1459_ = lean_apply_3(v_f_1450_, v_acc_1454_, v_k_1457_, v_v_1458_);
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_add(v_i_1453_, v___x_1460_);
lean_dec(v_i_1453_);
v_i_1453_ = v___x_1461_;
v_acc_1454_ = v___x_1459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_f_1463_, lean_object* v_keys_1464_, lean_object* v_vals_1465_, lean_object* v_i_1466_, lean_object* v_acc_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1463_, v_keys_1464_, v_vals_1465_, v_i_1466_, v_acc_1467_);
lean_dec_ref(v_vals_1465_);
lean_dec_ref(v_keys_1464_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1469_, lean_object* v_as_1470_, size_t v_i_1471_, size_t v_stop_1472_, lean_object* v_b_1473_){
_start:
{
lean_object* v___y_1475_; uint8_t v___x_1479_; 
v___x_1479_ = lean_usize_dec_eq(v_i_1471_, v_stop_1472_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_array_uget_borrowed(v_as_1470_, v_i_1471_);
switch(lean_obj_tag(v___x_1480_))
{
case 0:
{
lean_object* v_key_1481_; lean_object* v_val_1482_; lean_object* v___x_1483_; 
v_key_1481_ = lean_ctor_get(v___x_1480_, 0);
v_val_1482_ = lean_ctor_get(v___x_1480_, 1);
lean_inc(v_f_1469_);
lean_inc(v_val_1482_);
lean_inc(v_key_1481_);
v___x_1483_ = lean_apply_3(v_f_1469_, v_b_1473_, v_key_1481_, v_val_1482_);
v___y_1475_ = v___x_1483_;
goto v___jp_1474_;
}
case 1:
{
lean_object* v_node_1484_; lean_object* v___x_1485_; 
v_node_1484_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_f_1469_);
v___x_1485_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1469_, v_node_1484_, v_b_1473_);
v___y_1475_ = v___x_1485_;
goto v___jp_1474_;
}
default: 
{
v___y_1475_ = v_b_1473_;
goto v___jp_1474_;
}
}
}
else
{
lean_dec(v_f_1469_);
return v_b_1473_;
}
v___jp_1474_:
{
size_t v___x_1476_; size_t v___x_1477_; 
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_add(v_i_1471_, v___x_1476_);
v_i_1471_ = v___x_1477_;
v_b_1473_ = v___y_1475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
if (lean_obj_tag(v_x_1487_) == 0)
{
lean_object* v_es_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_es_1489_ = lean_ctor_get(v_x_1487_, 0);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_array_get_size(v_es_1489_);
v___x_1492_ = lean_nat_dec_lt(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec(v_f_1486_);
return v_x_1488_;
}
else
{
size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = ((size_t)0ULL);
v___x_1494_ = lean_usize_of_nat(v___x_1491_);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1486_, v_es_1489_, v___x_1493_, v___x_1494_, v_x_1488_);
return v___x_1495_;
}
}
else
{
lean_object* v_ks_1496_; lean_object* v_vs_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_ks_1496_ = lean_ctor_get(v_x_1487_, 0);
v_vs_1497_ = lean_ctor_get(v_x_1487_, 1);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1486_, v_ks_1496_, v_vs_1497_, v___x_1498_, v_x_1488_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1500_, v_x_1501_, v_x_1502_);
lean_dec_ref(v_x_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1504_, lean_object* v_as_1505_, lean_object* v_i_1506_, lean_object* v_stop_1507_, lean_object* v_b_1508_){
_start:
{
size_t v_i_boxed_1509_; size_t v_stop_boxed_1510_; lean_object* v_res_1511_; 
v_i_boxed_1509_ = lean_unbox_usize(v_i_1506_);
lean_dec(v_i_1506_);
v_stop_boxed_1510_ = lean_unbox_usize(v_stop_1507_);
lean_dec(v_stop_1507_);
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1504_, v_as_1505_, v_i_boxed_1509_, v_stop_boxed_1510_, v_b_1508_);
lean_dec_ref(v_as_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1512_, lean_object* v_x1_1513_, lean_object* v_x2_1514_, lean_object* v_x3_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_apply_3(v_f_1512_, v_x1_1513_, v_x2_1514_, v_x3_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1517_, lean_object* v_f_1518_, lean_object* v_init_1519_){
_start:
{
lean_object* v___f_1520_; lean_object* v___x_1521_; 
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1520_, 0, v_f_1518_);
v___x_1521_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1520_, v_map_1517_, v_init_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1522_, lean_object* v_f_1523_, lean_object* v_init_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1522_, v_f_1523_, v_init_1524_);
lean_dec_ref(v_map_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1526_, lean_object* v_k_1527_, lean_object* v_v_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_k_1527_);
lean_ctor_set(v___x_1529_, 1, v_v_1528_);
v___x_1530_ = lean_array_push(v_ps_1526_, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1534_){
_start:
{
lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___f_1535_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1536_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1537_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1534_, v___f_1535_, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1538_);
lean_dec_ref(v_m_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_fst_1542_; lean_object* v_fst_1543_; uint8_t v___x_1544_; 
v_fst_1542_ = lean_ctor_get(v___y_1540_, 0);
v_fst_1543_ = lean_ctor_get(v___y_1541_, 0);
v___x_1544_ = l_Lean_Name_quickLt(v_fst_1542_, v_fst_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_res_1547_; lean_object* v_r_1548_; 
v_res_1547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1545_, v___y_1546_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v___y_1545_);
v_r_1548_ = lean_box(v_res_1547_);
return v_r_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_hi_1549_, lean_object* v_pivot_1550_, lean_object* v_as_1551_, lean_object* v_i_1552_, lean_object* v_k_1553_){
_start:
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_nat_dec_lt(v_k_1553_, v_hi_1549_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec(v_k_1553_);
v___x_1555_ = lean_array_fswap(v_as_1551_, v_i_1552_, v_hi_1549_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_i_1552_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
return v___x_1556_;
}
else
{
lean_object* v___x_1557_; lean_object* v_fst_1558_; lean_object* v_fst_1559_; uint8_t v___x_1560_; 
v___x_1557_ = lean_array_fget_borrowed(v_as_1551_, v_k_1553_);
v_fst_1558_ = lean_ctor_get(v___x_1557_, 0);
v_fst_1559_ = lean_ctor_get(v_pivot_1550_, 0);
v___x_1560_ = l_Lean_Name_quickLt(v_fst_1558_, v_fst_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = lean_nat_add(v_k_1553_, v___x_1561_);
lean_dec(v_k_1553_);
v_k_1553_ = v___x_1562_;
goto _start;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_array_fswap(v_as_1551_, v_i_1552_, v_k_1553_);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_i_1552_, v___x_1565_);
lean_dec(v_i_1552_);
v___x_1567_ = lean_nat_add(v_k_1553_, v___x_1565_);
lean_dec(v_k_1553_);
v_as_1551_ = v___x_1564_;
v_i_1552_ = v___x_1566_;
v_k_1553_ = v___x_1567_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_hi_1569_, lean_object* v_pivot_1570_, lean_object* v_as_1571_, lean_object* v_i_1572_, lean_object* v_k_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1569_, v_pivot_1570_, v_as_1571_, v_i_1572_, v_k_1573_);
lean_dec_ref(v_pivot_1570_);
lean_dec(v_hi_1569_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_1575_, lean_object* v_as_1576_, lean_object* v_lo_1577_, lean_object* v_hi_1578_){
_start:
{
lean_object* v___y_1580_; uint8_t v___x_1590_; 
v___x_1590_ = lean_nat_dec_lt(v_lo_1577_, v_hi_1578_);
if (v___x_1590_ == 0)
{
lean_dec(v_lo_1577_);
return v_as_1576_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_mid_1593_; lean_object* v___y_1595_; lean_object* v___y_1601_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1591_ = lean_nat_add(v_lo_1577_, v_hi_1578_);
v___x_1592_ = lean_unsigned_to_nat(1u);
v_mid_1593_ = lean_nat_shiftr(v___x_1591_, v___x_1592_);
lean_dec(v___x_1591_);
v___x_1606_ = lean_array_fget_borrowed(v_as_1576_, v_mid_1593_);
v___x_1607_ = lean_array_fget_borrowed(v_as_1576_, v_lo_1577_);
v___x_1608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1606_, v___x_1607_);
if (v___x_1608_ == 0)
{
v___y_1601_ = v_as_1576_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_array_fswap(v_as_1576_, v_lo_1577_, v_mid_1593_);
v___y_1601_ = v___x_1609_;
goto v___jp_1600_;
}
v___jp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1596_ = lean_array_fget_borrowed(v___y_1595_, v_mid_1593_);
v___x_1597_ = lean_array_fget_borrowed(v___y_1595_, v_hi_1578_);
v___x_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_dec(v_mid_1593_);
v___y_1580_ = v___y_1595_;
goto v___jp_1579_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_array_fswap(v___y_1595_, v_mid_1593_, v_hi_1578_);
lean_dec(v_mid_1593_);
v___y_1580_ = v___x_1599_;
goto v___jp_1579_;
}
}
v___jp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1602_ = lean_array_fget_borrowed(v___y_1601_, v_hi_1578_);
v___x_1603_ = lean_array_fget_borrowed(v___y_1601_, v_lo_1577_);
v___x_1604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
v___y_1595_ = v___y_1601_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_array_fswap(v___y_1601_, v_lo_1577_, v_hi_1578_);
v___y_1595_ = v___x_1605_;
goto v___jp_1594_;
}
}
}
v___jp_1579_:
{
lean_object* v_pivot_1581_; lean_object* v___x_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; uint8_t v___x_1585_; 
v_pivot_1581_ = lean_array_fget(v___y_1580_, v_hi_1578_);
lean_inc_n(v_lo_1577_, 2);
v___x_1582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1578_, v_pivot_1581_, v___y_1580_, v_lo_1577_, v_lo_1577_);
lean_dec(v_pivot_1581_);
v_fst_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_fst_1583_);
v_snd_1584_ = lean_ctor_get(v___x_1582_, 1);
lean_inc(v_snd_1584_);
lean_dec_ref(v___x_1582_);
v___x_1585_ = lean_nat_dec_le(v_hi_1578_, v_fst_1583_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1575_, v_snd_1584_, v_lo_1577_, v_fst_1583_);
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = lean_nat_add(v_fst_1583_, v___x_1587_);
lean_dec(v_fst_1583_);
v_as_1576_ = v___x_1586_;
v_lo_1577_ = v___x_1588_;
goto _start;
}
else
{
lean_dec(v_fst_1583_);
lean_dec(v_lo_1577_);
return v_snd_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_1610_, lean_object* v_as_1611_, lean_object* v_lo_1612_, lean_object* v_hi_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1610_, v_as_1611_, v_lo_1612_, v_hi_1613_);
lean_dec(v_hi_1613_);
lean_dec(v_n_1610_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1617_, lean_object* v_s_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___y_1625_; lean_object* v___y_1626_; uint8_t v___x_1629_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1622_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1618_);
v___x_1623_ = lean_array_get_size(v___x_1622_);
v___x_1629_ = lean_nat_dec_eq(v___x_1623_, v___x_1620_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___y_1633_; uint8_t v___x_1635_; 
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_nat_sub(v___x_1623_, v___x_1630_);
v___x_1635_ = lean_nat_dec_le(v___x_1620_, v___x_1631_);
if (v___x_1635_ == 0)
{
lean_inc(v___x_1631_);
v___y_1633_ = v___x_1631_;
goto v___jp_1632_;
}
else
{
v___y_1633_ = v___x_1620_;
goto v___jp_1632_;
}
v___jp_1632_:
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_nat_dec_le(v___y_1633_, v___x_1631_);
if (v___x_1634_ == 0)
{
lean_dec(v___x_1631_);
lean_inc(v___y_1633_);
v___y_1625_ = v___y_1633_;
v___y_1626_ = v___y_1633_;
goto v___jp_1624_;
}
else
{
v___y_1625_ = v___y_1633_;
v___y_1626_ = v___x_1631_;
goto v___jp_1624_;
}
}
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1621_);
lean_ctor_set(v___x_1636_, 1, v___x_1621_);
lean_ctor_set(v___x_1636_, 2, v___x_1622_);
return v___x_1636_;
}
v___jp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1623_, v___x_1622_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
v___x_1628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1621_);
lean_ctor_set(v___x_1628_, 1, v___x_1621_);
lean_ctor_set(v___x_1628_, 2, v___x_1627_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1637_, lean_object* v_s_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1637_, v_s_1638_, v_x_1639_);
lean_dec(v_x_1639_);
lean_dec_ref(v_s_1638_);
lean_dec_ref(v_x_1637_);
return v_res_1640_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1641_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1646_);
lean_dec_ref(v_x_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v_ks_1652_; lean_object* v_vs_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1677_; 
v_ks_1652_ = lean_ctor_get(v_x_1648_, 0);
v_vs_1653_ = lean_ctor_get(v_x_1648_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1655_ = v_x_1648_;
v_isShared_1656_ = v_isSharedCheck_1677_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_vs_1653_);
lean_inc(v_ks_1652_);
lean_dec(v_x_1648_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1677_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = lean_array_get_size(v_ks_1652_);
v___x_1658_ = lean_nat_dec_lt(v_x_1649_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
lean_dec(v_x_1649_);
v___x_1659_ = lean_array_push(v_ks_1652_, v_x_1650_);
v___x_1660_ = lean_array_push(v_vs_1653_, v_x_1651_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1660_);
lean_ctor_set(v___x_1655_, 0, v___x_1659_);
v___x_1662_ = v___x_1655_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
else
{
lean_object* v_k_x27_1664_; uint8_t v___x_1665_; 
v_k_x27_1664_ = lean_array_fget_borrowed(v_ks_1652_, v_x_1649_);
v___x_1665_ = lean_name_eq(v_x_1650_, v_k_x27_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1667_; 
if (v_isShared_1656_ == 0)
{
v___x_1667_ = v___x_1655_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_ks_1652_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_vs_1653_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_add(v_x_1649_, v___x_1668_);
lean_dec(v_x_1649_);
v_x_1648_ = v___x_1667_;
v_x_1649_ = v___x_1669_;
goto _start;
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1672_ = lean_array_fset(v_ks_1652_, v_x_1649_, v_x_1650_);
v___x_1673_ = lean_array_fset(v_vs_1653_, v_x_1649_, v_x_1651_);
lean_dec(v_x_1649_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1673_);
lean_ctor_set(v___x_1655_, 0, v___x_1672_);
v___x_1675_ = v___x_1655_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_n_1678_, lean_object* v_k_1679_, lean_object* v_v_1680_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_n_1678_, v___x_1681_, v_k_1679_, v_v_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_x_1684_, size_t v_x_1685_, size_t v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
if (lean_obj_tag(v_x_1684_) == 0)
{
lean_object* v_es_1689_; size_t v___x_1690_; size_t v___x_1691_; lean_object* v_j_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_es_1689_ = lean_ctor_get(v_x_1684_, 0);
v___x_1690_ = ((size_t)31ULL);
v___x_1691_ = lean_usize_land(v_x_1685_, v___x_1690_);
v_j_1692_ = lean_usize_to_nat(v___x_1691_);
v___x_1693_ = lean_array_get_size(v_es_1689_);
v___x_1694_ = lean_nat_dec_lt(v_j_1692_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_dec(v_j_1692_);
lean_dec(v_x_1688_);
lean_dec(v_x_1687_);
return v_x_1684_;
}
else
{
lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1733_; 
lean_inc_ref(v_es_1689_);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1684_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_x_1684_, 0);
lean_dec(v_unused_1734_);
v___x_1696_ = v_x_1684_;
v_isShared_1697_ = v_isSharedCheck_1733_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v_x_1684_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1733_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_v_1698_; lean_object* v___x_1699_; lean_object* v_xs_x27_1700_; lean_object* v___y_1702_; 
v_v_1698_ = lean_array_fget(v_es_1689_, v_j_1692_);
v___x_1699_ = lean_box(0);
v_xs_x27_1700_ = lean_array_fset(v_es_1689_, v_j_1692_, v___x_1699_);
switch(lean_obj_tag(v_v_1698_))
{
case 0:
{
lean_object* v_key_1707_; lean_object* v_val_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1718_; 
v_key_1707_ = lean_ctor_get(v_v_1698_, 0);
v_val_1708_ = lean_ctor_get(v_v_1698_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_v_1698_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1710_ = v_v_1698_;
v_isShared_1711_ = v_isSharedCheck_1718_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_val_1708_);
lean_inc(v_key_1707_);
lean_dec(v_v_1698_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1718_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_name_eq(v_x_1687_, v_key_1707_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_del_object(v___x_1710_);
v___x_1713_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1707_, v_val_1708_, v_x_1687_, v_x_1688_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
v___y_1702_ = v___x_1714_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1716_; 
lean_dec(v_val_1708_);
lean_dec(v_key_1707_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 1, v_x_1688_);
lean_ctor_set(v___x_1710_, 0, v_x_1687_);
v___x_1716_ = v___x_1710_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_x_1687_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_x_1688_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
v___y_1702_ = v___x_1716_;
goto v___jp_1701_;
}
}
}
}
case 1:
{
lean_object* v_node_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1731_; 
v_node_1719_ = lean_ctor_get(v_v_1698_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_v_1698_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1721_ = v_v_1698_;
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_node_1719_);
lean_dec(v_v_1698_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
size_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1723_ = ((size_t)5ULL);
v___x_1724_ = lean_usize_shift_right(v_x_1685_, v___x_1723_);
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_x_1686_, v___x_1725_);
v___x_1727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_node_1719_, v___x_1724_, v___x_1726_, v_x_1687_, v_x_1688_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1727_);
v___x_1729_ = v___x_1721_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v___y_1702_ = v___x_1729_;
goto v___jp_1701_;
}
}
}
default: 
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_x_1687_);
lean_ctor_set(v___x_1732_, 1, v_x_1688_);
v___y_1702_ = v___x_1732_;
goto v___jp_1701_;
}
}
v___jp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = lean_array_fset(v_xs_x27_1700_, v_j_1692_, v___y_1702_);
lean_dec(v_j_1692_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1703_);
v___x_1705_ = v___x_1696_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
else
{
lean_object* v_ks_1735_; lean_object* v_vs_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1754_; 
v_ks_1735_ = lean_ctor_get(v_x_1684_, 0);
v_vs_1736_ = lean_ctor_get(v_x_1684_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_x_1684_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1738_ = v_x_1684_;
v_isShared_1739_ = v_isSharedCheck_1754_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_vs_1736_);
lean_inc(v_ks_1735_);
lean_dec(v_x_1684_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1754_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_ks_1735_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_vs_1736_);
v___x_1741_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v_newNode_1742_; size_t v___x_1743_; uint8_t v___x_1744_; 
v_newNode_1742_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v___x_1741_, v_x_1687_, v_x_1688_);
v___x_1743_ = ((size_t)7ULL);
v___x_1744_ = lean_usize_dec_le(v___x_1743_, v_x_1686_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1742_);
v___x_1746_ = lean_unsigned_to_nat(4u);
v___x_1747_ = lean_nat_dec_lt(v___x_1745_, v___x_1746_);
lean_dec(v___x_1745_);
if (v___x_1747_ == 0)
{
lean_object* v_ks_1748_; lean_object* v_vs_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_ks_1748_ = lean_ctor_get(v_newNode_1742_, 0);
lean_inc_ref(v_ks_1748_);
v_vs_1749_ = lean_ctor_get(v_newNode_1742_, 1);
lean_inc_ref(v_vs_1749_);
lean_dec_ref(v_newNode_1742_);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0);
v___x_1752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_x_1686_, v_ks_1748_, v_vs_1749_, v___x_1750_, v___x_1751_);
lean_dec_ref(v_vs_1749_);
lean_dec_ref(v_ks_1748_);
return v___x_1752_;
}
else
{
return v_newNode_1742_;
}
}
else
{
return v_newNode_1742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t v_depth_1755_, lean_object* v_keys_1756_, lean_object* v_vals_1757_, lean_object* v_i_1758_, lean_object* v_entries_1759_){
_start:
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_array_get_size(v_keys_1756_);
v___x_1761_ = lean_nat_dec_lt(v_i_1758_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec(v_i_1758_);
return v_entries_1759_;
}
else
{
lean_object* v_k_1762_; lean_object* v_v_1763_; uint64_t v___y_1765_; 
v_k_1762_ = lean_array_fget_borrowed(v_keys_1756_, v_i_1758_);
v_v_1763_ = lean_array_fget_borrowed(v_vals_1757_, v_i_1758_);
if (lean_obj_tag(v_k_1762_) == 0)
{
uint64_t v___x_1776_; 
v___x_1776_ = 1723ULL;
v___y_1765_ = v___x_1776_;
goto v___jp_1764_;
}
else
{
uint64_t v_hash_1777_; 
v_hash_1777_ = lean_ctor_get_uint64(v_k_1762_, sizeof(void*)*2);
v___y_1765_ = v_hash_1777_;
goto v___jp_1764_;
}
v___jp_1764_:
{
size_t v_h_1766_; size_t v___x_1767_; lean_object* v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; size_t v_h_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_h_1766_ = lean_uint64_to_usize(v___y_1765_);
v___x_1767_ = ((size_t)5ULL);
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_sub(v_depth_1755_, v___x_1769_);
v___x_1771_ = lean_usize_mul(v___x_1767_, v___x_1770_);
v_h_1772_ = lean_usize_shift_right(v_h_1766_, v___x_1771_);
v___x_1773_ = lean_nat_add(v_i_1758_, v___x_1768_);
lean_dec(v_i_1758_);
lean_inc(v_v_1763_);
lean_inc(v_k_1762_);
v___x_1774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_entries_1759_, v_h_1772_, v_depth_1755_, v_k_1762_, v_v_1763_);
v_i_1758_ = v___x_1773_;
v_entries_1759_ = v___x_1774_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_1778_, lean_object* v_keys_1779_, lean_object* v_vals_1780_, lean_object* v_i_1781_, lean_object* v_entries_1782_){
_start:
{
size_t v_depth_boxed_1783_; lean_object* v_res_1784_; 
v_depth_boxed_1783_ = lean_unbox_usize(v_depth_1778_);
lean_dec(v_depth_1778_);
v_res_1784_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_boxed_1783_, v_keys_1779_, v_vals_1780_, v_i_1781_, v_entries_1782_);
lean_dec_ref(v_vals_1780_);
lean_dec_ref(v_keys_1779_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_x_1785_, lean_object* v_x_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_){
_start:
{
size_t v_x_1539__boxed_1790_; size_t v_x_1540__boxed_1791_; lean_object* v_res_1792_; 
v_x_1539__boxed_1790_ = lean_unbox_usize(v_x_1786_);
lean_dec(v_x_1786_);
v_x_1540__boxed_1791_ = lean_unbox_usize(v_x_1787_);
lean_dec(v_x_1787_);
v_res_1792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1785_, v_x_1539__boxed_1790_, v_x_1540__boxed_1791_, v_x_1788_, v_x_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_){
_start:
{
uint64_t v___y_1797_; 
if (lean_obj_tag(v_x_1794_) == 0)
{
uint64_t v___x_1801_; 
v___x_1801_ = 1723ULL;
v___y_1797_ = v___x_1801_;
goto v___jp_1796_;
}
else
{
uint64_t v_hash_1802_; 
v_hash_1802_ = lean_ctor_get_uint64(v_x_1794_, sizeof(void*)*2);
v___y_1797_ = v_hash_1802_;
goto v___jp_1796_;
}
v___jp_1796_:
{
size_t v___x_1798_; size_t v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_uint64_to_usize(v___y_1797_);
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1793_, v___x_1798_, v___x_1799_, v_x_1794_, v_x_1795_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1803_, lean_object* v_x_1804_){
_start:
{
lean_object* v_fst_1805_; lean_object* v_snd_1806_; lean_object* v___x_1807_; 
v_fst_1805_ = lean_ctor_get(v_x_1804_, 0);
lean_inc(v_fst_1805_);
v_snd_1806_ = lean_ctor_get(v_x_1804_, 1);
lean_inc(v_snd_1806_);
lean_dec_ref(v_x_1804_);
v___x_1807_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1803_, v_fst_1805_, v_snd_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1842_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1844_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_res_1852_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1849_, v_x_1850_, v_x_1851_);
lean_dec(v_x_1851_);
lean_dec_ref(v_x_1850_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1854_, lean_object* v_m_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1857_, lean_object* v_m_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1857_, v_m_1858_);
lean_dec_ref(v_m_1858_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1860_, lean_object* v_as_1861_, lean_object* v_lo_1862_, lean_object* v_hi_1863_, lean_object* v_w_1864_, lean_object* v_hlo_1865_, lean_object* v_hhi_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1860_, v_as_1861_, v_lo_1862_, v_hi_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1868_, lean_object* v_as_1869_, lean_object* v_lo_1870_, lean_object* v_hi_1871_, lean_object* v_w_1872_, lean_object* v_hlo_1873_, lean_object* v_hhi_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1868_, v_as_1869_, v_lo_1870_, v_hi_1871_, v_w_1872_, v_hlo_1873_, v_hhi_1874_);
lean_dec(v_hi_1871_);
lean_dec(v_n_1868_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1877_, v_x_1878_, v_x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1881_, lean_object* v_x_1882_, size_t v_x_1883_, lean_object* v_x_1884_){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1882_, v_x_1883_, v_x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
size_t v_x_1842__boxed_1890_; uint8_t v_res_1891_; lean_object* v_r_1892_; 
v_x_1842__boxed_1890_ = lean_unbox_usize(v_x_1888_);
lean_dec(v_x_1888_);
v_res_1891_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1886_, v_x_1887_, v_x_1842__boxed_1890_, v_x_1889_);
lean_dec(v_x_1889_);
lean_dec_ref(v_x_1887_);
v_r_1892_ = lean_box(v_res_1891_);
return v_r_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1893_, lean_object* v_00_u03b2_1894_, lean_object* v_map_1895_, lean_object* v_f_1896_, lean_object* v_init_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1895_, v_f_1896_, v_init_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1899_, lean_object* v_00_u03b2_1900_, lean_object* v_map_1901_, lean_object* v_f_1902_, lean_object* v_init_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1899_, v_00_u03b2_1900_, v_map_1901_, v_f_1902_, v_init_1903_);
lean_dec_ref(v_map_1901_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_n_1905_, lean_object* v_lo_1906_, lean_object* v_hi_1907_, lean_object* v_hhi_1908_, lean_object* v_pivot_1909_, lean_object* v_as_1910_, lean_object* v_i_1911_, lean_object* v_k_1912_, lean_object* v_ilo_1913_, lean_object* v_ik_1914_, lean_object* v_w_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1907_, v_pivot_1909_, v_as_1910_, v_i_1911_, v_k_1912_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_n_1917_, lean_object* v_lo_1918_, lean_object* v_hi_1919_, lean_object* v_hhi_1920_, lean_object* v_pivot_1921_, lean_object* v_as_1922_, lean_object* v_i_1923_, lean_object* v_k_1924_, lean_object* v_ilo_1925_, lean_object* v_ik_1926_, lean_object* v_w_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(v_n_1917_, v_lo_1918_, v_hi_1919_, v_hhi_1920_, v_pivot_1921_, v_as_1922_, v_i_1923_, v_k_1924_, v_ilo_1925_, v_ik_1926_, v_w_1927_);
lean_dec_ref(v_pivot_1921_);
lean_dec(v_hi_1919_);
lean_dec(v_lo_1918_);
lean_dec(v_n_1917_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1929_, lean_object* v_x_1930_, size_t v_x_1931_, size_t v_x_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1930_, v_x_1931_, v_x_1932_, v_x_1933_, v_x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1936_, lean_object* v_x_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_, lean_object* v_x_1941_){
_start:
{
size_t v_x_1857__boxed_1942_; size_t v_x_1858__boxed_1943_; lean_object* v_res_1944_; 
v_x_1857__boxed_1942_ = lean_unbox_usize(v_x_1938_);
lean_dec(v_x_1938_);
v_x_1858__boxed_1943_ = lean_unbox_usize(v_x_1939_);
lean_dec(v_x_1939_);
v_res_1944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1936_, v_x_1937_, v_x_1857__boxed_1942_, v_x_1858__boxed_1943_, v_x_1940_, v_x_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1945_, lean_object* v_keys_1946_, lean_object* v_vals_1947_, lean_object* v_heq_1948_, lean_object* v_i_1949_, lean_object* v_k_1950_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1946_, v_i_1949_, v_k_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1952_, lean_object* v_keys_1953_, lean_object* v_vals_1954_, lean_object* v_heq_1955_, lean_object* v_i_1956_, lean_object* v_k_1957_){
_start:
{
uint8_t v_res_1958_; lean_object* v_r_1959_; 
v_res_1958_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1952_, v_keys_1953_, v_vals_1954_, v_heq_1955_, v_i_1956_, v_k_1957_);
lean_dec(v_k_1957_);
lean_dec_ref(v_vals_1954_);
lean_dec_ref(v_keys_1953_);
v_r_1959_ = lean_box(v_res_1958_);
return v_r_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1960_, lean_object* v_f_1961_, lean_object* v_init_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1961_, v_map_1960_, v_init_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1964_, lean_object* v_f_1965_, lean_object* v_init_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1964_, v_f_1965_, v_init_1966_);
lean_dec_ref(v_map_1964_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1968_, lean_object* v_00_u03b2_1969_, lean_object* v_map_1970_, lean_object* v_f_1971_, lean_object* v_init_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1971_, v_map_1970_, v_init_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_map_1976_, lean_object* v_f_1977_, lean_object* v_init_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1974_, v_00_u03b2_1975_, v_map_1976_, v_f_1977_, v_init_1978_);
lean_dec_ref(v_map_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1980_, lean_object* v_n_1981_, lean_object* v_k_1982_, lean_object* v_v_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_n_1981_, v_k_1982_, v_v_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1985_, size_t v_depth_1986_, lean_object* v_keys_1987_, lean_object* v_vals_1988_, lean_object* v_heq_1989_, lean_object* v_i_1990_, lean_object* v_entries_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_1986_, v_keys_1987_, v_vals_1988_, v_i_1990_, v_entries_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1993_, lean_object* v_depth_1994_, lean_object* v_keys_1995_, lean_object* v_vals_1996_, lean_object* v_heq_1997_, lean_object* v_i_1998_, lean_object* v_entries_1999_){
_start:
{
size_t v_depth_boxed_2000_; lean_object* v_res_2001_; 
v_depth_boxed_2000_ = lean_unbox_usize(v_depth_1994_);
lean_dec(v_depth_1994_);
v_res_2001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(v_00_u03b2_1993_, v_depth_boxed_2000_, v_keys_1995_, v_vals_1996_, v_heq_1997_, v_i_1998_, v_entries_1999_);
lean_dec_ref(v_vals_1996_);
lean_dec_ref(v_keys_1995_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2002_, lean_object* v_00_u03b1_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_f_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_2005_, v_x_2006_, v_x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2009_, lean_object* v_00_u03b1_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_f_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_2009_, v_00_u03b1_2010_, v_00_u03b2_2011_, v_f_2012_, v_x_2013_, v_x_2014_);
lean_dec_ref(v_x_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_x_2017_, v_x_2018_, v_x_2019_, v_x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_00_u03c3_2024_, lean_object* v_f_2025_, lean_object* v_as_2026_, size_t v_i_2027_, size_t v_stop_2028_, lean_object* v_b_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_2025_, v_as_2026_, v_i_2027_, v_stop_2028_, v_b_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2031_, lean_object* v_00_u03b2_2032_, lean_object* v_00_u03c3_2033_, lean_object* v_f_2034_, lean_object* v_as_2035_, lean_object* v_i_2036_, lean_object* v_stop_2037_, lean_object* v_b_2038_){
_start:
{
size_t v_i_boxed_2039_; size_t v_stop_boxed_2040_; lean_object* v_res_2041_; 
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_stop_boxed_2040_ = lean_unbox_usize(v_stop_2037_);
lean_dec(v_stop_2037_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_2031_, v_00_u03b2_2032_, v_00_u03c3_2033_, v_f_2034_, v_as_2035_, v_i_boxed_2039_, v_stop_boxed_2040_, v_b_2038_);
lean_dec_ref(v_as_2035_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03c3_2042_, lean_object* v_00_u03b1_2043_, lean_object* v_00_u03b2_2044_, lean_object* v_f_2045_, lean_object* v_keys_2046_, lean_object* v_vals_2047_, lean_object* v_heq_2048_, lean_object* v_i_2049_, lean_object* v_acc_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_2045_, v_keys_2046_, v_vals_2047_, v_i_2049_, v_acc_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03c3_2052_, lean_object* v_00_u03b1_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_f_2055_, lean_object* v_keys_2056_, lean_object* v_vals_2057_, lean_object* v_heq_2058_, lean_object* v_i_2059_, lean_object* v_acc_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(v_00_u03c3_2052_, v_00_u03b1_2053_, v_00_u03b2_2054_, v_f_2055_, v_keys_2056_, v_vals_2057_, v_heq_2058_, v_i_2059_, v_acc_2060_);
lean_dec_ref(v_vals_2057_);
lean_dec_ref(v_keys_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary___lam__0(lean_object* v___x_2062_, lean_object* v___x_2063_, lean_object* v_s_2064_){
_start:
{
lean_object* v_addEntryFn_2065_; lean_object* v_importedEntries_2066_; lean_object* v_state_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_addEntryFn_2065_ = lean_ctor_get(v___x_2062_, 3);
lean_inc(v_addEntryFn_2065_);
lean_dec_ref(v___x_2062_);
v_importedEntries_2066_ = lean_ctor_get(v_s_2064_, 0);
v_state_2067_ = lean_ctor_get(v_s_2064_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_s_2064_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v_s_2064_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_state_2067_);
lean_inc(v_importedEntries_2066_);
lean_dec(v_s_2064_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_state_2071_; lean_object* v___x_2073_; 
v_state_2071_ = lean_apply_2(v_addEntryFn_2065_, v_state_2067_, v___x_2063_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 1, v_state_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_importedEntries_2066_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_state_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2076_, lean_object* v_fid_2077_, lean_object* v_v_2078_){
_start:
{
lean_object* v___x_2079_; lean_object* v_toEnvExtension_2080_; lean_object* v_asyncMode_2081_; uint8_t v_logWrites_2082_; lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2079_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2080_ = lean_ctor_get(v___x_2079_, 0);
v_asyncMode_2081_ = lean_ctor_get(v_toEnvExtension_2080_, 2);
v_logWrites_2082_ = lean_ctor_get_uint8(v_toEnvExtension_2080_, sizeof(void*)*6);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v_fid_2077_);
lean_ctor_set(v___x_2083_, 1, v_v_2078_);
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary___lam__0), 3, 2);
lean_closure_set(v___f_2084_, 0, v___x_2079_);
lean_closure_set(v___f_2084_, 1, v___x_2083_);
v___x_2085_ = lean_box(0);
v___x_2086_ = 1;
if (v_logWrites_2082_ == 0)
{
lean_object* v___x_2087_; 
lean_inc_ref(v_toEnvExtension_2080_);
v___x_2087_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2080_, v_env_2076_, v___f_2084_, v_asyncMode_2081_, v___x_2085_, v___x_2086_);
return v___x_2087_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_inc_ref_n(v_toEnvExtension_2080_, 2);
v___x_2088_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2080_, v_env_2076_);
lean_dec_ref(v_env_2076_);
v___x_2089_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2080_, v___x_2088_, v___f_2084_, v_asyncMode_2081_, v___x_2085_, v___x_2086_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2090_, lean_object* v_vals_2091_, lean_object* v_i_2092_, lean_object* v_k_2093_){
_start:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = lean_array_get_size(v_keys_2090_);
v___x_2095_ = lean_nat_dec_lt(v_i_2092_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
lean_dec(v_i_2092_);
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
else
{
lean_object* v_k_x27_2097_; uint8_t v___x_2098_; 
v_k_x27_2097_ = lean_array_fget_borrowed(v_keys_2090_, v_i_2092_);
v___x_2098_ = lean_name_eq(v_k_2093_, v_k_x27_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_add(v_i_2092_, v___x_2099_);
lean_dec(v_i_2092_);
v_i_2092_ = v___x_2100_;
goto _start;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_array_fget_borrowed(v_vals_2091_, v_i_2092_);
lean_dec(v_i_2092_);
lean_inc(v___x_2102_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2104_, lean_object* v_vals_2105_, lean_object* v_i_2106_, lean_object* v_k_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2104_, v_vals_2105_, v_i_2106_, v_k_2107_);
lean_dec(v_k_2107_);
lean_dec_ref(v_vals_2105_);
lean_dec_ref(v_keys_2104_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2109_, size_t v_x_2110_, lean_object* v_x_2111_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v_es_2112_; lean_object* v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; lean_object* v_j_2116_; lean_object* v___x_2117_; 
v_es_2112_ = lean_ctor_get(v_x_2109_, 0);
v___x_2113_ = lean_box(2);
v___x_2114_ = ((size_t)31ULL);
v___x_2115_ = lean_usize_land(v_x_2110_, v___x_2114_);
v_j_2116_ = lean_usize_to_nat(v___x_2115_);
v___x_2117_ = lean_array_get_borrowed(v___x_2113_, v_es_2112_, v_j_2116_);
lean_dec(v_j_2116_);
switch(lean_obj_tag(v___x_2117_))
{
case 0:
{
lean_object* v_key_2118_; lean_object* v_val_2119_; uint8_t v___x_2120_; 
v_key_2118_ = lean_ctor_get(v___x_2117_, 0);
v_val_2119_ = lean_ctor_get(v___x_2117_, 1);
v___x_2120_ = lean_name_eq(v_x_2111_, v_key_2118_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_box(0);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; 
lean_inc(v_val_2119_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v_val_2119_);
return v___x_2122_;
}
}
case 1:
{
lean_object* v_node_2123_; size_t v___x_2124_; size_t v___x_2125_; 
v_node_2123_ = lean_ctor_get(v___x_2117_, 0);
v___x_2124_ = ((size_t)5ULL);
v___x_2125_ = lean_usize_shift_right(v_x_2110_, v___x_2124_);
v_x_2109_ = v_node_2123_;
v_x_2110_ = v___x_2125_;
goto _start;
}
default: 
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_box(0);
return v___x_2127_;
}
}
}
else
{
lean_object* v_ks_2128_; lean_object* v_vs_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_ks_2128_ = lean_ctor_get(v_x_2109_, 0);
v_vs_2129_ = lean_ctor_get(v_x_2109_, 1);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2128_, v_vs_2129_, v___x_2130_, v_x_2111_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
size_t v_x_402__boxed_2135_; lean_object* v_res_2136_; 
v_x_402__boxed_2135_ = lean_unbox_usize(v_x_2133_);
lean_dec(v_x_2133_);
v_res_2136_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2132_, v_x_402__boxed_2135_, v_x_2134_);
lean_dec(v_x_2134_);
lean_dec_ref(v_x_2132_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2137_, lean_object* v_x_2138_){
_start:
{
uint64_t v___y_2140_; 
if (lean_obj_tag(v_x_2138_) == 0)
{
uint64_t v___x_2143_; 
v___x_2143_ = 1723ULL;
v___y_2140_ = v___x_2143_;
goto v___jp_2139_;
}
else
{
uint64_t v_hash_2144_; 
v_hash_2144_ = lean_ctor_get_uint64(v_x_2138_, sizeof(void*)*2);
v___y_2140_ = v_hash_2144_;
goto v___jp_2139_;
}
v___jp_2139_:
{
size_t v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_uint64_to_usize(v___y_2140_);
v___x_2142_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2137_, v___x_2141_, v_x_2138_);
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2145_, v_x_2146_);
lean_dec(v_x_2146_);
lean_dec_ref(v_x_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2148_, lean_object* v_k_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_m_2154_; lean_object* v_a_2155_; uint8_t v___x_2156_; 
v___x_2152_ = lean_nat_add(v_x_2150_, v_x_2151_);
v___x_2153_ = lean_unsigned_to_nat(1u);
v_m_2154_ = lean_nat_shiftr(v___x_2152_, v___x_2153_);
lean_dec(v___x_2152_);
v_a_2155_ = lean_array_fget_borrowed(v_as_2148_, v_m_2154_);
v___x_2156_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2155_, v_k_2149_);
if (v___x_2156_ == 0)
{
uint8_t v___x_2157_; 
lean_dec(v_x_2151_);
v___x_2157_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2149_, v_a_2155_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec(v_m_2154_);
lean_dec(v_x_2150_);
lean_inc(v_a_2155_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_a_2155_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = lean_nat_dec_eq(v_m_2154_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_nat_sub(v_m_2154_, v___x_2153_);
lean_dec(v_m_2154_);
v___x_2162_ = lean_nat_dec_lt(v___x_2161_, v_x_2150_);
if (v___x_2162_ == 0)
{
v_x_2151_ = v___x_2161_;
goto _start;
}
else
{
lean_object* v___x_2164_; 
lean_dec(v___x_2161_);
lean_dec(v_x_2150_);
v___x_2164_ = lean_box(0);
return v___x_2164_;
}
}
else
{
lean_object* v___x_2165_; 
lean_dec(v_m_2154_);
lean_dec(v_x_2150_);
v___x_2165_ = lean_box(0);
return v___x_2165_;
}
}
}
else
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
lean_dec(v_x_2150_);
v___x_2166_ = lean_nat_add(v_m_2154_, v___x_2153_);
lean_dec(v_m_2154_);
v___x_2167_ = lean_nat_dec_le(v___x_2166_, v_x_2151_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_dec(v___x_2166_);
lean_dec(v_x_2151_);
v___x_2168_ = lean_box(0);
return v___x_2168_;
}
else
{
v_x_2150_ = v___x_2166_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2170_, lean_object* v_k_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2170_, v_k_2171_, v_x_2172_, v_x_2173_);
lean_dec_ref(v_k_2171_);
lean_dec_ref(v_as_2170_);
return v_res_2174_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0(void){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0);
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2179_, lean_object* v_fid_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2191_; 
v___x_2181_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1);
v___x_2182_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2191_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2179_, v_fid_2180_);
if (lean_obj_tag(v___x_2191_) == 0)
{
goto v___jp_2183_;
}
else
{
lean_object* v_val_2192_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2214_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_2181_, v___x_2182_, v_env_2179_, v_val_2192_);
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
lean_inc(v_fid_2180_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_fid_2180_);
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
lean_dec(v_fid_2180_);
lean_dec_ref(v_env_2179_);
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
v___x_2195_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2181_, v___x_2182_, v_env_2179_, v_val_2192_, v___x_2194_);
lean_dec(v_val_2192_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_array_get_size(v___x_2195_);
v___x_2198_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_dec_ref(v___x_2195_);
goto v___jp_2183_;
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
goto v___jp_2183_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_box(0);
lean_inc(v_fid_2180_);
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_fid_2180_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2195_, v___x_2203_, v___x_2196_, v___x_2200_);
lean_dec_ref_known(v___x_2203_, 2);
lean_dec_ref(v___x_2195_);
if (lean_obj_tag(v___x_2204_) == 0)
{
goto v___jp_2183_;
}
else
{
lean_object* v_val_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_fid_2180_);
lean_dec_ref(v_env_2179_);
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
v___jp_2183_:
{
lean_object* v_toEnvExtension_2184_; lean_object* v_asyncMode_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v_snd_2189_; lean_object* v___x_2190_; 
v_toEnvExtension_2184_ = lean_ctor_get(v___x_2182_, 0);
v_asyncMode_2185_ = lean_ctor_get(v_toEnvExtension_2184_, 2);
v___x_2186_ = lean_box(0);
v___x_2187_ = 0;
v___x_2188_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2181_, v___x_2182_, v_env_2179_, v_asyncMode_2185_, v___x_2186_, v___x_2187_);
v_snd_2189_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_snd_2189_);
lean_dec(v___x_2188_);
v___x_2190_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2189_, v_fid_2180_);
lean_dec(v_fid_2180_);
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
size_t v_x_628__boxed_2262_; lean_object* v_res_2263_; 
v_x_628__boxed_2262_ = lean_unbox_usize(v_x_2260_);
lean_dec(v_x_2260_);
v_res_2263_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2258_, v_x_2259_, v_x_628__boxed_2262_, v_x_2261_);
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
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0(void){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_assignments_2284_; lean_object* v_currFnIdx_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2282_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0);
v___x_2283_ = lean_st_ref_get(v_a_2280_);
v_assignments_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_ref(v_assignments_2284_);
lean_dec(v___x_2283_);
v_currFnIdx_2285_ = lean_ctor_get(v_a_2279_, 1);
v___x_2286_ = lean_array_get(v___x_2282_, v_assignments_2284_, v_currFnIdx_2285_);
lean_dec_ref(v_assignments_2284_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2292_, v_a_2293_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_funVals_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_st_ref_get(v_a_2309_);
v_funVals_2313_ = lean_ctor_get(v___x_2312_, 1);
lean_inc_ref(v_funVals_2313_);
lean_dec(v___x_2312_);
v___x_2314_ = lean_array_get(v___x_2311_, v_funVals_2313_, v_funIdx_2308_);
lean_dec_ref(v_funVals_2313_);
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec(v_funIdx_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2320_, v_a_2322_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_funIdx_2329_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2338_, lean_object* v_as_2339_, lean_object* v_j_2340_){
_start:
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = lean_array_get_size(v_as_2339_);
v___x_2342_ = lean_nat_dec_lt(v_j_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; 
lean_dec(v_j_2340_);
v___x_2343_ = lean_box(0);
return v___x_2343_;
}
else
{
lean_object* v___x_2344_; lean_object* v_toSignature_2345_; lean_object* v_name_2346_; uint8_t v___x_2347_; 
v___x_2344_ = lean_array_fget_borrowed(v_as_2339_, v_j_2340_);
v_toSignature_2345_ = lean_ctor_get(v___x_2344_, 0);
v_name_2346_ = lean_ctor_get(v_toSignature_2345_, 0);
v___x_2347_ = lean_name_eq(v_name_2346_, v_declName_2338_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_nat_add(v_j_2340_, v___x_2348_);
lean_dec(v_j_2340_);
v_j_2340_ = v___x_2349_;
goto _start;
}
else
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_j_2340_);
return v___x_2351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2352_, lean_object* v_as_2353_, lean_object* v_j_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2352_, v_as_2353_, v_j_2354_);
lean_dec_ref(v_as_2353_);
lean_dec(v_declName_2352_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v_decls_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_decls_2360_ = lean_ctor_get(v_a_2357_, 0);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2356_, v_decls_2360_, v___x_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v_val_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2381_; 
v_val_2365_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2367_ = v___x_2362_;
v_isShared_2368_ = v_isSharedCheck_2381_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_val_2365_);
lean_dec(v___x_2362_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2381_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2380_; 
v___x_2369_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2365_, v_a_2358_);
lean_dec(v_val_2365_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2380_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2380_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v_a_2370_);
v___x_2375_ = v___x_2367_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2375_);
v___x_2377_ = v___x_2372_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_declName_2382_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2387_, v_a_2388_, v_a_2389_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_declName_2396_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_currFnIdx_2409_; lean_object* v___x_2410_; lean_object* v_assignments_2411_; lean_object* v_funVals_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2430_; 
v_currFnIdx_2409_ = lean_ctor_get(v_a_2406_, 1);
v___x_2410_ = lean_st_ref_take(v_a_2407_);
v_assignments_2411_ = lean_ctor_get(v___x_2410_, 0);
v_funVals_2412_ = lean_ctor_get(v___x_2410_, 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2414_ = v___x_2410_;
v_isShared_2415_ = v_isSharedCheck_2430_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_funVals_2412_);
lean_inc(v_assignments_2411_);
lean_dec(v___x_2410_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2430_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___y_2418_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2416_ = lean_box(0);
v___x_2424_ = lean_array_get_size(v_assignments_2411_);
v___x_2425_ = lean_nat_dec_lt(v_currFnIdx_2409_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_dec_ref(v_f_2405_);
v___y_2418_ = v_assignments_2411_;
goto v___jp_2417_;
}
else
{
lean_object* v_v_2426_; lean_object* v_xs_x27_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_v_2426_ = lean_array_fget(v_assignments_2411_, v_currFnIdx_2409_);
v_xs_x27_2427_ = lean_array_fset(v_assignments_2411_, v_currFnIdx_2409_, v___x_2416_);
v___x_2428_ = lean_apply_1(v_f_2405_, v_v_2426_);
v___x_2429_ = lean_array_fset(v_xs_x27_2427_, v_currFnIdx_2409_, v___x_2428_);
v___y_2418_ = v___x_2429_;
goto v___jp_2417_;
}
v___jp_2417_:
{
lean_object* v___x_2420_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___y_2418_);
v___x_2420_ = v___x_2414_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___y_2418_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_funVals_2412_);
v___x_2420_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_st_ref_put(v_a_2407_, v___x_2420_);
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2416_);
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2436_, v_a_2437_, v_a_2438_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2454_, lean_object* v_fallback_2455_, lean_object* v_x_2456_){
_start:
{
if (lean_obj_tag(v_x_2456_) == 0)
{
lean_inc(v_fallback_2455_);
return v_fallback_2455_;
}
else
{
lean_object* v_key_2457_; lean_object* v_value_2458_; lean_object* v_tail_2459_; uint8_t v___x_2460_; 
v_key_2457_ = lean_ctor_get(v_x_2456_, 0);
v_value_2458_ = lean_ctor_get(v_x_2456_, 1);
v_tail_2459_ = lean_ctor_get(v_x_2456_, 2);
v___x_2460_ = l_Lean_instBEqFVarId_beq(v_key_2457_, v_a_2454_);
if (v___x_2460_ == 0)
{
v_x_2456_ = v_tail_2459_;
goto _start;
}
else
{
lean_inc(v_value_2458_);
return v_value_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2462_, lean_object* v_fallback_2463_, lean_object* v_x_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2462_, v_fallback_2463_, v_x_2464_);
lean_dec(v_x_2464_);
lean_dec(v_fallback_2463_);
lean_dec(v_a_2462_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2466_, lean_object* v_a_2467_, lean_object* v_fallback_2468_){
_start:
{
lean_object* v_buckets_2469_; lean_object* v___x_2470_; uint64_t v___x_2471_; uint64_t v___x_2472_; uint64_t v___x_2473_; uint64_t v_fold_2474_; uint64_t v___x_2475_; uint64_t v___x_2476_; uint64_t v___x_2477_; size_t v___x_2478_; size_t v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_buckets_2469_ = lean_ctor_get(v_m_2466_, 1);
v___x_2470_ = lean_array_get_size(v_buckets_2469_);
v___x_2471_ = l_Lean_instHashableFVarId_hash(v_a_2467_);
v___x_2472_ = 32ULL;
v___x_2473_ = lean_uint64_shift_right(v___x_2471_, v___x_2472_);
v_fold_2474_ = lean_uint64_xor(v___x_2471_, v___x_2473_);
v___x_2475_ = 16ULL;
v___x_2476_ = lean_uint64_shift_right(v_fold_2474_, v___x_2475_);
v___x_2477_ = lean_uint64_xor(v_fold_2474_, v___x_2476_);
v___x_2478_ = lean_uint64_to_usize(v___x_2477_);
v___x_2479_ = lean_usize_of_nat(v___x_2470_);
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_sub(v___x_2479_, v___x_2480_);
v___x_2482_ = lean_usize_land(v___x_2478_, v___x_2481_);
v___x_2483_ = lean_array_uget_borrowed(v_buckets_2469_, v___x_2482_);
v___x_2484_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2467_, v_fallback_2468_, v___x_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2485_, lean_object* v_a_2486_, lean_object* v_fallback_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2485_, v_a_2486_, v_fallback_2487_);
lean_dec(v_fallback_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_m_2485_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2503_; 
v___x_2493_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2490_, v_a_2491_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2498_ = lean_box(0);
v___x_2499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2494_, v_var_2489_, v___x_2498_);
lean_dec(v_a_2494_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2499_);
v___x_2501_ = v___x_2496_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_var_2504_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2509_, v_a_2510_, v_a_2511_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_var_2518_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2527_, lean_object* v_m_2528_, lean_object* v_a_2529_, lean_object* v_fallback_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2528_, v_a_2529_, v_fallback_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2532_, lean_object* v_m_2533_, lean_object* v_a_2534_, lean_object* v_fallback_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2532_, v_m_2533_, v_a_2534_, v_fallback_2535_);
lean_dec(v_fallback_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_m_2533_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2537_, lean_object* v_a_2538_, lean_object* v_fallback_2539_, lean_object* v_x_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2538_, v_fallback_2539_, v_x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2542_, lean_object* v_a_2543_, lean_object* v_fallback_2544_, lean_object* v_x_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2542_, v_a_2543_, v_fallback_2544_, v_x_2545_);
lean_dec(v_x_2545_);
lean_dec(v_fallback_2544_);
lean_dec(v_a_2543_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
if (lean_obj_tag(v_arg_2547_) == 1)
{
lean_object* v_fvarId_2551_; lean_object* v___x_2552_; 
v_fvarId_2551_ = lean_ctor_get(v_arg_2547_, 0);
v___x_2552_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2551_, v_a_2548_, v_a_2549_);
return v___x_2552_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_box(1);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_arg_2555_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2560_, v_a_2561_, v_a_2562_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_arg_2569_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2578_, lean_object* v_b_2579_, lean_object* v_x_2580_){
_start:
{
if (lean_obj_tag(v_x_2580_) == 0)
{
lean_dec(v_b_2579_);
lean_dec(v_a_2578_);
return v_x_2580_;
}
else
{
lean_object* v_key_2581_; lean_object* v_value_2582_; lean_object* v_tail_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2595_; 
v_key_2581_ = lean_ctor_get(v_x_2580_, 0);
v_value_2582_ = lean_ctor_get(v_x_2580_, 1);
v_tail_2583_ = lean_ctor_get(v_x_2580_, 2);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_x_2580_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2585_ = v_x_2580_;
v_isShared_2586_ = v_isSharedCheck_2595_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_tail_2583_);
lean_inc(v_value_2582_);
lean_inc(v_key_2581_);
lean_dec(v_x_2580_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2595_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
uint8_t v___x_2587_; 
v___x_2587_ = l_Lean_instBEqFVarId_beq(v_key_2581_, v_a_2578_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2578_, v_b_2579_, v_tail_2583_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 2, v___x_2588_);
v___x_2590_ = v___x_2585_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_key_2581_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_value_2582_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
else
{
lean_object* v___x_2593_; 
lean_dec(v_value_2582_);
lean_dec(v_key_2581_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v_b_2579_);
lean_ctor_set(v___x_2585_, 0, v_a_2578_);
v___x_2593_ = v___x_2585_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2578_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_b_2579_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_tail_2583_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2596_, lean_object* v_x_2597_){
_start:
{
if (lean_obj_tag(v_x_2597_) == 0)
{
return v_x_2596_;
}
else
{
lean_object* v_key_2598_; lean_object* v_value_2599_; lean_object* v_tail_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2623_; 
v_key_2598_ = lean_ctor_get(v_x_2597_, 0);
v_value_2599_ = lean_ctor_get(v_x_2597_, 1);
v_tail_2600_ = lean_ctor_get(v_x_2597_, 2);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_x_2597_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2602_ = v_x_2597_;
v_isShared_2603_ = v_isSharedCheck_2623_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_tail_2600_);
lean_inc(v_value_2599_);
lean_inc(v_key_2598_);
lean_dec(v_x_2597_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2623_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; uint64_t v___x_2605_; uint64_t v___x_2606_; uint64_t v___x_2607_; uint64_t v_fold_2608_; uint64_t v___x_2609_; uint64_t v___x_2610_; uint64_t v___x_2611_; size_t v___x_2612_; size_t v___x_2613_; size_t v___x_2614_; size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2604_ = lean_array_get_size(v_x_2596_);
v___x_2605_ = l_Lean_instHashableFVarId_hash(v_key_2598_);
v___x_2606_ = 32ULL;
v___x_2607_ = lean_uint64_shift_right(v___x_2605_, v___x_2606_);
v_fold_2608_ = lean_uint64_xor(v___x_2605_, v___x_2607_);
v___x_2609_ = 16ULL;
v___x_2610_ = lean_uint64_shift_right(v_fold_2608_, v___x_2609_);
v___x_2611_ = lean_uint64_xor(v_fold_2608_, v___x_2610_);
v___x_2612_ = lean_uint64_to_usize(v___x_2611_);
v___x_2613_ = lean_usize_of_nat(v___x_2604_);
v___x_2614_ = ((size_t)1ULL);
v___x_2615_ = lean_usize_sub(v___x_2613_, v___x_2614_);
v___x_2616_ = lean_usize_land(v___x_2612_, v___x_2615_);
v___x_2617_ = lean_array_uget_borrowed(v_x_2596_, v___x_2616_);
lean_inc(v___x_2617_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 2, v___x_2617_);
v___x_2619_ = v___x_2602_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_key_2598_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_value_2599_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_array_uset(v_x_2596_, v___x_2616_, v___x_2619_);
v_x_2596_ = v___x_2620_;
v_x_2597_ = v_tail_2600_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2624_, lean_object* v_source_2625_, lean_object* v_target_2626_){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_array_get_size(v_source_2625_);
v___x_2628_ = lean_nat_dec_lt(v_i_2624_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_dec_ref(v_source_2625_);
lean_dec(v_i_2624_);
return v_target_2626_;
}
else
{
lean_object* v_es_2629_; lean_object* v___x_2630_; lean_object* v_source_2631_; lean_object* v_target_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v_es_2629_ = lean_array_fget(v_source_2625_, v_i_2624_);
v___x_2630_ = lean_box(0);
v_source_2631_ = lean_array_fset(v_source_2625_, v_i_2624_, v___x_2630_);
v_target_2632_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2626_, v_es_2629_);
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_nat_add(v_i_2624_, v___x_2633_);
lean_dec(v_i_2624_);
v_i_2624_ = v___x_2634_;
v_source_2625_ = v_source_2631_;
v_target_2626_ = v_target_2632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2636_){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v_nbuckets_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2637_ = lean_array_get_size(v_data_2636_);
v___x_2638_ = lean_unsigned_to_nat(2u);
v_nbuckets_2639_ = lean_nat_mul(v___x_2637_, v___x_2638_);
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = lean_box(0);
v___x_2642_ = lean_mk_array(v_nbuckets_2639_, v___x_2641_);
v___x_2643_ = lean_array_propagate_mark(v_data_2636_, v___x_2642_);
v___x_2644_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2640_, v_data_2636_, v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2645_, lean_object* v_x_2646_){
_start:
{
if (lean_obj_tag(v_x_2646_) == 0)
{
uint8_t v___x_2647_; 
v___x_2647_ = 0;
return v___x_2647_;
}
else
{
lean_object* v_key_2648_; lean_object* v_tail_2649_; uint8_t v___x_2650_; 
v_key_2648_ = lean_ctor_get(v_x_2646_, 0);
v_tail_2649_ = lean_ctor_get(v_x_2646_, 2);
v___x_2650_ = l_Lean_instBEqFVarId_beq(v_key_2648_, v_a_2645_);
if (v___x_2650_ == 0)
{
v_x_2646_ = v_tail_2649_;
goto _start;
}
else
{
return v___x_2650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2652_, lean_object* v_x_2653_){
_start:
{
uint8_t v_res_2654_; lean_object* v_r_2655_; 
v_res_2654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2652_, v_x_2653_);
lean_dec(v_x_2653_);
lean_dec(v_a_2652_);
v_r_2655_ = lean_box(v_res_2654_);
return v_r_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2656_, lean_object* v_a_2657_, lean_object* v_b_2658_){
_start:
{
lean_object* v_size_2659_; lean_object* v_buckets_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2703_; 
v_size_2659_ = lean_ctor_get(v_m_2656_, 0);
v_buckets_2660_ = lean_ctor_get(v_m_2656_, 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_m_2656_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2662_ = v_m_2656_;
v_isShared_2663_ = v_isSharedCheck_2703_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_buckets_2660_);
lean_inc(v_size_2659_);
lean_dec(v_m_2656_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2703_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; uint64_t v___x_2665_; uint64_t v___x_2666_; uint64_t v___x_2667_; uint64_t v_fold_2668_; uint64_t v___x_2669_; uint64_t v___x_2670_; uint64_t v___x_2671_; size_t v___x_2672_; size_t v___x_2673_; size_t v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; lean_object* v_bkt_2677_; uint8_t v___x_2678_; 
v___x_2664_ = lean_array_get_size(v_buckets_2660_);
v___x_2665_ = l_Lean_instHashableFVarId_hash(v_a_2657_);
v___x_2666_ = 32ULL;
v___x_2667_ = lean_uint64_shift_right(v___x_2665_, v___x_2666_);
v_fold_2668_ = lean_uint64_xor(v___x_2665_, v___x_2667_);
v___x_2669_ = 16ULL;
v___x_2670_ = lean_uint64_shift_right(v_fold_2668_, v___x_2669_);
v___x_2671_ = lean_uint64_xor(v_fold_2668_, v___x_2670_);
v___x_2672_ = lean_uint64_to_usize(v___x_2671_);
v___x_2673_ = lean_usize_of_nat(v___x_2664_);
v___x_2674_ = ((size_t)1ULL);
v___x_2675_ = lean_usize_sub(v___x_2673_, v___x_2674_);
v___x_2676_ = lean_usize_land(v___x_2672_, v___x_2675_);
v_bkt_2677_ = lean_array_uget_borrowed(v_buckets_2660_, v___x_2676_);
v___x_2678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2657_, v_bkt_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v_size_x27_2680_; lean_object* v___x_2681_; lean_object* v_buckets_x27_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2679_ = lean_unsigned_to_nat(1u);
v_size_x27_2680_ = lean_nat_add(v_size_2659_, v___x_2679_);
lean_dec(v_size_2659_);
lean_inc(v_bkt_2677_);
v___x_2681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2681_, 0, v_a_2657_);
lean_ctor_set(v___x_2681_, 1, v_b_2658_);
lean_ctor_set(v___x_2681_, 2, v_bkt_2677_);
v_buckets_x27_2682_ = lean_array_uset(v_buckets_2660_, v___x_2676_, v___x_2681_);
v___x_2683_ = lean_unsigned_to_nat(4u);
v___x_2684_ = lean_nat_mul(v_size_x27_2680_, v___x_2683_);
v___x_2685_ = lean_unsigned_to_nat(3u);
v___x_2686_ = lean_nat_div(v___x_2684_, v___x_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_array_get_size(v_buckets_x27_2682_);
v___x_2688_ = lean_nat_dec_le(v___x_2686_, v___x_2687_);
lean_dec(v___x_2686_);
if (v___x_2688_ == 0)
{
lean_object* v_val_2689_; lean_object* v___x_2691_; 
v_val_2689_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2682_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v_val_2689_);
lean_ctor_set(v___x_2662_, 0, v_size_x27_2680_);
v___x_2691_ = v___x_2662_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_size_x27_2680_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_val_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
else
{
lean_object* v___x_2694_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v_buckets_x27_2682_);
lean_ctor_set(v___x_2662_, 0, v_size_x27_2680_);
v___x_2694_ = v___x_2662_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_size_x27_2680_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_buckets_x27_2682_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v___x_2696_; lean_object* v_buckets_x27_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_inc(v_bkt_2677_);
v___x_2696_ = lean_box(0);
v_buckets_x27_2697_ = lean_array_uset(v_buckets_2660_, v___x_2676_, v___x_2696_);
v___x_2698_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2657_, v_b_2658_, v_bkt_2677_);
v___x_2699_ = lean_array_uset(v_buckets_x27_2697_, v___x_2676_, v___x_2698_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2699_);
v___x_2701_ = v___x_2662_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_size_2659_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2704_, lean_object* v___x_2705_, lean_object* v_x_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2706_, v_var_2704_, v___x_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2708_, lean_object* v_newVal_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v_env_2715_; lean_object* v___x_2716_; 
v___x_2714_ = lean_st_ref_get(v_a_2712_);
v_env_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc_ref(v_env_2715_);
lean_dec(v___x_2714_);
v___x_2716_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2708_, v_a_2710_, v_a_2711_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; lean_object* v___f_2719_; lean_object* v___x_2720_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2715_, v_a_2717_, v_newVal_2709_);
v___f_2719_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2719_, 0, v_var_2708_);
lean_closure_set(v___f_2719_, 1, v___x_2718_);
v___x_2720_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2719_, v_a_2710_, v_a_2711_);
return v___x_2720_;
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v_env_2715_);
lean_dec(v_newVal_2709_);
lean_dec(v_var_2708_);
v_a_2721_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2716_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2716_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2729_, lean_object* v_newVal_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2729_, v_newVal_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
lean_dec(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2736_, lean_object* v_newVal_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2736_, v_newVal_2737_, v_a_2738_, v_a_2739_, v_a_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2746_, lean_object* v_newVal_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2746_, v_newVal_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2756_, lean_object* v_m_2757_, lean_object* v_a_2758_, lean_object* v_b_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2757_, v_a_2758_, v_b_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2761_, lean_object* v_a_2762_, lean_object* v_x_2763_){
_start:
{
uint8_t v___x_2764_; 
v___x_2764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2762_, v_x_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2765_, lean_object* v_a_2766_, lean_object* v_x_2767_){
_start:
{
uint8_t v_res_2768_; lean_object* v_r_2769_; 
v_res_2768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2765_, v_a_2766_, v_x_2767_);
lean_dec(v_x_2767_);
lean_dec(v_a_2766_);
v_r_2769_ = lean_box(v_res_2768_);
return v_r_2769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2770_, lean_object* v_data_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2773_, lean_object* v_a_2774_, lean_object* v_b_2775_, lean_object* v_x_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2774_, v_b_2775_, v_x_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2778_, lean_object* v_i_2779_, lean_object* v_source_2780_, lean_object* v_target_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2779_, v_source_2780_, v_target_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_box(0);
v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2788_, v_var_2787_, v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___f_2795_; lean_object* v___x_2796_; 
v___f_2795_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2795_, 0, v_var_2791_);
v___x_2796_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2795_, v_a_2792_, v_a_2793_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2802_, v_a_2803_, v_a_2804_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v_env_2826_; lean_object* v_currFnIdx_2827_; lean_object* v___x_2828_; lean_object* v_fst_2830_; lean_object* v_snd_2831_; lean_object* v_assignments_2834_; lean_object* v_funVals_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2825_ = lean_st_ref_get(v_a_2823_);
v_env_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_ref(v_env_2826_);
lean_dec(v___x_2825_);
v_currFnIdx_2827_ = lean_ctor_get(v_a_2821_, 1);
v___x_2828_ = lean_st_ref_take(v_a_2822_);
v_assignments_2834_ = lean_ctor_get(v___x_2828_, 0);
v_funVals_2835_ = lean_ctor_get(v___x_2828_, 1);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_array_get_size(v_funVals_2835_);
v___x_2838_ = lean_nat_dec_lt(v_currFnIdx_2827_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_dec_ref(v_env_2826_);
lean_dec(v_v_2820_);
v_fst_2830_ = v___x_2836_;
v_snd_2831_ = v___x_2828_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2849_; 
lean_inc_ref(v_funVals_2835_);
lean_inc_ref(v_assignments_2834_);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; lean_object* v_unused_2851_; 
v_unused_2850_ = lean_ctor_get(v___x_2828_, 1);
lean_dec(v_unused_2850_);
v_unused_2851_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2851_);
v___x_2840_ = v___x_2828_;
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2828_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_v_2842_; lean_object* v_xs_x27_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
v_v_2842_ = lean_array_fget(v_funVals_2835_, v_currFnIdx_2827_);
v_xs_x27_2843_ = lean_array_fset(v_funVals_2835_, v_currFnIdx_2827_, v___x_2836_);
v___x_2844_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2826_, v_v_2820_, v_v_2842_);
v___x_2845_ = lean_array_fset(v_xs_x27_2843_, v_currFnIdx_2827_, v___x_2844_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v___x_2845_);
v___x_2847_ = v___x_2840_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_assignments_2834_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
v_fst_2830_ = v___x_2836_;
v_snd_2831_ = v___x_2847_;
goto v___jp_2829_;
}
}
}
v___jp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_st_ref_put(v_a_2822_, v_snd_2831_);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_fst_2830_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2858_, v_a_2859_, v_a_2860_, v_a_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2876_, uint8_t v_b_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_array_2882_; lean_object* v_start_2883_; lean_object* v_stop_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2921_; 
v_array_2882_ = lean_ctor_get(v_a_2876_, 0);
v_start_2883_ = lean_ctor_get(v_a_2876_, 1);
v_stop_2884_ = lean_ctor_get(v_a_2876_, 2);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_a_2876_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2886_ = v_a_2876_;
v_isShared_2887_ = v_isSharedCheck_2921_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_stop_2884_);
lean_inc(v_start_2883_);
lean_inc(v_array_2882_);
lean_dec(v_a_2876_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2921_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
uint8_t v___x_2888_; 
v___x_2888_ = lean_nat_dec_lt(v_start_2883_, v_stop_2884_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_del_object(v___x_2886_);
lean_dec(v_stop_2884_);
lean_dec(v_start_2883_);
lean_dec_ref(v_array_2882_);
v___x_2889_ = lean_box(v_b_2877_);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
else
{
lean_object* v___x_2891_; lean_object* v_fvarId_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2891_ = lean_array_fget_borrowed(v_array_2882_, v_start_2883_);
v_fvarId_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_fvarId_2892_);
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = lean_nat_add(v_start_2883_, v___x_2893_);
lean_dec(v_start_2883_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 1, v___x_2894_);
v___x_2896_ = v___x_2886_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_array_2882_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2920_, 2, v_stop_2884_);
v___x_2896_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2892_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v___x_2899_ = lean_box(0);
v___x_2900_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2898_, v___x_2899_);
lean_dec(v_a_2898_);
v___x_2901_ = lean_box(1);
v___x_2902_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2892_, v___x_2901_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_dec_ref_known(v___x_2902_, 1);
v_a_2876_ = v___x_2896_;
v_b_2877_ = v___x_2900_;
goto _start;
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref(v___x_2896_);
v_a_2904_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2902_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v___x_2896_);
lean_dec(v_fvarId_2892_);
v_a_2912_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2897_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2897_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2922_, lean_object* v_b_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_b_boxed_2928_; lean_object* v_res_2929_; 
v_b_boxed_2928_ = lean_unbox(v_b_2923_);
v_res_2929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2922_, v_b_boxed_2928_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2930_, lean_object* v___x_2931_, lean_object* v_x_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2932_, v_fvarId_2930_, v___x_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2934_, lean_object* v_as_2935_, size_t v_sz_2936_, size_t v_i_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_a_2943_; uint8_t v___x_2947_; 
v___x_2947_ = lean_usize_dec_lt(v_i_2937_, v_sz_2936_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref(v___x_2934_);
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_b_2938_);
return v___x_2948_;
}
else
{
lean_object* v_snd_2949_; lean_object* v_fst_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3016_; 
v_snd_2949_ = lean_ctor_get(v_b_2938_, 1);
v_fst_2950_ = lean_ctor_get(v_b_2938_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_b_2938_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2952_ = v_b_2938_;
v_isShared_2953_ = v_isSharedCheck_3016_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_snd_2949_);
lean_inc(v_fst_2950_);
lean_dec(v_b_2938_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3016_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_array_2954_; lean_object* v_start_2955_; lean_object* v_stop_2956_; uint8_t v___x_2957_; 
v_array_2954_ = lean_ctor_get(v_snd_2949_, 0);
v_start_2955_ = lean_ctor_get(v_snd_2949_, 1);
v_stop_2956_ = lean_ctor_get(v_snd_2949_, 2);
v___x_2957_ = lean_nat_dec_lt(v_start_2955_, v_stop_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2959_; 
lean_dec_ref(v___x_2934_);
if (v_isShared_2953_ == 0)
{
v___x_2959_ = v___x_2952_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_fst_2950_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_snd_2949_);
v___x_2959_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
else
{
lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3012_; 
lean_inc(v_stop_2956_);
lean_inc(v_start_2955_);
lean_inc_ref(v_array_2954_);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_snd_2949_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; lean_object* v_unused_3014_; lean_object* v_unused_3015_; 
v_unused_3013_ = lean_ctor_get(v_snd_2949_, 2);
lean_dec(v_unused_3013_);
v_unused_3014_ = lean_ctor_get(v_snd_2949_, 1);
lean_dec(v_unused_3014_);
v_unused_3015_ = lean_ctor_get(v_snd_2949_, 0);
lean_dec(v_unused_3015_);
v___x_2963_ = v_snd_2949_;
v_isShared_2964_ = v_isSharedCheck_3012_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v_snd_2949_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3012_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_a_2965_; lean_object* v_fvarId_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
v_a_2965_ = lean_array_uget_borrowed(v_as_2935_, v_i_2937_);
v_fvarId_2966_ = lean_ctor_get(v_a_2965_, 0);
v___x_2967_ = lean_array_fget(v_array_2954_, v_start_2955_);
v___x_2968_ = lean_unsigned_to_nat(1u);
v___x_2969_ = lean_nat_add(v_start_2955_, v___x_2968_);
lean_dec(v_start_2955_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2969_);
v___x_2971_ = v___x_2963_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_array_2954_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_stop_2956_);
v___x_2971_ = v_reuseFailAlloc_3011_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2966_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___x_2974_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2967_, v___y_2939_, v___y_2940_);
lean_dec(v___x_2967_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
lean_inc(v_a_2973_);
lean_inc_ref(v___x_2934_);
v___x_2976_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2934_, v_a_2973_, v_a_2975_);
v___x_2977_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2976_, v_a_2973_);
lean_dec(v_a_2973_);
if (v___x_2977_ == 0)
{
lean_object* v___f_2978_; lean_object* v___x_2979_; 
lean_dec(v_fst_2950_);
lean_inc(v_fvarId_2966_);
v___f_2978_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2978_, 0, v_fvarId_2966_);
lean_closure_set(v___f_2978_, 1, v___x_2976_);
v___x_2979_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2978_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
lean_dec_ref_known(v___x_2979_, 1);
v___x_2980_ = lean_box(v___x_2957_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_2971_);
lean_ctor_set(v___x_2952_, 0, v___x_2980_);
v___x_2982_ = v___x_2952_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2971_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
v_a_2943_ = v___x_2982_;
goto v___jp_2942_;
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v___x_2971_);
lean_del_object(v___x_2952_);
lean_dec_ref(v___x_2934_);
v_a_2984_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2979_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2979_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v___x_2993_; 
lean_dec(v___x_2976_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_2971_);
v___x_2993_ = v___x_2952_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_fst_2950_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2971_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
v_a_2943_ = v___x_2993_;
goto v___jp_2942_;
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_a_2973_);
lean_dec_ref(v___x_2971_);
lean_del_object(v___x_2952_);
lean_dec(v_fst_2950_);
lean_dec_ref(v___x_2934_);
v_a_2995_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2974_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2974_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2967_);
lean_del_object(v___x_2952_);
lean_dec(v_fst_2950_);
lean_dec_ref(v___x_2934_);
v_a_3003_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2972_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2972_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
}
}
v___jp_2942_:
{
size_t v___x_2944_; size_t v___x_2945_; 
v___x_2944_ = ((size_t)1ULL);
v___x_2945_ = lean_usize_add(v_i_2937_, v___x_2944_);
v_i_2937_ = v___x_2945_;
v_b_2938_ = v_a_2943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3017_, lean_object* v_as_3018_, lean_object* v_sz_3019_, lean_object* v_i_3020_, lean_object* v_b_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
size_t v_sz_boxed_3025_; size_t v_i_boxed_3026_; lean_object* v_res_3027_; 
v_sz_boxed_3025_ = lean_unbox_usize(v_sz_3019_);
lean_dec(v_sz_3019_);
v_i_boxed_3026_ = lean_unbox_usize(v_i_3020_);
lean_dec(v_i_3020_);
v_res_3027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3017_, v_as_3018_, v_sz_boxed_3025_, v_i_boxed_3026_, v_b_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec_ref(v_as_3018_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3028_, lean_object* v_args_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
uint8_t v_ret_3037_; lean_object* v___x_3038_; lean_object* v_env_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; size_t v_sz_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v_ret_3037_ = 0;
v___x_3038_ = lean_st_ref_get(v_a_3035_);
v_env_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc_ref(v_env_3039_);
lean_dec(v___x_3038_);
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_array_get_size(v_args_3029_);
v___x_3042_ = l_Array_toSubarray___redArg(v_args_3029_, v___x_3040_, v___x_3041_);
v___x_3043_ = lean_box(v_ret_3037_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_ctor_set(v___x_3044_, 1, v___x_3042_);
v_sz_3045_ = lean_array_size(v_params_3028_);
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3039_, v_params_3028_, v_sz_3045_, v___x_3046_, v___x_3044_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3065_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3065_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3065_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v_fst_3052_; lean_object* v_lower_3054_; lean_object* v_upper_3055_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v_fst_3052_ = lean_ctor_get(v_a_3048_, 0);
lean_inc(v_fst_3052_);
lean_dec(v_a_3048_);
v___x_3059_ = lean_array_get_size(v_params_3028_);
v___x_3060_ = lean_nat_dec_eq(v___x_3059_, v___x_3041_);
if (v___x_3060_ == 0)
{
uint8_t v___x_3061_; 
lean_del_object(v___x_3050_);
v___x_3061_ = lean_nat_dec_le(v___x_3041_, v___x_3040_);
if (v___x_3061_ == 0)
{
v_lower_3054_ = v___x_3041_;
v_upper_3055_ = v___x_3059_;
goto v___jp_3053_;
}
else
{
v_lower_3054_ = v___x_3040_;
v_upper_3055_ = v___x_3059_;
goto v___jp_3053_;
}
}
else
{
lean_object* v___x_3063_; 
lean_dec_ref(v_params_3028_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v_fst_3052_);
v___x_3063_ = v___x_3050_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_fst_3052_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
v___jp_3053_:
{
lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = l_Array_toSubarray___redArg(v_params_3028_, v_lower_3054_, v_upper_3055_);
v___x_3057_ = lean_unbox(v_fst_3052_);
lean_dec(v_fst_3052_);
v___x_3058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3056_, v___x_3057_, v_a_3030_, v_a_3031_, v_a_3035_);
return v___x_3058_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v_params_3028_);
v_a_3066_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3047_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3047_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3074_, lean_object* v_args_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3074_, v_args_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3084_, lean_object* v_as_3085_, size_t v_sz_3086_, size_t v_i_3087_, lean_object* v_b_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3084_, v_as_3085_, v_sz_3086_, v_i_3087_, v_b_3088_, v___y_3089_, v___y_3090_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3097_, lean_object* v_as_3098_, lean_object* v_sz_3099_, lean_object* v_i_3100_, lean_object* v_b_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
size_t v_sz_boxed_3109_; size_t v_i_boxed_3110_; lean_object* v_res_3111_; 
v_sz_boxed_3109_ = lean_unbox_usize(v_sz_3099_);
lean_dec(v_sz_3099_);
v_i_boxed_3110_ = lean_unbox_usize(v_i_3100_);
lean_dec(v_i_3100_);
v_res_3111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3097_, v_as_3098_, v_sz_boxed_3109_, v_i_boxed_3110_, v_b_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec_ref(v_as_3098_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3112_, lean_object* v_R_3113_, lean_object* v_a_3114_, uint8_t v_b_3115_, lean_object* v_c_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3114_, v_b_3115_, v___y_3117_, v___y_3118_, v___y_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3125_, lean_object* v_R_3126_, lean_object* v_a_3127_, lean_object* v_b_3128_, lean_object* v_c_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v_b_boxed_3137_; lean_object* v_res_3138_; 
v_b_boxed_3137_ = lean_unbox(v_b_3128_);
v_res_3138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3125_, v_R_3126_, v_a_3127_, v_b_boxed_3137_, v_c_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3139_, size_t v_sz_3140_, size_t v_i_3141_, uint8_t v_b_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
uint8_t v_a_3147_; uint8_t v___x_3151_; 
v___x_3151_ = lean_usize_dec_lt(v_i_3141_, v_sz_3140_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_box(v_b_3142_);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
else
{
lean_object* v_a_3154_; lean_object* v_fvarId_3155_; lean_object* v___x_3156_; 
v_a_3154_ = lean_array_uget_borrowed(v_as_3139_, v_i_3141_);
v_fvarId_3155_ = lean_ctor_get(v_a_3154_, 0);
v___x_3156_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3155_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = lean_box(1);
v___x_3159_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3158_, v_a_3157_);
lean_dec(v_a_3157_);
if (v___x_3159_ == 0)
{
lean_object* v___f_3160_; lean_object* v___x_3161_; 
lean_inc(v_fvarId_3155_);
v___f_3160_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3160_, 0, v_fvarId_3155_);
lean_closure_set(v___f_3160_, 1, v___x_3158_);
v___x_3161_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3160_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_dec_ref_known(v___x_3161_, 1);
v_a_3147_ = v___x_3151_;
goto v___jp_3146_;
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
v_a_3147_ = v_b_3142_;
goto v___jp_3146_;
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3156_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3156_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
v___jp_3146_:
{
size_t v___x_3148_; size_t v___x_3149_; 
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_add(v_i_3141_, v___x_3148_);
v_i_3141_ = v___x_3149_;
v_b_3142_ = v_a_3147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3178_, lean_object* v_sz_3179_, lean_object* v_i_3180_, lean_object* v_b_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
size_t v_sz_boxed_3185_; size_t v_i_boxed_3186_; uint8_t v_b_boxed_3187_; lean_object* v_res_3188_; 
v_sz_boxed_3185_ = lean_unbox_usize(v_sz_3179_);
lean_dec(v_sz_3179_);
v_i_boxed_3186_ = lean_unbox_usize(v_i_3180_);
lean_dec(v_i_3180_);
v_b_boxed_3187_ = lean_unbox(v_b_3181_);
v_res_3188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3178_, v_sz_boxed_3185_, v_i_boxed_3186_, v_b_boxed_3187_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec_ref(v_as_3178_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
uint8_t v_ret_3197_; size_t v_sz_3198_; size_t v___x_3199_; lean_object* v___x_3200_; 
v_ret_3197_ = 0;
v_sz_3198_ = lean_array_size(v_params_3189_);
v___x_3199_ = ((size_t)0ULL);
v___x_3200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3189_, v_sz_3198_, v___x_3199_, v_ret_3197_, v_a_3190_, v_a_3191_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec_ref(v_params_3201_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3210_, size_t v_sz_3211_, size_t v_i_3212_, uint8_t v_b_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3210_, v_sz_3211_, v_i_3212_, v_b_3213_, v___y_3214_, v___y_3215_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3222_, lean_object* v_sz_3223_, lean_object* v_i_3224_, lean_object* v_b_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
size_t v_sz_boxed_3233_; size_t v_i_boxed_3234_; uint8_t v_b_boxed_3235_; lean_object* v_res_3236_; 
v_sz_boxed_3233_ = lean_unbox_usize(v_sz_3223_);
lean_dec(v_sz_3223_);
v_i_boxed_3234_ = lean_unbox_usize(v_i_3224_);
lean_dec(v_i_3224_);
v_b_boxed_3235_ = lean_unbox(v_b_3225_);
v_res_3236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3222_, v_sz_boxed_3233_, v_i_boxed_3234_, v_b_boxed_3235_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v_as_3222_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3237_, size_t v_i_3238_, size_t v_stop_3239_, lean_object* v_b_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_eq(v_i_3238_, v_stop_3239_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v_fvarId_3246_; lean_object* v___x_3247_; 
v___x_3245_ = lean_array_uget_borrowed(v_as_3237_, v_i_3238_);
v_fvarId_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_fvarId_3246_);
v___x_3247_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3246_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; size_t v___x_3249_; size_t v___x_3250_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_add(v_i_3238_, v___x_3249_);
v_i_3238_ = v___x_3250_;
v_b_3240_ = v_a_3248_;
goto _start;
}
else
{
return v___x_3247_;
}
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3252_, 0, v_b_3240_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3253_, lean_object* v_i_3254_, lean_object* v_stop_3255_, lean_object* v_b_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
size_t v_i_boxed_3260_; size_t v_stop_boxed_3261_; lean_object* v_res_3262_; 
v_i_boxed_3260_ = lean_unbox_usize(v_i_3254_);
lean_dec(v_i_3254_);
v_stop_boxed_3261_ = lean_unbox_usize(v_stop_3255_);
lean_dec(v_stop_3255_);
v_res_3262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3253_, v_i_boxed_3260_, v_stop_boxed_3261_, v_b_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v_as_3253_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v_decl_3282_; lean_object* v_k_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; 
switch(lean_obj_tag(v_x_3263_))
{
case 0:
{
lean_object* v_k_3304_; 
v_k_3304_ = lean_ctor_get(v_x_3263_, 1);
lean_inc_ref(v_k_3304_);
lean_dec_ref_known(v_x_3263_, 2);
v_x_3263_ = v_k_3304_;
goto _start;
}
case 3:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec_ref_known(v_x_3263_, 2);
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
case 4:
{
lean_object* v_cases_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3330_; 
v_cases_3308_ = lean_ctor_get(v_x_3263_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_x_3263_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3310_ = v_x_3263_;
v_isShared_3311_ = v_isSharedCheck_3330_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_cases_3308_);
lean_dec(v_x_3263_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3330_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v_alts_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v_alts_3312_ = lean_ctor_get(v_cases_3308_, 3);
lean_inc_ref(v_alts_3312_);
lean_dec_ref(v_cases_3308_);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = lean_array_get_size(v_alts_3312_);
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_nat_dec_lt(v___x_3313_, v___x_3314_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3318_; 
lean_dec_ref(v_alts_3312_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set_tag(v___x_3310_, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3315_);
v___x_3318_ = v___x_3310_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3315_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
else
{
uint8_t v___x_3320_; 
v___x_3320_ = lean_nat_dec_le(v___x_3314_, v___x_3314_);
if (v___x_3320_ == 0)
{
if (v___x_3316_ == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v_alts_3312_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set_tag(v___x_3310_, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3315_);
v___x_3322_ = v___x_3310_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3315_);
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
size_t v___x_3324_; size_t v___x_3325_; lean_object* v___x_3326_; 
lean_del_object(v___x_3310_);
v___x_3324_ = ((size_t)0ULL);
v___x_3325_ = lean_usize_of_nat(v___x_3314_);
v___x_3326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3312_, v___x_3324_, v___x_3325_, v___x_3315_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec_ref(v_alts_3312_);
return v___x_3326_;
}
}
else
{
size_t v___x_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
lean_del_object(v___x_3310_);
v___x_3327_ = ((size_t)0ULL);
v___x_3328_ = lean_usize_of_nat(v___x_3314_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3312_, v___x_3327_, v___x_3328_, v___x_3315_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec_ref(v_alts_3312_);
return v___x_3329_;
}
}
}
}
case 5:
{
lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3338_; 
v_isSharedCheck_3338_ = !lean_is_exclusive(v_x_3263_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v_x_3263_, 0);
lean_dec(v_unused_3339_);
v___x_3332_ = v_x_3263_;
v_isShared_3333_ = v_isSharedCheck_3338_;
goto v_resetjp_3331_;
}
else
{
lean_dec(v_x_3263_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3338_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3334_ = lean_box(0);
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3334_);
v___x_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
case 6:
{
lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3347_; 
v_isSharedCheck_3347_ = !lean_is_exclusive(v_x_3263_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v_x_3263_, 0);
lean_dec(v_unused_3348_);
v___x_3341_ = v_x_3263_;
v_isShared_3342_ = v_isSharedCheck_3347_;
goto v_resetjp_3340_;
}
else
{
lean_dec(v_x_3263_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3347_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = lean_box(0);
if (v_isShared_3342_ == 0)
{
lean_ctor_set_tag(v___x_3341_, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3343_);
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
default: 
{
lean_object* v_decl_3349_; lean_object* v_k_3350_; 
v_decl_3349_ = lean_ctor_get(v_x_3263_, 0);
lean_inc_ref(v_decl_3349_);
v_k_3350_ = lean_ctor_get(v_x_3263_, 1);
lean_inc_ref(v_k_3350_);
lean_dec_ref(v_x_3263_);
v_decl_3282_ = v_decl_3349_;
v_k_3283_ = v_k_3350_;
v___y_3284_ = v_a_3264_;
v___y_3285_ = v_a_3265_;
v___y_3286_ = v_a_3266_;
v___y_3287_ = v_a_3267_;
v___y_3288_ = v_a_3268_;
v___y_3289_ = v_a_3269_;
goto v___jp_3281_;
}
}
v___jp_3271_:
{
if (lean_obj_tag(v___y_3279_) == 0)
{
lean_dec_ref_known(v___y_3279_, 1);
v_x_3263_ = v___y_3278_;
v_a_3264_ = v___y_3274_;
v_a_3265_ = v___y_3276_;
v_a_3266_ = v___y_3277_;
v_a_3267_ = v___y_3275_;
v_a_3268_ = v___y_3273_;
v_a_3269_ = v___y_3272_;
goto _start;
}
else
{
lean_dec_ref(v___y_3278_);
return v___y_3279_;
}
}
v___jp_3281_:
{
lean_object* v_params_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v_params_3290_ = lean_ctor_get(v_decl_3282_, 2);
lean_inc_ref(v_params_3290_);
lean_dec_ref(v_decl_3282_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_array_get_size(v_params_3290_);
v___x_3293_ = lean_nat_dec_lt(v___x_3291_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_dec_ref(v_params_3290_);
v_x_3263_ = v_k_3283_;
v_a_3264_ = v___y_3284_;
v_a_3265_ = v___y_3285_;
v_a_3266_ = v___y_3286_;
v_a_3267_ = v___y_3287_;
v_a_3268_ = v___y_3288_;
v_a_3269_ = v___y_3289_;
goto _start;
}
else
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_nat_dec_le(v___x_3292_, v___x_3292_);
if (v___x_3296_ == 0)
{
if (v___x_3293_ == 0)
{
lean_dec_ref(v_params_3290_);
v_x_3263_ = v_k_3283_;
v_a_3264_ = v___y_3284_;
v_a_3265_ = v___y_3285_;
v_a_3266_ = v___y_3286_;
v_a_3267_ = v___y_3287_;
v_a_3268_ = v___y_3288_;
v_a_3269_ = v___y_3289_;
goto _start;
}
else
{
size_t v___x_3298_; size_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = ((size_t)0ULL);
v___x_3299_ = lean_usize_of_nat(v___x_3292_);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3290_, v___x_3298_, v___x_3299_, v___x_3295_, v___y_3284_, v___y_3285_);
lean_dec_ref(v_params_3290_);
v___y_3272_ = v___y_3289_;
v___y_3273_ = v___y_3288_;
v___y_3274_ = v___y_3284_;
v___y_3275_ = v___y_3287_;
v___y_3276_ = v___y_3285_;
v___y_3277_ = v___y_3286_;
v___y_3278_ = v_k_3283_;
v___y_3279_ = v___x_3300_;
goto v___jp_3271_;
}
}
else
{
size_t v___x_3301_; size_t v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = ((size_t)0ULL);
v___x_3302_ = lean_usize_of_nat(v___x_3292_);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3290_, v___x_3301_, v___x_3302_, v___x_3295_, v___y_3284_, v___y_3285_);
lean_dec_ref(v_params_3290_);
v___y_3272_ = v___y_3289_;
v___y_3273_ = v___y_3288_;
v___y_3274_ = v___y_3284_;
v___y_3275_ = v___y_3287_;
v___y_3276_ = v___y_3285_;
v___y_3277_ = v___y_3286_;
v___y_3278_ = v_k_3283_;
v___y_3279_ = v___x_3303_;
goto v___jp_3271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3351_, size_t v_i_3352_, size_t v_stop_3353_, lean_object* v_b_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___y_3363_; uint8_t v___x_3369_; 
v___x_3369_ = lean_usize_dec_eq(v_i_3352_, v_stop_3353_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_array_uget_borrowed(v_as_3351_, v_i_3352_);
switch(lean_obj_tag(v___x_3370_))
{
case 0:
{
lean_object* v_code_3371_; 
v_code_3371_ = lean_ctor_get(v___x_3370_, 2);
lean_inc_ref(v_code_3371_);
v___y_3363_ = v_code_3371_;
goto v___jp_3362_;
}
case 1:
{
lean_object* v_code_3372_; 
v_code_3372_ = lean_ctor_get(v___x_3370_, 1);
lean_inc_ref(v_code_3372_);
v___y_3363_ = v_code_3372_;
goto v___jp_3362_;
}
default: 
{
lean_object* v_code_3373_; 
v_code_3373_ = lean_ctor_get(v___x_3370_, 0);
lean_inc_ref(v_code_3373_);
v___y_3363_ = v_code_3373_;
goto v___jp_3362_;
}
}
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_b_3354_);
return v___x_3374_;
}
v___jp_3362_:
{
lean_object* v___x_3364_; 
v___x_3364_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3363_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; size_t v___x_3366_; size_t v___x_3367_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_add(v_i_3352_, v___x_3366_);
v_i_3352_ = v___x_3367_;
v_b_3354_ = v_a_3365_;
goto _start;
}
else
{
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3375_, lean_object* v_i_3376_, lean_object* v_stop_3377_, lean_object* v_b_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
size_t v_i_boxed_3386_; size_t v_stop_boxed_3387_; lean_object* v_res_3388_; 
v_i_boxed_3386_ = lean_unbox_usize(v_i_3376_);
lean_dec(v_i_3376_);
v_stop_boxed_3387_ = lean_unbox_usize(v_stop_3377_);
lean_dec(v_stop_3377_);
v_res_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3375_, v_i_boxed_3386_, v_stop_boxed_3387_, v_b_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec_ref(v_as_3375_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3398_, size_t v_i_3399_, size_t v_stop_3400_, lean_object* v_b_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3398_, v_i_3399_, v_stop_3400_, v_b_3401_, v___y_3402_, v___y_3403_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3410_, lean_object* v_i_3411_, lean_object* v_stop_3412_, lean_object* v_b_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
size_t v_i_boxed_3421_; size_t v_stop_boxed_3422_; lean_object* v_res_3423_; 
v_i_boxed_3421_ = lean_unbox_usize(v_i_3411_);
lean_dec(v_i_3411_);
v_stop_boxed_3422_ = lean_unbox_usize(v_stop_3412_);
lean_dec(v_stop_3412_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3410_, v_i_boxed_3421_, v_stop_boxed_3422_, v_b_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v_as_3410_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3424_, lean_object* v_b_3425_){
_start:
{
lean_object* v_array_3426_; lean_object* v_start_3427_; lean_object* v_stop_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3441_; 
v_array_3426_ = lean_ctor_get(v_a_3424_, 0);
v_start_3427_ = lean_ctor_get(v_a_3424_, 1);
v_stop_3428_ = lean_ctor_get(v_a_3424_, 2);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_a_3424_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3430_ = v_a_3424_;
v_isShared_3431_ = v_isSharedCheck_3441_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_stop_3428_);
lean_inc(v_start_3427_);
lean_inc(v_array_3426_);
lean_dec(v_a_3424_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3441_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_nat_dec_lt(v_start_3427_, v_stop_3428_);
if (v___x_3432_ == 0)
{
lean_del_object(v___x_3430_);
lean_dec(v_stop_3428_);
lean_dec(v_start_3427_);
lean_dec_ref(v_array_3426_);
return v_b_3425_;
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3433_ = lean_unsigned_to_nat(1u);
v___x_3434_ = lean_nat_add(v_start_3427_, v___x_3433_);
lean_inc_ref(v_array_3426_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3434_);
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_array_3426_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_stop_3428_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = lean_array_fget(v_array_3426_, v_start_3427_);
lean_dec(v_start_3427_);
lean_dec_ref(v_array_3426_);
v___x_3438_ = lean_array_push(v_b_3425_, v___x_3437_);
v_a_3424_ = v___x_3436_;
v_b_3425_ = v___x_3438_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_bs_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
uint8_t v___x_3448_; 
v___x_3448_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3449_, 0, v_bs_3444_);
return v___x_3449_;
}
else
{
lean_object* v_v_3450_; lean_object* v___x_3451_; lean_object* v_bs_x27_3452_; lean_object* v___x_3453_; 
v_v_3450_ = lean_array_uget(v_bs_3444_, v_i_3443_);
v___x_3451_ = lean_unsigned_to_nat(0u);
v_bs_x27_3452_ = lean_array_uset(v_bs_3444_, v_i_3443_, v___x_3451_);
v___x_3453_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3450_, v___y_3445_, v___y_3446_);
lean_dec(v_v_3450_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; size_t v___x_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = ((size_t)1ULL);
v___x_3456_ = lean_usize_add(v_i_3443_, v___x_3455_);
v___x_3457_ = lean_array_uset(v_bs_x27_3452_, v_i_3443_, v_a_3454_);
v_i_3443_ = v___x_3456_;
v_bs_3444_ = v___x_3457_;
goto _start;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v_bs_x27_3452_);
v_a_3459_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3453_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3453_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3467_, lean_object* v_i_3468_, lean_object* v_bs_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
size_t v_sz_boxed_3473_; size_t v_i_boxed_3474_; lean_object* v_res_3475_; 
v_sz_boxed_3473_ = lean_unbox_usize(v_sz_3467_);
lean_dec(v_sz_3467_);
v_i_boxed_3474_ = lean_unbox_usize(v_i_3468_);
lean_dec(v_i_3468_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3473_, v_i_boxed_3474_, v_bs_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3476_, size_t v_i_3477_, size_t v_stop_3478_, lean_object* v_b_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
uint8_t v___x_3484_; 
v___x_3484_ = lean_usize_dec_eq(v_i_3477_, v_stop_3478_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v_fvarId_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3485_ = lean_array_uget_borrowed(v_as_3476_, v_i_3477_);
v_fvarId_3486_ = lean_ctor_get(v___x_3485_, 0);
v___x_3487_ = lean_box(1);
lean_inc(v_fvarId_3486_);
v___x_3488_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3486_, v___x_3487_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; size_t v___x_3490_; size_t v___x_3491_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = ((size_t)1ULL);
v___x_3491_ = lean_usize_add(v_i_3477_, v___x_3490_);
v_i_3477_ = v___x_3491_;
v_b_3479_ = v_a_3489_;
goto _start;
}
else
{
return v___x_3488_;
}
}
else
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3493_, 0, v_b_3479_);
return v___x_3493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3494_, lean_object* v_i_3495_, lean_object* v_stop_3496_, lean_object* v_b_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
size_t v_i_boxed_3502_; size_t v_stop_boxed_3503_; lean_object* v_res_3504_; 
v_i_boxed_3502_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_stop_boxed_3503_ = lean_unbox_usize(v_stop_3496_);
lean_dec(v_stop_3496_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3494_, v_i_boxed_3502_, v_stop_boxed_3503_, v_b_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v_as_3494_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3505_, size_t v_i_3506_, size_t v_stop_3507_, lean_object* v_b_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
uint8_t v___x_3513_; 
v___x_3513_ = lean_usize_dec_eq(v_i_3506_, v_stop_3507_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v_fst_3515_; lean_object* v_snd_3516_; lean_object* v_fvarId_3517_; lean_object* v___x_3518_; 
v___x_3514_ = lean_array_uget_borrowed(v_as_3505_, v_i_3506_);
v_fst_3515_ = lean_ctor_get(v___x_3514_, 0);
v_snd_3516_ = lean_ctor_get(v___x_3514_, 1);
v_fvarId_3517_ = lean_ctor_get(v_fst_3515_, 0);
lean_inc(v_snd_3516_);
lean_inc(v_fvarId_3517_);
v___x_3518_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3517_, v_snd_3516_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; size_t v___x_3520_; size_t v___x_3521_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v___x_3520_ = ((size_t)1ULL);
v___x_3521_ = lean_usize_add(v_i_3506_, v___x_3520_);
v_i_3506_ = v___x_3521_;
v_b_3508_ = v_a_3519_;
goto _start;
}
else
{
return v___x_3518_;
}
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v_b_3508_);
return v___x_3523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3524_, lean_object* v_i_3525_, lean_object* v_stop_3526_, lean_object* v_b_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
size_t v_i_boxed_3532_; size_t v_stop_boxed_3533_; lean_object* v_res_3534_; 
v_i_boxed_3532_ = lean_unbox_usize(v_i_3525_);
lean_dec(v_i_3525_);
v_stop_boxed_3533_ = lean_unbox_usize(v_stop_3526_);
lean_dec(v_stop_3526_);
v_res_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3524_, v_i_boxed_3532_, v_stop_boxed_3533_, v_b_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v_as_3524_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3537_, size_t v_i_3538_, size_t v_stop_3539_, lean_object* v_b_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_usize_dec_eq(v_i_3538_, v_stop_3539_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_array_uget_borrowed(v_as_3537_, v_i_3538_);
v___x_3550_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3549_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; size_t v___x_3552_; size_t v___x_3553_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3552_ = ((size_t)1ULL);
v___x_3553_ = lean_usize_add(v_i_3538_, v___x_3552_);
v_i_3538_ = v___x_3553_;
v_b_3540_ = v_a_3551_;
goto _start;
}
else
{
return v___x_3550_;
}
}
else
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_b_3540_);
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___y_3571_; 
switch(lean_obj_tag(v_letVal_3556_))
{
case 0:
{
lean_object* v_value_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3588_; 
v_value_3580_ = lean_ctor_get(v_letVal_3556_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_letVal_3556_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3582_ = v_letVal_3556_;
v_isShared_3583_ = v_isSharedCheck_3588_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_value_3580_);
lean_dec(v_letVal_3556_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3588_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3584_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3580_);
lean_dec_ref(v_value_3580_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3584_);
v___x_3586_ = v___x_3582_;
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
}
case 1:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_box(1);
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
case 2:
{
lean_object* v_idx_3591_; lean_object* v_struct_3592_; lean_object* v___x_3593_; lean_object* v_env_3594_; lean_object* v___x_3595_; 
v_idx_3591_ = lean_ctor_get(v_letVal_3556_, 1);
lean_inc(v_idx_3591_);
v_struct_3592_ = lean_ctor_get(v_letVal_3556_, 2);
lean_inc(v_struct_3592_);
lean_dec_ref_known(v_letVal_3556_, 3);
v___x_3593_ = lean_st_ref_get(v_a_3562_);
v_env_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_ref(v_env_3594_);
lean_dec(v___x_3593_);
v___x_3595_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3592_, v_a_3557_, v_a_3558_);
lean_dec(v_struct_3592_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3604_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3594_, v_a_3596_, v_idx_3591_);
lean_dec(v_idx_3591_);
lean_dec(v_a_3596_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
else
{
lean_dec_ref(v_env_3594_);
lean_dec(v_idx_3591_);
return v___x_3595_;
}
}
case 3:
{
lean_object* v_declName_3605_; lean_object* v_args_3606_; lean_object* v___x_3607_; lean_object* v_env_3608_; lean_object* v___x_3609_; lean_object* v_numFields_3611_; lean_object* v_lower_3612_; lean_object* v_upper_3613_; lean_object* v___x_3641_; lean_object* v___y_3710_; uint8_t v___x_3719_; 
v_declName_3605_ = lean_ctor_get(v_letVal_3556_, 0);
lean_inc(v_declName_3605_);
v_args_3606_ = lean_ctor_get(v_letVal_3556_, 2);
lean_inc_ref(v_args_3606_);
lean_dec_ref_known(v_letVal_3556_, 3);
v___x_3607_ = lean_st_ref_get(v_a_3562_);
v_env_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc_ref(v_env_3608_);
lean_dec(v___x_3607_);
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3641_ = lean_array_get_size(v_args_3606_);
v___x_3719_ = lean_nat_dec_lt(v___x_3609_, v___x_3641_);
if (v___x_3719_ == 0)
{
goto v___jp_3642_;
}
else
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = lean_box(0);
v___x_3721_ = lean_nat_dec_le(v___x_3641_, v___x_3641_);
if (v___x_3721_ == 0)
{
if (v___x_3719_ == 0)
{
goto v___jp_3642_;
}
else
{
size_t v___x_3722_; size_t v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = ((size_t)0ULL);
v___x_3723_ = lean_usize_of_nat(v___x_3641_);
v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3606_, v___x_3722_, v___x_3723_, v___x_3720_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
v___y_3710_ = v___x_3724_;
goto v___jp_3709_;
}
}
else
{
size_t v___x_3725_; size_t v___x_3726_; lean_object* v___x_3727_; 
v___x_3725_ = ((size_t)0ULL);
v___x_3726_ = lean_usize_of_nat(v___x_3641_);
v___x_3727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3606_, v___x_3725_, v___x_3726_, v___x_3720_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
v___y_3710_ = v___x_3727_;
goto v___jp_3709_;
}
}
v___jp_3610_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3614_ = l_Array_toSubarray___redArg(v_args_3606_, v_lower_3612_, v_upper_3613_);
v___x_3615_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3616_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3614_, v___x_3615_);
v___x_3617_ = lean_array_get_size(v___x_3616_);
v___x_3618_ = lean_nat_dec_eq(v_numFields_3611_, v___x_3617_);
lean_dec(v_numFields_3611_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
lean_dec_ref(v___x_3616_);
lean_dec(v_declName_3605_);
v___x_3619_ = lean_box(1);
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
else
{
size_t v_sz_3621_; size_t v___x_3622_; lean_object* v___x_3623_; 
v_sz_3621_ = lean_array_size(v___x_3616_);
v___x_3622_ = ((size_t)0ULL);
v___x_3623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3621_, v___x_3622_, v___x_3616_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3632_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3632_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3632_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3628_, 0, v_declName_3605_);
lean_ctor_set(v___x_3628_, 1, v_a_3624_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3628_);
v___x_3630_ = v___x_3626_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_declName_3605_);
v_a_3633_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3623_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3623_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
v___jp_3642_:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3559_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; uint8_t v___x_3645_; lean_object* v___x_3646_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3645_ = lean_unbox(v_a_3644_);
lean_dec(v_a_3644_);
lean_inc(v_declName_3605_);
v___x_3646_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3605_, v___x_3645_, v_a_3561_, v_a_3562_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3692_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3692_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3692_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
if (lean_obj_tag(v_a_3647_) == 1)
{
lean_object* v_val_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
lean_dec_ref(v_args_3606_);
v_val_3651_ = lean_ctor_get(v_a_3647_, 0);
lean_inc(v_val_3651_);
lean_dec_ref_known(v_a_3647_, 1);
v___x_3652_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3651_);
lean_dec(v_val_3651_);
v___x_3653_ = lean_nat_dec_eq(v___x_3652_, v___x_3641_);
lean_dec(v___x_3652_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
lean_dec_ref(v_env_3608_);
lean_dec(v_declName_3605_);
v___x_3654_ = lean_box(1);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v___x_3654_);
v___x_3656_ = v___x_3649_;
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
lean_object* v___x_3658_; 
lean_inc(v_declName_3605_);
v___x_3658_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3608_, v_declName_3605_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v___x_3659_; 
lean_del_object(v___x_3649_);
v___x_3659_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3605_, v_a_3557_, v_a_3558_);
lean_dec(v_declName_3605_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3672_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3672_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3672_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
if (lean_obj_tag(v_a_3660_) == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = lean_box(1);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3664_);
v___x_3666_ = v___x_3662_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
else
{
lean_object* v_val_3668_; lean_object* v___x_3670_; 
v_val_3668_ = lean_ctor_get(v_a_3660_, 0);
lean_inc(v_val_3668_);
lean_dec_ref_known(v_a_3660_, 1);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v_val_3668_);
v___x_3670_ = v___x_3662_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_val_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_a_3673_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3659_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3659_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
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
lean_object* v_val_3681_; lean_object* v___x_3683_; 
lean_dec(v_declName_3605_);
v_val_3681_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_val_3681_);
lean_dec_ref_known(v___x_3658_, 1);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v_val_3681_);
v___x_3683_ = v___x_3649_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_val_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
uint8_t v___x_3685_; lean_object* v___x_3686_; 
lean_del_object(v___x_3649_);
lean_dec(v_a_3647_);
v___x_3685_ = 0;
lean_inc(v_declName_3605_);
v___x_3686_ = l_Lean_Environment_find_x3f(v_env_3608_, v_declName_3605_, v___x_3685_);
if (lean_obj_tag(v___x_3686_) == 1)
{
lean_object* v_val_3687_; 
v_val_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_val_3687_);
lean_dec_ref_known(v___x_3686_, 1);
if (lean_obj_tag(v_val_3687_) == 6)
{
lean_object* v_val_3688_; lean_object* v_numParams_3689_; lean_object* v_numFields_3690_; uint8_t v___x_3691_; 
v_val_3688_ = lean_ctor_get(v_val_3687_, 0);
lean_inc_ref(v_val_3688_);
lean_dec_ref_known(v_val_3687_, 1);
v_numParams_3689_ = lean_ctor_get(v_val_3688_, 3);
lean_inc(v_numParams_3689_);
v_numFields_3690_ = lean_ctor_get(v_val_3688_, 4);
lean_inc(v_numFields_3690_);
lean_dec_ref(v_val_3688_);
v___x_3691_ = lean_nat_dec_le(v_numParams_3689_, v___x_3609_);
if (v___x_3691_ == 0)
{
v_numFields_3611_ = v_numFields_3690_;
v_lower_3612_ = v_numParams_3689_;
v_upper_3613_ = v___x_3641_;
goto v___jp_3610_;
}
else
{
lean_dec(v_numParams_3689_);
v_numFields_3611_ = v_numFields_3690_;
v_lower_3612_ = v___x_3609_;
v_upper_3613_ = v___x_3641_;
goto v___jp_3610_;
}
}
else
{
lean_dec(v_val_3687_);
lean_dec_ref(v_args_3606_);
lean_dec(v_declName_3605_);
goto v___jp_3564_;
}
}
else
{
lean_dec(v___x_3686_);
lean_dec_ref(v_args_3606_);
lean_dec(v_declName_3605_);
goto v___jp_3564_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec_ref(v_env_3608_);
lean_dec_ref(v_args_3606_);
lean_dec(v_declName_3605_);
v_a_3693_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3646_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3646_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v_env_3608_);
lean_dec_ref(v_args_3606_);
lean_dec(v_declName_3605_);
v_a_3701_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3643_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3643_);
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
v___jp_3709_:
{
if (lean_obj_tag(v___y_3710_) == 0)
{
lean_dec_ref_known(v___y_3710_, 1);
goto v___jp_3642_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref(v_env_3608_);
lean_dec_ref(v_args_3606_);
lean_dec(v_declName_3605_);
v_a_3711_ = lean_ctor_get(v___y_3710_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___y_3710_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___y_3710_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___y_3710_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
default: 
{
lean_object* v_args_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v_args_3728_ = lean_ctor_get(v_letVal_3556_, 1);
lean_inc_ref(v_args_3728_);
lean_dec_ref_known(v_letVal_3556_, 2);
v___x_3729_ = lean_unsigned_to_nat(0u);
v___x_3730_ = lean_array_get_size(v_args_3728_);
v___x_3731_ = lean_nat_dec_lt(v___x_3729_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_dec_ref(v_args_3728_);
goto v___jp_3567_;
}
else
{
lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3732_ = lean_box(0);
v___x_3733_ = lean_nat_dec_le(v___x_3730_, v___x_3730_);
if (v___x_3733_ == 0)
{
if (v___x_3731_ == 0)
{
lean_dec_ref(v_args_3728_);
goto v___jp_3567_;
}
else
{
size_t v___x_3734_; size_t v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = ((size_t)0ULL);
v___x_3735_ = lean_usize_of_nat(v___x_3730_);
v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3728_, v___x_3734_, v___x_3735_, v___x_3732_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
lean_dec_ref(v_args_3728_);
v___y_3571_ = v___x_3736_;
goto v___jp_3570_;
}
}
else
{
size_t v___x_3737_; size_t v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = ((size_t)0ULL);
v___x_3738_ = lean_usize_of_nat(v___x_3730_);
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3728_, v___x_3737_, v___x_3738_, v___x_3732_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
lean_dec_ref(v_args_3728_);
v___y_3571_ = v___x_3739_;
goto v___jp_3570_;
}
}
}
}
v___jp_3564_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_box(1);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
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
if (lean_obj_tag(v___y_3571_) == 0)
{
lean_dec_ref_known(v___y_3571_, 1);
goto v___jp_3567_;
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_a_3572_ = lean_ctor_get(v___y_3571_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___y_3571_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___y_3571_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___y_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3740_, lean_object* v_args_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v_params_3749_; lean_object* v_value_3750_; lean_object* v___x_3751_; 
v_params_3749_ = lean_ctor_get(v_funDecl_3740_, 2);
lean_inc_ref(v_params_3749_);
v_value_3750_ = lean_ctor_get(v_funDecl_3740_, 4);
lean_inc_ref(v_value_3750_);
lean_dec_ref(v_funDecl_3740_);
v___x_3751_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3749_, v_args_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3763_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3763_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3763_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
uint8_t v___x_3756_; 
v___x_3756_ = lean_unbox(v_a_3752_);
lean_dec(v_a_3752_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_dec_ref(v_value_3750_);
v___x_3757_ = lean_box(0);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3757_);
v___x_3759_ = v___x_3754_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
else
{
lean_object* v___x_3761_; 
lean_del_object(v___x_3754_);
lean_inc_ref(v_value_3750_);
v___x_3761_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3750_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v___x_3762_; 
lean_dec_ref_known(v___x_3761_, 1);
v___x_3762_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3750_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
return v___x_3762_;
}
else
{
lean_dec_ref(v_value_3750_);
return v___x_3761_;
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v_value_3750_);
v_a_3764_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3751_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3751_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3772_, lean_object* v_as_3773_, size_t v_sz_3774_, size_t v_i_3775_, lean_object* v_b_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_a_3785_; uint8_t v___x_3789_; 
v___x_3789_ = lean_usize_dec_lt(v_i_3775_, v_sz_3774_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v_b_3776_);
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; lean_object* v_a_3792_; 
v___x_3791_ = lean_box(0);
v_a_3792_ = lean_array_uget_borrowed(v_as_3773_, v_i_3775_);
if (lean_obj_tag(v_a_3792_) == 0)
{
lean_object* v_ctorName_3793_; lean_object* v_params_3794_; lean_object* v_code_3795_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3805_; lean_object* v___y_3807_; lean_object* v___x_3808_; 
v_ctorName_3793_ = lean_ctor_get(v_a_3792_, 0);
v_params_3794_ = lean_ctor_get(v_a_3792_, 1);
v_code_3795_ = lean_ctor_get(v_a_3792_, 2);
v___x_3808_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3772_, v_ctorName_3793_);
if (lean_obj_tag(v___x_3808_) == 1)
{
lean_object* v_val_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v_val_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_val_3809_);
lean_dec_ref_known(v___x_3808_, 1);
v___x_3810_ = l_Array_zip___redArg(v_params_3794_, v_val_3809_);
lean_dec(v_val_3809_);
v___x_3811_ = lean_unsigned_to_nat(0u);
v___x_3812_ = lean_array_get_size(v___x_3810_);
v___x_3813_ = lean_nat_dec_lt(v___x_3811_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_dec_ref(v___x_3810_);
v___y_3797_ = v___y_3777_;
v___y_3798_ = v___y_3778_;
v___y_3799_ = v___y_3779_;
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
goto v___jp_3796_;
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_nat_dec_le(v___x_3812_, v___x_3812_);
if (v___x_3814_ == 0)
{
if (v___x_3813_ == 0)
{
lean_dec_ref(v___x_3810_);
v___y_3797_ = v___y_3777_;
v___y_3798_ = v___y_3778_;
v___y_3799_ = v___y_3779_;
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
goto v___jp_3796_;
}
else
{
size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; 
v___x_3815_ = ((size_t)0ULL);
v___x_3816_ = lean_usize_of_nat(v___x_3812_);
v___x_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3810_, v___x_3815_, v___x_3816_, v___x_3791_, v___y_3777_, v___y_3778_, v___y_3782_);
lean_dec_ref(v___x_3810_);
v___y_3805_ = v___x_3817_;
goto v___jp_3804_;
}
}
else
{
size_t v___x_3818_; size_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = lean_usize_of_nat(v___x_3812_);
v___x_3820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3810_, v___x_3818_, v___x_3819_, v___x_3791_, v___y_3777_, v___y_3778_, v___y_3782_);
lean_dec_ref(v___x_3810_);
v___y_3805_ = v___x_3820_;
goto v___jp_3804_;
}
}
}
else
{
lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
lean_dec(v___x_3808_);
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = lean_array_get_size(v_params_3794_);
v___x_3823_ = lean_nat_dec_lt(v___x_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
v___y_3797_ = v___y_3777_;
v___y_3798_ = v___y_3778_;
v___y_3799_ = v___y_3779_;
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
goto v___jp_3796_;
}
else
{
uint8_t v___x_3824_; 
v___x_3824_ = lean_nat_dec_le(v___x_3822_, v___x_3822_);
if (v___x_3824_ == 0)
{
if (v___x_3823_ == 0)
{
v___y_3797_ = v___y_3777_;
v___y_3798_ = v___y_3778_;
v___y_3799_ = v___y_3779_;
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
goto v___jp_3796_;
}
else
{
size_t v___x_3825_; size_t v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = ((size_t)0ULL);
v___x_3826_ = lean_usize_of_nat(v___x_3822_);
v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3794_, v___x_3825_, v___x_3826_, v___x_3791_, v___y_3777_, v___y_3778_, v___y_3782_);
v___y_3807_ = v___x_3827_;
goto v___jp_3806_;
}
}
else
{
size_t v___x_3828_; size_t v___x_3829_; lean_object* v___x_3830_; 
v___x_3828_ = ((size_t)0ULL);
v___x_3829_ = lean_usize_of_nat(v___x_3822_);
v___x_3830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3794_, v___x_3828_, v___x_3829_, v___x_3791_, v___y_3777_, v___y_3778_, v___y_3782_);
v___y_3807_ = v___x_3830_;
goto v___jp_3806_;
}
}
}
v___jp_3796_:
{
lean_object* v___x_3803_; 
lean_inc_ref(v_code_3795_);
v___x_3803_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3795_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_dec_ref_known(v___x_3803_, 1);
v_a_3785_ = v___x_3791_;
goto v___jp_3784_;
}
else
{
return v___x_3803_;
}
}
v___jp_3804_:
{
if (lean_obj_tag(v___y_3805_) == 0)
{
lean_dec_ref_known(v___y_3805_, 1);
v___y_3797_ = v___y_3777_;
v___y_3798_ = v___y_3778_;
v___y_3799_ = v___y_3779_;
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
goto v___jp_3796_;
}
else
{
return v___y_3805_;
}
}
v___jp_3806_:
{
if (lean_obj_tag(v___y_3807_) == 0)
{
lean_dec_ref_known(v___y_3807_, 1);
v___y_3797_ = v___y_3777_;
v___y_3798_ = v___y_3778_;
v___y_3799_ = v___y_3779_;
v___y_3800_ = v___y_3780_;
v___y_3801_ = v___y_3781_;
v___y_3802_ = v___y_3782_;
goto v___jp_3796_;
}
else
{
return v___y_3807_;
}
}
}
else
{
lean_object* v_code_3831_; lean_object* v___x_3832_; 
v_code_3831_ = lean_ctor_get(v_a_3792_, 0);
lean_inc_ref(v_code_3831_);
v___x_3832_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3831_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_dec_ref_known(v___x_3832_, 1);
v_a_3785_ = v___x_3791_;
goto v___jp_3784_;
}
else
{
return v___x_3832_;
}
}
}
v___jp_3784_:
{
size_t v___x_3786_; size_t v___x_3787_; 
v___x_3786_ = ((size_t)1ULL);
v___x_3787_ = lean_usize_add(v_i_3775_, v___x_3786_);
v_i_3775_ = v___x_3787_;
v_b_3776_ = v_a_3785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_decl_3842_; lean_object* v_k_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; 
switch(lean_obj_tag(v_x_3833_))
{
case 0:
{
lean_object* v_decl_3853_; lean_object* v_k_3854_; lean_object* v_fvarId_3855_; lean_object* v_value_3856_; lean_object* v___x_3857_; 
v_decl_3853_ = lean_ctor_get(v_x_3833_, 0);
lean_inc_ref(v_decl_3853_);
v_k_3854_ = lean_ctor_get(v_x_3833_, 1);
lean_inc_ref(v_k_3854_);
lean_dec_ref_known(v_x_3833_, 2);
v_fvarId_3855_ = lean_ctor_get(v_decl_3853_, 0);
lean_inc(v_fvarId_3855_);
v_value_3856_ = lean_ctor_get(v_decl_3853_, 3);
lean_inc_n(v_value_3856_, 2);
lean_dec_ref(v_decl_3853_);
v___x_3857_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3856_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
v___x_3859_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3855_, v_a_3858_, v_a_3834_, v_a_3835_, v_a_3839_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_dec_ref_known(v___x_3859_, 1);
if (lean_obj_tag(v_value_3856_) == 4)
{
lean_object* v_fvarId_3860_; lean_object* v_args_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; 
v_fvarId_3860_ = lean_ctor_get(v_value_3856_, 0);
lean_inc(v_fvarId_3860_);
v_args_3861_ = lean_ctor_get(v_value_3856_, 1);
lean_inc_ref(v_args_3861_);
lean_dec_ref_known(v_value_3856_, 2);
v___x_3862_ = 0;
v___x_3863_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3862_, v_fvarId_3860_, v_a_3837_);
lean_dec(v_fvarId_3860_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
if (lean_obj_tag(v_a_3864_) == 1)
{
lean_object* v_val_3865_; lean_object* v___x_3866_; 
v_val_3865_ = lean_ctor_get(v_a_3864_, 0);
lean_inc(v_val_3865_);
lean_dec_ref_known(v_a_3864_, 1);
v___x_3866_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3865_, v_args_3861_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_dec_ref_known(v___x_3866_, 1);
v_x_3833_ = v_k_3854_;
goto _start;
}
else
{
lean_dec_ref(v_k_3854_);
return v___x_3866_;
}
}
else
{
lean_dec(v_a_3864_);
lean_dec_ref(v_args_3861_);
v_x_3833_ = v_k_3854_;
goto _start;
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_dec_ref(v_args_3861_);
lean_dec_ref(v_k_3854_);
v_a_3869_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3863_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3863_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_dec(v_value_3856_);
v_x_3833_ = v_k_3854_;
goto _start;
}
}
else
{
lean_dec(v_value_3856_);
lean_dec_ref(v_k_3854_);
return v___x_3859_;
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v_value_3856_);
lean_dec(v_fvarId_3855_);
lean_dec_ref(v_k_3854_);
v_a_3878_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3857_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3857_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3886_; lean_object* v_args_3887_; uint8_t v___x_3888_; lean_object* v___x_3889_; 
v_fvarId_3886_ = lean_ctor_get(v_x_3833_, 0);
lean_inc(v_fvarId_3886_);
v_args_3887_ = lean_ctor_get(v_x_3833_, 1);
lean_inc_ref(v_args_3887_);
lean_dec_ref_known(v_x_3833_, 2);
v___x_3888_ = 0;
v___x_3889_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3888_, v_fvarId_3886_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___y_3892_; lean_object* v___x_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = lean_array_get_size(v_args_3887_);
v___x_3896_ = lean_nat_dec_lt(v___x_3894_, v___x_3895_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; 
v___x_3897_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3890_, v_args_3887_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
return v___x_3897_;
}
else
{
lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_nat_dec_le(v___x_3895_, v___x_3895_);
if (v___x_3899_ == 0)
{
if (v___x_3896_ == 0)
{
lean_object* v___x_3900_; 
v___x_3900_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3890_, v_args_3887_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
return v___x_3900_;
}
else
{
size_t v___x_3901_; size_t v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = ((size_t)0ULL);
v___x_3902_ = lean_usize_of_nat(v___x_3895_);
v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3887_, v___x_3901_, v___x_3902_, v___x_3898_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
v___y_3892_ = v___x_3903_;
goto v___jp_3891_;
}
}
else
{
size_t v___x_3904_; size_t v___x_3905_; lean_object* v___x_3906_; 
v___x_3904_ = ((size_t)0ULL);
v___x_3905_ = lean_usize_of_nat(v___x_3895_);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3887_, v___x_3904_, v___x_3905_, v___x_3898_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
v___y_3892_ = v___x_3906_;
goto v___jp_3891_;
}
}
v___jp_3891_:
{
if (lean_obj_tag(v___y_3892_) == 0)
{
lean_object* v___x_3893_; 
lean_dec_ref_known(v___y_3892_, 1);
v___x_3893_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3890_, v_args_3887_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
return v___x_3893_;
}
else
{
lean_dec(v_a_3890_);
lean_dec_ref(v_args_3887_);
return v___y_3892_;
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec_ref(v_args_3887_);
v_a_3907_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3889_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3889_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
case 4:
{
lean_object* v_cases_3915_; lean_object* v_discr_3916_; lean_object* v_alts_3917_; lean_object* v___x_3918_; 
v_cases_3915_ = lean_ctor_get(v_x_3833_, 0);
lean_inc_ref(v_cases_3915_);
lean_dec_ref_known(v_x_3833_, 1);
v_discr_3916_ = lean_ctor_get(v_cases_3915_, 2);
lean_inc(v_discr_3916_);
v_alts_3917_ = lean_ctor_get(v_cases_3915_, 3);
lean_inc_ref(v_alts_3917_);
lean_dec_ref(v_cases_3915_);
v___x_3918_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3916_, v_a_3834_, v_a_3835_);
lean_dec(v_discr_3916_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; size_t v_sz_3921_; size_t v___x_3922_; lean_object* v___x_3923_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = lean_box(0);
v_sz_3921_ = lean_array_size(v_alts_3917_);
v___x_3922_ = ((size_t)0ULL);
v___x_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3919_, v_alts_3917_, v_sz_3921_, v___x_3922_, v___x_3920_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
lean_dec_ref(v_alts_3917_);
lean_dec(v_a_3919_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v___x_3923_, 0);
lean_dec(v_unused_3931_);
v___x_3925_ = v___x_3923_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v___x_3923_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3920_);
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3920_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
else
{
return v___x_3923_;
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v_alts_3917_);
v_a_3932_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3918_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3918_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3940_; lean_object* v___x_3941_; 
v_fvarId_3940_ = lean_ctor_get(v_x_3833_, 0);
lean_inc(v_fvarId_3940_);
lean_dec_ref_known(v_x_3833_, 1);
v___x_3941_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3940_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v___x_3942_; 
lean_dec_ref_known(v___x_3941_, 1);
v___x_3942_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3940_, v_a_3834_, v_a_3835_);
lean_dec(v_fvarId_3940_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3944_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v___x_3944_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3943_, v_a_3834_, v_a_3835_, v_a_3839_);
return v___x_3944_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
v_a_3945_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3942_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3942_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
lean_dec(v_fvarId_3940_);
return v___x_3941_;
}
}
case 6:
{
lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3960_; 
v_isSharedCheck_3960_ = !lean_is_exclusive(v_x_3833_);
if (v_isSharedCheck_3960_ == 0)
{
lean_object* v_unused_3961_; 
v_unused_3961_ = lean_ctor_get(v_x_3833_, 0);
lean_dec(v_unused_3961_);
v___x_3954_ = v_x_3833_;
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
else
{
lean_dec(v_x_3833_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3956_ = lean_box(0);
if (v_isShared_3955_ == 0)
{
lean_ctor_set_tag(v___x_3954_, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3956_);
v___x_3958_ = v___x_3954_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
default: 
{
lean_object* v_decl_3962_; lean_object* v_k_3963_; 
v_decl_3962_ = lean_ctor_get(v_x_3833_, 0);
lean_inc_ref(v_decl_3962_);
v_k_3963_ = lean_ctor_get(v_x_3833_, 1);
lean_inc_ref(v_k_3963_);
lean_dec_ref(v_x_3833_);
v_decl_3842_ = v_decl_3962_;
v_k_3843_ = v_k_3963_;
v___y_3844_ = v_a_3834_;
v___y_3845_ = v_a_3835_;
v___y_3846_ = v_a_3836_;
v___y_3847_ = v_a_3837_;
v___y_3848_ = v_a_3838_;
v___y_3849_ = v_a_3839_;
goto v___jp_3841_;
}
}
v___jp_3841_:
{
lean_object* v_value_3850_; lean_object* v___x_3851_; 
v_value_3850_ = lean_ctor_get(v_decl_3842_, 4);
lean_inc_ref(v_value_3850_);
lean_dec_ref(v_decl_3842_);
v___x_3851_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3850_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_dec_ref_known(v___x_3851_, 1);
v_x_3833_ = v_k_3843_;
v_a_3834_ = v___y_3844_;
v_a_3835_ = v___y_3845_;
v_a_3836_ = v___y_3846_;
v_a_3837_ = v___y_3847_;
v_a_3838_ = v___y_3848_;
v_a_3839_ = v___y_3849_;
goto _start;
}
else
{
lean_dec_ref(v_k_3843_);
return v___x_3851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
uint8_t v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = 0;
v___x_3973_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3972_, v_var_3964_, v_a_3968_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4006_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_4006_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4006_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
if (lean_obj_tag(v_a_3974_) == 1)
{
lean_object* v_val_3978_; lean_object* v_params_3979_; lean_object* v_value_3980_; lean_object* v___x_3981_; 
lean_del_object(v___x_3976_);
v_val_3978_ = lean_ctor_get(v_a_3974_, 0);
lean_inc(v_val_3978_);
lean_dec_ref_known(v_a_3974_, 1);
v_params_3979_ = lean_ctor_get(v_val_3978_, 2);
lean_inc_ref(v_params_3979_);
v_value_3980_ = lean_ctor_get(v_val_3978_, 4);
lean_inc_ref(v_value_3980_);
lean_dec(v_val_3978_);
v___x_3981_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3979_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec_ref(v_params_3979_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3993_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_3993_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3993_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
uint8_t v___x_3986_; 
v___x_3986_ = lean_unbox(v_a_3982_);
lean_dec(v_a_3982_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3989_; 
lean_dec_ref(v_value_3980_);
v___x_3987_ = lean_box(0);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3987_);
v___x_3989_ = v___x_3984_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
else
{
lean_object* v___x_3991_; 
lean_del_object(v___x_3984_);
lean_inc_ref(v_value_3980_);
v___x_3991_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3980_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v___x_3992_; 
lean_dec_ref_known(v___x_3991_, 1);
v___x_3992_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3980_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
return v___x_3992_;
}
else
{
lean_dec_ref(v_value_3980_);
return v___x_3991_;
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_value_3980_);
v_a_3994_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3981_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3981_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
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
lean_object* v___x_4002_; lean_object* v___x_4004_; 
lean_dec(v_a_3974_);
v___x_4002_ = lean_box(0);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v___x_4002_);
v___x_4004_ = v___x_3976_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
v_a_4007_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3973_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3973_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
if (lean_obj_tag(v_arg_4015_) == 1)
{
lean_object* v_fvarId_4023_; lean_object* v___x_4024_; 
v_fvarId_4023_ = lean_ctor_get(v_arg_4015_, 0);
v___x_4024_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4023_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
return v___x_4024_;
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_box(0);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec(v_arg_4027_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_4036_, lean_object* v_i_4037_, lean_object* v_stop_4038_, lean_object* v_b_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
size_t v_i_boxed_4047_; size_t v_stop_boxed_4048_; lean_object* v_res_4049_; 
v_i_boxed_4047_ = lean_unbox_usize(v_i_4037_);
lean_dec(v_i_4037_);
v_stop_boxed_4048_ = lean_unbox_usize(v_stop_4038_);
lean_dec(v_stop_4038_);
v_res_4049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_4036_, v_i_boxed_4047_, v_stop_boxed_4048_, v_b_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec_ref(v_as_4036_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_4050_, lean_object* v_args_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_4050_, v_args_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_var_4060_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4069_, lean_object* v_as_4070_, lean_object* v_sz_4071_, lean_object* v_i_4072_, lean_object* v_b_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
size_t v_sz_boxed_4081_; size_t v_i_boxed_4082_; lean_object* v_res_4083_; 
v_sz_boxed_4081_ = lean_unbox_usize(v_sz_4071_);
lean_dec(v_sz_4071_);
v_i_boxed_4082_ = lean_unbox_usize(v_i_4072_);
lean_dec(v_i_4072_);
v_res_4083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4069_, v_as_4070_, v_sz_boxed_4081_, v_i_boxed_4082_, v_b_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec_ref(v_as_4070_);
lean_dec(v_a_4069_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4102_, lean_object* v_R_4103_, lean_object* v_a_4104_, lean_object* v_b_4105_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4104_, v_b_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4107_, size_t v_i_4108_, lean_object* v_bs_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4107_, v_i_4108_, v_bs_4109_, v___y_4110_, v___y_4111_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4118_, lean_object* v_i_4119_, lean_object* v_bs_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
size_t v_sz_boxed_4128_; size_t v_i_boxed_4129_; lean_object* v_res_4130_; 
v_sz_boxed_4128_ = lean_unbox_usize(v_sz_4118_);
lean_dec(v_sz_4118_);
v_i_boxed_4129_ = lean_unbox_usize(v_i_4119_);
lean_dec(v_i_4119_);
v_res_4130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4128_, v_i_boxed_4129_, v_bs_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4131_, size_t v_i_4132_, size_t v_stop_4133_, lean_object* v_b_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4131_, v_i_4132_, v_stop_4133_, v_b_4134_, v___y_4135_, v___y_4136_, v___y_4140_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4143_, lean_object* v_i_4144_, lean_object* v_stop_4145_, lean_object* v_b_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
size_t v_i_boxed_4154_; size_t v_stop_boxed_4155_; lean_object* v_res_4156_; 
v_i_boxed_4154_ = lean_unbox_usize(v_i_4144_);
lean_dec(v_i_4144_);
v_stop_boxed_4155_ = lean_unbox_usize(v_stop_4145_);
lean_dec(v_stop_4145_);
v_res_4156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4143_, v_i_boxed_4154_, v_stop_boxed_4155_, v_b_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec_ref(v_as_4143_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4157_, size_t v_i_4158_, size_t v_stop_4159_, lean_object* v_b_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4157_, v_i_4158_, v_stop_4159_, v_b_4160_, v___y_4161_, v___y_4162_, v___y_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4169_, lean_object* v_i_4170_, lean_object* v_stop_4171_, lean_object* v_b_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
size_t v_i_boxed_4180_; size_t v_stop_boxed_4181_; lean_object* v_res_4182_; 
v_i_boxed_4180_ = lean_unbox_usize(v_i_4170_);
lean_dec(v_i_4170_);
v_stop_boxed_4181_ = lean_unbox_usize(v_stop_4171_);
lean_dec(v_stop_4171_);
v_res_4182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4169_, v_i_boxed_4180_, v_stop_boxed_4181_, v_b_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec_ref(v_as_4169_);
return v_res_4182_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = lean_unsigned_to_nat(32u);
v___x_4184_ = lean_mk_empty_array_with_capacity(v___x_4183_);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4186_ = ((size_t)5ULL);
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = lean_unsigned_to_nat(32u);
v___x_4189_ = lean_mk_empty_array_with_capacity(v___x_4188_);
v___x_4190_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4191_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v___x_4189_);
lean_ctor_set(v___x_4191_, 2, v___x_4187_);
lean_ctor_set(v___x_4191_, 3, v___x_4187_);
lean_ctor_set_usize(v___x_4191_, 4, v___x_4186_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v_traceState_4195_; lean_object* v_traces_4196_; lean_object* v___x_4197_; lean_object* v_traceState_4198_; lean_object* v_env_4199_; lean_object* v_nextMacroScope_4200_; lean_object* v_ngen_4201_; lean_object* v_auxDeclNGen_4202_; lean_object* v_cache_4203_; lean_object* v_recordedDeps_4204_; lean_object* v_messages_4205_; lean_object* v_infoState_4206_; lean_object* v_snapshotTasks_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4226_; 
v___x_4194_ = lean_st_ref_get(v___y_4192_);
v_traceState_4195_ = lean_ctor_get(v___x_4194_, 4);
lean_inc_ref(v_traceState_4195_);
lean_dec(v___x_4194_);
v_traces_4196_ = lean_ctor_get(v_traceState_4195_, 0);
lean_inc_ref(v_traces_4196_);
lean_dec_ref(v_traceState_4195_);
v___x_4197_ = lean_st_ref_take(v___y_4192_);
v_traceState_4198_ = lean_ctor_get(v___x_4197_, 4);
v_env_4199_ = lean_ctor_get(v___x_4197_, 0);
v_nextMacroScope_4200_ = lean_ctor_get(v___x_4197_, 1);
v_ngen_4201_ = lean_ctor_get(v___x_4197_, 2);
v_auxDeclNGen_4202_ = lean_ctor_get(v___x_4197_, 3);
v_cache_4203_ = lean_ctor_get(v___x_4197_, 5);
v_recordedDeps_4204_ = lean_ctor_get(v___x_4197_, 6);
v_messages_4205_ = lean_ctor_get(v___x_4197_, 7);
v_infoState_4206_ = lean_ctor_get(v___x_4197_, 8);
v_snapshotTasks_4207_ = lean_ctor_get(v___x_4197_, 9);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4209_ = v___x_4197_;
v_isShared_4210_ = v_isSharedCheck_4226_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_snapshotTasks_4207_);
lean_inc(v_infoState_4206_);
lean_inc(v_messages_4205_);
lean_inc(v_recordedDeps_4204_);
lean_inc(v_cache_4203_);
lean_inc(v_traceState_4198_);
lean_inc(v_auxDeclNGen_4202_);
lean_inc(v_ngen_4201_);
lean_inc(v_nextMacroScope_4200_);
lean_inc(v_env_4199_);
lean_dec(v___x_4197_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4226_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
uint64_t v_tid_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4224_; 
v_tid_4211_ = lean_ctor_get_uint64(v_traceState_4198_, sizeof(void*)*1);
v_isSharedCheck_4224_ = !lean_is_exclusive(v_traceState_4198_);
if (v_isSharedCheck_4224_ == 0)
{
lean_object* v_unused_4225_; 
v_unused_4225_ = lean_ctor_get(v_traceState_4198_, 0);
lean_dec(v_unused_4225_);
v___x_4213_ = v_traceState_4198_;
v_isShared_4214_ = v_isSharedCheck_4224_;
goto v_resetjp_4212_;
}
else
{
lean_dec(v_traceState_4198_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4224_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4215_);
lean_ctor_set_uint64(v_reuseFailAlloc_4223_, sizeof(void*)*1, v_tid_4211_);
v___x_4217_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4219_; 
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 4, v___x_4217_);
v___x_4219_ = v___x_4209_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_env_4199_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v_nextMacroScope_4200_);
lean_ctor_set(v_reuseFailAlloc_4222_, 2, v_ngen_4201_);
lean_ctor_set(v_reuseFailAlloc_4222_, 3, v_auxDeclNGen_4202_);
lean_ctor_set(v_reuseFailAlloc_4222_, 4, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4222_, 5, v_cache_4203_);
lean_ctor_set(v_reuseFailAlloc_4222_, 6, v_recordedDeps_4204_);
lean_ctor_set(v_reuseFailAlloc_4222_, 7, v_messages_4205_);
lean_ctor_set(v_reuseFailAlloc_4222_, 8, v_infoState_4206_);
lean_ctor_set(v_reuseFailAlloc_4222_, 9, v_snapshotTasks_4207_);
v___x_4219_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = lean_st_ref_put(v___y_4192_, v___x_4219_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_traces_4196_);
return v___x_4221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4227_);
lean_dec(v___y_4227_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4235_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
return v_res_4245_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4246_, lean_object* v_opt_4247_){
_start:
{
lean_object* v_name_4248_; lean_object* v_defValue_4249_; lean_object* v_map_4250_; lean_object* v___x_4251_; 
v_name_4248_ = lean_ctor_get(v_opt_4247_, 0);
v_defValue_4249_ = lean_ctor_get(v_opt_4247_, 1);
v_map_4250_ = lean_ctor_get(v_opts_4246_, 0);
v___x_4251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4250_, v_name_4248_);
if (lean_obj_tag(v___x_4251_) == 0)
{
uint8_t v___x_4252_; 
v___x_4252_ = lean_unbox(v_defValue_4249_);
return v___x_4252_;
}
else
{
lean_object* v_val_4253_; 
v_val_4253_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_val_4253_);
lean_dec_ref_known(v___x_4251_, 1);
if (lean_obj_tag(v_val_4253_) == 1)
{
uint8_t v_v_4254_; 
v_v_4254_ = lean_ctor_get_uint8(v_val_4253_, 0);
lean_dec_ref_known(v_val_4253_, 0);
return v_v_4254_;
}
else
{
uint8_t v___x_4255_; 
lean_dec(v_val_4253_);
v___x_4255_ = lean_unbox(v_defValue_4249_);
return v___x_4255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4256_, lean_object* v_opt_4257_){
_start:
{
uint8_t v_res_4258_; lean_object* v_r_4259_; 
v_res_4258_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4256_, v_opt_4257_);
lean_dec_ref(v_opt_4257_);
lean_dec_ref(v_opts_4256_);
v_r_4259_ = lean_box(v_res_4258_);
return v_r_4259_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4261_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4262_ = l_Lean_stringToMessageData(v___x_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4263_, lean_object* v_x_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4272_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4273_ = l_Lean_MessageData_ofName(v_name_4263_);
v___x_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4276_, v_x_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v_x_4277_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4286_, lean_object* v_opt_4287_){
_start:
{
lean_object* v_name_4288_; lean_object* v_defValue_4289_; lean_object* v_map_4290_; lean_object* v___x_4291_; 
v_name_4288_ = lean_ctor_get(v_opt_4287_, 0);
v_defValue_4289_ = lean_ctor_get(v_opt_4287_, 1);
v_map_4290_ = lean_ctor_get(v_opts_4286_, 0);
v___x_4291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4290_, v_name_4288_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_inc(v_defValue_4289_);
return v_defValue_4289_;
}
else
{
lean_object* v_val_4292_; 
v_val_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_val_4292_);
lean_dec_ref_known(v___x_4291_, 1);
if (lean_obj_tag(v_val_4292_) == 3)
{
lean_object* v_v_4293_; 
v_v_4293_ = lean_ctor_get(v_val_4292_, 0);
lean_inc(v_v_4293_);
lean_dec_ref_known(v_val_4292_, 1);
return v_v_4293_;
}
else
{
lean_dec(v_val_4292_);
lean_inc(v_defValue_4289_);
return v_defValue_4289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4294_, lean_object* v_opt_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4294_, v_opt_4295_);
lean_dec_ref(v_opt_4295_);
lean_dec_ref(v_opts_4294_);
return v_res_4296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4297_){
_start:
{
if (lean_obj_tag(v_e_4297_) == 0)
{
uint8_t v___x_4298_; 
v___x_4298_ = 2;
return v___x_4298_;
}
else
{
uint8_t v___x_4299_; 
v___x_4299_ = 0;
return v___x_4299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4300_){
_start:
{
uint8_t v_res_4301_; lean_object* v_r_4302_; 
v_res_4301_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4300_);
lean_dec_ref(v_e_4300_);
v_r_4302_ = lean_box(v_res_4301_);
return v_r_4302_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4303_){
_start:
{
if (lean_obj_tag(v_x_4303_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_a_4305_ = lean_ctor_get(v_x_4303_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_x_4303_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v_x_4303_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v_x_4303_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set_tag(v___x_4307_, 1);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
v_a_4313_ = lean_ctor_get(v_x_4303_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_x_4303_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v_x_4303_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v_x_4303_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set_tag(v___x_4315_, 0);
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4324_, size_t v_i_4325_, lean_object* v_bs_4326_){
_start:
{
uint8_t v___x_4327_; 
v___x_4327_ = lean_usize_dec_lt(v_i_4325_, v_sz_4324_);
if (v___x_4327_ == 0)
{
return v_bs_4326_;
}
else
{
lean_object* v_v_4328_; lean_object* v_msg_4329_; lean_object* v___x_4330_; lean_object* v_bs_x27_4331_; size_t v___x_4332_; size_t v___x_4333_; lean_object* v___x_4334_; 
v_v_4328_ = lean_array_uget_borrowed(v_bs_4326_, v_i_4325_);
v_msg_4329_ = lean_ctor_get(v_v_4328_, 1);
lean_inc_ref(v_msg_4329_);
v___x_4330_ = lean_unsigned_to_nat(0u);
v_bs_x27_4331_ = lean_array_uset(v_bs_4326_, v_i_4325_, v___x_4330_);
v___x_4332_ = ((size_t)1ULL);
v___x_4333_ = lean_usize_add(v_i_4325_, v___x_4332_);
v___x_4334_ = lean_array_uset(v_bs_x27_4331_, v_i_4325_, v_msg_4329_);
v_i_4325_ = v___x_4333_;
v_bs_4326_ = v___x_4334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4336_, lean_object* v_i_4337_, lean_object* v_bs_4338_){
_start:
{
size_t v_sz_boxed_4339_; size_t v_i_boxed_4340_; lean_object* v_res_4341_; 
v_sz_boxed_4339_ = lean_unbox_usize(v_sz_4336_);
lean_dec(v_sz_4336_);
v_i_boxed_4340_ = lean_unbox_usize(v_i_4337_);
lean_dec(v_i_4337_);
v_res_4341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4339_, v_i_boxed_4340_, v_bs_4338_);
return v_res_4341_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
return v___x_4343_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4344_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4345_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
lean_ctor_set(v___x_4346_, 2, v___x_4345_);
lean_ctor_set(v___x_4346_, 3, v___x_4345_);
lean_ctor_set(v___x_4346_, 4, v___x_4344_);
lean_ctor_set(v___x_4346_, 5, v___x_4344_);
lean_ctor_set(v___x_4346_, 6, v___x_4344_);
lean_ctor_set(v___x_4346_, 7, v___x_4344_);
lean_ctor_set(v___x_4346_, 8, v___x_4344_);
lean_ctor_set(v___x_4346_, 9, v___x_4344_);
lean_ctor_set(v___x_4346_, 10, v___x_4344_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4347_, lean_object* v_data_4348_, lean_object* v_ref_4349_, lean_object* v_msg_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v_toCold_4356_; lean_object* v_currRecDepth_4357_; lean_object* v_ref_4358_; uint16_t v_optionFlags_4359_; uint8_t v_suppressElabErrors_4360_; uint8_t v_isRecordingDeps_4361_; lean_object* v_ref_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v_traceState_4365_; lean_object* v_traces_4366_; lean_object* v___x_4367_; size_t v_sz_4368_; size_t v___x_4369_; lean_object* v___x_4370_; lean_object* v_msg_4371_; lean_object* v___x_4372_; lean_object* v_env_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v_toCold_4356_ = lean_ctor_get(v___y_4353_, 0);
v_currRecDepth_4357_ = lean_ctor_get(v___y_4353_, 1);
v_ref_4358_ = lean_ctor_get(v___y_4353_, 2);
v_optionFlags_4359_ = lean_ctor_get_uint16(v___y_4353_, sizeof(void*)*3);
v_suppressElabErrors_4360_ = lean_ctor_get_uint8(v___y_4353_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4361_ = lean_ctor_get_uint8(v___y_4353_, sizeof(void*)*3 + 3);
v_ref_4362_ = l_Lean_replaceRef(v_ref_4349_, v_ref_4358_);
lean_inc(v_currRecDepth_4357_);
lean_inc_ref(v_toCold_4356_);
v___x_4363_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4363_, 0, v_toCold_4356_);
lean_ctor_set(v___x_4363_, 1, v_currRecDepth_4357_);
lean_ctor_set(v___x_4363_, 2, v_ref_4362_);
lean_ctor_set_uint16(v___x_4363_, sizeof(void*)*3, v_optionFlags_4359_);
lean_ctor_set_uint8(v___x_4363_, sizeof(void*)*3 + 2, v_suppressElabErrors_4360_);
lean_ctor_set_uint8(v___x_4363_, sizeof(void*)*3 + 3, v_isRecordingDeps_4361_);
v___x_4364_ = lean_st_ref_get(v___y_4354_);
v_traceState_4365_ = lean_ctor_get(v___x_4364_, 4);
lean_inc_ref(v_traceState_4365_);
lean_dec(v___x_4364_);
v_traces_4366_ = lean_ctor_get(v_traceState_4365_, 0);
lean_inc_ref(v_traces_4366_);
lean_dec_ref(v_traceState_4365_);
v___x_4367_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4366_);
lean_dec_ref(v_traces_4366_);
v_sz_4368_ = lean_array_size(v___x_4367_);
v___x_4369_ = ((size_t)0ULL);
v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4368_, v___x_4369_, v___x_4367_);
v_msg_4371_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4371_, 0, v_data_4348_);
lean_ctor_set(v_msg_4371_, 1, v_msg_4350_);
lean_ctor_set(v_msg_4371_, 2, v___x_4370_);
v___x_4372_ = lean_st_ref_get(v___y_4354_);
v_env_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc_ref(v_env_4373_);
lean_dec(v___x_4372_);
v___x_4374_ = lean_st_ref_get(v___y_4352_);
v___x_4375_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4351_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4428_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4428_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4428_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v_lctx_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4426_; 
v_lctx_4380_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v___x_4374_, 1);
lean_dec(v_unused_4427_);
v___x_4382_ = v___x_4374_;
v_isShared_4383_ = v_isSharedCheck_4426_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_lctx_4380_);
lean_dec(v___x_4374_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4426_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
uint8_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4384_ = lean_unbox(v_a_4376_);
lean_dec(v_a_4376_);
v___x_4385_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4380_, v___x_4384_);
lean_dec_ref(v_lctx_4380_);
v___x_4386_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___x_4363_);
lean_dec_ref_known(v___x_4363_, 3);
v___x_4387_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4388_, 0, v_env_4373_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
lean_ctor_set(v___x_4388_, 2, v___x_4385_);
lean_ctor_set(v___x_4388_, 3, v___x_4386_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set_tag(v___x_4382_, 3);
lean_ctor_set(v___x_4382_, 1, v_msg_4371_);
lean_ctor_set(v___x_4382_, 0, v___x_4388_);
v___x_4390_ = v___x_4382_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_msg_4371_);
v___x_4390_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v_traceState_4392_; lean_object* v_env_4393_; lean_object* v_nextMacroScope_4394_; lean_object* v_ngen_4395_; lean_object* v_auxDeclNGen_4396_; lean_object* v_cache_4397_; lean_object* v_recordedDeps_4398_; lean_object* v_messages_4399_; lean_object* v_infoState_4400_; lean_object* v_snapshotTasks_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4424_; 
v___x_4391_ = lean_st_ref_take(v___y_4354_);
v_traceState_4392_ = lean_ctor_get(v___x_4391_, 4);
v_env_4393_ = lean_ctor_get(v___x_4391_, 0);
v_nextMacroScope_4394_ = lean_ctor_get(v___x_4391_, 1);
v_ngen_4395_ = lean_ctor_get(v___x_4391_, 2);
v_auxDeclNGen_4396_ = lean_ctor_get(v___x_4391_, 3);
v_cache_4397_ = lean_ctor_get(v___x_4391_, 5);
v_recordedDeps_4398_ = lean_ctor_get(v___x_4391_, 6);
v_messages_4399_ = lean_ctor_get(v___x_4391_, 7);
v_infoState_4400_ = lean_ctor_get(v___x_4391_, 8);
v_snapshotTasks_4401_ = lean_ctor_get(v___x_4391_, 9);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4403_ = v___x_4391_;
v_isShared_4404_ = v_isSharedCheck_4424_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_snapshotTasks_4401_);
lean_inc(v_infoState_4400_);
lean_inc(v_messages_4399_);
lean_inc(v_recordedDeps_4398_);
lean_inc(v_cache_4397_);
lean_inc(v_traceState_4392_);
lean_inc(v_auxDeclNGen_4396_);
lean_inc(v_ngen_4395_);
lean_inc(v_nextMacroScope_4394_);
lean_inc(v_env_4393_);
lean_dec(v___x_4391_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4424_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
uint64_t v_tid_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4422_; 
v_tid_4405_ = lean_ctor_get_uint64(v_traceState_4392_, sizeof(void*)*1);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_traceState_4392_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; 
v_unused_4423_ = lean_ctor_get(v_traceState_4392_, 0);
lean_dec(v_unused_4423_);
v___x_4407_ = v_traceState_4392_;
v_isShared_4408_ = v_isSharedCheck_4422_;
goto v_resetjp_4406_;
}
else
{
lean_dec(v_traceState_4392_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4422_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; 
v___x_4409_ = lean_box(0);
v___x_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4410_, 0, v_ref_4349_);
lean_ctor_set(v___x_4410_, 1, v___x_4390_);
v___x_4411_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4347_, v___x_4410_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4411_);
v___x_4413_ = v___x_4407_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4411_);
lean_ctor_set_uint64(v_reuseFailAlloc_4421_, sizeof(void*)*1, v_tid_4405_);
v___x_4413_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4415_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 4, v___x_4413_);
v___x_4415_ = v___x_4403_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_env_4393_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_nextMacroScope_4394_);
lean_ctor_set(v_reuseFailAlloc_4420_, 2, v_ngen_4395_);
lean_ctor_set(v_reuseFailAlloc_4420_, 3, v_auxDeclNGen_4396_);
lean_ctor_set(v_reuseFailAlloc_4420_, 4, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4420_, 5, v_cache_4397_);
lean_ctor_set(v_reuseFailAlloc_4420_, 6, v_recordedDeps_4398_);
lean_ctor_set(v_reuseFailAlloc_4420_, 7, v_messages_4399_);
lean_ctor_set(v_reuseFailAlloc_4420_, 8, v_infoState_4400_);
lean_ctor_set(v_reuseFailAlloc_4420_, 9, v_snapshotTasks_4401_);
v___x_4415_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4416_ = lean_st_ref_put(v___y_4354_, v___x_4415_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4409_);
v___x_4418_ = v___x_4378_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4409_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
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
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v___x_4374_);
lean_dec_ref(v_env_4373_);
lean_dec_ref_known(v_msg_4371_, 3);
lean_dec_ref_known(v___x_4363_, 3);
lean_dec(v_ref_4349_);
lean_dec_ref(v_oldTraces_4347_);
v_a_4429_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4375_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4375_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4437_, lean_object* v_data_4438_, lean_object* v_ref_4439_, lean_object* v_msg_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4437_, v_data_4438_, v_ref_4439_, v_msg_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
return v_res_4446_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4447_; double v___x_4448_; 
v___x_4447_ = lean_unsigned_to_nat(0u);
v___x_4448_ = lean_float_of_nat(v___x_4447_);
return v___x_4448_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4451_ = l_Lean_stringToMessageData(v___x_4450_);
return v___x_4451_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4452_; double v___x_4453_; 
v___x_4452_ = lean_unsigned_to_nat(1000u);
v___x_4453_ = lean_float_of_nat(v___x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4454_, uint8_t v_collapsed_4455_, lean_object* v_tag_4456_, lean_object* v_opts_4457_, uint8_t v_clsEnabled_4458_, lean_object* v_oldTraces_4459_, lean_object* v_msg_4460_, lean_object* v_resStartStop_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_fst_4469_; lean_object* v_snd_4470_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v_data_4474_; lean_object* v_fst_4477_; lean_object* v_snd_4478_; lean_object* v___x_4479_; uint8_t v___x_4480_; lean_object* v___y_4482_; lean_object* v_a_4483_; uint8_t v___y_4498_; double v___y_4530_; 
v_fst_4469_ = lean_ctor_get(v_resStartStop_4461_, 0);
lean_inc(v_fst_4469_);
v_snd_4470_ = lean_ctor_get(v_resStartStop_4461_, 1);
lean_inc(v_snd_4470_);
lean_dec_ref(v_resStartStop_4461_);
v_fst_4477_ = lean_ctor_get(v_snd_4470_, 0);
lean_inc(v_fst_4477_);
v_snd_4478_ = lean_ctor_get(v_snd_4470_, 1);
lean_inc(v_snd_4478_);
lean_dec(v_snd_4470_);
v___x_4479_ = l_Lean_trace_profiler;
v___x_4480_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4457_, v___x_4479_);
if (v___x_4480_ == 0)
{
v___y_4498_ = v___x_4480_;
goto v___jp_4497_;
}
else
{
lean_object* v___x_4535_; uint8_t v___x_4536_; 
v___x_4535_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4536_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4457_, v___x_4535_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; lean_object* v___x_4538_; double v___x_4539_; double v___x_4540_; double v___x_4541_; 
v___x_4537_ = l_Lean_trace_profiler_threshold;
v___x_4538_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4457_, v___x_4537_);
v___x_4539_ = lean_float_of_nat(v___x_4538_);
v___x_4540_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4541_ = lean_float_div(v___x_4539_, v___x_4540_);
v___y_4530_ = v___x_4541_;
goto v___jp_4529_;
}
else
{
lean_object* v___x_4542_; lean_object* v___x_4543_; double v___x_4544_; 
v___x_4542_ = l_Lean_trace_profiler_threshold;
v___x_4543_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4457_, v___x_4542_);
v___x_4544_ = lean_float_of_nat(v___x_4543_);
v___y_4530_ = v___x_4544_;
goto v___jp_4529_;
}
}
v___jp_4471_:
{
lean_object* v___x_4475_; 
lean_inc(v___y_4472_);
v___x_4475_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4459_, v_data_4474_, v___y_4472_, v___y_4473_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v___x_4476_; 
lean_dec_ref_known(v___x_4475_, 1);
v___x_4476_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4469_);
return v___x_4476_;
}
else
{
lean_dec(v_fst_4469_);
return v___x_4475_;
}
}
v___jp_4481_:
{
uint8_t v_result_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; double v___x_4487_; lean_object* v_data_4488_; 
v_result_4484_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4469_);
v___x_4485_ = lean_box(v_result_4484_);
v___x_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
v___x_4487_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4456_);
lean_inc_ref(v___x_4486_);
lean_inc(v_cls_4454_);
v_data_4488_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4488_, 0, v_cls_4454_);
lean_ctor_set(v_data_4488_, 1, v___x_4486_);
lean_ctor_set(v_data_4488_, 2, v_tag_4456_);
lean_ctor_set_float(v_data_4488_, sizeof(void*)*3, v___x_4487_);
lean_ctor_set_float(v_data_4488_, sizeof(void*)*3 + 8, v___x_4487_);
lean_ctor_set_uint8(v_data_4488_, sizeof(void*)*3 + 16, v_collapsed_4455_);
if (v___x_4480_ == 0)
{
lean_dec_ref_known(v___x_4486_, 1);
lean_dec(v_snd_4478_);
lean_dec(v_fst_4477_);
lean_dec_ref(v_tag_4456_);
lean_dec(v_cls_4454_);
v___y_4472_ = v___y_4482_;
v___y_4473_ = v_a_4483_;
v_data_4474_ = v_data_4488_;
goto v___jp_4471_;
}
else
{
lean_object* v_data_4489_; double v___x_4490_; double v___x_4491_; 
lean_dec_ref_known(v_data_4488_, 3);
v_data_4489_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4489_, 0, v_cls_4454_);
lean_ctor_set(v_data_4489_, 1, v___x_4486_);
lean_ctor_set(v_data_4489_, 2, v_tag_4456_);
v___x_4490_ = lean_unbox_float(v_fst_4477_);
lean_dec(v_fst_4477_);
lean_ctor_set_float(v_data_4489_, sizeof(void*)*3, v___x_4490_);
v___x_4491_ = lean_unbox_float(v_snd_4478_);
lean_dec(v_snd_4478_);
lean_ctor_set_float(v_data_4489_, sizeof(void*)*3 + 8, v___x_4491_);
lean_ctor_set_uint8(v_data_4489_, sizeof(void*)*3 + 16, v_collapsed_4455_);
v___y_4472_ = v___y_4482_;
v___y_4473_ = v_a_4483_;
v_data_4474_ = v_data_4489_;
goto v___jp_4471_;
}
}
v___jp_4492_:
{
lean_object* v_ref_4493_; lean_object* v___x_4494_; 
v_ref_4493_ = lean_ctor_get(v___y_4466_, 2);
lean_inc(v___y_4467_);
lean_inc_ref(v___y_4466_);
lean_inc(v___y_4465_);
lean_inc_ref(v___y_4464_);
lean_inc(v___y_4463_);
lean_inc_ref(v___y_4462_);
lean_inc(v_fst_4469_);
v___x_4494_ = lean_apply_8(v_msg_4460_, v_fst_4469_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, lean_box(0));
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4494_, 1);
v___y_4482_ = v_ref_4493_;
v_a_4483_ = v_a_4495_;
goto v___jp_4481_;
}
else
{
lean_object* v___x_4496_; 
lean_dec_ref_known(v___x_4494_, 1);
v___x_4496_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4482_ = v_ref_4493_;
v_a_4483_ = v___x_4496_;
goto v___jp_4481_;
}
}
v___jp_4497_:
{
if (v_clsEnabled_4458_ == 0)
{
if (v___y_4498_ == 0)
{
lean_object* v___x_4499_; lean_object* v_traceState_4500_; lean_object* v_env_4501_; lean_object* v_nextMacroScope_4502_; lean_object* v_ngen_4503_; lean_object* v_auxDeclNGen_4504_; lean_object* v_cache_4505_; lean_object* v_recordedDeps_4506_; lean_object* v_messages_4507_; lean_object* v_infoState_4508_; lean_object* v_snapshotTasks_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_snd_4478_);
lean_dec(v_fst_4477_);
lean_dec_ref(v_msg_4460_);
lean_dec_ref(v_tag_4456_);
lean_dec(v_cls_4454_);
v___x_4499_ = lean_st_ref_take(v___y_4467_);
v_traceState_4500_ = lean_ctor_get(v___x_4499_, 4);
v_env_4501_ = lean_ctor_get(v___x_4499_, 0);
v_nextMacroScope_4502_ = lean_ctor_get(v___x_4499_, 1);
v_ngen_4503_ = lean_ctor_get(v___x_4499_, 2);
v_auxDeclNGen_4504_ = lean_ctor_get(v___x_4499_, 3);
v_cache_4505_ = lean_ctor_get(v___x_4499_, 5);
v_recordedDeps_4506_ = lean_ctor_get(v___x_4499_, 6);
v_messages_4507_ = lean_ctor_get(v___x_4499_, 7);
v_infoState_4508_ = lean_ctor_get(v___x_4499_, 8);
v_snapshotTasks_4509_ = lean_ctor_get(v___x_4499_, 9);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4511_ = v___x_4499_;
v_isShared_4512_ = v_isSharedCheck_4528_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_snapshotTasks_4509_);
lean_inc(v_infoState_4508_);
lean_inc(v_messages_4507_);
lean_inc(v_recordedDeps_4506_);
lean_inc(v_cache_4505_);
lean_inc(v_traceState_4500_);
lean_inc(v_auxDeclNGen_4504_);
lean_inc(v_ngen_4503_);
lean_inc(v_nextMacroScope_4502_);
lean_inc(v_env_4501_);
lean_dec(v___x_4499_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4528_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
uint64_t v_tid_4513_; lean_object* v_traces_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4527_; 
v_tid_4513_ = lean_ctor_get_uint64(v_traceState_4500_, sizeof(void*)*1);
v_traces_4514_ = lean_ctor_get(v_traceState_4500_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_traceState_4500_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4516_ = v_traceState_4500_;
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_traces_4514_);
lean_dec(v_traceState_4500_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; lean_object* v___x_4520_; 
v___x_4518_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4459_, v_traces_4514_);
lean_dec_ref(v_traces_4514_);
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4518_);
v___x_4520_ = v___x_4516_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4518_);
lean_ctor_set_uint64(v_reuseFailAlloc_4526_, sizeof(void*)*1, v_tid_4513_);
v___x_4520_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4522_; 
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 4, v___x_4520_);
v___x_4522_ = v___x_4511_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_env_4501_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_nextMacroScope_4502_);
lean_ctor_set(v_reuseFailAlloc_4525_, 2, v_ngen_4503_);
lean_ctor_set(v_reuseFailAlloc_4525_, 3, v_auxDeclNGen_4504_);
lean_ctor_set(v_reuseFailAlloc_4525_, 4, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4525_, 5, v_cache_4505_);
lean_ctor_set(v_reuseFailAlloc_4525_, 6, v_recordedDeps_4506_);
lean_ctor_set(v_reuseFailAlloc_4525_, 7, v_messages_4507_);
lean_ctor_set(v_reuseFailAlloc_4525_, 8, v_infoState_4508_);
lean_ctor_set(v_reuseFailAlloc_4525_, 9, v_snapshotTasks_4509_);
v___x_4522_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = lean_st_ref_put(v___y_4467_, v___x_4522_);
v___x_4524_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4469_);
return v___x_4524_;
}
}
}
}
}
else
{
goto v___jp_4492_;
}
}
else
{
goto v___jp_4492_;
}
}
v___jp_4529_:
{
double v___x_4531_; double v___x_4532_; double v___x_4533_; uint8_t v___x_4534_; 
v___x_4531_ = lean_unbox_float(v_snd_4478_);
v___x_4532_ = lean_unbox_float(v_fst_4477_);
v___x_4533_ = lean_float_sub(v___x_4531_, v___x_4532_);
v___x_4534_ = lean_float_decLt(v___y_4530_, v___x_4533_);
v___y_4498_ = v___x_4534_;
goto v___jp_4497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4545_, lean_object* v_collapsed_4546_, lean_object* v_tag_4547_, lean_object* v_opts_4548_, lean_object* v_clsEnabled_4549_, lean_object* v_oldTraces_4550_, lean_object* v_msg_4551_, lean_object* v_resStartStop_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
uint8_t v_collapsed_boxed_4560_; uint8_t v_clsEnabled_boxed_4561_; lean_object* v_res_4562_; 
v_collapsed_boxed_4560_ = lean_unbox(v_collapsed_4546_);
v_clsEnabled_boxed_4561_ = lean_unbox(v_clsEnabled_4549_);
v_res_4562_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4545_, v_collapsed_boxed_4560_, v_tag_4547_, v_opts_4548_, v_clsEnabled_boxed_4561_, v_oldTraces_4550_, v_msg_4551_, v_resStartStop_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec_ref(v_opts_4548_);
return v_res_4562_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4566_; double v___x_4567_; 
v___x_4566_ = lean_unsigned_to_nat(1000000000u);
v___x_4567_ = lean_float_of_nat(v___x_4566_);
return v___x_4567_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4576_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4577_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4578_ = l_Lean_Name_append(v___x_4577_, v___x_4576_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4579_, lean_object* v___x_4580_, lean_object* v_a_4581_, lean_object* v_b_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_a_4591_; uint8_t v___x_4595_; 
v___x_4595_ = lean_nat_dec_lt(v_a_4581_, v_upperBound_4579_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; 
lean_dec(v_a_4581_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v_b_4582_);
return v___x_4596_;
}
else
{
lean_object* v___x_4597_; lean_object* v_toSignature_4598_; lean_object* v_value_4599_; lean_object* v_name_4600_; lean_object* v_params_4601_; uint8_t v_safe_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
lean_dec_ref(v_b_4582_);
v___x_4597_ = lean_array_fget_borrowed(v___x_4580_, v_a_4581_);
v_toSignature_4598_ = lean_ctor_get(v___x_4597_, 0);
v_value_4599_ = lean_ctor_get(v___x_4597_, 1);
v_name_4600_ = lean_ctor_get(v_toSignature_4598_, 0);
v_params_4601_ = lean_ctor_get(v_toSignature_4598_, 3);
v_safe_4602_ = lean_ctor_get_uint8(v_toSignature_4598_, sizeof(void*)*4);
v___x_4603_ = lean_box(0);
v___x_4604_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4602_ == 0)
{
v_a_4591_ = v___x_4604_;
goto v___jp_4590_;
}
else
{
lean_object* v___f_4605_; lean_object* v___x_4606_; 
lean_inc(v_name_4600_);
v___f_4605_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4605_, 0, v_name_4600_);
v___x_4606_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4581_, v___y_4584_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___y_4609_; lean_object* v_decls_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; uint8_t v___y_4649_; lean_object* v_a_4650_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; uint8_t v___y_4668_; lean_object* v_a_4669_; lean_object* v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; uint8_t v___y_4683_; lean_object* v___y_4750_; uint8_t v___x_4759_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref_known(v___x_4606_, 1);
v_decls_4639_ = lean_ctor_get(v___y_4583_, 0);
v___x_4640_ = lean_unsigned_to_nat(0u);
v___x_4641_ = lean_array_get_size(v_params_4601_);
lean_inc(v_a_4581_);
lean_inc_ref(v_decls_4639_);
v___x_4642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4642_, 0, v_decls_4639_);
lean_ctor_set(v___x_4642_, 1, v_a_4581_);
v___x_4759_ = lean_nat_dec_lt(v___x_4640_, v___x_4641_);
if (v___x_4759_ == 0)
{
goto v___jp_4732_;
}
else
{
uint8_t v___x_4760_; 
v___x_4760_ = lean_nat_dec_le(v___x_4641_, v___x_4641_);
if (v___x_4760_ == 0)
{
if (v___x_4759_ == 0)
{
goto v___jp_4732_;
}
else
{
size_t v___x_4761_; size_t v___x_4762_; lean_object* v___x_4763_; 
v___x_4761_ = ((size_t)0ULL);
v___x_4762_ = lean_usize_of_nat(v___x_4641_);
v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4601_, v___x_4761_, v___x_4762_, v___x_4603_, v___x_4642_, v___y_4584_, v___y_4588_);
v___y_4750_ = v___x_4763_;
goto v___jp_4749_;
}
}
else
{
size_t v___x_4764_; size_t v___x_4765_; lean_object* v___x_4766_; 
v___x_4764_ = ((size_t)0ULL);
v___x_4765_ = lean_usize_of_nat(v___x_4641_);
v___x_4766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4601_, v___x_4764_, v___x_4765_, v___x_4603_, v___x_4642_, v___y_4584_, v___y_4588_);
v___y_4750_ = v___x_4766_;
goto v___jp_4749_;
}
}
v___jp_4608_:
{
if (lean_obj_tag(v___y_4609_) == 0)
{
lean_object* v___x_4610_; 
lean_dec_ref_known(v___y_4609_, 1);
v___x_4610_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4581_, v___y_4584_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4622_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4622_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4622_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
uint8_t v___x_4615_; 
v___x_4615_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4607_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec(v_a_4607_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
lean_dec(v_a_4581_);
v___x_4616_ = lean_box(v___x_4595_);
v___x_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
v___x_4618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
lean_ctor_set(v___x_4618_, 1, v___x_4603_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4618_);
v___x_4620_ = v___x_4613_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
else
{
lean_del_object(v___x_4613_);
v_a_4591_ = v___x_4604_;
goto v___jp_4590_;
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec(v_a_4607_);
lean_dec(v_a_4581_);
v_a_4623_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4610_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4610_);
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
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec(v_a_4607_);
lean_dec(v_a_4581_);
v_a_4631_ = lean_ctor_get(v___y_4609_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___y_4609_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___y_4609_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___y_4609_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
v___jp_4643_:
{
lean_object* v___x_4651_; double v___x_4652_; double v___x_4653_; double v___x_4654_; double v___x_4655_; double v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4651_ = lean_io_mono_nanos_now();
v___x_4652_ = lean_float_of_nat(v___y_4647_);
v___x_4653_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4654_ = lean_float_div(v___x_4652_, v___x_4653_);
v___x_4655_ = lean_float_of_nat(v___x_4651_);
v___x_4656_ = lean_float_div(v___x_4655_, v___x_4653_);
v___x_4657_ = lean_box_float(v___x_4654_);
v___x_4658_ = lean_box_float(v___x_4656_);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4657_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v_a_4650_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
lean_inc_ref(v___y_4648_);
lean_inc(v___y_4646_);
v___x_4661_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4646_, v___x_4595_, v___y_4648_, v___y_4644_, v___y_4649_, v___y_4645_, v___f_4605_, v___x_4660_, v___x_4642_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec_ref_known(v___x_4642_, 2);
v___y_4609_ = v___x_4661_;
goto v___jp_4608_;
}
v___jp_4662_:
{
lean_object* v___x_4670_; double v___x_4671_; double v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4670_ = lean_io_get_num_heartbeats();
v___x_4671_ = lean_float_of_nat(v___y_4665_);
v___x_4672_ = lean_float_of_nat(v___x_4670_);
v___x_4673_ = lean_box_float(v___x_4671_);
v___x_4674_ = lean_box_float(v___x_4672_);
v___x_4675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4673_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v_a_4669_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
lean_inc_ref(v___y_4667_);
lean_inc(v___y_4666_);
v___x_4677_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4666_, v___x_4595_, v___y_4667_, v___y_4663_, v___y_4668_, v___y_4664_, v___f_4605_, v___x_4676_, v___x_4642_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec_ref_known(v___x_4642_, 2);
v___y_4609_ = v___x_4677_;
goto v___jp_4608_;
}
v___jp_4678_:
{
lean_object* v___x_4684_; 
v___x_4684_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4588_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
v___x_4686_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4687_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4679_, v___x_4686_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = lean_io_mono_nanos_now();
v___x_4689_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4680_, v___x_4642_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4689_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4689_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
lean_ctor_set_tag(v___x_4692_, 1);
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
v___y_4644_ = v___y_4679_;
v___y_4645_ = v_a_4685_;
v___y_4646_ = v___y_4681_;
v___y_4647_ = v___x_4688_;
v___y_4648_ = v___y_4682_;
v___y_4649_ = v___y_4683_;
v_a_4650_ = v___x_4695_;
goto v___jp_4643_;
}
}
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
v_a_4698_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4689_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4689_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
lean_ctor_set_tag(v___x_4700_, 0);
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
v___y_4644_ = v___y_4679_;
v___y_4645_ = v_a_4685_;
v___y_4646_ = v___y_4681_;
v___y_4647_ = v___x_4688_;
v___y_4648_ = v___y_4682_;
v___y_4649_ = v___y_4683_;
v_a_4650_ = v___x_4703_;
goto v___jp_4643_;
}
}
}
}
else
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = lean_io_get_num_heartbeats();
v___x_4707_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4680_, v___x_4642_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4707_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
lean_ctor_set_tag(v___x_4710_, 1);
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
v___y_4663_ = v___y_4679_;
v___y_4664_ = v_a_4685_;
v___y_4665_ = v___x_4706_;
v___y_4666_ = v___y_4681_;
v___y_4667_ = v___y_4682_;
v___y_4668_ = v___y_4683_;
v_a_4669_ = v___x_4713_;
goto v___jp_4662_;
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
v_a_4716_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4718_ = v___x_4707_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4707_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
lean_ctor_set_tag(v___x_4718_, 0);
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
v___y_4663_ = v___y_4679_;
v___y_4664_ = v_a_4685_;
v___y_4665_ = v___x_4706_;
v___y_4666_ = v___y_4681_;
v___y_4667_ = v___y_4682_;
v___y_4668_ = v___y_4683_;
v_a_4669_ = v___x_4721_;
goto v___jp_4662_;
}
}
}
}
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
lean_dec_ref(v___y_4680_);
lean_dec_ref_known(v___x_4642_, 2);
lean_dec(v_a_4607_);
lean_dec_ref(v___f_4605_);
lean_dec(v_a_4581_);
v_a_4724_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4684_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4684_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
v___jp_4732_:
{
if (lean_obj_tag(v_value_4599_) == 0)
{
lean_object* v_toCold_4733_; lean_object* v_options_4734_; uint8_t v_hasTrace_4735_; 
v_toCold_4733_ = lean_ctor_get(v___y_4587_, 0);
v_options_4734_ = lean_ctor_get(v_toCold_4733_, 2);
v_hasTrace_4735_ = lean_ctor_get_uint8(v_options_4734_, sizeof(void*)*1);
if (v_hasTrace_4735_ == 0)
{
lean_object* v_code_4736_; lean_object* v___x_4737_; 
lean_dec_ref(v___f_4605_);
v_code_4736_ = lean_ctor_get(v_value_4599_, 0);
lean_inc_ref(v_code_4736_);
v___x_4737_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4736_, v___x_4642_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec_ref_known(v___x_4642_, 2);
v___y_4609_ = v___x_4737_;
goto v___jp_4608_;
}
else
{
lean_object* v_code_4738_; lean_object* v_inheritedTraceOptions_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; 
v_code_4738_ = lean_ctor_get(v_value_4599_, 0);
v_inheritedTraceOptions_4739_ = lean_ctor_get(v_toCold_4733_, 11);
v___x_4740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4741_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4742_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4739_, v_options_4734_, v___x_4742_);
if (v___x_4743_ == 0)
{
lean_object* v___x_4744_; uint8_t v___x_4745_; 
v___x_4744_ = l_Lean_trace_profiler;
v___x_4745_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4734_, v___x_4744_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; 
lean_dec_ref(v___f_4605_);
lean_inc_ref(v_code_4738_);
v___x_4746_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4738_, v___x_4642_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec_ref_known(v___x_4642_, 2);
v___y_4609_ = v___x_4746_;
goto v___jp_4608_;
}
else
{
lean_inc_ref(v_code_4738_);
v___y_4679_ = v_options_4734_;
v___y_4680_ = v_code_4738_;
v___y_4681_ = v___x_4740_;
v___y_4682_ = v___x_4741_;
v___y_4683_ = v___x_4743_;
goto v___jp_4678_;
}
}
else
{
lean_inc_ref(v_code_4738_);
v___y_4679_ = v_options_4734_;
v___y_4680_ = v_code_4738_;
v___y_4681_ = v___x_4740_;
v___y_4682_ = v___x_4741_;
v___y_4683_ = v___x_4743_;
goto v___jp_4678_;
}
}
}
else
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
lean_dec_ref(v___f_4605_);
v___x_4747_ = lean_box(1);
v___x_4748_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4747_, v___x_4642_, v___y_4584_, v___y_4588_);
lean_dec_ref_known(v___x_4642_, 2);
v___y_4609_ = v___x_4748_;
goto v___jp_4608_;
}
}
v___jp_4749_:
{
if (lean_obj_tag(v___y_4750_) == 0)
{
lean_dec_ref_known(v___y_4750_, 1);
goto v___jp_4732_;
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec_ref_known(v___x_4642_, 2);
lean_dec(v_a_4607_);
lean_dec_ref(v___f_4605_);
lean_dec(v_a_4581_);
v_a_4751_ = lean_ctor_get(v___y_4750_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___y_4750_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___y_4750_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___y_4750_);
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
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
lean_dec_ref(v___f_4605_);
lean_dec(v_a_4581_);
v_a_4767_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4606_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4606_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
v___jp_4590_:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = lean_unsigned_to_nat(1u);
v___x_4593_ = lean_nat_add(v_a_4581_, v___x_4592_);
lean_dec(v_a_4581_);
lean_inc_ref(v_a_4591_);
v_a_4581_ = v___x_4593_;
v_b_4582_ = v_a_4591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4775_, lean_object* v___x_4776_, lean_object* v_a_4777_, lean_object* v_b_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4775_, v___x_4776_, v_a_4777_, v_b_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec_ref(v___x_4776_);
lean_dec(v_upperBound_4775_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_){
_start:
{
lean_object* v_decls_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v_decls_4794_ = lean_ctor_get(v_a_4787_, 0);
v___x_4795_ = lean_array_get_size(v_decls_4794_);
v___x_4796_ = lean_unsigned_to_nat(0u);
v___x_4797_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4798_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4795_, v_decls_4794_, v___x_4796_, v___x_4797_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4813_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4801_ = v___x_4798_;
v_isShared_4802_ = v_isSharedCheck_4813_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4798_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4813_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v_fst_4803_; 
v_fst_4803_ = lean_ctor_get(v_a_4799_, 0);
lean_inc(v_fst_4803_);
lean_dec(v_a_4799_);
if (lean_obj_tag(v_fst_4803_) == 0)
{
uint8_t v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___x_4804_ = 0;
v___x_4805_ = lean_box(v___x_4804_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v___x_4805_);
v___x_4807_ = v___x_4801_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
else
{
lean_object* v_val_4809_; lean_object* v___x_4811_; 
v_val_4809_ = lean_ctor_get(v_fst_4803_, 0);
lean_inc(v_val_4809_);
lean_dec_ref_known(v_fst_4803_, 1);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v_val_4809_);
v___x_4811_ = v___x_4801_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_val_4809_);
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
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
v_a_4814_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4798_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4798_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4830_, lean_object* v_x_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4831_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4840_, lean_object* v_x_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4840_, v_x_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4850_, lean_object* v___x_4851_, lean_object* v_inst_4852_, lean_object* v_R_4853_, lean_object* v_a_4854_, lean_object* v_b_4855_, lean_object* v_c_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4850_, v___x_4851_, v_a_4854_, v_b_4855_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4865_, lean_object* v___x_4866_, lean_object* v_inst_4867_, lean_object* v_R_4868_, lean_object* v_a_4869_, lean_object* v_b_4870_, lean_object* v_c_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4865_, v___x_4866_, v_inst_4867_, v_R_4868_, v_a_4869_, v_b_4870_, v_c_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec_ref(v___x_4866_);
lean_dec(v_upperBound_4865_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4880_, lean_object* v_data_4881_, lean_object* v_ref_4882_, lean_object* v_msg_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4880_, v_data_4881_, v_ref_4882_, v_msg_4883_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4892_, lean_object* v_data_4893_, lean_object* v_ref_4894_, lean_object* v_msg_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4892_, v_data_4893_, v_ref_4894_, v_msg_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4906_, lean_object* v_msg_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v_ref_4913_; lean_object* v___x_4914_; lean_object* v_env_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v_ref_4913_ = lean_ctor_get(v___y_4910_, 2);
v___x_4914_ = lean_st_ref_get(v___y_4911_);
v_env_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc_ref(v_env_4915_);
lean_dec(v___x_4914_);
v___x_4916_ = lean_st_ref_get(v___y_4909_);
v___x_4917_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4908_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4977_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4977_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4977_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_lctx_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4975_; 
v_lctx_4922_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v___x_4916_, 1);
lean_dec(v_unused_4976_);
v___x_4924_ = v___x_4916_;
v_isShared_4925_ = v_isSharedCheck_4975_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_lctx_4922_);
lean_dec(v___x_4916_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4975_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
uint8_t v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4932_; 
v___x_4926_ = lean_unbox(v_a_4918_);
lean_dec(v_a_4918_);
v___x_4927_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4922_, v___x_4926_);
lean_dec_ref(v_lctx_4922_);
v___x_4928_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4910_);
v___x_4929_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4930_, 0, v_env_4915_);
lean_ctor_set(v___x_4930_, 1, v___x_4929_);
lean_ctor_set(v___x_4930_, 2, v___x_4927_);
lean_ctor_set(v___x_4930_, 3, v___x_4928_);
if (v_isShared_4925_ == 0)
{
lean_ctor_set_tag(v___x_4924_, 3);
lean_ctor_set(v___x_4924_, 1, v_msg_4907_);
lean_ctor_set(v___x_4924_, 0, v___x_4930_);
v___x_4932_ = v___x_4924_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_msg_4907_);
v___x_4932_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
lean_object* v___x_4933_; lean_object* v_traceState_4934_; lean_object* v_env_4935_; lean_object* v_nextMacroScope_4936_; lean_object* v_ngen_4937_; lean_object* v_auxDeclNGen_4938_; lean_object* v_cache_4939_; lean_object* v_recordedDeps_4940_; lean_object* v_messages_4941_; lean_object* v_infoState_4942_; lean_object* v_snapshotTasks_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4973_; 
v___x_4933_ = lean_st_ref_take(v___y_4911_);
v_traceState_4934_ = lean_ctor_get(v___x_4933_, 4);
v_env_4935_ = lean_ctor_get(v___x_4933_, 0);
v_nextMacroScope_4936_ = lean_ctor_get(v___x_4933_, 1);
v_ngen_4937_ = lean_ctor_get(v___x_4933_, 2);
v_auxDeclNGen_4938_ = lean_ctor_get(v___x_4933_, 3);
v_cache_4939_ = lean_ctor_get(v___x_4933_, 5);
v_recordedDeps_4940_ = lean_ctor_get(v___x_4933_, 6);
v_messages_4941_ = lean_ctor_get(v___x_4933_, 7);
v_infoState_4942_ = lean_ctor_get(v___x_4933_, 8);
v_snapshotTasks_4943_ = lean_ctor_get(v___x_4933_, 9);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4945_ = v___x_4933_;
v_isShared_4946_ = v_isSharedCheck_4973_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_snapshotTasks_4943_);
lean_inc(v_infoState_4942_);
lean_inc(v_messages_4941_);
lean_inc(v_recordedDeps_4940_);
lean_inc(v_cache_4939_);
lean_inc(v_traceState_4934_);
lean_inc(v_auxDeclNGen_4938_);
lean_inc(v_ngen_4937_);
lean_inc(v_nextMacroScope_4936_);
lean_inc(v_env_4935_);
lean_dec(v___x_4933_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4973_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
uint64_t v_tid_4947_; lean_object* v_traces_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4972_; 
v_tid_4947_ = lean_ctor_get_uint64(v_traceState_4934_, sizeof(void*)*1);
v_traces_4948_ = lean_ctor_get(v_traceState_4934_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v_traceState_4934_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4950_ = v_traceState_4934_;
v_isShared_4951_ = v_isSharedCheck_4972_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_traces_4948_);
lean_dec(v_traceState_4934_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4972_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; double v___x_4954_; uint8_t v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4963_; 
v___x_4952_ = lean_box(0);
v___x_4953_ = lean_box(0);
v___x_4954_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4955_ = 0;
v___x_4956_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4957_, 0, v_cls_4906_);
lean_ctor_set(v___x_4957_, 1, v___x_4953_);
lean_ctor_set(v___x_4957_, 2, v___x_4956_);
lean_ctor_set_float(v___x_4957_, sizeof(void*)*3, v___x_4954_);
lean_ctor_set_float(v___x_4957_, sizeof(void*)*3 + 8, v___x_4954_);
lean_ctor_set_uint8(v___x_4957_, sizeof(void*)*3 + 16, v___x_4955_);
v___x_4958_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4959_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4957_);
lean_ctor_set(v___x_4959_, 1, v___x_4932_);
lean_ctor_set(v___x_4959_, 2, v___x_4958_);
lean_inc(v_ref_4913_);
v___x_4960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4960_, 0, v_ref_4913_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = l_Lean_PersistentArray_push___redArg(v_traces_4948_, v___x_4960_);
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 0, v___x_4961_);
v___x_4963_ = v___x_4950_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4961_);
lean_ctor_set_uint64(v_reuseFailAlloc_4971_, sizeof(void*)*1, v_tid_4947_);
v___x_4963_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
lean_object* v___x_4965_; 
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 4, v___x_4963_);
v___x_4965_ = v___x_4945_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_env_4935_);
lean_ctor_set(v_reuseFailAlloc_4970_, 1, v_nextMacroScope_4936_);
lean_ctor_set(v_reuseFailAlloc_4970_, 2, v_ngen_4937_);
lean_ctor_set(v_reuseFailAlloc_4970_, 3, v_auxDeclNGen_4938_);
lean_ctor_set(v_reuseFailAlloc_4970_, 4, v___x_4963_);
lean_ctor_set(v_reuseFailAlloc_4970_, 5, v_cache_4939_);
lean_ctor_set(v_reuseFailAlloc_4970_, 6, v_recordedDeps_4940_);
lean_ctor_set(v_reuseFailAlloc_4970_, 7, v_messages_4941_);
lean_ctor_set(v_reuseFailAlloc_4970_, 8, v_infoState_4942_);
lean_ctor_set(v_reuseFailAlloc_4970_, 9, v_snapshotTasks_4943_);
v___x_4965_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
lean_object* v___x_4966_; lean_object* v___x_4968_; 
v___x_4966_ = lean_st_ref_put(v___y_4911_, v___x_4965_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4952_);
v___x_4968_ = v___x_4920_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v___x_4952_);
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
lean_dec(v___x_4916_);
lean_dec_ref(v_env_4915_);
lean_dec_ref(v_msg_4907_);
lean_dec(v_cls_4906_);
v_a_4978_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4917_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4917_);
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
lean_object* v___x_5054_; lean_object* v_decls_5055_; lean_object* v_funVals_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5096_; 
v___x_5054_ = lean_st_ref_take(v_a_5045_);
v_decls_5055_ = lean_ctor_get(v_a_5044_, 0);
v_funVals_5056_ = lean_ctor_get(v___x_5054_, 1);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5096_ == 0)
{
lean_object* v_unused_5097_; 
v_unused_5097_ = lean_ctor_get(v___x_5054_, 0);
lean_dec(v_unused_5097_);
v___x_5058_ = v___x_5054_;
v_isShared_5059_ = v_isSharedCheck_5096_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_funVals_5056_);
lean_dec(v___x_5054_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5096_;
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
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v___x_5062_);
lean_ctor_set(v_reuseFailAlloc_5095_, 1, v_funVals_5056_);
v___x_5064_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = lean_st_ref_put(v_a_5045_, v___x_5064_);
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
lean_object* v_toCold_5069_; lean_object* v_options_5070_; uint8_t v_hasTrace_5071_; 
v_toCold_5069_ = lean_ctor_get(v_a_5048_, 0);
v_options_5070_ = lean_ctor_get(v_toCold_5069_, 2);
v_hasTrace_5071_ = lean_ctor_get_uint8(v_options_5070_, sizeof(void*)*1);
if (v_hasTrace_5071_ == 0)
{
lean_dec(v_n_5043_);
goto v___jp_5051_;
}
else
{
lean_object* v_inheritedTraceOptions_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; 
v_inheritedTraceOptions_5072_ = lean_ctor_get(v_toCold_5069_, 11);
v___x_5073_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5074_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5072_, v_options_5070_, v___x_5074_);
if (v___x_5075_ == 0)
{
lean_dec(v_n_5043_);
goto v___jp_5051_;
}
else
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5076_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5077_ = l_Nat_reprFast(v_n_5043_);
v___x_5078_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5077_);
v___x_5079_ = l_Lean_MessageData_ofFormat(v___x_5078_);
v___x_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5076_);
lean_ctor_set(v___x_5080_, 1, v___x_5079_);
v___x_5081_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5080_);
lean_ctor_set(v___x_5082_, 1, v___x_5081_);
v___x_5083_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5073_, v___x_5082_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_dec_ref_known(v___x_5083_, 1);
goto v___jp_5051_;
}
else
{
return v___x_5083_;
}
}
}
}
else
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_unsigned_to_nat(1u);
v___x_5085_ = lean_nat_add(v_n_5043_, v___x_5084_);
lean_dec(v_n_5043_);
v_n_5043_ = v___x_5085_;
goto _start;
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v_n_5043_);
v_a_5087_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5066_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5066_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
lean_dec(v_a_5104_);
lean_dec_ref(v_a_5103_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5099_);
return v_res_5106_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
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
lean_object* v_ref_5118_; lean_object* v___x_5119_; lean_object* v_env_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_ref_5118_ = lean_ctor_get(v___y_5115_, 2);
v___x_5119_ = lean_st_ref_get(v___y_5116_);
v_env_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc_ref(v_env_5120_);
lean_dec(v___x_5119_);
v___x_5121_ = lean_st_ref_get(v___y_5114_);
v___x_5122_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5113_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5182_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5125_ = v___x_5122_;
v_isShared_5126_ = v_isSharedCheck_5182_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5122_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5182_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v_lctx_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5180_; 
v_lctx_5127_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5180_ == 0)
{
lean_object* v_unused_5181_; 
v_unused_5181_ = lean_ctor_get(v___x_5121_, 1);
lean_dec(v_unused_5181_);
v___x_5129_ = v___x_5121_;
v_isShared_5130_ = v_isSharedCheck_5180_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_lctx_5127_);
lean_dec(v___x_5121_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5180_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
uint8_t v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5137_; 
v___x_5131_ = lean_unbox(v_a_5123_);
lean_dec(v_a_5123_);
v___x_5132_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5127_, v___x_5131_);
lean_dec_ref(v_lctx_5127_);
v___x_5133_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5115_);
v___x_5134_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_5135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5135_, 0, v_env_5120_);
lean_ctor_set(v___x_5135_, 1, v___x_5134_);
lean_ctor_set(v___x_5135_, 2, v___x_5132_);
lean_ctor_set(v___x_5135_, 3, v___x_5133_);
if (v_isShared_5130_ == 0)
{
lean_ctor_set_tag(v___x_5129_, 3);
lean_ctor_set(v___x_5129_, 1, v_msg_5112_);
lean_ctor_set(v___x_5129_, 0, v___x_5135_);
v___x_5137_ = v___x_5129_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5135_);
lean_ctor_set(v_reuseFailAlloc_5179_, 1, v_msg_5112_);
v___x_5137_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
lean_object* v___x_5138_; lean_object* v_traceState_5139_; lean_object* v_env_5140_; lean_object* v_nextMacroScope_5141_; lean_object* v_ngen_5142_; lean_object* v_auxDeclNGen_5143_; lean_object* v_cache_5144_; lean_object* v_recordedDeps_5145_; lean_object* v_messages_5146_; lean_object* v_infoState_5147_; lean_object* v_snapshotTasks_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5178_; 
v___x_5138_ = lean_st_ref_take(v___y_5116_);
v_traceState_5139_ = lean_ctor_get(v___x_5138_, 4);
v_env_5140_ = lean_ctor_get(v___x_5138_, 0);
v_nextMacroScope_5141_ = lean_ctor_get(v___x_5138_, 1);
v_ngen_5142_ = lean_ctor_get(v___x_5138_, 2);
v_auxDeclNGen_5143_ = lean_ctor_get(v___x_5138_, 3);
v_cache_5144_ = lean_ctor_get(v___x_5138_, 5);
v_recordedDeps_5145_ = lean_ctor_get(v___x_5138_, 6);
v_messages_5146_ = lean_ctor_get(v___x_5138_, 7);
v_infoState_5147_ = lean_ctor_get(v___x_5138_, 8);
v_snapshotTasks_5148_ = lean_ctor_get(v___x_5138_, 9);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5150_ = v___x_5138_;
v_isShared_5151_ = v_isSharedCheck_5178_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_snapshotTasks_5148_);
lean_inc(v_infoState_5147_);
lean_inc(v_messages_5146_);
lean_inc(v_recordedDeps_5145_);
lean_inc(v_cache_5144_);
lean_inc(v_traceState_5139_);
lean_inc(v_auxDeclNGen_5143_);
lean_inc(v_ngen_5142_);
lean_inc(v_nextMacroScope_5141_);
lean_inc(v_env_5140_);
lean_dec(v___x_5138_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5178_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
uint64_t v_tid_5152_; lean_object* v_traces_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5177_; 
v_tid_5152_ = lean_ctor_get_uint64(v_traceState_5139_, sizeof(void*)*1);
v_traces_5153_ = lean_ctor_get(v_traceState_5139_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_traceState_5139_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5155_ = v_traceState_5139_;
v_isShared_5156_ = v_isSharedCheck_5177_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_traces_5153_);
lean_dec(v_traceState_5139_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5177_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5157_; lean_object* v___x_5158_; double v___x_5159_; uint8_t v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5168_; 
v___x_5157_ = lean_box(0);
v___x_5158_ = lean_box(0);
v___x_5159_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5160_ = 0;
v___x_5161_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5162_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5162_, 0, v_cls_5111_);
lean_ctor_set(v___x_5162_, 1, v___x_5158_);
lean_ctor_set(v___x_5162_, 2, v___x_5161_);
lean_ctor_set_float(v___x_5162_, sizeof(void*)*3, v___x_5159_);
lean_ctor_set_float(v___x_5162_, sizeof(void*)*3 + 8, v___x_5159_);
lean_ctor_set_uint8(v___x_5162_, sizeof(void*)*3 + 16, v___x_5160_);
v___x_5163_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5164_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5162_);
lean_ctor_set(v___x_5164_, 1, v___x_5137_);
lean_ctor_set(v___x_5164_, 2, v___x_5163_);
lean_inc(v_ref_5118_);
v___x_5165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5165_, 0, v_ref_5118_);
lean_ctor_set(v___x_5165_, 1, v___x_5164_);
v___x_5166_ = l_Lean_PersistentArray_push___redArg(v_traces_5153_, v___x_5165_);
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 0, v___x_5166_);
v___x_5168_ = v___x_5155_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5166_);
lean_ctor_set_uint64(v_reuseFailAlloc_5176_, sizeof(void*)*1, v_tid_5152_);
v___x_5168_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
lean_object* v___x_5170_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 4, v___x_5168_);
v___x_5170_ = v___x_5150_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_env_5140_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_nextMacroScope_5141_);
lean_ctor_set(v_reuseFailAlloc_5175_, 2, v_ngen_5142_);
lean_ctor_set(v_reuseFailAlloc_5175_, 3, v_auxDeclNGen_5143_);
lean_ctor_set(v_reuseFailAlloc_5175_, 4, v___x_5168_);
lean_ctor_set(v_reuseFailAlloc_5175_, 5, v_cache_5144_);
lean_ctor_set(v_reuseFailAlloc_5175_, 6, v_recordedDeps_5145_);
lean_ctor_set(v_reuseFailAlloc_5175_, 7, v_messages_5146_);
lean_ctor_set(v_reuseFailAlloc_5175_, 8, v_infoState_5147_);
lean_ctor_set(v_reuseFailAlloc_5175_, 9, v_snapshotTasks_5148_);
v___x_5170_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_5173_; 
v___x_5171_ = lean_st_ref_put(v___y_5116_, v___x_5170_);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v___x_5157_);
v___x_5173_ = v___x_5125_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5157_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
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
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec(v___x_5121_);
lean_dec_ref(v_env_5120_);
lean_dec_ref(v_msg_5112_);
lean_dec(v_cls_5111_);
v_a_5183_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5122_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5122_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5191_, lean_object* v_msg_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5191_, v_msg_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_);
lean_dec(v___y_5196_);
lean_dec_ref(v___y_5195_);
lean_dec(v___y_5194_);
lean_dec_ref(v___y_5193_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5199_, size_t v_i_5200_, size_t v_stop_5201_, lean_object* v_b_5202_){
_start:
{
uint8_t v___x_5204_; 
v___x_5204_ = lean_usize_dec_eq(v_i_5200_, v_stop_5201_);
if (v___x_5204_ == 0)
{
lean_object* v_fst_5205_; lean_object* v_snd_5206_; lean_object* v___x_5207_; lean_object* v_snd_5208_; lean_object* v_fst_5209_; lean_object* v_fst_5210_; lean_object* v_snd_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5225_; 
v_fst_5205_ = lean_ctor_get(v_b_5202_, 0);
lean_inc(v_fst_5205_);
v_snd_5206_ = lean_ctor_get(v_b_5202_, 1);
lean_inc(v_snd_5206_);
lean_dec_ref(v_b_5202_);
v___x_5207_ = lean_array_uget_borrowed(v_as_5199_, v_i_5200_);
v_snd_5208_ = lean_ctor_get(v___x_5207_, 1);
lean_inc(v_snd_5208_);
v_fst_5209_ = lean_ctor_get(v___x_5207_, 0);
v_fst_5210_ = lean_ctor_get(v_snd_5208_, 0);
v_snd_5211_ = lean_ctor_get(v_snd_5208_, 1);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_snd_5208_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5213_ = v_snd_5208_;
v_isShared_5214_ = v_isSharedCheck_5225_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_snd_5211_);
lean_inc(v_fst_5210_);
lean_dec(v_snd_5208_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5225_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v_fvarId_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5220_; 
v_fvarId_5215_ = lean_ctor_get(v_fst_5209_, 0);
v___x_5216_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_5210_, v_fst_5205_);
lean_dec(v_fst_5210_);
v___x_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5217_, 0, v_snd_5211_);
lean_inc(v_fvarId_5215_);
v___x_5218_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5206_, v_fvarId_5215_, v___x_5217_);
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 1, v___x_5218_);
lean_ctor_set(v___x_5213_, 0, v___x_5216_);
v___x_5220_ = v___x_5213_;
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
v___x_5222_ = lean_usize_add(v_i_5200_, v___x_5221_);
v_i_5200_ = v___x_5222_;
v_b_5202_ = v___x_5220_;
goto _start;
}
}
}
else
{
lean_object* v___x_5226_; 
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v_b_5202_);
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
v___x_5353_ = lean_unsigned_to_nat(650u);
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
lean_object* v_ctorName_5386_; lean_object* v_params_5387_; lean_object* v_code_5388_; uint8_t v___x_5389_; lean_object* v___y_5391_; lean_object* v___y_5392_; lean_object* v___y_5405_; uint8_t v___x_5409_; 
v_ctorName_5386_ = lean_ctor_get(v_a_5373_, 0);
v_params_5387_ = lean_ctor_get(v_a_5373_, 1);
v_code_5388_ = lean_ctor_get(v_a_5373_, 2);
v___x_5389_ = 0;
v___x_5409_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5360_, v_ctorName_5386_);
if (v___x_5409_ == 0)
{
lean_object* v_toCold_5410_; lean_object* v_options_5411_; uint8_t v_hasTrace_5412_; 
v_toCold_5410_ = lean_ctor_get(v___y_5367_, 0);
v_options_5411_ = lean_ctor_get(v_toCold_5410_, 2);
v_hasTrace_5412_ = lean_ctor_get_uint8(v_options_5411_, sizeof(void*)*1);
if (v_hasTrace_5412_ == 0)
{
v___y_5405_ = v___y_5366_;
goto v___jp_5404_;
}
else
{
lean_object* v_inheritedTraceOptions_5413_; lean_object* v_cls_5414_; lean_object* v___x_5415_; uint8_t v___x_5416_; 
v_inheritedTraceOptions_5413_ = lean_ctor_get(v_toCold_5410_, 11);
v_cls_5414_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5415_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5416_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5413_, v_options_5411_, v___x_5415_);
if (v___x_5416_ == 0)
{
v___y_5405_ = v___y_5366_;
goto v___jp_5404_;
}
else
{
lean_object* v___x_5417_; 
lean_inc(v_discr_5361_);
v___x_5417_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5361_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_a_5418_);
lean_dec_ref_known(v___x_5417_, 1);
v___x_5419_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5418_, v___x_5416_);
v___x_5421_ = lean_string_append(v___x_5419_, v___x_5420_);
lean_dec_ref(v___x_5420_);
v___x_5422_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5423_ = lean_string_append(v___x_5421_, v___x_5422_);
lean_inc(v_ctorName_5386_);
v___x_5424_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5386_, v___x_5416_);
v___x_5425_ = lean_string_append(v___x_5423_, v___x_5424_);
lean_dec_ref(v___x_5424_);
v___x_5426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
v___x_5427_ = l_Lean_MessageData_ofFormat(v___x_5426_);
v___x_5428_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5414_, v___x_5427_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_dec_ref_known(v___x_5428_, 1);
v___y_5405_ = v___y_5366_;
goto v___jp_5404_;
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5428_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5437_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5417_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5417_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
}
}
else
{
lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5445_ = lean_unsigned_to_nat(0u);
v___x_5446_ = lean_array_get_size(v_params_5387_);
v___x_5447_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5362_, v_params_5387_, v___x_5445_, v___x_5446_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5447_) == 0)
{
lean_object* v_a_5448_; lean_object* v___x_5461_; uint8_t v___x_5462_; lean_object* v_fst_5464_; lean_object* v_snd_5465_; lean_object* v___y_5478_; 
v_a_5448_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_a_5448_);
lean_dec_ref_known(v___x_5447_, 1);
v___x_5461_ = lean_array_get_size(v_a_5448_);
v___x_5462_ = lean_nat_dec_eq(v___x_5461_, v___x_5445_);
if (v___x_5462_ == 0)
{
if (v___x_5409_ == 0)
{
lean_dec(v_a_5448_);
goto v___jp_5449_;
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
v___x_5493_ = lean_nat_dec_lt(v___x_5445_, v___x_5461_);
if (v___x_5493_ == 0)
{
lean_dec(v_a_5448_);
v_fst_5464_ = v_a_5491_;
v_snd_5465_ = v___x_5492_;
goto v___jp_5463_;
}
else
{
lean_object* v___x_5494_; uint8_t v___x_5495_; 
lean_inc(v_a_5491_);
v___x_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5494_, 0, v_a_5491_);
lean_ctor_set(v___x_5494_, 1, v___x_5492_);
v___x_5495_ = lean_nat_dec_le(v___x_5461_, v___x_5461_);
if (v___x_5495_ == 0)
{
if (v___x_5493_ == 0)
{
lean_dec_ref_known(v___x_5494_, 2);
lean_dec(v_a_5448_);
v_fst_5464_ = v_a_5491_;
v_snd_5465_ = v___x_5492_;
goto v___jp_5463_;
}
else
{
size_t v___x_5496_; size_t v___x_5497_; lean_object* v___x_5498_; 
lean_dec(v_a_5491_);
v___x_5496_ = ((size_t)0ULL);
v___x_5497_ = lean_usize_of_nat(v___x_5461_);
v___x_5498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5448_, v___x_5496_, v___x_5497_, v___x_5494_);
lean_dec(v_a_5448_);
v___y_5478_ = v___x_5498_;
goto v___jp_5477_;
}
}
else
{
size_t v___x_5499_; size_t v___x_5500_; lean_object* v___x_5501_; 
lean_dec(v_a_5491_);
v___x_5499_ = ((size_t)0ULL);
v___x_5500_ = lean_usize_of_nat(v___x_5461_);
v___x_5501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5448_, v___x_5499_, v___x_5500_, v___x_5494_);
lean_dec(v_a_5448_);
v___y_5478_ = v___x_5501_;
goto v___jp_5477_;
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_a_5448_);
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
lean_dec(v_a_5448_);
goto v___jp_5449_;
}
v___jp_5449_:
{
lean_object* v___x_5450_; 
lean_inc_ref(v_code_5388_);
v___x_5450_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5362_, v_code_5388_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_object* v_a_5451_; lean_object* v___x_5452_; 
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
lean_inc(v_a_5451_);
lean_dec_ref_known(v___x_5450_, 1);
lean_inc_ref(v_a_5373_);
v___x_5452_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5373_, v_a_5451_);
v_a_5375_ = v___x_5452_;
goto v___jp_5374_;
}
else
{
lean_object* v_a_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5460_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5453_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5460_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5460_ == 0)
{
v___x_5455_ = v___x_5450_;
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_a_5453_);
lean_dec(v___x_5450_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v___x_5458_; 
if (v_isShared_5456_ == 0)
{
v___x_5458_ = v___x_5455_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5453_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
}
}
v___jp_5463_:
{
lean_object* v___x_5466_; 
v___x_5466_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5389_, v_fst_5464_, v_snd_5465_, v___x_5462_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
lean_dec_ref(v_snd_5465_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; lean_object* v___x_5468_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
lean_inc(v_a_5467_);
lean_dec_ref_known(v___x_5466_, 1);
lean_inc_ref(v_a_5373_);
v___x_5468_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5373_, v_a_5467_);
v_a_5375_ = v___x_5468_;
goto v___jp_5374_;
}
else
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5476_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5469_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5471_ = v___x_5466_;
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5466_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5474_; 
if (v_isShared_5472_ == 0)
{
v___x_5474_ = v___x_5471_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
v___jp_5477_:
{
if (lean_obj_tag(v___y_5478_) == 0)
{
lean_object* v_a_5479_; lean_object* v_fst_5480_; lean_object* v_snd_5481_; 
v_a_5479_ = lean_ctor_get(v___y_5478_, 0);
lean_inc(v_a_5479_);
lean_dec_ref_known(v___y_5478_, 1);
v_fst_5480_ = lean_ctor_get(v_a_5479_, 0);
lean_inc(v_fst_5480_);
v_snd_5481_ = lean_ctor_get(v_a_5479_, 1);
lean_inc(v_snd_5481_);
lean_dec(v_a_5479_);
v_fst_5464_ = v_fst_5480_;
v_snd_5465_ = v_snd_5481_;
goto v___jp_5463_;
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5482_ = lean_ctor_get(v___y_5478_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___y_5478_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___y_5478_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___y_5478_);
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
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5510_ = lean_ctor_get(v___x_5447_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5447_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5447_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5447_);
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
lean_object* v___x_5393_; 
v___x_5393_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5389_, v___y_5392_, v___y_5391_);
lean_dec_ref(v___y_5392_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v___x_5394_; lean_object* v___x_5395_; 
lean_dec_ref_known(v___x_5393_, 1);
lean_inc_ref(v_resultType_5359_);
v___x_5394_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5394_, 0, v_resultType_5359_);
lean_inc_ref(v_a_5373_);
v___x_5395_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5373_, v___x_5394_);
v_a_5375_ = v___x_5395_;
goto v___jp_5374_;
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
lean_dec_ref(v_as_5364_);
lean_dec(v_i_5363_);
lean_dec(v_discr_5361_);
lean_dec_ref(v_resultType_5359_);
v_a_5396_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5393_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5393_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
if (v_isShared_5399_ == 0)
{
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
v___jp_5404_:
{
switch(lean_obj_tag(v_a_5373_))
{
case 0:
{
lean_object* v_code_5406_; 
v_code_5406_ = lean_ctor_get(v_a_5373_, 2);
lean_inc_ref(v_code_5406_);
v___y_5391_ = v___y_5405_;
v___y_5392_ = v_code_5406_;
goto v___jp_5390_;
}
case 1:
{
lean_object* v_code_5407_; 
v_code_5407_ = lean_ctor_get(v_a_5373_, 1);
lean_inc_ref(v_code_5407_);
v___y_5391_ = v___y_5405_;
v___y_5392_ = v_code_5407_;
goto v___jp_5390_;
}
default: 
{
lean_object* v_code_5408_; 
v_code_5408_ = lean_ctor_get(v_a_5373_, 0);
lean_inc_ref(v_code_5408_);
v___y_5391_ = v___y_5405_;
v___y_5392_ = v_code_5408_;
goto v___jp_5390_;
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
lean_object* v_decl_5538_; lean_object* v_k_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; 
switch(lean_obj_tag(v_code_5531_))
{
case 0:
{
lean_object* v_decl_5651_; lean_object* v_k_5652_; lean_object* v___x_5653_; 
v_decl_5651_ = lean_ctor_get(v_code_5531_, 0);
v_k_5652_ = lean_ctor_get(v_code_5531_, 1);
lean_inc_ref(v_k_5652_);
v___x_5653_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5530_, v_k_5652_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5690_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5656_ = v___x_5653_;
v_isShared_5657_ = v_isSharedCheck_5690_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_dec(v___x_5653_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5690_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
size_t v___x_5658_; size_t v___x_5659_; uint8_t v___x_5660_; 
v___x_5658_ = lean_ptr_addr(v_k_5652_);
v___x_5659_ = lean_ptr_addr(v_a_5654_);
v___x_5660_ = lean_usize_dec_eq(v___x_5658_, v___x_5659_);
if (v___x_5660_ == 0)
{
lean_object* v___x_5662_; uint8_t v_isShared_5663_; uint8_t v_isSharedCheck_5670_; 
lean_inc_ref(v_decl_5651_);
v_isSharedCheck_5670_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5670_ == 0)
{
lean_object* v_unused_5671_; lean_object* v_unused_5672_; 
v_unused_5671_ = lean_ctor_get(v_code_5531_, 1);
lean_dec(v_unused_5671_);
v_unused_5672_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5672_);
v___x_5662_ = v_code_5531_;
v_isShared_5663_ = v_isSharedCheck_5670_;
goto v_resetjp_5661_;
}
else
{
lean_dec(v_code_5531_);
v___x_5662_ = lean_box(0);
v_isShared_5663_ = v_isSharedCheck_5670_;
goto v_resetjp_5661_;
}
v_resetjp_5661_:
{
lean_object* v___x_5665_; 
if (v_isShared_5663_ == 0)
{
lean_ctor_set(v___x_5662_, 1, v_a_5654_);
v___x_5665_ = v___x_5662_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_decl_5651_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_a_5654_);
v___x_5665_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
lean_object* v___x_5667_; 
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 0, v___x_5665_);
v___x_5667_ = v___x_5656_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v___x_5665_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
}
else
{
size_t v___x_5673_; uint8_t v___x_5674_; 
v___x_5673_ = lean_ptr_addr(v_decl_5651_);
v___x_5674_ = lean_usize_dec_eq(v___x_5673_, v___x_5673_);
if (v___x_5674_ == 0)
{
lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5684_; 
lean_inc_ref(v_decl_5651_);
v_isSharedCheck_5684_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5684_ == 0)
{
lean_object* v_unused_5685_; lean_object* v_unused_5686_; 
v_unused_5685_ = lean_ctor_get(v_code_5531_, 1);
lean_dec(v_unused_5685_);
v_unused_5686_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5686_);
v___x_5676_ = v_code_5531_;
v_isShared_5677_ = v_isSharedCheck_5684_;
goto v_resetjp_5675_;
}
else
{
lean_dec(v_code_5531_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5684_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 1, v_a_5654_);
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_decl_5651_);
lean_ctor_set(v_reuseFailAlloc_5683_, 1, v_a_5654_);
v___x_5679_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
lean_object* v___x_5681_; 
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 0, v___x_5679_);
v___x_5681_ = v___x_5656_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v___x_5679_);
v___x_5681_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
return v___x_5681_;
}
}
}
}
else
{
lean_object* v___x_5688_; 
lean_dec(v_a_5654_);
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 0, v_code_5531_);
v___x_5688_ = v___x_5656_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_code_5531_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_5531_, 2);
return v___x_5653_;
}
}
case 1:
{
lean_object* v_decl_5691_; lean_object* v_k_5692_; 
v_decl_5691_ = lean_ctor_get(v_code_5531_, 0);
v_k_5692_ = lean_ctor_get(v_code_5531_, 1);
lean_inc_ref(v_k_5692_);
lean_inc_ref(v_decl_5691_);
v_decl_5538_ = v_decl_5691_;
v_k_5539_ = v_k_5692_;
v___y_5540_ = v_a_5532_;
v___y_5541_ = v_a_5533_;
v___y_5542_ = v_a_5534_;
v___y_5543_ = v_a_5535_;
goto v___jp_5537_;
}
case 2:
{
lean_object* v_decl_5693_; lean_object* v_k_5694_; 
v_decl_5693_ = lean_ctor_get(v_code_5531_, 0);
v_k_5694_ = lean_ctor_get(v_code_5531_, 1);
lean_inc_ref(v_k_5694_);
lean_inc_ref(v_decl_5693_);
v_decl_5538_ = v_decl_5693_;
v_k_5539_ = v_k_5694_;
v___y_5540_ = v_a_5532_;
v___y_5541_ = v_a_5533_;
v___y_5542_ = v_a_5534_;
v___y_5543_ = v_a_5535_;
goto v___jp_5537_;
}
case 4:
{
lean_object* v_cases_5695_; lean_object* v_typeName_5696_; lean_object* v_resultType_5697_; lean_object* v_discr_5698_; lean_object* v_alts_5699_; lean_object* v___x_5701_; uint8_t v_isShared_5702_; uint8_t v_isSharedCheck_5740_; 
v_cases_5695_ = lean_ctor_get(v_code_5531_, 0);
lean_inc_ref(v_cases_5695_);
v_typeName_5696_ = lean_ctor_get(v_cases_5695_, 0);
v_resultType_5697_ = lean_ctor_get(v_cases_5695_, 1);
v_discr_5698_ = lean_ctor_get(v_cases_5695_, 2);
v_alts_5699_ = lean_ctor_get(v_cases_5695_, 3);
v_isSharedCheck_5740_ = !lean_is_exclusive(v_cases_5695_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5701_ = v_cases_5695_;
v_isShared_5702_ = v_isSharedCheck_5740_;
goto v_resetjp_5700_;
}
else
{
lean_inc(v_alts_5699_);
lean_inc(v_discr_5698_);
lean_inc(v_resultType_5697_);
lean_inc(v_typeName_5696_);
lean_dec(v_cases_5695_);
v___x_5701_ = lean_box(0);
v_isShared_5702_ = v_isSharedCheck_5740_;
goto v_resetjp_5700_;
}
v_resetjp_5700_:
{
lean_object* v___x_5703_; lean_object* v_discrVal_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
v___x_5703_ = lean_box(0);
v_discrVal_5704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5530_, v_discr_5698_, v___x_5703_);
v___x_5705_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5699_);
lean_inc(v_discr_5698_);
lean_inc_ref(v_resultType_5697_);
v___x_5706_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5697_, v_discrVal_5704_, v_discr_5698_, v_assignment_5530_, v___x_5705_, v_alts_5699_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
lean_dec(v_discrVal_5704_);
if (lean_obj_tag(v___x_5706_) == 0)
{
lean_object* v_a_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5731_; 
v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5731_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5731_ == 0)
{
v___x_5709_ = v___x_5706_;
v_isShared_5710_ = v_isSharedCheck_5731_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_a_5707_);
lean_dec(v___x_5706_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5731_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
size_t v___x_5711_; size_t v___x_5712_; uint8_t v___x_5713_; 
v___x_5711_ = lean_ptr_addr(v_alts_5699_);
lean_dec_ref(v_alts_5699_);
v___x_5712_ = lean_ptr_addr(v_a_5707_);
v___x_5713_ = lean_usize_dec_eq(v___x_5711_, v___x_5712_);
if (v___x_5713_ == 0)
{
lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5726_; 
v_isSharedCheck_5726_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5726_ == 0)
{
lean_object* v_unused_5727_; 
v_unused_5727_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5727_);
v___x_5715_ = v_code_5531_;
v_isShared_5716_ = v_isSharedCheck_5726_;
goto v_resetjp_5714_;
}
else
{
lean_dec(v_code_5531_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5726_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
lean_object* v___x_5718_; 
if (v_isShared_5702_ == 0)
{
lean_ctor_set(v___x_5701_, 3, v_a_5707_);
v___x_5718_ = v___x_5701_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_typeName_5696_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v_resultType_5697_);
lean_ctor_set(v_reuseFailAlloc_5725_, 2, v_discr_5698_);
lean_ctor_set(v_reuseFailAlloc_5725_, 3, v_a_5707_);
v___x_5718_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
lean_object* v___x_5720_; 
if (v_isShared_5716_ == 0)
{
lean_ctor_set(v___x_5715_, 0, v___x_5718_);
v___x_5720_ = v___x_5715_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v___x_5718_);
v___x_5720_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
lean_object* v___x_5722_; 
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 0, v___x_5720_);
v___x_5722_ = v___x_5709_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5723_; 
v_reuseFailAlloc_5723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5723_, 0, v___x_5720_);
v___x_5722_ = v_reuseFailAlloc_5723_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
return v___x_5722_;
}
}
}
}
}
else
{
lean_object* v___x_5729_; 
lean_dec(v_a_5707_);
lean_del_object(v___x_5701_);
lean_dec(v_discr_5698_);
lean_dec_ref(v_resultType_5697_);
lean_dec(v_typeName_5696_);
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 0, v_code_5531_);
v___x_5729_ = v___x_5709_;
goto v_reusejp_5728_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_code_5531_);
v___x_5729_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5728_;
}
v_reusejp_5728_:
{
return v___x_5729_;
}
}
}
}
else
{
lean_object* v_a_5732_; lean_object* v___x_5734_; uint8_t v_isShared_5735_; uint8_t v_isSharedCheck_5739_; 
lean_del_object(v___x_5701_);
lean_dec_ref(v_alts_5699_);
lean_dec(v_discr_5698_);
lean_dec_ref(v_resultType_5697_);
lean_dec(v_typeName_5696_);
lean_dec_ref_known(v_code_5531_, 1);
v_a_5732_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5739_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5739_ == 0)
{
v___x_5734_ = v___x_5706_;
v_isShared_5735_ = v_isSharedCheck_5739_;
goto v_resetjp_5733_;
}
else
{
lean_inc(v_a_5732_);
lean_dec(v___x_5706_);
v___x_5734_ = lean_box(0);
v_isShared_5735_ = v_isSharedCheck_5739_;
goto v_resetjp_5733_;
}
v_resetjp_5733_:
{
lean_object* v___x_5737_; 
if (v_isShared_5735_ == 0)
{
v___x_5737_ = v___x_5734_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5738_; 
v_reuseFailAlloc_5738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5738_, 0, v_a_5732_);
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
default: 
{
lean_object* v___x_5741_; 
v___x_5741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5741_, 0, v_code_5531_);
return v___x_5741_;
}
}
v___jp_5537_:
{
lean_object* v_params_5544_; lean_object* v_type_5545_; lean_object* v_value_5546_; uint8_t v___x_5547_; lean_object* v___x_5548_; 
v_params_5544_ = lean_ctor_get(v_decl_5538_, 2);
lean_inc_ref(v_params_5544_);
v_type_5545_ = lean_ctor_get(v_decl_5538_, 3);
lean_inc_ref(v_type_5545_);
v_value_5546_ = lean_ctor_get(v_decl_5538_, 4);
v___x_5547_ = 0;
lean_inc_ref(v_value_5546_);
v___x_5548_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5530_, v_value_5546_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_);
if (lean_obj_tag(v___x_5548_) == 0)
{
lean_object* v_a_5549_; lean_object* v___x_5550_; 
v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
lean_inc(v_a_5549_);
lean_dec_ref_known(v___x_5548_, 1);
v___x_5550_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5547_, v_decl_5538_, v_type_5545_, v_params_5544_, v_a_5549_, v___y_5541_);
if (lean_obj_tag(v___x_5550_) == 0)
{
lean_object* v_a_5551_; lean_object* v___x_5552_; 
v_a_5551_ = lean_ctor_get(v___x_5550_, 0);
lean_inc(v_a_5551_);
lean_dec_ref_known(v___x_5550_, 1);
v___x_5552_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5530_, v_k_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_);
if (lean_obj_tag(v___x_5552_) == 0)
{
switch(lean_obj_tag(v_code_5531_))
{
case 1:
{
lean_object* v_a_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5592_; 
v_a_5553_ = lean_ctor_get(v___x_5552_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5555_ = v___x_5552_;
v_isShared_5556_ = v_isSharedCheck_5592_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_a_5553_);
lean_dec(v___x_5552_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5592_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v_decl_5557_; lean_object* v_k_5558_; size_t v___x_5559_; size_t v___x_5560_; uint8_t v___x_5561_; 
v_decl_5557_ = lean_ctor_get(v_code_5531_, 0);
v_k_5558_ = lean_ctor_get(v_code_5531_, 1);
v___x_5559_ = lean_ptr_addr(v_k_5558_);
v___x_5560_ = lean_ptr_addr(v_a_5553_);
v___x_5561_ = lean_usize_dec_eq(v___x_5559_, v___x_5560_);
if (v___x_5561_ == 0)
{
lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5571_; 
v_isSharedCheck_5571_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5571_ == 0)
{
lean_object* v_unused_5572_; lean_object* v_unused_5573_; 
v_unused_5572_ = lean_ctor_get(v_code_5531_, 1);
lean_dec(v_unused_5572_);
v_unused_5573_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5573_);
v___x_5563_ = v_code_5531_;
v_isShared_5564_ = v_isSharedCheck_5571_;
goto v_resetjp_5562_;
}
else
{
lean_dec(v_code_5531_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5571_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 1, v_a_5553_);
lean_ctor_set(v___x_5563_, 0, v_a_5551_);
v___x_5566_ = v___x_5563_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5551_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v_a_5553_);
v___x_5566_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 0, v___x_5566_);
v___x_5568_ = v___x_5555_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___x_5566_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
}
}
else
{
size_t v___x_5574_; size_t v___x_5575_; uint8_t v___x_5576_; 
v___x_5574_ = lean_ptr_addr(v_decl_5557_);
v___x_5575_ = lean_ptr_addr(v_a_5551_);
v___x_5576_ = lean_usize_dec_eq(v___x_5574_, v___x_5575_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5586_; 
v_isSharedCheck_5586_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5586_ == 0)
{
lean_object* v_unused_5587_; lean_object* v_unused_5588_; 
v_unused_5587_ = lean_ctor_get(v_code_5531_, 1);
lean_dec(v_unused_5587_);
v_unused_5588_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5588_);
v___x_5578_ = v_code_5531_;
v_isShared_5579_ = v_isSharedCheck_5586_;
goto v_resetjp_5577_;
}
else
{
lean_dec(v_code_5531_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5586_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5581_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 1, v_a_5553_);
lean_ctor_set(v___x_5578_, 0, v_a_5551_);
v___x_5581_ = v___x_5578_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5551_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_a_5553_);
v___x_5581_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
lean_object* v___x_5583_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 0, v___x_5581_);
v___x_5583_ = v___x_5555_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5581_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
}
else
{
lean_object* v___x_5590_; 
lean_dec(v_a_5553_);
lean_dec(v_a_5551_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 0, v_code_5531_);
v___x_5590_ = v___x_5555_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_code_5531_);
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
}
case 2:
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5632_; 
v_a_5593_ = lean_ctor_get(v___x_5552_, 0);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5595_ = v___x_5552_;
v_isShared_5596_ = v_isSharedCheck_5632_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5552_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5632_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v_decl_5597_; lean_object* v_k_5598_; size_t v___x_5599_; size_t v___x_5600_; uint8_t v___x_5601_; 
v_decl_5597_ = lean_ctor_get(v_code_5531_, 0);
v_k_5598_ = lean_ctor_get(v_code_5531_, 1);
v___x_5599_ = lean_ptr_addr(v_k_5598_);
v___x_5600_ = lean_ptr_addr(v_a_5593_);
v___x_5601_ = lean_usize_dec_eq(v___x_5599_, v___x_5600_);
if (v___x_5601_ == 0)
{
lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5611_; 
v_isSharedCheck_5611_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5611_ == 0)
{
lean_object* v_unused_5612_; lean_object* v_unused_5613_; 
v_unused_5612_ = lean_ctor_get(v_code_5531_, 1);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5613_);
v___x_5603_ = v_code_5531_;
v_isShared_5604_ = v_isSharedCheck_5611_;
goto v_resetjp_5602_;
}
else
{
lean_dec(v_code_5531_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5611_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 1, v_a_5593_);
lean_ctor_set(v___x_5603_, 0, v_a_5551_);
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5551_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_a_5593_);
v___x_5606_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
lean_object* v___x_5608_; 
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 0, v___x_5606_);
v___x_5608_ = v___x_5595_;
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
size_t v___x_5614_; size_t v___x_5615_; uint8_t v___x_5616_; 
v___x_5614_ = lean_ptr_addr(v_decl_5597_);
v___x_5615_ = lean_ptr_addr(v_a_5551_);
v___x_5616_ = lean_usize_dec_eq(v___x_5614_, v___x_5615_);
if (v___x_5616_ == 0)
{
lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5626_; 
v_isSharedCheck_5626_ = !lean_is_exclusive(v_code_5531_);
if (v_isSharedCheck_5626_ == 0)
{
lean_object* v_unused_5627_; lean_object* v_unused_5628_; 
v_unused_5627_ = lean_ctor_get(v_code_5531_, 1);
lean_dec(v_unused_5627_);
v_unused_5628_ = lean_ctor_get(v_code_5531_, 0);
lean_dec(v_unused_5628_);
v___x_5618_ = v_code_5531_;
v_isShared_5619_ = v_isSharedCheck_5626_;
goto v_resetjp_5617_;
}
else
{
lean_dec(v_code_5531_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5626_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 1, v_a_5593_);
lean_ctor_set(v___x_5618_, 0, v_a_5551_);
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5551_);
lean_ctor_set(v_reuseFailAlloc_5625_, 1, v_a_5593_);
v___x_5621_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
lean_object* v___x_5623_; 
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 0, v___x_5621_);
v___x_5623_ = v___x_5595_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v___x_5621_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
}
else
{
lean_object* v___x_5630_; 
lean_dec(v_a_5593_);
lean_dec(v_a_5551_);
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 0, v_code_5531_);
v___x_5630_ = v___x_5595_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_code_5531_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
}
}
default: 
{
lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5641_; 
lean_dec(v_a_5551_);
lean_dec_ref(v_code_5531_);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5641_ == 0)
{
lean_object* v_unused_5642_; 
v_unused_5642_ = lean_ctor_get(v___x_5552_, 0);
lean_dec(v_unused_5642_);
v___x_5634_ = v___x_5552_;
v_isShared_5635_ = v_isSharedCheck_5641_;
goto v_resetjp_5633_;
}
else
{
lean_dec(v___x_5552_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5641_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5639_; 
v___x_5636_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5637_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5636_);
if (v_isShared_5635_ == 0)
{
lean_ctor_set(v___x_5634_, 0, v___x_5637_);
v___x_5639_ = v___x_5634_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v___x_5637_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
}
else
{
lean_dec(v_a_5551_);
lean_dec_ref(v_code_5531_);
return v___x_5552_;
}
}
else
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5650_; 
lean_dec_ref(v_k_5539_);
lean_dec_ref(v_code_5531_);
v_a_5643_ = lean_ctor_get(v___x_5550_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5550_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5645_ = v___x_5550_;
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5550_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
else
{
lean_dec_ref(v_type_5545_);
lean_dec_ref(v_params_5544_);
lean_dec_ref(v_k_5539_);
lean_dec_ref(v_decl_5538_);
lean_dec_ref(v_code_5531_);
return v___x_5548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5742_, lean_object* v_code_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5742_, v_code_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec(v_a_5747_);
lean_dec_ref(v_a_5746_);
lean_dec(v_a_5745_);
lean_dec_ref(v_a_5744_);
lean_dec_ref(v_assignment_5742_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5750_, lean_object* v_discrVal_5751_, lean_object* v_discr_5752_, lean_object* v_assignment_5753_, lean_object* v_i_5754_, lean_object* v_as_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v_res_5761_; 
v_res_5761_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5750_, v_discrVal_5751_, v_discr_5752_, v_assignment_5753_, v_i_5754_, v_as_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
lean_dec(v___y_5759_);
lean_dec_ref(v___y_5758_);
lean_dec(v___y_5757_);
lean_dec_ref(v___y_5756_);
lean_dec_ref(v_assignment_5753_);
lean_dec(v_discrVal_5751_);
return v_res_5761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5762_, lean_object* v_m_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v___x_5765_; 
v___x_5765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5763_, v_a_5764_);
return v___x_5765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5766_, lean_object* v_m_5767_, lean_object* v_a_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5766_, v_m_5767_, v_a_5768_);
lean_dec(v_a_5768_);
lean_dec_ref(v_m_5767_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5770_, size_t v_i_5771_, size_t v_stop_5772_, lean_object* v_b_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_){
_start:
{
lean_object* v___x_5779_; 
v___x_5779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5770_, v_i_5771_, v_stop_5772_, v_b_5773_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5780_, lean_object* v_i_5781_, lean_object* v_stop_5782_, lean_object* v_b_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_){
_start:
{
size_t v_i_boxed_5789_; size_t v_stop_boxed_5790_; lean_object* v_res_5791_; 
v_i_boxed_5789_ = lean_unbox_usize(v_i_5781_);
lean_dec(v_i_5781_);
v_stop_boxed_5790_ = lean_unbox_usize(v_stop_5782_);
lean_dec(v_stop_5782_);
v_res_5791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5780_, v_i_boxed_5789_, v_stop_boxed_5790_, v_b_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec_ref(v_as_5780_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5792_, lean_object* v_a_5793_, lean_object* v_x_5794_){
_start:
{
lean_object* v___x_5795_; 
v___x_5795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5793_, v_x_5794_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5796_, lean_object* v_a_5797_, lean_object* v_x_5798_){
_start:
{
lean_object* v_res_5799_; 
v_res_5799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5796_, v_a_5797_, v_x_5798_);
lean_dec(v_x_5798_);
lean_dec(v_a_5797_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5800_, lean_object* v_v_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_){
_start:
{
if (lean_obj_tag(v_v_5801_) == 0)
{
lean_object* v_code_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5831_; 
v_code_5807_ = lean_ctor_get(v_v_5801_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_v_5801_);
if (v_isSharedCheck_5831_ == 0)
{
v___x_5809_ = v_v_5801_;
v_isShared_5810_ = v_isSharedCheck_5831_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_code_5807_);
lean_dec(v_v_5801_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5831_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
lean_object* v___x_5811_; 
lean_inc(v___y_5805_);
lean_inc_ref(v___y_5804_);
lean_inc(v___y_5803_);
lean_inc_ref(v___y_5802_);
v___x_5811_ = lean_apply_6(v_f_5800_, v_code_5807_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, lean_box(0));
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5822_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5822_ == 0)
{
v___x_5814_ = v___x_5811_;
v_isShared_5815_ = v_isSharedCheck_5822_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_a_5812_);
lean_dec(v___x_5811_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5822_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5817_; 
if (v_isShared_5810_ == 0)
{
lean_ctor_set(v___x_5809_, 0, v_a_5812_);
v___x_5817_ = v___x_5809_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_a_5812_);
v___x_5817_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
lean_object* v___x_5819_; 
if (v_isShared_5815_ == 0)
{
lean_ctor_set(v___x_5814_, 0, v___x_5817_);
v___x_5819_ = v___x_5814_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v___x_5817_);
v___x_5819_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
return v___x_5819_;
}
}
}
}
else
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5830_; 
lean_del_object(v___x_5809_);
v_a_5823_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5825_ = v___x_5811_;
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5811_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v___x_5828_; 
if (v_isShared_5826_ == 0)
{
v___x_5828_ = v___x_5825_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_a_5823_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
return v___x_5828_;
}
}
}
}
}
else
{
lean_object* v___x_5832_; 
lean_dec_ref(v_f_5800_);
v___x_5832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5832_, 0, v_v_5801_);
return v___x_5832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5833_, lean_object* v_v_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_){
_start:
{
lean_object* v_res_5840_; 
v_res_5840_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5833_, v_v_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
lean_dec(v___y_5838_);
lean_dec_ref(v___y_5837_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
return v_res_5840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5841_, lean_object* v_f_5842_, lean_object* v_v_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
lean_object* v___x_5849_; 
v___x_5849_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5842_, v_v_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5850_, lean_object* v_f_5851_, lean_object* v_v_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_){
_start:
{
uint8_t v_pu_boxed_5858_; lean_object* v_res_5859_; 
v_pu_boxed_5858_ = lean_unbox(v_pu_5850_);
v_res_5859_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5858_, v_f_5851_, v_v_5852_, v___y_5853_, v___y_5854_, v___y_5855_, v___y_5856_);
lean_dec(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5860_, lean_object* v_x_5861_){
_start:
{
if (lean_obj_tag(v_x_5861_) == 0)
{
return v_x_5860_;
}
else
{
lean_object* v_key_5862_; lean_object* v_value_5863_; lean_object* v_tail_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; 
v_key_5862_ = lean_ctor_get(v_x_5861_, 0);
v_value_5863_ = lean_ctor_get(v_x_5861_, 1);
v_tail_5864_ = lean_ctor_get(v_x_5861_, 2);
lean_inc(v_value_5863_);
lean_inc(v_key_5862_);
v___x_5865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5865_, 0, v_key_5862_);
lean_ctor_set(v___x_5865_, 1, v_value_5863_);
v___x_5866_ = lean_array_push(v_x_5860_, v___x_5865_);
v_x_5860_ = v___x_5866_;
v_x_5861_ = v_tail_5864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5868_, lean_object* v_x_5869_){
_start:
{
lean_object* v_res_5870_; 
v_res_5870_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5868_, v_x_5869_);
lean_dec(v_x_5869_);
return v_res_5870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5871_, size_t v_i_5872_, size_t v_stop_5873_, lean_object* v_b_5874_){
_start:
{
uint8_t v___x_5875_; 
v___x_5875_ = lean_usize_dec_eq(v_i_5872_, v_stop_5873_);
if (v___x_5875_ == 0)
{
lean_object* v___x_5876_; lean_object* v___x_5877_; size_t v___x_5878_; size_t v___x_5879_; 
v___x_5876_ = lean_array_uget_borrowed(v_as_5871_, v_i_5872_);
v___x_5877_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5874_, v___x_5876_);
v___x_5878_ = ((size_t)1ULL);
v___x_5879_ = lean_usize_add(v_i_5872_, v___x_5878_);
v_i_5872_ = v___x_5879_;
v_b_5874_ = v___x_5877_;
goto _start;
}
else
{
return v_b_5874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5881_, lean_object* v_i_5882_, lean_object* v_stop_5883_, lean_object* v_b_5884_){
_start:
{
size_t v_i_boxed_5885_; size_t v_stop_boxed_5886_; lean_object* v_res_5887_; 
v_i_boxed_5885_ = lean_unbox_usize(v_i_5882_);
lean_dec(v_i_5882_);
v_stop_boxed_5886_ = lean_unbox_usize(v_stop_5883_);
lean_dec(v_stop_5883_);
v_res_5887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5881_, v_i_boxed_5885_, v_stop_boxed_5886_, v_b_5884_);
lean_dec_ref(v_as_5881_);
return v_res_5887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5888_, size_t v_sz_5889_, size_t v_i_5890_, lean_object* v_bs_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_){
_start:
{
uint8_t v___x_5897_; 
v___x_5897_ = lean_usize_dec_lt(v_i_5890_, v_sz_5889_);
if (v___x_5897_ == 0)
{
lean_object* v___x_5898_; 
v___x_5898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5898_, 0, v_bs_5891_);
return v___x_5898_;
}
else
{
lean_object* v_v_5899_; lean_object* v_fst_5900_; lean_object* v_snd_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5925_; 
v_v_5899_ = lean_array_uget(v_bs_5891_, v_i_5890_);
v_fst_5900_ = lean_ctor_get(v_v_5899_, 0);
v_snd_5901_ = lean_ctor_get(v_v_5899_, 1);
v_isSharedCheck_5925_ = !lean_is_exclusive(v_v_5899_);
if (v_isSharedCheck_5925_ == 0)
{
v___x_5903_ = v_v_5899_;
v_isShared_5904_ = v_isSharedCheck_5925_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_snd_5901_);
lean_inc(v_fst_5900_);
lean_dec(v_v_5899_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5925_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5905_; lean_object* v_bs_x27_5906_; lean_object* v___x_5907_; 
v___x_5905_ = lean_unsigned_to_nat(0u);
v_bs_x27_5906_ = lean_array_uset(v_bs_5891_, v_i_5890_, v___x_5905_);
v___x_5907_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5900_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
if (lean_obj_tag(v___x_5907_) == 0)
{
lean_object* v_a_5908_; lean_object* v___x_5909_; lean_object* v___x_5911_; 
v_a_5908_ = lean_ctor_get(v___x_5907_, 0);
lean_inc(v_a_5908_);
lean_dec_ref_known(v___x_5907_, 1);
v___x_5909_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5908_, v_a_5888_);
if (v_isShared_5904_ == 0)
{
lean_ctor_set(v___x_5903_, 0, v___x_5909_);
v___x_5911_ = v___x_5903_;
goto v_reusejp_5910_;
}
else
{
lean_object* v_reuseFailAlloc_5916_; 
v_reuseFailAlloc_5916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5916_, 0, v___x_5909_);
lean_ctor_set(v_reuseFailAlloc_5916_, 1, v_snd_5901_);
v___x_5911_ = v_reuseFailAlloc_5916_;
goto v_reusejp_5910_;
}
v_reusejp_5910_:
{
size_t v___x_5912_; size_t v___x_5913_; lean_object* v___x_5914_; 
v___x_5912_ = ((size_t)1ULL);
v___x_5913_ = lean_usize_add(v_i_5890_, v___x_5912_);
v___x_5914_ = lean_array_uset(v_bs_x27_5906_, v_i_5890_, v___x_5911_);
v_i_5890_ = v___x_5913_;
v_bs_5891_ = v___x_5914_;
goto _start;
}
}
else
{
lean_object* v_a_5917_; lean_object* v___x_5919_; uint8_t v_isShared_5920_; uint8_t v_isSharedCheck_5924_; 
lean_dec_ref(v_bs_x27_5906_);
lean_del_object(v___x_5903_);
lean_dec(v_snd_5901_);
v_a_5917_ = lean_ctor_get(v___x_5907_, 0);
v_isSharedCheck_5924_ = !lean_is_exclusive(v___x_5907_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5919_ = v___x_5907_;
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
else
{
lean_inc(v_a_5917_);
lean_dec(v___x_5907_);
v___x_5919_ = lean_box(0);
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
v_resetjp_5918_:
{
lean_object* v___x_5922_; 
if (v_isShared_5920_ == 0)
{
v___x_5922_ = v___x_5919_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_a_5917_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5926_, lean_object* v_sz_5927_, lean_object* v_i_5928_, lean_object* v_bs_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_){
_start:
{
uint8_t v_a_2418__boxed_5935_; size_t v_sz_boxed_5936_; size_t v_i_boxed_5937_; lean_object* v_res_5938_; 
v_a_2418__boxed_5935_ = lean_unbox(v_a_5926_);
v_sz_boxed_5936_ = lean_unbox_usize(v_sz_5927_);
lean_dec(v_sz_5927_);
v_i_boxed_5937_ = lean_unbox_usize(v_i_5928_);
lean_dec(v_i_5928_);
v_res_5938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2418__boxed_5935_, v_sz_boxed_5936_, v_i_boxed_5937_, v_bs_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_);
lean_dec(v___y_5933_);
lean_dec_ref(v___y_5932_);
lean_dec(v___y_5931_);
lean_dec_ref(v___y_5930_);
return v_res_5938_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5939_){
_start:
{
lean_object* v_fst_5940_; lean_object* v_snd_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_5964_; 
v_fst_5940_ = lean_ctor_get(v_x_5939_, 0);
v_snd_5941_ = lean_ctor_get(v_x_5939_, 1);
v_isSharedCheck_5964_ = !lean_is_exclusive(v_x_5939_);
if (v_isSharedCheck_5964_ == 0)
{
v___x_5943_ = v_x_5939_;
v_isShared_5944_ = v_isSharedCheck_5964_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_snd_5941_);
lean_inc(v_fst_5940_);
lean_dec(v_x_5939_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_5964_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5949_; 
v___x_5945_ = l_String_quote(v_fst_5940_);
v___x_5946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5945_);
v___x_5947_ = lean_box(0);
if (v_isShared_5944_ == 0)
{
lean_ctor_set_tag(v___x_5943_, 1);
lean_ctor_set(v___x_5943_, 1, v___x_5947_);
lean_ctor_set(v___x_5943_, 0, v___x_5946_);
v___x_5949_ = v___x_5943_;
goto v_reusejp_5948_;
}
else
{
lean_object* v_reuseFailAlloc_5963_; 
v_reuseFailAlloc_5963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5963_, 0, v___x_5946_);
lean_ctor_set(v_reuseFailAlloc_5963_, 1, v___x_5947_);
v___x_5949_ = v_reuseFailAlloc_5963_;
goto v_reusejp_5948_;
}
v_reusejp_5948_:
{
lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; uint8_t v___x_5961_; lean_object* v___x_5962_; 
v___x_5950_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5941_);
v___x_5951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
lean_ctor_set(v___x_5951_, 1, v___x_5949_);
v___x_5952_ = l_List_reverse___redArg(v___x_5951_);
v___x_5953_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5954_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5952_, v___x_5953_);
v___x_5955_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5956_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
lean_ctor_set(v___x_5957_, 1, v___x_5954_);
v___x_5958_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5957_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5955_);
lean_ctor_set(v___x_5960_, 1, v___x_5959_);
v___x_5961_ = 0;
v___x_5962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5962_, 0, v___x_5960_);
lean_ctor_set_uint8(v___x_5962_, sizeof(void*)*1, v___x_5961_);
return v___x_5962_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5965_, lean_object* v_x_5966_, lean_object* v_x_5967_){
_start:
{
if (lean_obj_tag(v_x_5967_) == 0)
{
lean_dec(v_x_5965_);
return v_x_5966_;
}
else
{
lean_object* v_head_5968_; lean_object* v_tail_5969_; lean_object* v___x_5971_; uint8_t v_isShared_5972_; uint8_t v_isSharedCheck_5979_; 
v_head_5968_ = lean_ctor_get(v_x_5967_, 0);
v_tail_5969_ = lean_ctor_get(v_x_5967_, 1);
v_isSharedCheck_5979_ = !lean_is_exclusive(v_x_5967_);
if (v_isSharedCheck_5979_ == 0)
{
v___x_5971_ = v_x_5967_;
v_isShared_5972_ = v_isSharedCheck_5979_;
goto v_resetjp_5970_;
}
else
{
lean_inc(v_tail_5969_);
lean_inc(v_head_5968_);
lean_dec(v_x_5967_);
v___x_5971_ = lean_box(0);
v_isShared_5972_ = v_isSharedCheck_5979_;
goto v_resetjp_5970_;
}
v_resetjp_5970_:
{
lean_object* v___x_5974_; 
lean_inc(v_x_5965_);
if (v_isShared_5972_ == 0)
{
lean_ctor_set_tag(v___x_5971_, 5);
lean_ctor_set(v___x_5971_, 1, v_x_5965_);
lean_ctor_set(v___x_5971_, 0, v_x_5966_);
v___x_5974_ = v___x_5971_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_x_5966_);
lean_ctor_set(v_reuseFailAlloc_5978_, 1, v_x_5965_);
v___x_5974_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5975_; lean_object* v___x_5976_; 
v___x_5975_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5968_);
v___x_5976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5974_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v_x_5966_ = v___x_5976_;
v_x_5967_ = v_tail_5969_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5980_, lean_object* v_x_5981_, lean_object* v_x_5982_){
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
lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5990_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5983_);
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5980_, v___x_5991_, v_tail_5984_);
return v___x_5992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5995_, lean_object* v_x_5996_){
_start:
{
if (lean_obj_tag(v_x_5995_) == 0)
{
lean_object* v___x_5997_; 
lean_dec(v_x_5996_);
v___x_5997_ = lean_box(0);
return v___x_5997_;
}
else
{
lean_object* v_tail_5998_; 
v_tail_5998_ = lean_ctor_get(v_x_5995_, 1);
if (lean_obj_tag(v_tail_5998_) == 0)
{
lean_object* v_head_5999_; lean_object* v___x_6000_; 
lean_dec(v_x_5996_);
v_head_5999_ = lean_ctor_get(v_x_5995_, 0);
lean_inc(v_head_5999_);
lean_dec_ref_known(v_x_5995_, 2);
v___x_6000_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5999_);
return v___x_6000_;
}
else
{
lean_object* v_head_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
lean_inc(v_tail_5998_);
v_head_6001_ = lean_ctor_get(v_x_5995_, 0);
lean_inc(v_head_6001_);
lean_dec_ref_known(v_x_5995_, 2);
v___x_6002_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_6001_);
v___x_6003_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5996_, v___x_6002_, v_tail_5998_);
return v___x_6003_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_6005_; lean_object* v___x_6006_; 
v___x_6005_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_6006_ = lean_string_length(v___x_6005_);
return v___x_6006_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_6007_; lean_object* v___x_6008_; 
v___x_6007_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_6008_ = lean_nat_to_int(v___x_6007_);
return v___x_6008_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_6014_){
_start:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; uint8_t v___x_6017_; 
v___x_6015_ = lean_array_get_size(v_xs_6014_);
v___x_6016_ = lean_unsigned_to_nat(0u);
v___x_6017_ = lean_nat_dec_eq(v___x_6015_, v___x_6016_);
if (v___x_6017_ == 0)
{
lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
v___x_6018_ = lean_array_to_list(v_xs_6014_);
v___x_6019_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_6020_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_6018_, v___x_6019_);
v___x_6021_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_6022_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_6023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
lean_ctor_set(v___x_6023_, 1, v___x_6020_);
v___x_6024_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6023_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___x_6026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6021_);
lean_ctor_set(v___x_6026_, 1, v___x_6025_);
v___x_6027_ = l_Std_Format_fill(v___x_6026_);
return v___x_6027_;
}
else
{
lean_object* v___x_6028_; 
lean_dec_ref(v_xs_6014_);
v___x_6028_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_6028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_6031_, lean_object* v_decl_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_){
_start:
{
lean_object* v___y_6039_; lean_object* v___y_6040_; lean_object* v___y_6041_; lean_object* v___y_6042_; lean_object* v_toCold_6072_; lean_object* v_options_6073_; uint8_t v_hasTrace_6074_; 
v_toCold_6072_ = lean_ctor_get(v_a_6035_, 0);
v_options_6073_ = lean_ctor_get(v_toCold_6072_, 2);
v_hasTrace_6074_ = lean_ctor_get_uint8(v_options_6073_, sizeof(void*)*1);
if (v_hasTrace_6074_ == 0)
{
v___y_6039_ = v_a_6033_;
v___y_6040_ = v_a_6034_;
v___y_6041_ = v_a_6035_;
v___y_6042_ = v_a_6036_;
goto v___jp_6038_;
}
else
{
lean_object* v_inheritedTraceOptions_6075_; lean_object* v_cls_6076_; uint8_t v___y_6078_; lean_object* v___y_6079_; lean_object* v___x_6115_; uint8_t v___x_6116_; 
v_inheritedTraceOptions_6075_ = lean_ctor_get(v_toCold_6072_, 11);
v_cls_6076_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6115_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6075_, v_options_6073_, v___x_6115_);
if (v___x_6116_ == 0)
{
v___y_6039_ = v_a_6033_;
v___y_6040_ = v_a_6034_;
v___y_6041_ = v_a_6035_;
v___y_6042_ = v_a_6036_;
goto v___jp_6038_;
}
else
{
lean_object* v_size_6117_; lean_object* v_buckets_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; uint8_t v___x_6122_; 
v_size_6117_ = lean_ctor_get(v_assignment_6031_, 0);
v_buckets_6118_ = lean_ctor_get(v_assignment_6031_, 1);
v___x_6119_ = lean_mk_empty_array_with_capacity(v_size_6117_);
v___x_6120_ = lean_unsigned_to_nat(0u);
v___x_6121_ = lean_array_get_size(v_buckets_6118_);
v___x_6122_ = lean_nat_dec_lt(v___x_6120_, v___x_6121_);
if (v___x_6122_ == 0)
{
v___y_6078_ = v___x_6116_;
v___y_6079_ = v___x_6119_;
goto v___jp_6077_;
}
else
{
size_t v___x_6123_; size_t v___x_6124_; lean_object* v___x_6125_; 
v___x_6123_ = ((size_t)0ULL);
v___x_6124_ = lean_usize_of_nat(v___x_6121_);
v___x_6125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6118_, v___x_6123_, v___x_6124_, v___x_6119_);
v___y_6078_ = v___x_6116_;
v___y_6079_ = v___x_6125_;
goto v___jp_6077_;
}
}
v___jp_6077_:
{
size_t v_sz_6080_; size_t v___x_6081_; lean_object* v___x_6082_; 
v_sz_6080_ = lean_array_size(v___y_6079_);
v___x_6081_ = ((size_t)0ULL);
v___x_6082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6078_, v_sz_6080_, v___x_6081_, v___y_6079_, v_a_6033_, v_a_6034_, v_a_6035_, v_a_6036_);
if (lean_obj_tag(v___x_6082_) == 0)
{
lean_object* v_toSignature_6083_; lean_object* v_a_6084_; lean_object* v_name_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; 
v_toSignature_6083_ = lean_ctor_get(v_decl_6032_, 0);
v_a_6084_ = lean_ctor_get(v___x_6082_, 0);
lean_inc(v_a_6084_);
lean_dec_ref_known(v___x_6082_, 1);
v_name_6085_ = lean_ctor_get(v_toSignature_6083_, 0);
v___x_6086_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6085_);
v___x_6087_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6085_, v___y_6078_);
v___x_6088_ = lean_string_append(v___x_6086_, v___x_6087_);
lean_dec_ref(v___x_6087_);
v___x_6089_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6090_ = lean_string_append(v___x_6088_, v___x_6089_);
v___x_6091_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6084_);
v___x_6092_ = l_Std_Format_defWidth;
v___x_6093_ = lean_unsigned_to_nat(0u);
v___x_6094_ = l_Std_Format_pretty(v___x_6091_, v___x_6092_, v___x_6093_, v___x_6093_);
v___x_6095_ = lean_string_append(v___x_6090_, v___x_6094_);
lean_dec_ref(v___x_6094_);
v___x_6096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
v___x_6097_ = l_Lean_MessageData_ofFormat(v___x_6096_);
v___x_6098_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_6076_, v___x_6097_, v_a_6033_, v_a_6034_, v_a_6035_, v_a_6036_);
if (lean_obj_tag(v___x_6098_) == 0)
{
lean_dec_ref_known(v___x_6098_, 1);
v___y_6039_ = v_a_6033_;
v___y_6040_ = v_a_6034_;
v___y_6041_ = v_a_6035_;
v___y_6042_ = v_a_6036_;
goto v___jp_6038_;
}
else
{
lean_object* v_a_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6106_; 
lean_dec_ref(v_decl_6032_);
lean_dec_ref(v_assignment_6031_);
v_a_6099_ = lean_ctor_get(v___x_6098_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v___x_6098_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6101_ = v___x_6098_;
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
else
{
lean_inc(v_a_6099_);
lean_dec(v___x_6098_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6104_; 
if (v_isShared_6102_ == 0)
{
v___x_6104_ = v___x_6101_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6099_);
v___x_6104_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
return v___x_6104_;
}
}
}
}
else
{
lean_object* v_a_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6114_; 
lean_dec_ref(v_decl_6032_);
lean_dec_ref(v_assignment_6031_);
v_a_6107_ = lean_ctor_get(v___x_6082_, 0);
v_isSharedCheck_6114_ = !lean_is_exclusive(v___x_6082_);
if (v_isSharedCheck_6114_ == 0)
{
v___x_6109_ = v___x_6082_;
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
else
{
lean_inc(v_a_6107_);
lean_dec(v___x_6082_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6112_; 
if (v_isShared_6110_ == 0)
{
v___x_6112_ = v___x_6109_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6113_; 
v_reuseFailAlloc_6113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_a_6107_);
v___x_6112_ = v_reuseFailAlloc_6113_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
return v___x_6112_;
}
}
}
}
}
v___jp_6038_:
{
lean_object* v_toSignature_6043_; lean_object* v_value_6044_; uint8_t v_recursive_6045_; lean_object* v_inlineAttr_x3f_6046_; lean_object* v___x_6048_; uint8_t v_isShared_6049_; uint8_t v_isSharedCheck_6071_; 
v_toSignature_6043_ = lean_ctor_get(v_decl_6032_, 0);
v_value_6044_ = lean_ctor_get(v_decl_6032_, 1);
v_recursive_6045_ = lean_ctor_get_uint8(v_decl_6032_, sizeof(void*)*3);
v_inlineAttr_x3f_6046_ = lean_ctor_get(v_decl_6032_, 2);
v_isSharedCheck_6071_ = !lean_is_exclusive(v_decl_6032_);
if (v_isSharedCheck_6071_ == 0)
{
v___x_6048_ = v_decl_6032_;
v_isShared_6049_ = v_isSharedCheck_6071_;
goto v_resetjp_6047_;
}
else
{
lean_inc(v_inlineAttr_x3f_6046_);
lean_inc(v_value_6044_);
lean_inc(v_toSignature_6043_);
lean_dec(v_decl_6032_);
v___x_6048_ = lean_box(0);
v_isShared_6049_ = v_isSharedCheck_6071_;
goto v_resetjp_6047_;
}
v_resetjp_6047_:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; 
v___x_6050_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_6050_, 0, v_assignment_6031_);
v___x_6051_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_6050_, v_value_6044_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_);
if (lean_obj_tag(v___x_6051_) == 0)
{
lean_object* v_a_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6062_; 
v_a_6052_ = lean_ctor_get(v___x_6051_, 0);
v_isSharedCheck_6062_ = !lean_is_exclusive(v___x_6051_);
if (v_isSharedCheck_6062_ == 0)
{
v___x_6054_ = v___x_6051_;
v_isShared_6055_ = v_isSharedCheck_6062_;
goto v_resetjp_6053_;
}
else
{
lean_inc(v_a_6052_);
lean_dec(v___x_6051_);
v___x_6054_ = lean_box(0);
v_isShared_6055_ = v_isSharedCheck_6062_;
goto v_resetjp_6053_;
}
v_resetjp_6053_:
{
lean_object* v___x_6057_; 
if (v_isShared_6049_ == 0)
{
lean_ctor_set(v___x_6048_, 1, v_a_6052_);
v___x_6057_ = v___x_6048_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6061_; 
v_reuseFailAlloc_6061_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6061_, 0, v_toSignature_6043_);
lean_ctor_set(v_reuseFailAlloc_6061_, 1, v_a_6052_);
lean_ctor_set(v_reuseFailAlloc_6061_, 2, v_inlineAttr_x3f_6046_);
lean_ctor_set_uint8(v_reuseFailAlloc_6061_, sizeof(void*)*3, v_recursive_6045_);
v___x_6057_ = v_reuseFailAlloc_6061_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
lean_object* v___x_6059_; 
if (v_isShared_6055_ == 0)
{
lean_ctor_set(v___x_6054_, 0, v___x_6057_);
v___x_6059_ = v___x_6054_;
goto v_reusejp_6058_;
}
else
{
lean_object* v_reuseFailAlloc_6060_; 
v_reuseFailAlloc_6060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6060_, 0, v___x_6057_);
v___x_6059_ = v_reuseFailAlloc_6060_;
goto v_reusejp_6058_;
}
v_reusejp_6058_:
{
return v___x_6059_;
}
}
}
}
else
{
lean_object* v_a_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6070_; 
lean_del_object(v___x_6048_);
lean_dec(v_inlineAttr_x3f_6046_);
lean_dec_ref(v_toSignature_6043_);
v_a_6063_ = lean_ctor_get(v___x_6051_, 0);
v_isSharedCheck_6070_ = !lean_is_exclusive(v___x_6051_);
if (v_isSharedCheck_6070_ == 0)
{
v___x_6065_ = v___x_6051_;
v_isShared_6066_ = v_isSharedCheck_6070_;
goto v_resetjp_6064_;
}
else
{
lean_inc(v_a_6063_);
lean_dec(v___x_6051_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6070_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v___x_6068_; 
if (v_isShared_6066_ == 0)
{
v___x_6068_ = v___x_6065_;
goto v_reusejp_6067_;
}
else
{
lean_object* v_reuseFailAlloc_6069_; 
v_reuseFailAlloc_6069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6069_, 0, v_a_6063_);
v___x_6068_ = v_reuseFailAlloc_6069_;
goto v_reusejp_6067_;
}
v_reusejp_6067_:
{
return v___x_6068_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6126_, lean_object* v_decl_6127_, lean_object* v_a_6128_, lean_object* v_a_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_){
_start:
{
lean_object* v_res_6133_; 
v_res_6133_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6126_, v_decl_6127_, v_a_6128_, v_a_6129_, v_a_6130_, v_a_6131_);
lean_dec(v_a_6131_);
lean_dec_ref(v_a_6130_);
lean_dec(v_a_6129_);
lean_dec_ref(v_a_6128_);
return v_res_6133_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6134_, lean_object* v_x_6135_){
_start:
{
lean_object* v___x_6136_; 
v___x_6136_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6134_);
return v___x_6136_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6137_, lean_object* v_x_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6137_, v_x_6138_);
lean_dec(v_x_6138_);
return v_res_6139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6140_, size_t v_i_6141_, lean_object* v_bs_6142_){
_start:
{
uint8_t v___x_6143_; 
v___x_6143_ = lean_usize_dec_lt(v_i_6141_, v_sz_6140_);
if (v___x_6143_ == 0)
{
return v_bs_6142_;
}
else
{
lean_object* v_v_6144_; lean_object* v_toSignature_6145_; lean_object* v_name_6146_; lean_object* v___x_6147_; lean_object* v_bs_x27_6148_; size_t v___x_6149_; size_t v___x_6150_; lean_object* v___x_6151_; 
v_v_6144_ = lean_array_uget_borrowed(v_bs_6142_, v_i_6141_);
v_toSignature_6145_ = lean_ctor_get(v_v_6144_, 0);
v_name_6146_ = lean_ctor_get(v_toSignature_6145_, 0);
lean_inc(v_name_6146_);
v___x_6147_ = lean_unsigned_to_nat(0u);
v_bs_x27_6148_ = lean_array_uset(v_bs_6142_, v_i_6141_, v___x_6147_);
v___x_6149_ = ((size_t)1ULL);
v___x_6150_ = lean_usize_add(v_i_6141_, v___x_6149_);
v___x_6151_ = lean_array_uset(v_bs_x27_6148_, v_i_6141_, v_name_6146_);
v_i_6141_ = v___x_6150_;
v_bs_6142_ = v___x_6151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6153_, lean_object* v_i_6154_, lean_object* v_bs_6155_){
_start:
{
size_t v_sz_boxed_6156_; size_t v_i_boxed_6157_; lean_object* v_res_6158_; 
v_sz_boxed_6156_ = lean_unbox_usize(v_sz_6153_);
lean_dec(v_sz_6153_);
v_i_boxed_6157_ = lean_unbox_usize(v_i_6154_);
lean_dec(v_i_6154_);
v_res_6158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6156_, v_i_boxed_6157_, v_bs_6155_);
return v_res_6158_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6159_, lean_object* v_a_6160_){
_start:
{
if (lean_obj_tag(v_a_6159_) == 0)
{
lean_object* v___x_6161_; 
v___x_6161_ = l_List_reverse___redArg(v_a_6160_);
return v___x_6161_;
}
else
{
lean_object* v_head_6162_; lean_object* v_tail_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6172_; 
v_head_6162_ = lean_ctor_get(v_a_6159_, 0);
v_tail_6163_ = lean_ctor_get(v_a_6159_, 1);
v_isSharedCheck_6172_ = !lean_is_exclusive(v_a_6159_);
if (v_isSharedCheck_6172_ == 0)
{
v___x_6165_ = v_a_6159_;
v_isShared_6166_ = v_isSharedCheck_6172_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_tail_6163_);
lean_inc(v_head_6162_);
lean_dec(v_a_6159_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6172_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6167_; lean_object* v___x_6169_; 
v___x_6167_ = l_Lean_MessageData_ofName(v_head_6162_);
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 1, v_a_6160_);
lean_ctor_set(v___x_6165_, 0, v___x_6167_);
v___x_6169_ = v___x_6165_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v___x_6167_);
lean_ctor_set(v_reuseFailAlloc_6171_, 1, v_a_6160_);
v___x_6169_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
v_a_6159_ = v_tail_6163_;
v_a_6160_ = v___x_6169_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6174_; lean_object* v___x_6175_; 
v___x_6174_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6175_ = l_Lean_stringToMessageData(v___x_6174_);
return v___x_6175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6176_, lean_object* v_x_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_){
_start:
{
lean_object* v___x_6185_; size_t v_sz_6186_; size_t v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; 
v___x_6185_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6186_ = lean_array_size(v___y_6176_);
v___x_6187_ = ((size_t)0ULL);
v___x_6188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6186_, v___x_6187_, v___y_6176_);
v___x_6189_ = lean_array_to_list(v___x_6188_);
v___x_6190_ = lean_box(0);
v___x_6191_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6189_, v___x_6190_);
v___x_6192_ = l_Lean_MessageData_ofList(v___x_6191_);
v___x_6193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6185_);
lean_ctor_set(v___x_6193_, 1, v___x_6192_);
v___x_6194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6193_);
return v___x_6194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6195_, lean_object* v_x_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_){
_start:
{
lean_object* v_res_6204_; 
v_res_6204_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6195_, v_x_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_);
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6199_);
lean_dec(v___y_6198_);
lean_dec_ref(v___y_6197_);
lean_dec_ref(v_x_6196_);
return v_res_6204_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_6205_; 
v___x_6205_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default___redArg();
return v___x_6205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6206_, lean_object* v_n_6207_, lean_object* v_j_6208_, lean_object* v_a_6209_){
_start:
{
lean_object* v_zero_6210_; uint8_t v_isZero_6211_; 
v_zero_6210_ = lean_unsigned_to_nat(0u);
v_isZero_6211_ = lean_nat_dec_eq(v_j_6208_, v_zero_6210_);
if (v_isZero_6211_ == 1)
{
lean_dec(v_j_6208_);
return v_a_6209_;
}
else
{
lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v_toSignature_6215_; uint8_t v_safe_6216_; lean_object* v_one_6217_; lean_object* v_n_6218_; 
v___x_6212_ = lean_nat_sub(v_n_6207_, v_j_6208_);
v___x_6213_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6214_ = lean_array_get_borrowed(v___x_6213_, v___y_6206_, v___x_6212_);
lean_dec(v___x_6212_);
v_toSignature_6215_ = lean_ctor_get(v___x_6214_, 0);
v_safe_6216_ = lean_ctor_get_uint8(v_toSignature_6215_, sizeof(void*)*4);
v_one_6217_ = lean_unsigned_to_nat(1u);
v_n_6218_ = lean_nat_sub(v_j_6208_, v_one_6217_);
lean_dec(v_j_6208_);
if (v_safe_6216_ == 0)
{
lean_object* v___x_6219_; lean_object* v___x_6220_; 
v___x_6219_ = lean_box(1);
v___x_6220_ = lean_array_push(v_a_6209_, v___x_6219_);
v_j_6208_ = v_n_6218_;
v_a_6209_ = v___x_6220_;
goto _start;
}
else
{
lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6222_ = lean_box(0);
v___x_6223_ = lean_array_push(v_a_6209_, v___x_6222_);
v_j_6208_ = v_n_6218_;
v_a_6209_ = v___x_6223_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6225_, lean_object* v_n_6226_, lean_object* v_j_6227_, lean_object* v_a_6228_){
_start:
{
lean_object* v_res_6229_; 
v_res_6229_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6225_, v_n_6226_, v_j_6227_, v_a_6228_);
lean_dec(v_n_6226_);
lean_dec_ref(v___y_6225_);
return v_res_6229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6230_, size_t v_sz_6231_, size_t v_i_6232_, lean_object* v_bs_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
uint8_t v___x_6239_; 
v___x_6239_ = lean_usize_dec_lt(v_i_6232_, v_sz_6231_);
if (v___x_6239_ == 0)
{
lean_object* v___x_6240_; 
v___x_6240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6240_, 0, v_bs_6233_);
return v___x_6240_;
}
else
{
lean_object* v_v_6241_; lean_object* v_toSignature_6242_; uint8_t v_safe_6243_; lean_object* v___x_6244_; lean_object* v_bs_x27_6245_; lean_object* v_a_6247_; 
v_v_6241_ = lean_array_uget(v_bs_6233_, v_i_6232_);
v_toSignature_6242_ = lean_ctor_get(v_v_6241_, 0);
v_safe_6243_ = lean_ctor_get_uint8(v_toSignature_6242_, sizeof(void*)*4);
v___x_6244_ = lean_unsigned_to_nat(0u);
v_bs_x27_6245_ = lean_array_uset(v_bs_6233_, v_i_6232_, v___x_6244_);
if (v_safe_6243_ == 0)
{
v_a_6247_ = v_v_6241_;
goto v___jp_6246_;
}
else
{
lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6252_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0);
v___x_6253_ = lean_usize_to_nat(v_i_6232_);
v___x_6254_ = lean_array_get_borrowed(v___x_6252_, v___x_6230_, v___x_6253_);
lean_dec(v___x_6253_);
lean_inc(v___x_6254_);
v___x_6255_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6254_, v_v_6241_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
if (lean_obj_tag(v___x_6255_) == 0)
{
lean_object* v_a_6256_; 
v_a_6256_ = lean_ctor_get(v___x_6255_, 0);
lean_inc(v_a_6256_);
lean_dec_ref_known(v___x_6255_, 1);
v_a_6247_ = v_a_6256_;
goto v___jp_6246_;
}
else
{
lean_object* v_a_6257_; lean_object* v___x_6259_; uint8_t v_isShared_6260_; uint8_t v_isSharedCheck_6264_; 
lean_dec_ref(v_bs_x27_6245_);
v_a_6257_ = lean_ctor_get(v___x_6255_, 0);
v_isSharedCheck_6264_ = !lean_is_exclusive(v___x_6255_);
if (v_isSharedCheck_6264_ == 0)
{
v___x_6259_ = v___x_6255_;
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
else
{
lean_inc(v_a_6257_);
lean_dec(v___x_6255_);
v___x_6259_ = lean_box(0);
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
v_resetjp_6258_:
{
lean_object* v___x_6262_; 
if (v_isShared_6260_ == 0)
{
v___x_6262_ = v___x_6259_;
goto v_reusejp_6261_;
}
else
{
lean_object* v_reuseFailAlloc_6263_; 
v_reuseFailAlloc_6263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_a_6257_);
v___x_6262_ = v_reuseFailAlloc_6263_;
goto v_reusejp_6261_;
}
v_reusejp_6261_:
{
return v___x_6262_;
}
}
}
}
v___jp_6246_:
{
size_t v___x_6248_; size_t v___x_6249_; lean_object* v___x_6250_; 
v___x_6248_ = ((size_t)1ULL);
v___x_6249_ = lean_usize_add(v_i_6232_, v___x_6248_);
v___x_6250_ = lean_array_uset(v_bs_x27_6245_, v_i_6232_, v_a_6247_);
v_i_6232_ = v___x_6249_;
v_bs_6233_ = v___x_6250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6265_, lean_object* v_sz_6266_, lean_object* v_i_6267_, lean_object* v_bs_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
size_t v_sz_boxed_6274_; size_t v_i_boxed_6275_; lean_object* v_res_6276_; 
v_sz_boxed_6274_ = lean_unbox_usize(v_sz_6266_);
lean_dec(v_sz_6266_);
v_i_boxed_6275_ = lean_unbox_usize(v_i_6267_);
lean_dec(v_i_6267_);
v_res_6276_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6265_, v_sz_boxed_6274_, v_i_boxed_6275_, v_bs_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
lean_dec_ref(v___x_6265_);
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6279_, lean_object* v_pivot_6280_, lean_object* v_as_6281_, lean_object* v_i_6282_, lean_object* v_k_6283_){
_start:
{
uint8_t v___x_6284_; 
v___x_6284_ = lean_nat_dec_lt(v_k_6283_, v_hi_6279_);
if (v___x_6284_ == 0)
{
lean_object* v___x_6285_; lean_object* v___x_6286_; 
lean_dec(v_k_6283_);
lean_dec_ref(v_pivot_6280_);
v___x_6285_ = lean_array_fswap(v_as_6281_, v_i_6282_, v_hi_6279_);
v___x_6286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6286_, 0, v_i_6282_);
lean_ctor_set(v___x_6286_, 1, v___x_6285_);
return v___x_6286_;
}
else
{
lean_object* v___x_6287_; lean_object* v_toSignature_6288_; lean_object* v_toSignature_6289_; lean_object* v_name_6290_; lean_object* v_name_6291_; uint8_t v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; uint8_t v___x_6302_; 
v___x_6287_ = lean_array_fget_borrowed(v_as_6281_, v_k_6283_);
v_toSignature_6288_ = lean_ctor_get(v___x_6287_, 0);
v_toSignature_6289_ = lean_ctor_get(v_pivot_6280_, 0);
v_name_6290_ = lean_ctor_get(v_toSignature_6288_, 0);
v_name_6291_ = lean_ctor_get(v_toSignature_6289_, 0);
v___x_6292_ = 0;
v___x_6293_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6292_, v___x_6287_);
v___x_6294_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6295_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6296_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6290_);
v___x_6297_ = l_Lean_Name_toString(v_name_6290_, v___x_6284_);
v___x_6298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6298_, 0, v___x_6293_);
lean_ctor_set(v___x_6298_, 1, v___x_6297_);
v___x_6299_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6292_, v_pivot_6280_);
lean_inc(v_name_6291_);
v___x_6300_ = l_Lean_Name_toString(v_name_6291_, v___x_6284_);
v___x_6301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6301_, 0, v___x_6299_);
lean_ctor_set(v___x_6301_, 1, v___x_6300_);
v___x_6302_ = l_Prod_lexLtDec___redArg(v___x_6294_, v___x_6295_, v___x_6296_, v___x_6298_, v___x_6301_);
if (v___x_6302_ == 0)
{
lean_object* v___x_6303_; lean_object* v___x_6304_; 
v___x_6303_ = lean_unsigned_to_nat(1u);
v___x_6304_ = lean_nat_add(v_k_6283_, v___x_6303_);
lean_dec(v_k_6283_);
v_k_6283_ = v___x_6304_;
goto _start;
}
else
{
lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; 
v___x_6306_ = lean_array_fswap(v_as_6281_, v_i_6282_, v_k_6283_);
v___x_6307_ = lean_unsigned_to_nat(1u);
v___x_6308_ = lean_nat_add(v_i_6282_, v___x_6307_);
lean_dec(v_i_6282_);
v___x_6309_ = lean_nat_add(v_k_6283_, v___x_6307_);
lean_dec(v_k_6283_);
v_as_6281_ = v___x_6306_;
v_i_6282_ = v___x_6308_;
v_k_6283_ = v___x_6309_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6311_, lean_object* v_pivot_6312_, lean_object* v_as_6313_, lean_object* v_i_6314_, lean_object* v_k_6315_){
_start:
{
lean_object* v_res_6316_; 
v_res_6316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6311_, v_pivot_6312_, v_as_6313_, v_i_6314_, v_k_6315_);
lean_dec(v_hi_6311_);
return v_res_6316_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6317_, lean_object* v_l_6318_, lean_object* v_r_6319_){
_start:
{
lean_object* v_toSignature_6320_; lean_object* v_toSignature_6321_; lean_object* v_name_6322_; lean_object* v_name_6323_; uint8_t v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; uint8_t v___x_6334_; 
v_toSignature_6320_ = lean_ctor_get(v_l_6318_, 0);
v_toSignature_6321_ = lean_ctor_get(v_r_6319_, 0);
v_name_6322_ = lean_ctor_get(v_toSignature_6320_, 0);
lean_inc(v_name_6322_);
v_name_6323_ = lean_ctor_get(v_toSignature_6321_, 0);
lean_inc(v_name_6323_);
v___x_6324_ = 0;
v___x_6325_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6324_, v_l_6318_);
lean_dec_ref(v_l_6318_);
v___x_6326_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6327_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6328_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6329_ = l_Lean_Name_toString(v_name_6322_, v___x_6317_);
v___x_6330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6330_, 0, v___x_6325_);
lean_ctor_set(v___x_6330_, 1, v___x_6329_);
v___x_6331_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6324_, v_r_6319_);
lean_dec_ref(v_r_6319_);
v___x_6332_ = l_Lean_Name_toString(v_name_6323_, v___x_6317_);
v___x_6333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6333_, 0, v___x_6331_);
lean_ctor_set(v___x_6333_, 1, v___x_6332_);
v___x_6334_ = l_Prod_lexLtDec___redArg(v___x_6326_, v___x_6327_, v___x_6328_, v___x_6330_, v___x_6333_);
return v___x_6334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6335_, lean_object* v_l_6336_, lean_object* v_r_6337_){
_start:
{
uint8_t v___x_13221__boxed_6338_; uint8_t v_res_6339_; lean_object* v_r_6340_; 
v___x_13221__boxed_6338_ = lean_unbox(v___x_6335_);
v_res_6339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13221__boxed_6338_, v_l_6336_, v_r_6337_);
v_r_6340_ = lean_box(v_res_6339_);
return v_r_6340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6341_, lean_object* v_as_6342_, lean_object* v_lo_6343_, lean_object* v_hi_6344_){
_start:
{
lean_object* v___y_6346_; uint8_t v___x_6356_; 
v___x_6356_ = lean_nat_dec_lt(v_lo_6343_, v_hi_6344_);
if (v___x_6356_ == 0)
{
lean_dec(v_lo_6343_);
return v_as_6342_;
}
else
{
lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v_mid_6359_; lean_object* v___y_6361_; lean_object* v___y_6367_; lean_object* v___x_6372_; lean_object* v___x_6373_; uint8_t v___x_6374_; 
v___x_6357_ = lean_nat_add(v_lo_6343_, v_hi_6344_);
v___x_6358_ = lean_unsigned_to_nat(1u);
v_mid_6359_ = lean_nat_shiftr(v___x_6357_, v___x_6358_);
lean_dec(v___x_6357_);
v___x_6372_ = lean_array_fget_borrowed(v_as_6342_, v_mid_6359_);
v___x_6373_ = lean_array_fget_borrowed(v_as_6342_, v_lo_6343_);
lean_inc(v___x_6373_);
lean_inc(v___x_6372_);
v___x_6374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6356_, v___x_6372_, v___x_6373_);
if (v___x_6374_ == 0)
{
v___y_6367_ = v_as_6342_;
goto v___jp_6366_;
}
else
{
lean_object* v___x_6375_; 
v___x_6375_ = lean_array_fswap(v_as_6342_, v_lo_6343_, v_mid_6359_);
v___y_6367_ = v___x_6375_;
goto v___jp_6366_;
}
v___jp_6360_:
{
lean_object* v___x_6362_; lean_object* v___x_6363_; uint8_t v___x_6364_; 
v___x_6362_ = lean_array_fget_borrowed(v___y_6361_, v_mid_6359_);
v___x_6363_ = lean_array_fget_borrowed(v___y_6361_, v_hi_6344_);
lean_inc(v___x_6363_);
lean_inc(v___x_6362_);
v___x_6364_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6356_, v___x_6362_, v___x_6363_);
if (v___x_6364_ == 0)
{
lean_dec(v_mid_6359_);
v___y_6346_ = v___y_6361_;
goto v___jp_6345_;
}
else
{
lean_object* v___x_6365_; 
v___x_6365_ = lean_array_fswap(v___y_6361_, v_mid_6359_, v_hi_6344_);
lean_dec(v_mid_6359_);
v___y_6346_ = v___x_6365_;
goto v___jp_6345_;
}
}
v___jp_6366_:
{
lean_object* v___x_6368_; lean_object* v___x_6369_; uint8_t v___x_6370_; 
v___x_6368_ = lean_array_fget_borrowed(v___y_6367_, v_hi_6344_);
v___x_6369_ = lean_array_fget_borrowed(v___y_6367_, v_lo_6343_);
lean_inc(v___x_6369_);
lean_inc(v___x_6368_);
v___x_6370_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6356_, v___x_6368_, v___x_6369_);
if (v___x_6370_ == 0)
{
v___y_6361_ = v___y_6367_;
goto v___jp_6360_;
}
else
{
lean_object* v___x_6371_; 
v___x_6371_ = lean_array_fswap(v___y_6367_, v_lo_6343_, v_hi_6344_);
v___y_6361_ = v___x_6371_;
goto v___jp_6360_;
}
}
}
v___jp_6345_:
{
lean_object* v_pivot_6347_; lean_object* v___x_6348_; lean_object* v_fst_6349_; lean_object* v_snd_6350_; uint8_t v___x_6351_; 
v_pivot_6347_ = lean_array_fget(v___y_6346_, v_hi_6344_);
lean_inc_n(v_lo_6343_, 2);
v___x_6348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6344_, v_pivot_6347_, v___y_6346_, v_lo_6343_, v_lo_6343_);
v_fst_6349_ = lean_ctor_get(v___x_6348_, 0);
lean_inc(v_fst_6349_);
v_snd_6350_ = lean_ctor_get(v___x_6348_, 1);
lean_inc(v_snd_6350_);
lean_dec_ref(v___x_6348_);
v___x_6351_ = lean_nat_dec_le(v_hi_6344_, v_fst_6349_);
if (v___x_6351_ == 0)
{
lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; 
v___x_6352_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6341_, v_snd_6350_, v_lo_6343_, v_fst_6349_);
v___x_6353_ = lean_unsigned_to_nat(1u);
v___x_6354_ = lean_nat_add(v_fst_6349_, v___x_6353_);
lean_dec(v_fst_6349_);
v_as_6342_ = v___x_6352_;
v_lo_6343_ = v___x_6354_;
goto _start;
}
else
{
lean_dec(v_fst_6349_);
lean_dec(v_lo_6343_);
return v_snd_6350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6376_, lean_object* v_as_6377_, lean_object* v_lo_6378_, lean_object* v_hi_6379_){
_start:
{
lean_object* v_res_6380_; 
v_res_6380_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6376_, v_as_6377_, v_lo_6378_, v_hi_6379_);
lean_dec(v_hi_6379_);
lean_dec(v_n_6376_);
return v_res_6380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6381_, lean_object* v___x_6382_, lean_object* v_n_6383_, lean_object* v_j_6384_, lean_object* v_a_6385_){
_start:
{
lean_object* v_zero_6386_; uint8_t v_isZero_6387_; 
v_zero_6386_ = lean_unsigned_to_nat(0u);
v_isZero_6387_ = lean_nat_dec_eq(v_j_6384_, v_zero_6386_);
if (v_isZero_6387_ == 1)
{
lean_dec(v_j_6384_);
return v_a_6385_;
}
else
{
lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v_toSignature_6390_; lean_object* v_name_6391_; lean_object* v___x_6392_; lean_object* v_one_6393_; lean_object* v_n_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6388_ = lean_nat_sub(v_n_6383_, v_j_6384_);
v___x_6389_ = lean_array_fget_borrowed(v___y_6381_, v___x_6388_);
v_toSignature_6390_ = lean_ctor_get(v___x_6389_, 0);
v_name_6391_ = lean_ctor_get(v_toSignature_6390_, 0);
v___x_6392_ = lean_box(0);
v_one_6393_ = lean_unsigned_to_nat(1u);
v_n_6394_ = lean_nat_sub(v_j_6384_, v_one_6393_);
lean_dec(v_j_6384_);
v___x_6395_ = lean_array_get_borrowed(v___x_6392_, v___x_6382_, v___x_6388_);
lean_dec(v___x_6388_);
lean_inc(v___x_6395_);
lean_inc(v_name_6391_);
v___x_6396_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6385_, v_name_6391_, v___x_6395_);
v_j_6384_ = v_n_6394_;
v_a_6385_ = v___x_6396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6398_, lean_object* v___x_6399_, lean_object* v_n_6400_, lean_object* v_j_6401_, lean_object* v_a_6402_){
_start:
{
lean_object* v_res_6403_; 
v_res_6403_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6398_, v___x_6399_, v_n_6400_, v_j_6401_, v_a_6402_);
lean_dec(v_n_6400_);
lean_dec_ref(v___x_6399_);
lean_dec_ref(v___y_6398_);
return v_res_6403_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6404_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_6405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6405_, 0, v___x_6404_);
return v___x_6405_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6406_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6407_, 0, v___x_6406_);
lean_ctor_set(v___x_6407_, 1, v___x_6406_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6410_, lean_object* v_a_6411_, lean_object* v_a_6412_, lean_object* v_a_6413_, lean_object* v_a_6414_){
_start:
{
lean_object* v___y_6417_; lean_object* v___y_6418_; lean_object* v___y_6419_; size_t v___y_6420_; size_t v___y_6421_; lean_object* v___y_6422_; lean_object* v___y_6457_; uint8_t v___y_6458_; lean_object* v___y_6459_; lean_object* v___y_6460_; lean_object* v___y_6461_; lean_object* v___y_6462_; lean_object* v___y_6463_; size_t v___y_6464_; lean_object* v___y_6465_; uint8_t v___y_6466_; size_t v___y_6467_; lean_object* v___y_6468_; lean_object* v___y_6469_; lean_object* v___y_6470_; lean_object* v_a_6471_; lean_object* v___y_6481_; lean_object* v___y_6482_; uint8_t v___y_6483_; lean_object* v___y_6484_; lean_object* v___y_6485_; lean_object* v___y_6486_; lean_object* v___y_6487_; lean_object* v___y_6488_; size_t v___y_6489_; uint8_t v___y_6490_; size_t v___y_6491_; lean_object* v___y_6492_; lean_object* v___y_6493_; lean_object* v___y_6494_; lean_object* v_a_6495_; lean_object* v___x_6507_; lean_object* v___y_6509_; uint8_t v___y_6510_; lean_object* v___y_6511_; lean_object* v___y_6512_; lean_object* v___y_6513_; lean_object* v___y_6514_; lean_object* v___y_6515_; size_t v___y_6516_; uint8_t v___y_6517_; size_t v___y_6518_; lean_object* v___y_6519_; lean_object* v___y_6520_; lean_object* v___y_6562_; lean_object* v___x_6586_; lean_object* v___y_6588_; lean_object* v___y_6589_; uint8_t v___x_6591_; 
v___x_6507_ = lean_unsigned_to_nat(0u);
v___x_6586_ = lean_array_get_size(v_decls_6410_);
v___x_6591_ = lean_nat_dec_eq(v___x_6586_, v___x_6507_);
if (v___x_6591_ == 0)
{
lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___y_6595_; uint8_t v___x_6597_; 
v___x_6592_ = lean_unsigned_to_nat(1u);
v___x_6593_ = lean_nat_sub(v___x_6586_, v___x_6592_);
v___x_6597_ = lean_nat_dec_le(v___x_6507_, v___x_6593_);
if (v___x_6597_ == 0)
{
lean_inc(v___x_6593_);
v___y_6595_ = v___x_6593_;
goto v___jp_6594_;
}
else
{
v___y_6595_ = v___x_6507_;
goto v___jp_6594_;
}
v___jp_6594_:
{
uint8_t v___x_6596_; 
v___x_6596_ = lean_nat_dec_le(v___y_6595_, v___x_6593_);
if (v___x_6596_ == 0)
{
lean_dec(v___x_6593_);
lean_inc(v___y_6595_);
v___y_6588_ = v___y_6595_;
v___y_6589_ = v___y_6595_;
goto v___jp_6587_;
}
else
{
v___y_6588_ = v___y_6595_;
v___y_6589_ = v___x_6593_;
goto v___jp_6587_;
}
}
}
else
{
v___y_6562_ = v_decls_6410_;
goto v___jp_6561_;
}
v___jp_6416_:
{
if (lean_obj_tag(v___y_6422_) == 0)
{
lean_object* v___x_6423_; lean_object* v_assignments_6424_; lean_object* v_funVals_6425_; lean_object* v___x_6426_; lean_object* v_env_6427_; lean_object* v_nextMacroScope_6428_; lean_object* v_ngen_6429_; lean_object* v_auxDeclNGen_6430_; lean_object* v_traceState_6431_; lean_object* v_recordedDeps_6432_; lean_object* v_messages_6433_; lean_object* v_infoState_6434_; lean_object* v_snapshotTasks_6435_; lean_object* v___x_6437_; uint8_t v_isShared_6438_; uint8_t v_isSharedCheck_6446_; 
lean_dec_ref_known(v___y_6422_, 1);
v___x_6423_ = lean_st_ref_get(v___y_6419_);
lean_dec(v___y_6419_);
v_assignments_6424_ = lean_ctor_get(v___x_6423_, 0);
lean_inc_ref(v_assignments_6424_);
v_funVals_6425_ = lean_ctor_get(v___x_6423_, 1);
lean_inc_ref(v_funVals_6425_);
lean_dec(v___x_6423_);
v___x_6426_ = lean_st_ref_take(v_a_6414_);
v_env_6427_ = lean_ctor_get(v___x_6426_, 0);
v_nextMacroScope_6428_ = lean_ctor_get(v___x_6426_, 1);
v_ngen_6429_ = lean_ctor_get(v___x_6426_, 2);
v_auxDeclNGen_6430_ = lean_ctor_get(v___x_6426_, 3);
v_traceState_6431_ = lean_ctor_get(v___x_6426_, 4);
v_recordedDeps_6432_ = lean_ctor_get(v___x_6426_, 6);
v_messages_6433_ = lean_ctor_get(v___x_6426_, 7);
v_infoState_6434_ = lean_ctor_get(v___x_6426_, 8);
v_snapshotTasks_6435_ = lean_ctor_get(v___x_6426_, 9);
v_isSharedCheck_6446_ = !lean_is_exclusive(v___x_6426_);
if (v_isSharedCheck_6446_ == 0)
{
lean_object* v_unused_6447_; 
v_unused_6447_ = lean_ctor_get(v___x_6426_, 5);
lean_dec(v_unused_6447_);
v___x_6437_ = v___x_6426_;
v_isShared_6438_ = v_isSharedCheck_6446_;
goto v_resetjp_6436_;
}
else
{
lean_inc(v_snapshotTasks_6435_);
lean_inc(v_infoState_6434_);
lean_inc(v_messages_6433_);
lean_inc(v_recordedDeps_6432_);
lean_inc(v_traceState_6431_);
lean_inc(v_auxDeclNGen_6430_);
lean_inc(v_ngen_6429_);
lean_inc(v_nextMacroScope_6428_);
lean_inc(v_env_6427_);
lean_dec(v___x_6426_);
v___x_6437_ = lean_box(0);
v_isShared_6438_ = v_isSharedCheck_6446_;
goto v_resetjp_6436_;
}
v_resetjp_6436_:
{
lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6442_; 
lean_inc(v___y_6418_);
v___x_6439_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6417_, v_funVals_6425_, v___y_6418_, v___y_6418_, v_env_6427_);
lean_dec(v___y_6418_);
lean_dec_ref(v_funVals_6425_);
v___x_6440_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
if (v_isShared_6438_ == 0)
{
lean_ctor_set(v___x_6437_, 5, v___x_6440_);
lean_ctor_set(v___x_6437_, 0, v___x_6439_);
v___x_6442_ = v___x_6437_;
goto v_reusejp_6441_;
}
else
{
lean_object* v_reuseFailAlloc_6445_; 
v_reuseFailAlloc_6445_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6445_, 0, v___x_6439_);
lean_ctor_set(v_reuseFailAlloc_6445_, 1, v_nextMacroScope_6428_);
lean_ctor_set(v_reuseFailAlloc_6445_, 2, v_ngen_6429_);
lean_ctor_set(v_reuseFailAlloc_6445_, 3, v_auxDeclNGen_6430_);
lean_ctor_set(v_reuseFailAlloc_6445_, 4, v_traceState_6431_);
lean_ctor_set(v_reuseFailAlloc_6445_, 5, v___x_6440_);
lean_ctor_set(v_reuseFailAlloc_6445_, 6, v_recordedDeps_6432_);
lean_ctor_set(v_reuseFailAlloc_6445_, 7, v_messages_6433_);
lean_ctor_set(v_reuseFailAlloc_6445_, 8, v_infoState_6434_);
lean_ctor_set(v_reuseFailAlloc_6445_, 9, v_snapshotTasks_6435_);
v___x_6442_ = v_reuseFailAlloc_6445_;
goto v_reusejp_6441_;
}
v_reusejp_6441_:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; 
v___x_6443_ = lean_st_ref_put(v_a_6414_, v___x_6442_);
v___x_6444_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6424_, v___y_6421_, v___y_6420_, v___y_6417_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
lean_dec_ref(v_assignments_6424_);
return v___x_6444_;
}
}
}
else
{
lean_object* v_a_6448_; lean_object* v___x_6450_; uint8_t v_isShared_6451_; uint8_t v_isSharedCheck_6455_; 
lean_dec(v___y_6419_);
lean_dec(v___y_6418_);
lean_dec_ref(v___y_6417_);
v_a_6448_ = lean_ctor_get(v___y_6422_, 0);
v_isSharedCheck_6455_ = !lean_is_exclusive(v___y_6422_);
if (v_isSharedCheck_6455_ == 0)
{
v___x_6450_ = v___y_6422_;
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
else
{
lean_inc(v_a_6448_);
lean_dec(v___y_6422_);
v___x_6450_ = lean_box(0);
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
v_resetjp_6449_:
{
lean_object* v___x_6453_; 
if (v_isShared_6451_ == 0)
{
v___x_6453_ = v___x_6450_;
goto v_reusejp_6452_;
}
else
{
lean_object* v_reuseFailAlloc_6454_; 
v_reuseFailAlloc_6454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6454_, 0, v_a_6448_);
v___x_6453_ = v_reuseFailAlloc_6454_;
goto v_reusejp_6452_;
}
v_reusejp_6452_:
{
return v___x_6453_;
}
}
}
}
v___jp_6456_:
{
lean_object* v___x_6472_; double v___x_6473_; double v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
v___x_6472_ = lean_io_get_num_heartbeats();
v___x_6473_ = lean_float_of_nat(v___y_6465_);
v___x_6474_ = lean_float_of_nat(v___x_6472_);
v___x_6475_ = lean_box_float(v___x_6473_);
v___x_6476_ = lean_box_float(v___x_6474_);
v___x_6477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6477_, 0, v___x_6475_);
lean_ctor_set(v___x_6477_, 1, v___x_6476_);
v___x_6478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6478_, 0, v_a_6471_);
lean_ctor_set(v___x_6478_, 1, v___x_6477_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6470_);
v___x_6479_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6470_, v___y_6458_, v___y_6463_, v___y_6469_, v___y_6466_, v___y_6468_, v___y_6457_, v___x_6478_, v___y_6460_, v___y_6462_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
lean_dec_ref(v___y_6460_);
v___y_6417_ = v___y_6459_;
v___y_6418_ = v___y_6461_;
v___y_6419_ = v___y_6462_;
v___y_6420_ = v___y_6467_;
v___y_6421_ = v___y_6464_;
v___y_6422_ = v___x_6479_;
goto v___jp_6416_;
}
v___jp_6480_:
{
lean_object* v___x_6496_; double v___x_6497_; double v___x_6498_; double v___x_6499_; double v___x_6500_; double v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; 
v___x_6496_ = lean_io_mono_nanos_now();
v___x_6497_ = lean_float_of_nat(v___y_6481_);
v___x_6498_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6499_ = lean_float_div(v___x_6497_, v___x_6498_);
v___x_6500_ = lean_float_of_nat(v___x_6496_);
v___x_6501_ = lean_float_div(v___x_6500_, v___x_6498_);
v___x_6502_ = lean_box_float(v___x_6499_);
v___x_6503_ = lean_box_float(v___x_6501_);
v___x_6504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6504_, 0, v___x_6502_);
lean_ctor_set(v___x_6504_, 1, v___x_6503_);
v___x_6505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6505_, 0, v_a_6495_);
lean_ctor_set(v___x_6505_, 1, v___x_6504_);
lean_inc_ref(v___y_6488_);
lean_inc(v___y_6494_);
v___x_6506_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6494_, v___y_6483_, v___y_6488_, v___y_6493_, v___y_6490_, v___y_6492_, v___y_6482_, v___x_6505_, v___y_6485_, v___y_6487_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
lean_dec_ref(v___y_6485_);
v___y_6417_ = v___y_6484_;
v___y_6418_ = v___y_6486_;
v___y_6419_ = v___y_6487_;
v___y_6420_ = v___y_6491_;
v___y_6421_ = v___y_6489_;
v___y_6422_ = v___x_6506_;
goto v___jp_6416_;
}
v___jp_6508_:
{
lean_object* v___x_6521_; lean_object* v_a_6522_; lean_object* v___x_6523_; uint8_t v___x_6524_; 
v___x_6521_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6414_);
v_a_6522_ = lean_ctor_get(v___x_6521_, 0);
lean_inc(v_a_6522_);
lean_dec_ref(v___x_6521_);
v___x_6523_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6524_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6519_, v___x_6523_);
if (v___x_6524_ == 0)
{
lean_object* v___x_6525_; lean_object* v___x_6526_; 
v___x_6525_ = lean_io_mono_nanos_now();
v___x_6526_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6507_, v___y_6512_, v___y_6514_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
if (lean_obj_tag(v___x_6526_) == 0)
{
lean_object* v_a_6527_; lean_object* v___x_6529_; uint8_t v_isShared_6530_; uint8_t v_isSharedCheck_6534_; 
v_a_6527_ = lean_ctor_get(v___x_6526_, 0);
v_isSharedCheck_6534_ = !lean_is_exclusive(v___x_6526_);
if (v_isSharedCheck_6534_ == 0)
{
v___x_6529_ = v___x_6526_;
v_isShared_6530_ = v_isSharedCheck_6534_;
goto v_resetjp_6528_;
}
else
{
lean_inc(v_a_6527_);
lean_dec(v___x_6526_);
v___x_6529_ = lean_box(0);
v_isShared_6530_ = v_isSharedCheck_6534_;
goto v_resetjp_6528_;
}
v_resetjp_6528_:
{
lean_object* v___x_6532_; 
if (v_isShared_6530_ == 0)
{
lean_ctor_set_tag(v___x_6529_, 1);
v___x_6532_ = v___x_6529_;
goto v_reusejp_6531_;
}
else
{
lean_object* v_reuseFailAlloc_6533_; 
v_reuseFailAlloc_6533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6533_, 0, v_a_6527_);
v___x_6532_ = v_reuseFailAlloc_6533_;
goto v_reusejp_6531_;
}
v_reusejp_6531_:
{
v___y_6481_ = v___x_6525_;
v___y_6482_ = v___y_6509_;
v___y_6483_ = v___y_6510_;
v___y_6484_ = v___y_6511_;
v___y_6485_ = v___y_6512_;
v___y_6486_ = v___y_6513_;
v___y_6487_ = v___y_6514_;
v___y_6488_ = v___y_6515_;
v___y_6489_ = v___y_6516_;
v___y_6490_ = v___y_6517_;
v___y_6491_ = v___y_6518_;
v___y_6492_ = v_a_6522_;
v___y_6493_ = v___y_6519_;
v___y_6494_ = v___y_6520_;
v_a_6495_ = v___x_6532_;
goto v___jp_6480_;
}
}
}
else
{
lean_object* v_a_6535_; lean_object* v___x_6537_; uint8_t v_isShared_6538_; uint8_t v_isSharedCheck_6542_; 
v_a_6535_ = lean_ctor_get(v___x_6526_, 0);
v_isSharedCheck_6542_ = !lean_is_exclusive(v___x_6526_);
if (v_isSharedCheck_6542_ == 0)
{
v___x_6537_ = v___x_6526_;
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
else
{
lean_inc(v_a_6535_);
lean_dec(v___x_6526_);
v___x_6537_ = lean_box(0);
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
v_resetjp_6536_:
{
lean_object* v___x_6540_; 
if (v_isShared_6538_ == 0)
{
lean_ctor_set_tag(v___x_6537_, 0);
v___x_6540_ = v___x_6537_;
goto v_reusejp_6539_;
}
else
{
lean_object* v_reuseFailAlloc_6541_; 
v_reuseFailAlloc_6541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6541_, 0, v_a_6535_);
v___x_6540_ = v_reuseFailAlloc_6541_;
goto v_reusejp_6539_;
}
v_reusejp_6539_:
{
v___y_6481_ = v___x_6525_;
v___y_6482_ = v___y_6509_;
v___y_6483_ = v___y_6510_;
v___y_6484_ = v___y_6511_;
v___y_6485_ = v___y_6512_;
v___y_6486_ = v___y_6513_;
v___y_6487_ = v___y_6514_;
v___y_6488_ = v___y_6515_;
v___y_6489_ = v___y_6516_;
v___y_6490_ = v___y_6517_;
v___y_6491_ = v___y_6518_;
v___y_6492_ = v_a_6522_;
v___y_6493_ = v___y_6519_;
v___y_6494_ = v___y_6520_;
v_a_6495_ = v___x_6540_;
goto v___jp_6480_;
}
}
}
}
else
{
lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6543_ = lean_io_get_num_heartbeats();
v___x_6544_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6507_, v___y_6512_, v___y_6514_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
if (lean_obj_tag(v___x_6544_) == 0)
{
lean_object* v_a_6545_; lean_object* v___x_6547_; uint8_t v_isShared_6548_; uint8_t v_isSharedCheck_6552_; 
v_a_6545_ = lean_ctor_get(v___x_6544_, 0);
v_isSharedCheck_6552_ = !lean_is_exclusive(v___x_6544_);
if (v_isSharedCheck_6552_ == 0)
{
v___x_6547_ = v___x_6544_;
v_isShared_6548_ = v_isSharedCheck_6552_;
goto v_resetjp_6546_;
}
else
{
lean_inc(v_a_6545_);
lean_dec(v___x_6544_);
v___x_6547_ = lean_box(0);
v_isShared_6548_ = v_isSharedCheck_6552_;
goto v_resetjp_6546_;
}
v_resetjp_6546_:
{
lean_object* v___x_6550_; 
if (v_isShared_6548_ == 0)
{
lean_ctor_set_tag(v___x_6547_, 1);
v___x_6550_ = v___x_6547_;
goto v_reusejp_6549_;
}
else
{
lean_object* v_reuseFailAlloc_6551_; 
v_reuseFailAlloc_6551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6551_, 0, v_a_6545_);
v___x_6550_ = v_reuseFailAlloc_6551_;
goto v_reusejp_6549_;
}
v_reusejp_6549_:
{
v___y_6457_ = v___y_6509_;
v___y_6458_ = v___y_6510_;
v___y_6459_ = v___y_6511_;
v___y_6460_ = v___y_6512_;
v___y_6461_ = v___y_6513_;
v___y_6462_ = v___y_6514_;
v___y_6463_ = v___y_6515_;
v___y_6464_ = v___y_6516_;
v___y_6465_ = v___x_6543_;
v___y_6466_ = v___y_6517_;
v___y_6467_ = v___y_6518_;
v___y_6468_ = v_a_6522_;
v___y_6469_ = v___y_6519_;
v___y_6470_ = v___y_6520_;
v_a_6471_ = v___x_6550_;
goto v___jp_6456_;
}
}
}
else
{
lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6560_; 
v_a_6553_ = lean_ctor_get(v___x_6544_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6544_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6555_ = v___x_6544_;
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_dec(v___x_6544_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6558_; 
if (v_isShared_6556_ == 0)
{
lean_ctor_set_tag(v___x_6555_, 0);
v___x_6558_ = v___x_6555_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
v___y_6457_ = v___y_6509_;
v___y_6458_ = v___y_6510_;
v___y_6459_ = v___y_6511_;
v___y_6460_ = v___y_6512_;
v___y_6461_ = v___y_6513_;
v___y_6462_ = v___y_6514_;
v___y_6463_ = v___y_6515_;
v___y_6464_ = v___y_6516_;
v___y_6465_ = v___x_6543_;
v___y_6466_ = v___y_6517_;
v___y_6467_ = v___y_6518_;
v___y_6468_ = v_a_6522_;
v___y_6469_ = v___y_6519_;
v___y_6470_ = v___y_6520_;
v_a_6471_ = v___x_6558_;
goto v___jp_6456_;
}
}
}
}
}
v___jp_6561_:
{
lean_object* v___f_6563_; size_t v_sz_6564_; size_t v___x_6565_; lean_object* v_assignments_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v_funVals_6569_; lean_object* v_ctx_6570_; lean_object* v_state_6571_; lean_object* v___x_6572_; uint8_t v___x_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v_toCold_6576_; lean_object* v_options_6577_; uint8_t v_hasTrace_6578_; 
lean_inc_ref_n(v___y_6562_, 3);
v___f_6563_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6563_, 0, v___y_6562_);
v_sz_6564_ = lean_array_size(v___y_6562_);
v___x_6565_ = ((size_t)0ULL);
v_assignments_6566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6564_, v___x_6565_, v___y_6562_);
v___x_6567_ = lean_array_get_size(v___y_6562_);
v___x_6568_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2));
v_funVals_6569_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6562_, v___x_6567_, v___x_6567_, v___x_6568_);
v_ctx_6570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6570_, 0, v___y_6562_);
lean_ctor_set(v_ctx_6570_, 1, v___x_6507_);
v_state_6571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6571_, 0, v_assignments_6566_);
lean_ctor_set(v_state_6571_, 1, v_funVals_6569_);
v___x_6572_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6573_ = 1;
v___x_6574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6575_ = lean_st_mk_ref(v_state_6571_);
v_toCold_6576_ = lean_ctor_get(v_a_6413_, 0);
v_options_6577_ = lean_ctor_get(v_toCold_6576_, 2);
v_hasTrace_6578_ = lean_ctor_get_uint8(v_options_6577_, sizeof(void*)*1);
if (v_hasTrace_6578_ == 0)
{
lean_object* v___x_6579_; 
lean_dec_ref(v___f_6563_);
v___x_6579_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6507_, v_ctx_6570_, v___x_6575_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
lean_dec_ref_known(v_ctx_6570_, 2);
v___y_6417_ = v___y_6562_;
v___y_6418_ = v___x_6567_;
v___y_6419_ = v___x_6575_;
v___y_6420_ = v___x_6565_;
v___y_6421_ = v_sz_6564_;
v___y_6422_ = v___x_6579_;
goto v___jp_6416_;
}
else
{
lean_object* v_inheritedTraceOptions_6580_; lean_object* v___x_6581_; uint8_t v___x_6582_; 
v_inheritedTraceOptions_6580_ = lean_ctor_get(v_toCold_6576_, 11);
v___x_6581_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6582_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6580_, v_options_6577_, v___x_6581_);
if (v___x_6582_ == 0)
{
lean_object* v___x_6583_; uint8_t v___x_6584_; 
v___x_6583_ = l_Lean_trace_profiler;
v___x_6584_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6577_, v___x_6583_);
if (v___x_6584_ == 0)
{
lean_object* v___x_6585_; 
lean_dec_ref(v___f_6563_);
v___x_6585_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6507_, v_ctx_6570_, v___x_6575_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_);
lean_dec_ref_known(v_ctx_6570_, 2);
v___y_6417_ = v___y_6562_;
v___y_6418_ = v___x_6567_;
v___y_6419_ = v___x_6575_;
v___y_6420_ = v___x_6565_;
v___y_6421_ = v_sz_6564_;
v___y_6422_ = v___x_6585_;
goto v___jp_6416_;
}
else
{
v___y_6509_ = v___f_6563_;
v___y_6510_ = v___x_6573_;
v___y_6511_ = v___y_6562_;
v___y_6512_ = v_ctx_6570_;
v___y_6513_ = v___x_6567_;
v___y_6514_ = v___x_6575_;
v___y_6515_ = v___x_6574_;
v___y_6516_ = v_sz_6564_;
v___y_6517_ = v___x_6582_;
v___y_6518_ = v___x_6565_;
v___y_6519_ = v_options_6577_;
v___y_6520_ = v___x_6572_;
goto v___jp_6508_;
}
}
else
{
v___y_6509_ = v___f_6563_;
v___y_6510_ = v___x_6573_;
v___y_6511_ = v___y_6562_;
v___y_6512_ = v_ctx_6570_;
v___y_6513_ = v___x_6567_;
v___y_6514_ = v___x_6575_;
v___y_6515_ = v___x_6574_;
v___y_6516_ = v_sz_6564_;
v___y_6517_ = v___x_6582_;
v___y_6518_ = v___x_6565_;
v___y_6519_ = v_options_6577_;
v___y_6520_ = v___x_6572_;
goto v___jp_6508_;
}
}
}
v___jp_6587_:
{
lean_object* v___x_6590_; 
v___x_6590_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6586_, v_decls_6410_, v___y_6588_, v___y_6589_);
lean_dec(v___y_6589_);
v___y_6562_ = v___x_6590_;
goto v___jp_6561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_, lean_object* v_a_6603_){
_start:
{
lean_object* v_res_6604_; 
v_res_6604_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6598_, v_a_6599_, v_a_6600_, v_a_6601_, v_a_6602_);
lean_dec(v_a_6602_);
lean_dec_ref(v_a_6601_);
lean_dec(v_a_6600_);
lean_dec_ref(v_a_6599_);
return v_res_6604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6605_, lean_object* v_n_6606_, lean_object* v_j_6607_, lean_object* v_a_6608_, lean_object* v_a_6609_){
_start:
{
lean_object* v___x_6610_; 
v___x_6610_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6605_, v_n_6606_, v_j_6607_, v_a_6609_);
return v___x_6610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6611_, lean_object* v_n_6612_, lean_object* v_j_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_){
_start:
{
lean_object* v_res_6616_; 
v_res_6616_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6611_, v_n_6612_, v_j_6613_, v_a_6614_, v_a_6615_);
lean_dec(v_n_6612_);
lean_dec_ref(v___y_6611_);
return v_res_6616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6617_, lean_object* v___x_6618_, lean_object* v_n_6619_, lean_object* v_j_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_){
_start:
{
lean_object* v___x_6623_; 
v___x_6623_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6617_, v___x_6618_, v_n_6619_, v_j_6620_, v_a_6622_);
return v___x_6623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6624_, lean_object* v___x_6625_, lean_object* v_n_6626_, lean_object* v_j_6627_, lean_object* v_a_6628_, lean_object* v_a_6629_){
_start:
{
lean_object* v_res_6630_; 
v_res_6630_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6624_, v___x_6625_, v_n_6626_, v_j_6627_, v_a_6628_, v_a_6629_);
lean_dec(v_n_6626_);
lean_dec_ref(v___x_6625_);
lean_dec_ref(v___y_6624_);
return v_res_6630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6631_, lean_object* v_as_6632_, size_t v_sz_6633_, size_t v_i_6634_, lean_object* v_bs_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_){
_start:
{
lean_object* v___x_6641_; 
v___x_6641_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6631_, v_sz_6633_, v_i_6634_, v_bs_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_);
return v___x_6641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6642_, lean_object* v_as_6643_, lean_object* v_sz_6644_, lean_object* v_i_6645_, lean_object* v_bs_6646_, lean_object* v___y_6647_, lean_object* v___y_6648_, lean_object* v___y_6649_, lean_object* v___y_6650_, lean_object* v___y_6651_){
_start:
{
size_t v_sz_boxed_6652_; size_t v_i_boxed_6653_; lean_object* v_res_6654_; 
v_sz_boxed_6652_ = lean_unbox_usize(v_sz_6644_);
lean_dec(v_sz_6644_);
v_i_boxed_6653_ = lean_unbox_usize(v_i_6645_);
lean_dec(v_i_6645_);
v_res_6654_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6642_, v_as_6643_, v_sz_boxed_6652_, v_i_boxed_6653_, v_bs_6646_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v_as_6643_);
lean_dec_ref(v___x_6642_);
return v_res_6654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6655_, lean_object* v_as_6656_, lean_object* v_lo_6657_, lean_object* v_hi_6658_, lean_object* v_w_6659_, lean_object* v_hlo_6660_, lean_object* v_hhi_6661_){
_start:
{
lean_object* v___x_6662_; 
v___x_6662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6655_, v_as_6656_, v_lo_6657_, v_hi_6658_);
return v___x_6662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6663_, lean_object* v_as_6664_, lean_object* v_lo_6665_, lean_object* v_hi_6666_, lean_object* v_w_6667_, lean_object* v_hlo_6668_, lean_object* v_hhi_6669_){
_start:
{
lean_object* v_res_6670_; 
v_res_6670_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6663_, v_as_6664_, v_lo_6665_, v_hi_6666_, v_w_6667_, v_hlo_6668_, v_hhi_6669_);
lean_dec(v_hi_6666_);
lean_dec(v_n_6663_);
return v_res_6670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6671_, lean_object* v_lo_6672_, lean_object* v_hi_6673_, lean_object* v_hhi_6674_, lean_object* v_pivot_6675_, lean_object* v_as_6676_, lean_object* v_i_6677_, lean_object* v_k_6678_, lean_object* v_ilo_6679_, lean_object* v_ik_6680_, lean_object* v_w_6681_){
_start:
{
lean_object* v___x_6682_; 
v___x_6682_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6673_, v_pivot_6675_, v_as_6676_, v_i_6677_, v_k_6678_);
return v___x_6682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6683_, lean_object* v_lo_6684_, lean_object* v_hi_6685_, lean_object* v_hhi_6686_, lean_object* v_pivot_6687_, lean_object* v_as_6688_, lean_object* v_i_6689_, lean_object* v_k_6690_, lean_object* v_ilo_6691_, lean_object* v_ik_6692_, lean_object* v_w_6693_){
_start:
{
lean_object* v_res_6694_; 
v_res_6694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6683_, v_lo_6684_, v_hi_6685_, v_hhi_6686_, v_pivot_6687_, v_as_6688_, v_i_6689_, v_k_6690_, v_ilo_6691_, v_ik_6692_, v_w_6693_);
lean_dec(v_hi_6685_);
lean_dec(v_lo_6684_);
lean_dec(v_n_6683_);
return v_res_6694_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; 
v___x_6754_ = lean_unsigned_to_nat(3955956072u);
v___x_6755_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6756_ = l_Lean_Name_num___override(v___x_6755_, v___x_6754_);
return v___x_6756_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; 
v___x_6758_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6759_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6760_ = l_Lean_Name_str___override(v___x_6759_, v___x_6758_);
return v___x_6760_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; 
v___x_6762_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6763_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6764_ = l_Lean_Name_str___override(v___x_6763_, v___x_6762_);
return v___x_6764_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; 
v___x_6765_ = lean_unsigned_to_nat(2u);
v___x_6766_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6767_ = l_Lean_Name_num___override(v___x_6766_, v___x_6765_);
return v___x_6767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6769_; uint8_t v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; 
v___x_6769_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6770_ = 1;
v___x_6771_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6772_ = l_Lean_registerTraceClass(v___x_6769_, v___x_6770_, v___x_6771_);
return v___x_6772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6773_){
_start:
{
lean_object* v_res_6774_; 
v_res_6774_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6774_;
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
