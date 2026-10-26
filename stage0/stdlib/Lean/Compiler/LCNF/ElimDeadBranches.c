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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = ((size_t)0ULL);
v___x_415_ = lean_usize_of_nat(v___x_411_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_409_, v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
v_x_405_ = v_tail_408_;
goto _start;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
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
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1___boxed(lean_object* v_x_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_x_420_);
lean_dec(v_x_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_424_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_425_ = lean_unsigned_to_nat(42u);
v___x_426_ = lean_unsigned_to_nat(122u);
v___x_427_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__0));
v___x_428_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_429_ = l_mkPanicMessageWithDecl(v___x_428_, v___x_427_, v___x_426_, v___x_425_, v___x_424_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(lean_object* v_env_430_, lean_object* v_vs_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = l_List_all___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__1(v_vs_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v_env_430_);
v___x_433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_433_, 0, v_vs_431_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_box(0);
v___x_435_ = l_List_head_x21___redArg(v___x_434_, v_vs_431_);
if (lean_obj_tag(v___x_435_) == 2)
{
lean_object* v_i_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_i_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_i_436_);
lean_dec_ref_known(v___x_435_, 2);
v___x_437_ = l_List_lengthTR___redArg(v_vs_431_);
v___x_438_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v_i_436_, v_env_430_, v___x_437_);
lean_dec(v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_439_, 0, v_vs_431_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; 
lean_dec(v_vs_431_);
v___x_440_ = lean_box(1);
return v___x_440_;
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v___x_435_);
lean_dec(v_vs_431_);
lean_dec_ref(v_env_430_);
v___x_441_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup___closed__1);
v___x_442_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__2(v___x_441_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(lean_object* v_msg_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_box(0);
v___x_445_ = lean_panic_fn_borrowed(v___x_444_, v_msg_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_dec(v_x_446_);
return v_x_447_;
}
else
{
lean_object* v_head_449_; lean_object* v_tail_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_460_; 
v_head_449_ = lean_ctor_get(v_x_448_, 0);
v_tail_450_ = lean_ctor_get(v_x_448_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_460_ == 0)
{
v___x_452_ = v_x_448_;
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_tail_450_);
lean_inc(v_head_449_);
lean_dec(v_x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
lean_inc(v_x_446_);
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 5);
lean_ctor_set(v___x_452_, 1, v_x_446_);
lean_ctor_set(v___x_452_, 0, v_x_447_);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_x_447_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_x_446_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_449_);
v___x_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v_x_447_ = v___x_457_;
v_x_448_ = v_tail_450_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_463_; 
lean_dec(v_x_462_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
lean_object* v_tail_464_; 
v_tail_464_ = lean_ctor_get(v_x_461_, 1);
if (lean_obj_tag(v_tail_464_) == 0)
{
lean_object* v_head_465_; lean_object* v___x_466_; 
lean_dec(v_x_462_);
v_head_465_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_head_465_);
lean_dec_ref_known(v_x_461_, 2);
v___x_466_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_465_);
return v___x_466_;
}
else
{
lean_object* v_head_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc(v_tail_464_);
v_head_467_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_head_467_);
lean_dec_ref_known(v_x_461_, 2);
v___x_468_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_head_467_);
v___x_469_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0_spec__3(v_x_462_, v___x_468_, v_tail_464_);
return v___x_469_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__2));
v___x_482_ = lean_string_length(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__7);
v___x_484_ = lean_nat_to_int(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(lean_object* v_a_489_){
_start:
{
if (lean_obj_tag(v_a_489_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__1));
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; 
v___x_491_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_492_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0_spec__0(v_a_489_, v___x_491_);
v___x_493_ = lean_obj_once(&l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__8);
v___x_494_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__9));
v___x_495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_492_);
v___x_496_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_493_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = 0;
v___x_500_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(lean_object* v_env_506_, lean_object* v_v1_507_, lean_object* v_v2_508_){
_start:
{
lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_516_; lean_object* v_i_517_; lean_object* v_vs_518_; 
switch(lean_obj_tag(v_v1_507_))
{
case 0:
{
switch(lean_obj_tag(v_v2_508_))
{
case 2:
{
lean_object* v_i_525_; lean_object* v_vs_526_; 
v_i_525_ = lean_ctor_get(v_v2_508_, 0);
lean_inc(v_i_525_);
v_vs_526_ = lean_ctor_get(v_v2_508_, 1);
lean_inc_ref(v_vs_526_);
v___y_516_ = v_v2_508_;
v_i_517_ = v_i_525_;
v_vs_518_ = v_vs_526_;
goto v___jp_515_;
}
case 3:
{
lean_object* v_vs_527_; lean_object* v___x_528_; 
v_vs_527_ = lean_ctor_get(v_v2_508_, 0);
lean_inc(v_vs_527_);
lean_dec_ref_known(v_v2_508_, 1);
v___x_528_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_506_, v_vs_527_);
return v___x_528_;
}
default: 
{
lean_dec_ref(v_env_506_);
return v_v2_508_;
}
}
}
case 1:
{
lean_dec(v_v2_508_);
lean_dec_ref(v_env_506_);
return v_v1_507_;
}
case 2:
{
switch(lean_obj_tag(v_v2_508_))
{
case 0:
{
lean_object* v_i_529_; lean_object* v_vs_530_; 
v_i_529_ = lean_ctor_get(v_v1_507_, 0);
lean_inc(v_i_529_);
v_vs_530_ = lean_ctor_get(v_v1_507_, 1);
lean_inc_ref(v_vs_530_);
v___y_516_ = v_v1_507_;
v_i_517_ = v_i_529_;
v_vs_518_ = v_vs_530_;
goto v___jp_515_;
}
case 1:
{
lean_dec_ref_known(v_v1_507_, 2);
lean_dec_ref(v_env_506_);
return v_v2_508_;
}
case 2:
{
lean_object* v_i_531_; lean_object* v_vs_532_; lean_object* v_i_533_; lean_object* v_vs_534_; uint8_t v___x_535_; 
v_i_531_ = lean_ctor_get(v_v1_507_, 0);
v_vs_532_ = lean_ctor_get(v_v1_507_, 1);
v_i_533_ = lean_ctor_get(v_v2_508_, 0);
v_vs_534_ = lean_ctor_get(v_v2_508_, 1);
v___x_535_ = lean_name_eq(v_i_531_, v_i_533_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_536_ = lean_box(0);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v_v2_508_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_538_, 0, v_v1_507_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_506_, v___x_538_);
return v___x_539_;
}
else
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_549_; 
lean_inc_ref(v_vs_534_);
lean_inc_ref(v_vs_532_);
lean_inc(v_i_531_);
lean_dec_ref_known(v_v1_507_, 2);
v_isSharedCheck_549_ = !lean_is_exclusive(v_v2_508_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_550_ = lean_ctor_get(v_v2_508_, 1);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_v2_508_, 0);
lean_dec(v_unused_551_);
v___x_541_ = v_v2_508_;
v_isShared_542_ = v_isSharedCheck_549_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_v2_508_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_549_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
lean_inc_ref(v_env_506_);
v___x_545_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_506_, v_vs_532_, v_vs_534_, v___x_543_, v___x_544_);
lean_dec_ref(v_vs_534_);
lean_dec_ref(v_vs_532_);
lean_inc_ref(v___x_545_);
lean_inc(v_i_531_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_545_);
lean_ctor_set(v___x_541_, 0, v_i_531_);
v___x_547_ = v___x_541_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_i_531_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
v___y_516_ = v___x_547_;
v_i_517_ = v_i_531_;
v_vs_518_ = v___x_545_;
goto v___jp_515_;
}
}
}
}
default: 
{
lean_object* v_vs_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_vs_552_ = lean_ctor_get(v_v2_508_, 0);
lean_inc(v_vs_552_);
lean_dec_ref_known(v_v2_508_, 1);
lean_inc_ref(v_env_506_);
v___x_553_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_506_, v_vs_552_, v_v1_507_);
v___x_554_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_506_, v___x_553_);
return v___x_554_;
}
}
}
default: 
{
switch(lean_obj_tag(v_v2_508_))
{
case 0:
{
lean_object* v_vs_555_; lean_object* v___x_556_; 
v_vs_555_ = lean_ctor_get(v_v1_507_, 0);
lean_inc(v_vs_555_);
lean_dec_ref_known(v_v1_507_, 1);
v___x_556_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_506_, v_vs_555_);
return v___x_556_;
}
case 1:
{
lean_dec_ref_known(v_v1_507_, 1);
lean_dec_ref(v_env_506_);
return v_v2_508_;
}
case 3:
{
lean_object* v_vs_557_; lean_object* v_vs_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_vs_557_ = lean_ctor_get(v_v1_507_, 0);
lean_inc(v_vs_557_);
lean_dec_ref_known(v_v1_507_, 1);
v_vs_558_ = lean_ctor_get(v_v2_508_, 0);
lean_inc(v_vs_558_);
lean_dec_ref_known(v_v2_508_, 1);
lean_inc_ref(v_env_506_);
v___x_559_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(v_env_506_, v_vs_558_, v_vs_557_);
v___x_560_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_506_, v___x_559_);
return v___x_560_;
}
default: 
{
lean_object* v_vs_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_vs_561_ = lean_ctor_get(v_v1_507_, 0);
lean_inc(v_vs_561_);
lean_dec_ref_known(v_v1_507_, 1);
lean_inc_ref(v_env_506_);
v___x_562_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_506_, v_vs_561_, v_v2_508_);
v___x_563_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup(v_env_506_, v___x_562_);
return v___x_563_;
}
}
}
}
v___jp_509_:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_inductHasNumCtors(v___y_511_, v_env_506_, v___x_512_);
if (v___x_513_ == 0)
{
return v___y_510_;
}
else
{
lean_object* v___x_514_; 
lean_dec(v___y_510_);
v___x_514_ = lean_box(1);
return v___x_514_;
}
}
v___jp_515_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_array_get_size(v_vs_518_);
v___x_521_ = lean_nat_dec_lt(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec_ref(v_vs_518_);
v___y_510_ = v___y_516_;
v___y_511_ = v_i_517_;
goto v___jp_509_;
}
else
{
size_t v___x_522_; size_t v___x_523_; uint8_t v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___x_520_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_merge_cleanup_spec__0(v_vs_518_, v___x_522_, v___x_523_);
lean_dec_ref(v_vs_518_);
if (v___x_524_ == 0)
{
v___y_510_ = v___y_516_;
v___y_511_ = v_i_517_;
goto v___jp_509_;
}
else
{
lean_dec(v_i_517_);
lean_dec_ref(v_env_506_);
return v___y_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(lean_object* v_env_564_, lean_object* v_as_565_, lean_object* v_bs_566_, lean_object* v_i_567_, lean_object* v_cs_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v_as_565_);
v___x_570_ = lean_nat_dec_lt(v_i_567_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v_i_567_);
lean_dec_ref(v_env_564_);
return v_cs_568_;
}
else
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v_bs_566_);
v___x_572_ = lean_nat_dec_lt(v_i_567_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec(v_i_567_);
lean_dec_ref(v_env_564_);
return v_cs_568_;
}
else
{
lean_object* v_a_573_; lean_object* v_b_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_a_573_ = lean_array_fget_borrowed(v_as_565_, v_i_567_);
v_b_574_ = lean_array_fget_borrowed(v_bs_566_, v_i_567_);
lean_inc(v_b_574_);
lean_inc(v_a_573_);
lean_inc_ref(v_env_564_);
v___x_575_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_564_, v_a_573_, v_b_574_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_i_567_, v___x_576_);
lean_dec(v_i_567_);
v___x_578_ = lean_array_push(v_cs_568_, v___x_575_);
v_i_567_ = v___x_577_;
v_cs_568_ = v___x_578_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(lean_object* v_env_580_, lean_object* v_vs_581_, lean_object* v_v_582_){
_start:
{
if (lean_obj_tag(v_vs_581_) == 0)
{
lean_object* v___x_601_; 
lean_dec_ref(v_env_580_);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v_v_582_);
lean_ctor_set(v___x_601_, 1, v_vs_581_);
return v___x_601_;
}
else
{
lean_object* v_head_602_; 
v_head_602_ = lean_ctor_get(v_vs_581_, 0);
if (lean_obj_tag(v_head_602_) == 2)
{
if (lean_obj_tag(v_v_582_) == 2)
{
lean_object* v_tail_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_631_; 
lean_inc_ref(v_head_602_);
v_tail_603_ = lean_ctor_get(v_vs_581_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_vs_581_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_vs_581_, 0);
lean_dec(v_unused_632_);
v___x_605_ = v_vs_581_;
v_isShared_606_ = v_isSharedCheck_631_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_tail_603_);
lean_dec(v_vs_581_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_631_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_i_607_; lean_object* v_vs_608_; lean_object* v_i_609_; lean_object* v_vs_610_; uint8_t v___x_611_; 
v_i_607_ = lean_ctor_get(v_head_602_, 0);
v_vs_608_ = lean_ctor_get(v_head_602_, 1);
v_i_609_ = lean_ctor_get(v_v_582_, 0);
v_vs_610_ = lean_ctor_get(v_v_582_, 1);
v___x_611_ = lean_name_eq(v_i_607_, v_i_609_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_580_, v_tail_603_, v_v_582_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_612_);
v___x_614_ = v___x_605_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_head_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_628_; 
lean_inc_ref(v_vs_610_);
lean_inc_ref(v_vs_608_);
lean_inc(v_i_607_);
lean_dec_ref_known(v_head_602_, 2);
v_isSharedCheck_628_ = !lean_is_exclusive(v_v_582_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; lean_object* v_unused_630_; 
v_unused_629_ = lean_ctor_get(v_v_582_, 1);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_v_582_, 0);
lean_dec(v_unused_630_);
v___x_617_ = v_v_582_;
v_isShared_618_ = v_isSharedCheck_628_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_v_582_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_628_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__3));
v___x_621_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_580_, v_vs_608_, v_vs_610_, v___x_619_, v___x_620_);
lean_dec_ref(v_vs_610_);
lean_dec_ref(v_vs_608_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_621_);
lean_ctor_set(v___x_617_, 0, v_i_607_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_i_607_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_621_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_623_);
v___x_625_ = v___x_605_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_tail_603_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_580_);
goto v___jp_583_;
}
}
else
{
lean_dec_ref(v_env_580_);
goto v___jp_583_;
}
}
v___jp_583_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_584_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_585_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__0));
v___x_586_ = lean_unsigned_to_nat(92u);
v___x_587_ = lean_unsigned_to_nat(12u);
v___x_588_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__1));
v___x_589_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_v_582_);
v___x_590_ = l_Std_Format_defWidth;
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = l_Std_Format_pretty(v___x_589_, v___x_590_, v___x_591_, v___x_591_);
v___x_593_ = lean_string_append(v___x_588_, v___x_592_);
lean_dec_ref(v___x_592_);
v___x_594_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice___closed__2));
v___x_595_ = lean_string_append(v___x_593_, v___x_594_);
v___x_596_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_vs_581_);
v___x_597_ = l_Std_Format_pretty(v___x_596_, v___x_590_, v___x_591_, v___x_591_);
v___x_598_ = lean_string_append(v___x_595_, v___x_597_);
lean_dec_ref(v___x_597_);
v___x_599_ = l_mkPanicMessageWithDecl(v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = l_panic___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__1(v___x_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_merge_spec__4(lean_object* v_env_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_dec_ref(v_env_633_);
return v_x_634_;
}
else
{
lean_object* v_head_636_; lean_object* v_tail_637_; lean_object* v___x_638_; 
v_head_636_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_head_636_);
v_tail_637_ = lean_ctor_get(v_x_635_, 1);
lean_inc(v_tail_637_);
lean_dec_ref_known(v_x_635_, 2);
lean_inc_ref(v_env_633_);
v___x_638_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice(v_env_633_, v_x_634_, v_head_636_);
v_x_634_ = v___x_638_;
v_x_635_ = v_tail_637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2___boxed(lean_object* v_env_640_, lean_object* v_as_641_, lean_object* v_bs_642_, lean_object* v_i_643_, lean_object* v_cs_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__2(v_env_640_, v_as_641_, v_bs_642_, v_i_643_, v_cs_644_);
lean_dec_ref(v_bs_642_);
lean_dec_ref(v_as_641_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(lean_object* v_a_646_, lean_object* v_n_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg(v_a_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___boxed(lean_object* v_a_649_, lean_object* v_n_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0(v_a_649_, v_n_650_);
lean_dec(v_n_650_);
return v_res_651_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(lean_object* v_a_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
else
{
lean_object* v_head_655_; lean_object* v_tail_656_; uint8_t v___x_657_; 
v_head_655_ = lean_ctor_get(v_x_653_, 0);
v_tail_656_ = lean_ctor_get(v_x_653_, 1);
v___x_657_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_652_, v_head_655_);
if (v___x_657_ == 0)
{
v_x_653_ = v_tail_656_;
goto _start;
}
else
{
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object* v_a_659_, lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v_a_659_, v_x_660_);
lean_dec(v_x_660_);
lean_dec(v_a_659_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(lean_object* v_env_663_, lean_object* v_forbiddenTypes_x27_664_, lean_object* v_n_665_, size_t v_sz_666_, size_t v_i_667_, lean_object* v_bs_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = lean_usize_dec_lt(v_i_667_, v_sz_666_);
if (v___x_669_ == 0)
{
lean_dec(v_forbiddenTypes_x27_664_);
lean_dec_ref(v_env_663_);
return v_bs_668_;
}
else
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_bs_x27_672_; lean_object* v___x_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v_v_670_ = lean_array_uget(v_bs_668_, v_i_667_);
v___x_671_ = lean_unsigned_to_nat(0u);
v_bs_x27_672_ = lean_array_uset(v_bs_668_, v_i_667_, v___x_671_);
lean_inc(v_forbiddenTypes_x27_664_);
lean_inc_ref(v_env_663_);
v___x_673_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_663_, v_v_670_, v_forbiddenTypes_x27_664_, v_n_665_);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_667_, v___x_674_);
v___x_676_ = lean_array_uset(v_bs_x27_672_, v_i_667_, v___x_673_);
v_i_667_ = v___x_675_;
v_bs_668_ = v___x_676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(lean_object* v_env_678_, lean_object* v_v_679_, lean_object* v_forbiddenTypes_680_, lean_object* v_remainingDepth_681_){
_start:
{
lean_object* v_zero_682_; uint8_t v_isZero_683_; 
v_zero_682_ = lean_unsigned_to_nat(0u);
v_isZero_683_ = lean_nat_dec_eq(v_remainingDepth_681_, v_zero_682_);
if (v_isZero_683_ == 1)
{
lean_object* v___x_684_; 
lean_dec(v_forbiddenTypes_680_);
lean_dec(v_v_679_);
lean_dec_ref(v_env_678_);
v___x_684_ = lean_box(1);
return v___x_684_;
}
else
{
lean_object* v_one_685_; lean_object* v_n_686_; 
v_one_685_ = lean_unsigned_to_nat(1u);
v_n_686_ = lean_nat_sub(v_remainingDepth_681_, v_one_685_);
switch(lean_obj_tag(v_v_679_))
{
case 2:
{
lean_object* v_i_687_; lean_object* v_vs_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_707_; 
v_i_687_ = lean_ctor_get(v_v_679_, 0);
v_vs_688_ = lean_ctor_get(v_v_679_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_v_679_);
if (v_isSharedCheck_707_ == 0)
{
v___x_690_ = v_v_679_;
v_isShared_691_ = v_isSharedCheck_707_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_vs_688_);
lean_inc(v_i_687_);
lean_dec(v_v_679_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_707_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_forbiddenTypes_x27_693_; lean_object* v_induct_700_; lean_object* v_toConstantVal_701_; uint8_t v_isRec_702_; lean_object* v_name_703_; uint8_t v___x_704_; 
lean_inc_ref(v_env_678_);
lean_inc(v_i_687_);
v_induct_700_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor(v_i_687_, v_env_678_);
v_toConstantVal_701_ = lean_ctor_get(v_induct_700_, 0);
lean_inc_ref(v_toConstantVal_701_);
v_isRec_702_ = lean_ctor_get_uint8(v_induct_700_, sizeof(void*)*6);
lean_dec_ref(v_induct_700_);
v_name_703_ = lean_ctor_get(v_toConstantVal_701_, 0);
lean_inc(v_name_703_);
lean_dec_ref(v_toConstantVal_701_);
v___x_704_ = l_Lean_NameSet_contains(v_forbiddenTypes_680_, v_name_703_);
if (v___x_704_ == 0)
{
if (v_isRec_702_ == 0)
{
lean_dec(v_name_703_);
v_forbiddenTypes_x27_693_ = v_forbiddenTypes_680_;
goto v___jp_692_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_NameSet_insert(v_forbiddenTypes_680_, v_name_703_);
v_forbiddenTypes_x27_693_ = v___x_705_;
goto v___jp_692_;
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v_name_703_);
lean_del_object(v___x_690_);
lean_dec_ref(v_vs_688_);
lean_dec(v_i_687_);
lean_dec(v_n_686_);
lean_dec(v_forbiddenTypes_680_);
lean_dec_ref(v_env_678_);
v___x_706_ = lean_box(1);
return v___x_706_;
}
v___jp_692_:
{
size_t v_sz_694_; size_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v_sz_694_ = lean_array_size(v_vs_688_);
v___x_695_ = ((size_t)0ULL);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_678_, v_forbiddenTypes_x27_693_, v_n_686_, v_sz_694_, v___x_695_, v_vs_688_);
lean_dec(v_n_686_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_696_);
v___x_698_ = v___x_690_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_i_687_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
case 3:
{
lean_object* v_vs_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_719_; 
v_vs_708_ = lean_ctor_get(v_v_679_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_v_679_);
if (v_isSharedCheck_719_ == 0)
{
v___x_710_ = v_v_679_;
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_vs_708_);
lean_dec(v_v_679_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v_vs_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_712_ = lean_box(0);
v_vs_713_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_678_, v_forbiddenTypes_680_, v_n_686_, v_vs_708_, v___x_712_);
lean_dec(v_n_686_);
v___x_714_ = lean_box(1);
v___x_715_ = l_List_elem___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__2(v___x_714_, v_vs_713_);
if (v___x_715_ == 0)
{
lean_object* v___x_717_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v_vs_713_);
v___x_717_ = v___x_710_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_vs_713_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_dec(v_vs_713_);
lean_del_object(v___x_710_);
return v___x_714_;
}
}
}
default: 
{
lean_dec(v_n_686_);
lean_dec(v_forbiddenTypes_680_);
lean_dec_ref(v_env_678_);
return v_v_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(lean_object* v_env_720_, lean_object* v_forbiddenTypes_721_, lean_object* v_n_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
if (lean_obj_tag(v_a_723_) == 0)
{
lean_object* v___x_725_; 
lean_dec(v_forbiddenTypes_721_);
lean_dec_ref(v_env_720_);
v___x_725_ = l_List_reverse___redArg(v_a_724_);
return v___x_725_;
}
else
{
lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v_head_726_ = lean_ctor_get(v_a_723_, 0);
v_tail_727_ = lean_ctor_get(v_a_723_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_736_ == 0)
{
v___x_729_ = v_a_723_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_tail_727_);
lean_inc(v_head_726_);
lean_dec(v_a_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
lean_inc(v_forbiddenTypes_721_);
lean_inc_ref(v_env_720_);
v___x_731_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_720_, v_head_726_, v_forbiddenTypes_721_, v_n_722_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_a_724_);
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_a_724_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
v_a_723_ = v_tail_727_;
v_a_724_ = v___x_733_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object* v_env_737_, lean_object* v_forbiddenTypes_738_, lean_object* v_n_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_List_mapTR_loop___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__1(v_env_737_, v_forbiddenTypes_738_, v_n_739_, v_a_740_, v_a_741_);
lean_dec(v_n_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object* v_env_743_, lean_object* v_forbiddenTypes_x27_744_, lean_object* v_n_745_, lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_bs_748_){
_start:
{
size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v_sz_boxed_749_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_750_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go_spec__0(v_env_743_, v_forbiddenTypes_x27_744_, v_n_745_, v_sz_boxed_749_, v_i_boxed_750_, v_bs_748_);
lean_dec(v_n_745_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go___boxed(lean_object* v_env_752_, lean_object* v_v_753_, lean_object* v_forbiddenTypes_754_, lean_object* v_remainingDepth_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_752_, v_v_753_, v_forbiddenTypes_754_, v_remainingDepth_755_);
lean_dec(v_remainingDepth_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(lean_object* v_env_757_, lean_object* v_v_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = l_Lean_NameSet_empty;
v___x_760_ = lean_unsigned_to_nat(8u);
v___x_761_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_truncate_go(v_env_757_, v_v_758_, v___x_759_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(lean_object* v_env_762_, lean_object* v_v1_763_, lean_object* v_v2_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_inc_ref(v_env_762_);
v___x_765_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_merge(v_env_762_, v_v1_763_, v_v2_764_);
v___x_766_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_truncate(v_env_762_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
uint8_t v___x_769_; 
v___x_769_ = 0;
return v___x_769_;
}
else
{
lean_object* v_head_770_; lean_object* v_tail_771_; uint8_t v___x_772_; 
v_head_770_ = lean_ctor_get(v_x_768_, 0);
v_tail_771_ = lean_ctor_get(v_x_768_, 1);
v___x_772_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_head_770_, v_x_767_);
if (v___x_772_ == 0)
{
v_x_768_ = v_tail_771_;
goto _start;
}
else
{
return v___x_772_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
switch(lean_obj_tag(v_x_774_))
{
case 2:
{
lean_object* v_i_776_; uint8_t v___x_777_; 
v_i_776_ = lean_ctor_get(v_x_774_, 0);
v___x_777_ = lean_name_eq(v_i_776_, v_x_775_);
return v___x_777_;
}
case 3:
{
lean_object* v_vs_778_; uint8_t v___x_779_; 
v_vs_778_ = lean_ctor_get(v_x_774_, 0);
v___x_779_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_775_, v_vs_778_);
return v___x_779_;
}
default: 
{
uint8_t v___x_780_; 
v___x_780_ = 1;
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor___boxed(lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_x_781_, v_x_782_);
lean_dec(v_x_782_);
lean_dec(v_x_781_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0___boxed(lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_List_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor_spec__0(v_x_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec(v_x_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(lean_object* v_x_792_, lean_object* v_as_x27_793_, lean_object* v_b_794_){
_start:
{
if (lean_obj_tag(v_as_x27_793_) == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v_b_794_);
return v___x_795_;
}
else
{
lean_object* v_head_796_; lean_object* v_tail_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_b_794_);
v_head_796_ = lean_ctor_get(v_as_x27_793_, 0);
v_tail_797_ = lean_ctor_get(v_as_x27_793_, 1);
v___x_798_ = lean_box(0);
v___x_799_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_796_) == 2)
{
lean_object* v_i_800_; lean_object* v_vs_801_; uint8_t v___x_802_; 
v_i_800_ = lean_ctor_get(v_head_796_, 0);
v_vs_801_ = lean_ctor_get(v_head_796_, 1);
v___x_802_ = lean_name_eq(v_i_800_, v_x_792_);
if (v___x_802_ == 0)
{
v_as_x27_793_ = v_tail_797_;
v_b_794_ = v___x_799_;
goto _start;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_inc_ref(v_vs_801_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v_vs_801_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_798_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
else
{
v_as_x27_793_ = v_tail_797_;
v_b_794_ = v___x_799_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___boxed(lean_object* v_x_808_, lean_object* v_as_x27_809_, lean_object* v_b_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_808_, v_as_x27_809_, v_b_810_);
lean_dec(v_as_x27_809_);
lean_dec(v_x_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
switch(lean_obj_tag(v_x_812_))
{
case 2:
{
lean_object* v_i_814_; lean_object* v_vs_815_; uint8_t v___x_816_; 
v_i_814_ = lean_ctor_get(v_x_812_, 0);
v_vs_815_ = lean_ctor_get(v_x_812_, 1);
v___x_816_ = lean_name_eq(v_i_814_, v_x_813_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
v___x_817_ = lean_box(0);
return v___x_817_;
}
else
{
lean_object* v___x_818_; 
lean_inc_ref(v_vs_815_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_vs_815_);
return v___x_818_;
}
}
case 3:
{
lean_object* v_vs_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_val_823_; lean_object* v_fst_824_; 
v_vs_819_ = lean_ctor_get(v_x_812_, 0);
v___x_820_ = lean_box(0);
v___x_821_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg___closed__0));
v___x_822_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_813_, v_vs_819_, v___x_821_);
v_val_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_823_);
lean_dec(v___x_822_);
v_fst_824_ = lean_ctor_get(v_val_823_, 0);
lean_inc(v_fst_824_);
lean_dec(v_val_823_);
if (lean_obj_tag(v_fst_824_) == 0)
{
return v___x_820_;
}
else
{
return v_fst_824_;
}
}
default: 
{
lean_object* v___x_825_; 
v___x_825_ = lean_box(0);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs___boxed(lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_x_826_, v_x_827_);
lean_dec(v_x_827_);
lean_dec(v_x_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(lean_object* v_x_829_, lean_object* v_as_830_, lean_object* v_as_x27_831_, lean_object* v_b_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___redArg(v_x_829_, v_as_x27_831_, v_b_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0___boxed(lean_object* v_x_835_, lean_object* v_as_836_, lean_object* v_as_x27_837_, lean_object* v_b_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs_spec__0(v_x_835_, v_as_836_, v_as_x27_837_, v_b_838_, v_a_839_);
lean_dec(v_as_x27_837_);
lean_dec(v_as_836_);
lean_dec(v_x_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(lean_object* v_a_853_){
_start:
{
lean_object* v_zero_854_; uint8_t v_isZero_855_; 
v_zero_854_ = lean_unsigned_to_nat(0u);
v_isZero_855_ = lean_nat_dec_eq(v_a_853_, v_zero_854_);
if (v_isZero_855_ == 1)
{
lean_object* v___x_856_; 
v___x_856_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__3));
return v___x_856_;
}
else
{
lean_object* v_one_857_; lean_object* v_n_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_one_857_ = lean_unsigned_to_nat(1u);
v_n_858_ = lean_nat_sub(v_a_853_, v_one_857_);
v___x_859_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__5));
v___x_860_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_858_);
lean_dec(v_n_858_);
v___x_861_ = lean_mk_empty_array_with_capacity(v_one_857_);
v___x_862_ = lean_array_push(v___x_861_, v___x_860_);
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_859_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___boxed(lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_a_864_);
lean_dec(v_a_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(lean_object* v_n_866_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(8u);
v___x_868_ = lean_nat_dec_lt(v___x_867_, v_n_866_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall(v_n_866_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = lean_box(1);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat___boxed(lean_object* v_n_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_n_871_);
lean_dec(v_n_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(lean_object* v_x_873_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_object* v_val_874_; lean_object* v___x_875_; 
v_val_874_ = lean_ctor_get(v_x_873_, 0);
v___x_875_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat(v_val_874_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = lean_box(1);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit___boxed(lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_x_877_);
lean_dec_ref(v_x_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(lean_object* v_env_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
switch(lean_obj_tag(v_x_880_))
{
case 2:
{
lean_object* v_vs_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
lean_dec_ref(v_env_879_);
v_vs_882_ = lean_ctor_get(v_x_880_, 1);
v___x_883_ = lean_array_get_size(v_vs_882_);
v___x_884_ = lean_nat_dec_lt(v_x_881_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = lean_box(0);
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = lean_array_fget_borrowed(v_vs_882_, v_x_881_);
lean_inc(v___x_886_);
return v___x_886_;
}
}
case 3:
{
lean_object* v_vs_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_vs_887_ = lean_ctor_get(v_x_880_, 0);
v___x_888_ = lean_box(0);
v___x_889_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_879_, v_x_881_, v___x_888_, v_vs_887_);
return v___x_889_;
}
default: 
{
lean_dec_ref(v_env_879_);
lean_inc(v_x_880_);
return v_x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(lean_object* v_env_890_, lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_dec_ref(v_env_890_);
return v_x_892_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_head_894_ = lean_ctor_get(v_x_893_, 0);
v_tail_895_ = lean_ctor_get(v_x_893_, 1);
lean_inc_ref_n(v_env_890_, 2);
v___x_896_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_890_, v_head_894_, v_x_891_);
v___x_897_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_890_, v_x_892_, v___x_896_);
v_x_892_ = v___x_897_;
v_x_893_ = v_tail_895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0___boxed(lean_object* v_env_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_List_foldl___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_proj_spec__0(v_env_899_, v_x_900_, v_x_901_, v_x_902_);
lean_dec(v_x_902_);
lean_dec(v_x_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj___boxed(lean_object* v_env_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_904_, v_x_905_, v_x_906_);
lean_dec(v_x_906_);
lean_dec(v_x_905_);
return v_res_907_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 2)
{
lean_object* v_vs_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_vs_909_ = lean_ctor_get(v_x_908_, 1);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_array_get_size(v_vs_909_);
v___x_912_ = lean_nat_dec_lt(v___x_910_, v___x_911_);
if (v___x_912_ == 0)
{
uint8_t v___x_913_; 
v___x_913_ = 1;
return v___x_913_;
}
else
{
if (v___x_912_ == 0)
{
return v___x_912_;
}
else
{
size_t v___x_914_; size_t v___x_915_; uint8_t v___x_916_; 
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_911_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_vs_909_, v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
return v___x_912_;
}
else
{
uint8_t v___x_917_; 
v___x_917_ = 0;
return v___x_917_;
}
}
}
}
else
{
uint8_t v___x_918_; 
v___x_918_ = 0;
return v___x_918_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(lean_object* v_as_919_, size_t v_i_920_, size_t v_stop_921_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_eq(v_i_920_, v_stop_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_uget_borrowed(v_as_919_, v_i_920_);
v___x_924_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v___x_923_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; 
v___x_925_ = 1;
return v___x_925_;
}
else
{
size_t v___x_926_; size_t v___x_927_; 
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_920_, v___x_926_);
v_i_920_ = v___x_927_;
goto _start;
}
}
else
{
uint8_t v___x_929_; 
v___x_929_ = 0;
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0___boxed(lean_object* v_as_930_, lean_object* v_i_931_, lean_object* v_stop_932_){
_start:
{
size_t v_i_boxed_933_; size_t v_stop_boxed_934_; uint8_t v_res_935_; lean_object* v_r_936_; 
v_i_boxed_933_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_stop_boxed_934_ = lean_unbox_usize(v_stop_932_);
lean_dec(v_stop_932_);
v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral_spec__0(v_as_930_, v_i_boxed_933_, v_stop_boxed_934_);
lean_dec_ref(v_as_930_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral___boxed(lean_object* v_x_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_x_937_);
lean_dec(v_x_937_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(lean_object* v_msg_940_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_panic_fn_borrowed(v___x_941_, v_msg_940_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_945_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__1));
v___x_946_ = lean_unsigned_to_nat(9u);
v___x_947_ = lean_unsigned_to_nat(271u);
v___x_948_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__0));
v___x_949_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_950_ = l_mkPanicMessageWithDecl(v___x_949_, v___x_948_, v___x_947_, v___x_946_, v___x_945_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(lean_object* v_a_951_){
_start:
{
if (lean_obj_tag(v_a_951_) == 2)
{
lean_object* v_i_955_; 
v_i_955_ = lean_ctor_get(v_a_951_, 0);
if (lean_obj_tag(v_i_955_) == 1)
{
lean_object* v_pre_956_; 
v_pre_956_ = lean_ctor_get(v_i_955_, 0);
if (lean_obj_tag(v_pre_956_) == 1)
{
lean_object* v_pre_957_; 
v_pre_957_ = lean_ctor_get(v_pre_956_, 0);
if (lean_obj_tag(v_pre_957_) == 0)
{
lean_object* v_vs_958_; lean_object* v_str_959_; lean_object* v_str_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_vs_958_ = lean_ctor_get(v_a_951_, 1);
v_str_959_ = lean_ctor_get(v_i_955_, 1);
v_str_960_ = lean_ctor_get(v_pre_956_, 1);
v___x_961_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_962_ = lean_string_dec_eq(v_str_960_, v___x_961_);
if (v___x_962_ == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_964_ = lean_string_dec_eq(v_str_959_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_966_ = lean_string_dec_eq(v_str_959_, v___x_965_);
if (v___x_966_ == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_array_get_size(v_vs_958_);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
goto v___jp_952_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = lean_array_fget_borrowed(v_vs_958_, v___x_970_);
v___x_972_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_971_);
v___x_973_ = lean_nat_add(v___x_972_, v___x_968_);
lean_dec(v___x_972_);
return v___x_973_;
}
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_array_get_size(v_vs_958_);
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_nat_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
goto v___jp_952_;
}
else
{
return v___x_975_;
}
}
}
}
else
{
goto v___jp_952_;
}
}
else
{
goto v___jp_952_;
}
}
else
{
goto v___jp_952_;
}
}
else
{
goto v___jp_952_;
}
v___jp_952_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___closed__2);
v___x_954_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant_spec__0(v___x_953_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant___boxed(lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v_a_977_);
lean_dec(v_a_977_);
return v_res_978_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_instMonadEIO___redArg();
return v___x_979_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Array_instInhabited___redArg();
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_toApplicative_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1026_; 
v___x_989_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__0);
v___x_990_ = l_StateRefT_x27_instMonad___redArg(v___x_989_);
v_toApplicative_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v___x_990_, 1);
lean_dec(v_unused_1027_);
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1026_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_toApplicative_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1026_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_toFunctor_995_; lean_object* v_toSeq_996_; lean_object* v_toSeqLeft_997_; lean_object* v_toSeqRight_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1024_; 
v_toFunctor_995_ = lean_ctor_get(v_toApplicative_991_, 0);
v_toSeq_996_ = lean_ctor_get(v_toApplicative_991_, 2);
v_toSeqLeft_997_ = lean_ctor_get(v_toApplicative_991_, 3);
v_toSeqRight_998_ = lean_ctor_get(v_toApplicative_991_, 4);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_toApplicative_991_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_toApplicative_991_, 1);
lean_dec(v_unused_1025_);
v___x_1000_ = v_toApplicative_991_;
v_isShared_1001_ = v_isSharedCheck_1024_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_toSeqRight_998_);
lean_inc(v_toSeqLeft_997_);
lean_inc(v_toSeq_996_);
lean_inc(v_toFunctor_995_);
lean_dec(v_toApplicative_991_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1024_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1011_; 
v___f_1002_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__1));
v___f_1003_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__2));
lean_inc_ref(v_toFunctor_995_);
v___f_1004_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1004_, 0, v_toFunctor_995_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toFunctor_995_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___f_1004_);
lean_ctor_set(v___x_1006_, 1, v___f_1005_);
v___f_1007_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1007_, 0, v_toSeqRight_998_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toSeqLeft_997_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toSeq_996_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 4, v___f_1007_);
lean_ctor_set(v___x_1000_, 3, v___f_1008_);
lean_ctor_set(v___x_1000_, 2, v___f_1009_);
lean_ctor_set(v___x_1000_, 1, v___f_1002_);
lean_ctor_set(v___x_1000_, 0, v___x_1006_);
v___x_1011_ = v___x_1000_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___f_1002_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v___f_1009_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v___f_1008_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v___f_1007_);
v___x_1011_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___f_1003_);
lean_ctor_set(v___x_993_, 0, v___x_1011_);
v___x_1013_ = v___x_993_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___f_1003_);
v___x_1013_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___f_1019_; lean_object* v___x_1803__overap_1020_; lean_object* v___x_1021_; 
v___x_1014_ = l_StateRefT_x27_instMonad___redArg(v___x_1013_);
v___x_1015_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_instInhabitedOfMonad___redArg(v___x_1014_, v___x_1017_);
v___f_1019_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1019_, 0, v___x_1018_);
v___x_1803__overap_1020_ = lean_panic_fn_borrowed(v___f_1019_, v_msg_983_);
lean_dec_ref(v___f_1019_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
v___x_1021_ = lean_apply_5(v___x_1803__overap_1020_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, lean_box(0));
return v___x_1021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___boxed(lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v_msg_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(lean_object* v_as_1035_, size_t v_i_1036_, size_t v_stop_1037_, lean_object* v_b_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1036_, v_stop_1037_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v_fst_1041_; lean_object* v_snd_1042_; lean_object* v_fst_1043_; lean_object* v_snd_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1057_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1035_, v_i_1036_);
v_fst_1041_ = lean_ctor_get(v___x_1040_, 0);
v_snd_1042_ = lean_ctor_get(v___x_1040_, 1);
v_fst_1043_ = lean_ctor_get(v_b_1038_, 0);
v_snd_1044_ = lean_ctor_get(v_b_1038_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_b_1038_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1046_ = v_b_1038_;
v_isShared_1047_ = v_isSharedCheck_1057_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_snd_1044_);
lean_inc(v_fst_1043_);
lean_dec(v_b_1038_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1057_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1048_ = l_Array_append___redArg(v_fst_1043_, v_fst_1041_);
lean_inc(v_snd_1042_);
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_snd_1042_);
v___x_1050_ = lean_array_push(v_snd_1044_, v___x_1049_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1050_);
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1052_ = v___x_1046_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
size_t v___x_1053_; size_t v___x_1054_; 
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_1036_, v___x_1053_);
v_i_1036_ = v___x_1054_;
v_b_1038_ = v___x_1052_;
goto _start;
}
}
}
else
{
return v_b_1038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2___boxed(lean_object* v_as_1058_, lean_object* v_i_1059_, lean_object* v_stop_1060_, lean_object* v_b_1061_){
_start:
{
size_t v_i_boxed_1062_; size_t v_stop_boxed_1063_; lean_object* v_res_1064_; 
v_i_boxed_1062_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_stop_boxed_1063_ = lean_unbox_usize(v_stop_1060_);
lean_dec(v_stop_1060_);
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_as_1058_, v_i_boxed_1062_, v_stop_boxed_1063_, v_b_1061_);
lean_dec_ref(v_as_1058_);
return v_res_1064_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1069_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1070_ = lean_unsigned_to_nat(65u);
v___x_1071_ = lean_unsigned_to_nat(258u);
v___x_1072_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1073_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1074_ = l_mkPanicMessageWithDecl(v___x_1073_, v___x_1072_, v___x_1071_, v___x_1070_, v___x_1069_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1081_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_1082_ = lean_unsigned_to_nat(9u);
v___x_1083_ = lean_unsigned_to_nat(266u);
v___x_1084_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__2));
v___x_1085_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__0));
v___x_1086_ = l_mkPanicMessageWithDecl(v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_, v___x_1081_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; 
if (lean_obj_tag(v_a_1087_) == 2)
{
lean_object* v_i_1133_; lean_object* v_vs_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1254_; 
v_i_1133_ = lean_ctor_get(v_a_1087_, 0);
v_vs_1134_ = lean_ctor_get(v_a_1087_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_a_1087_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1136_ = v_a_1087_;
v_isShared_1137_ = v_isSharedCheck_1254_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_vs_1134_);
lean_inc(v_i_1133_);
lean_dec(v_a_1087_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1254_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_ctorName_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; 
if (lean_obj_tag(v_i_1133_) == 1)
{
lean_object* v_pre_1176_; 
v_pre_1176_ = lean_ctor_get(v_i_1133_, 0);
if (lean_obj_tag(v_pre_1176_) == 1)
{
lean_object* v_pre_1177_; 
v_pre_1177_ = lean_ctor_get(v_pre_1176_, 0);
if (lean_obj_tag(v_pre_1177_) == 0)
{
lean_object* v_str_1178_; lean_object* v_str_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_str_1178_ = lean_ctor_get(v_i_1133_, 1);
v_str_1179_ = lean_ctor_get(v_pre_1176_, 1);
v___x_1180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__0));
v___x_1181_ = lean_string_dec_eq(v_str_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
v_ctorName_1139_ = v_i_1133_;
v___y_1140_ = v_a_1088_;
v___y_1141_ = v_a_1089_;
v___y_1142_ = v_a_1090_;
v___y_1143_ = v_a_1091_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
lean_inc(v_pre_1177_);
lean_inc_ref(v_str_1178_);
lean_dec_ref_known(v_i_1133_, 2);
v___x_1182_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__1));
v___x_1183_ = lean_string_dec_eq(v_str_1178_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_ofNat_goSmall___closed__4));
v___x_1185_ = lean_string_dec_eq(v_str_1178_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = l_Lean_Name_str___override(v_pre_1177_, v___x_1180_);
v___x_1187_ = l_Lean_Name_str___override(v___x_1186_, v_str_1178_);
v_ctorName_1139_ = v___x_1187_;
v___y_1140_ = v_a_1088_;
v___y_1141_ = v_a_1089_;
v___y_1142_ = v_a_1090_;
v___y_1143_ = v_a_1091_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
lean_dec_ref(v_str_1178_);
v___x_1188_ = lean_array_get_size(v_vs_1134_);
v___x_1189_ = lean_unsigned_to_nat(1u);
v___x_1190_ = lean_nat_dec_eq(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = l_Lean_Name_str___override(v_pre_1177_, v___x_1180_);
v___x_1192_ = l_Lean_Name_str___override(v___x_1191_, v___x_1184_);
v_ctorName_1139_ = v___x_1192_;
v___y_1140_ = v_a_1088_;
v___y_1141_ = v_a_1089_;
v___y_1142_ = v_a_1090_;
v___y_1143_ = v_a_1091_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_val_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_del_object(v___x_1136_);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_array_fget(v_vs_1134_, v___x_1193_);
lean_dec_ref(v_vs_1134_);
v___x_1195_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_getNatConstant(v___x_1194_);
lean_dec(v___x_1194_);
v_val_1196_ = lean_nat_add(v___x_1195_, v___x_1189_);
lean_dec(v___x_1195_);
v___x_1197_ = 0;
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_val_1196_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
v___x_1200_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1201_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1197_, v___x_1199_, v___x_1200_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1214_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_fvarId_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v_fvarId_1206_ = lean_ctor_get(v_a_1202_, 0);
lean_inc(v_fvarId_1206_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_a_1202_);
v___x_1208_ = lean_mk_empty_array_with_capacity(v___x_1189_);
v___x_1209_ = lean_array_push(v___x_1208_, v___x_1207_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v_fvarId_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1210_);
v___x_1212_ = v___x_1204_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1201_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1201_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
lean_dec_ref(v_str_1178_);
v___x_1223_ = lean_array_get_size(v_vs_1134_);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = lean_nat_dec_eq(v___x_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = l_Lean_Name_str___override(v_pre_1177_, v___x_1180_);
v___x_1227_ = l_Lean_Name_str___override(v___x_1226_, v___x_1182_);
v_ctorName_1139_ = v___x_1227_;
v___y_1140_ = v_a_1088_;
v___y_1141_ = v_a_1089_;
v___y_1142_ = v_a_1090_;
v___y_1143_ = v_a_1091_;
goto v___jp_1138_;
}
else
{
uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_del_object(v___x_1136_);
lean_dec_ref(v_vs_1134_);
v___x_1228_ = 0;
v___x_1229_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__6));
v___x_1230_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1231_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1228_, v___x_1229_, v___x_1230_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1245_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1245_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1245_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_fvarId_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v_fvarId_1236_ = lean_ctor_get(v_a_1232_, 0);
lean_inc(v_fvarId_1236_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_a_1232_);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_mk_empty_array_with_capacity(v___x_1238_);
v___x_1240_ = lean_array_push(v___x_1239_, v___x_1237_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_fvarId_1236_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1241_);
v___x_1243_ = v___x_1234_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1231_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1231_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
}
else
{
v_ctorName_1139_ = v_i_1133_;
v___y_1140_ = v_a_1088_;
v___y_1141_ = v_a_1089_;
v___y_1142_ = v_a_1090_;
v___y_1143_ = v_a_1091_;
goto v___jp_1138_;
}
}
else
{
v_ctorName_1139_ = v_i_1133_;
v___y_1140_ = v_a_1088_;
v___y_1141_ = v_a_1089_;
v___y_1142_ = v_a_1090_;
v___y_1143_ = v_a_1091_;
goto v___jp_1138_;
}
}
else
{
v_ctorName_1139_ = v_i_1133_;
v___y_1140_ = v_a_1088_;
v___y_1141_ = v_a_1089_;
v___y_1142_ = v_a_1090_;
v___y_1143_ = v_a_1091_;
goto v___jp_1138_;
}
v___jp_1138_:
{
lean_object* v___x_1144_; lean_object* v_env_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_st_ref_get(v___y_1143_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc_ref(v_env_1145_);
lean_dec(v___x_1144_);
v___x_1146_ = 0;
lean_inc(v_ctorName_1139_);
v___x_1147_ = l_Lean_Environment_find_x3f(v_env_1145_, v_ctorName_1139_, v___x_1146_);
if (lean_obj_tag(v___x_1147_) == 1)
{
lean_object* v_val_1148_; 
v_val_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v___x_1147_, 1);
if (lean_obj_tag(v_val_1148_) == 6)
{
lean_object* v_val_1149_; size_t v_sz_1150_; size_t v___x_1151_; lean_object* v___x_1152_; 
v_val_1149_ = lean_ctor_get(v_val_1148_, 0);
lean_inc_ref(v_val_1149_);
lean_dec_ref_known(v_val_1148_, 1);
v_sz_1150_ = lean_array_size(v_vs_1134_);
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_1150_, v___x_1151_, v_vs_1134_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v_numParams_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v_numParams_1154_ = lean_ctor_get(v_val_1149_, 3);
lean_inc(v_numParams_1154_);
lean_dec_ref(v_val_1149_);
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__4));
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_mk_array(v_numParams_1154_, v___x_1157_);
v___x_1159_ = lean_array_get_size(v_a_1153_);
v___x_1160_ = lean_nat_dec_lt(v___x_1155_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_dec(v_a_1153_);
lean_del_object(v___x_1136_);
v___y_1094_ = v___y_1143_;
v___y_1095_ = v___y_1141_;
v___y_1096_ = v___y_1140_;
v___y_1097_ = v___y_1142_;
v___y_1098_ = v_ctorName_1139_;
v_fst_1099_ = v___x_1156_;
v_snd_1100_ = v___x_1158_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1162_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
lean_ctor_set(v___x_1136_, 1, v___x_1158_);
lean_ctor_set(v___x_1136_, 0, v___x_1156_);
v___x_1162_ = v___x_1136_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1158_);
v___x_1162_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
size_t v___x_1163_; lean_object* v___x_1164_; lean_object* v_fst_1165_; lean_object* v_snd_1166_; 
v___x_1163_ = lean_usize_of_nat(v___x_1159_);
v___x_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__2(v_a_1153_, v___x_1151_, v___x_1163_, v___x_1162_);
lean_dec(v_a_1153_);
v_fst_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_fst_1165_);
v_snd_1166_ = lean_ctor_get(v___x_1164_, 1);
lean_inc(v_snd_1166_);
lean_dec_ref(v___x_1164_);
v___y_1094_ = v___y_1143_;
v___y_1095_ = v___y_1141_;
v___y_1096_ = v___y_1140_;
v___y_1097_ = v___y_1142_;
v___y_1098_ = v_ctorName_1139_;
v_fst_1099_ = v_fst_1165_;
v_snd_1100_ = v_snd_1166_;
goto v___jp_1093_;
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_val_1149_);
lean_dec(v_ctorName_1139_);
lean_del_object(v___x_1136_);
v_a_1168_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1152_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1152_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_dec(v_val_1148_);
lean_dec(v_ctorName_1139_);
lean_del_object(v___x_1136_);
lean_dec_ref(v_vs_1134_);
v___y_1127_ = v___y_1140_;
v___y_1128_ = v___y_1141_;
v___y_1129_ = v___y_1142_;
v___y_1130_ = v___y_1143_;
goto v___jp_1126_;
}
}
else
{
lean_dec(v___x_1147_);
lean_dec(v_ctorName_1139_);
lean_del_object(v___x_1136_);
lean_dec_ref(v_vs_1134_);
v___y_1127_ = v___y_1140_;
v___y_1128_ = v___y_1141_;
v___y_1129_ = v___y_1142_;
v___y_1130_ = v___y_1143_;
goto v___jp_1126_;
}
}
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v_a_1087_);
v___x_1255_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__7);
v___x_1256_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1255_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
return v___x_1256_;
}
v___jp_1093_:
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1101_ = 0;
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1103_, 0, v___y_1098_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
lean_ctor_set(v___x_1103_, 2, v_snd_1100_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__1));
v___x_1105_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1101_, v___x_1103_, v___x_1104_, v___y_1096_, v___y_1095_, v___y_1097_, v___y_1094_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1117_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1117_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1117_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_fvarId_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v_fvarId_1110_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_fvarId_1110_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_a_1106_);
v___x_1112_ = lean_array_push(v_fst_1099_, v___x_1111_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v_fvarId_1110_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1113_);
v___x_1115_ = v___x_1108_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v_fst_1099_);
v_a_1118_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1105_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1105_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
v___jp_1126_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___closed__3);
v___x_1132_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0(v___x_1131_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(size_t v_sz_1257_, size_t v_i_1258_, lean_object* v_bs_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_usize_dec_lt(v_i_1258_, v_sz_1257_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v_bs_1259_);
return v___x_1266_;
}
else
{
lean_object* v_v_1267_; lean_object* v___x_1268_; lean_object* v_bs_x27_1269_; lean_object* v___x_1270_; 
v_v_1267_ = lean_array_uget(v_bs_1259_, v_i_1258_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v_bs_x27_1269_ = lean_array_uset(v_bs_1259_, v_i_1258_, v___x_1268_);
v___x_1270_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1267_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = lean_usize_add(v_i_1258_, v___x_1272_);
v___x_1274_ = lean_array_uset(v_bs_x27_1269_, v_i_1258_, v_a_1271_);
v_i_1258_ = v___x_1273_;
v_bs_1259_ = v___x_1274_;
goto _start;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_bs_x27_1269_);
v_a_1276_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1270_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1270_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1___boxed(lean_object* v_sz_1284_, lean_object* v_i_1285_, lean_object* v_bs_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
size_t v_sz_boxed_1292_; size_t v_i_boxed_1293_; lean_object* v_res_1294_; 
v_sz_boxed_1292_ = lean_unbox_usize(v_sz_1284_);
lean_dec(v_sz_1284_);
v_i_boxed_1293_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__1(v_sz_boxed_1292_, v_i_boxed_1293_, v_bs_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go___boxed(lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(lean_object* v_v_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_isLiteral(v_v_1302_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v_v_1302_);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1320_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_a_1312_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1311_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral___boxed(lean_object* v_v_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_v_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
return v_res_1335_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(lean_object* v_a_1336_, lean_object* v_b_1337_){
_start:
{
lean_object* v_fst_1338_; lean_object* v_fst_1339_; uint8_t v___x_1340_; 
v_fst_1338_ = lean_ctor_get(v_a_1336_, 0);
v_fst_1339_ = lean_ctor_get(v_b_1337_, 0);
v___x_1340_ = l_Lean_Name_quickLt(v_fst_1338_, v_fst_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt___boxed(lean_object* v_a_1341_, lean_object* v_b_1342_){
_start:
{
uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_res_1343_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_decLt(v_a_1341_, v_b_1342_);
lean_dec_ref(v_b_1342_);
lean_dec_ref(v_a_1341_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(lean_object* v_entries_1347_, lean_object* v_fid_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_array_get_size(v_entries_1347_);
v___x_1351_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v_fid_1348_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_nat_sub(v___x_1350_, v___x_1353_);
v___x_1355_ = lean_nat_dec_le(v___x_1349_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_dec(v___x_1354_);
lean_dec(v_fid_1348_);
v___x_1356_ = lean_box(0);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_fid_1348_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__0));
v___x_1360_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___closed__1));
v___x_1361_ = l_Array_binSearchAux___redArg(v___x_1359_, v___x_1360_, v_entries_1347_, v___x_1358_, v___x_1349_, v___x_1354_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_box(0);
return v___x_1362_;
}
else
{
lean_object* v_val_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1371_; 
v_val_1363_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1365_ = v___x_1361_;
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_val_1363_);
lean_dec(v___x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_snd_1367_; lean_object* v___x_1369_; 
v_snd_1367_ = lean_ctor_get(v_val_1363_, 1);
lean_inc(v_snd_1367_);
lean_dec(v_val_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v_snd_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_snd_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f___boxed(lean_object* v_entries_1372_, lean_object* v_fid_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_findAtSorted_x3f(v_entries_1372_, v_fid_1373_);
lean_dec_ref(v_entries_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_es_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_array_mk(v_es_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1377_, lean_object* v_i_1378_, lean_object* v_k_1379_){
_start:
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_array_get_size(v_keys_1377_);
v___x_1381_ = lean_nat_dec_lt(v_i_1378_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec(v_i_1378_);
return v___x_1381_;
}
else
{
lean_object* v_k_x27_1382_; uint8_t v___x_1383_; 
v_k_x27_1382_ = lean_array_fget_borrowed(v_keys_1377_, v_i_1378_);
v___x_1383_ = lean_name_eq(v_k_1379_, v_k_x27_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_i_1378_, v___x_1384_);
lean_dec(v_i_1378_);
v_i_1378_ = v___x_1385_;
goto _start;
}
else
{
lean_dec(v_i_1378_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1387_, lean_object* v_i_1388_, lean_object* v_k_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1387_, v_i_1388_, v_k_1389_);
lean_dec(v_k_1389_);
lean_dec_ref(v_keys_1387_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1392_, size_t v_x_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 0)
{
lean_object* v_es_1395_; lean_object* v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v_j_1399_; lean_object* v___x_1400_; 
v_es_1395_ = lean_ctor_get(v_x_1392_, 0);
v___x_1396_ = lean_box(2);
v___x_1397_ = ((size_t)31ULL);
v___x_1398_ = lean_usize_land(v_x_1393_, v___x_1397_);
v_j_1399_ = lean_usize_to_nat(v___x_1398_);
v___x_1400_ = lean_array_get_borrowed(v___x_1396_, v_es_1395_, v_j_1399_);
lean_dec(v_j_1399_);
switch(lean_obj_tag(v___x_1400_))
{
case 0:
{
lean_object* v_key_1401_; uint8_t v___x_1402_; 
v_key_1401_ = lean_ctor_get(v___x_1400_, 0);
v___x_1402_ = lean_name_eq(v_x_1394_, v_key_1401_);
return v___x_1402_;
}
case 1:
{
lean_object* v_node_1403_; size_t v___x_1404_; size_t v___x_1405_; 
v_node_1403_ = lean_ctor_get(v___x_1400_, 0);
v___x_1404_ = ((size_t)5ULL);
v___x_1405_ = lean_usize_shift_right(v_x_1393_, v___x_1404_);
v_x_1392_ = v_node_1403_;
v_x_1393_ = v___x_1405_;
goto _start;
}
default: 
{
uint8_t v___x_1407_; 
v___x_1407_ = 0;
return v___x_1407_;
}
}
}
else
{
lean_object* v_ks_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_ks_1408_ = lean_ctor_get(v_x_1392_, 0);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1408_, v___x_1409_, v_x_1394_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
size_t v_x_1145__boxed_1414_; uint8_t v_res_1415_; lean_object* v_r_1416_; 
v_x_1145__boxed_1414_ = lean_unbox_usize(v_x_1412_);
lean_dec(v_x_1412_);
v_res_1415_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1411_, v_x_1145__boxed_1414_, v_x_1413_);
lean_dec(v_x_1413_);
lean_dec_ref(v_x_1411_);
v_r_1416_ = lean_box(v_res_1415_);
return v_r_1416_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
uint64_t v___y_1420_; 
if (lean_obj_tag(v_x_1418_) == 0)
{
uint64_t v___x_1423_; 
v___x_1423_ = 1723ULL;
v___y_1420_ = v___x_1423_;
goto v___jp_1419_;
}
else
{
uint64_t v_hash_1424_; 
v_hash_1424_ = lean_ctor_get_uint64(v_x_1418_, sizeof(void*)*2);
v___y_1420_ = v_hash_1424_;
goto v___jp_1419_;
}
v___jp_1419_:
{
size_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = lean_uint64_to_usize(v___y_1420_);
v___x_1422_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1417_, v___x_1421_, v_x_1418_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
uint8_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1425_, v_x_1426_);
lean_dec(v_x_1426_);
lean_dec_ref(v_x_1425_);
v_r_1428_ = lean_box(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x1_1429_, lean_object* v_x2_1430_){
_start:
{
lean_object* v_fst_1431_; uint8_t v___x_1432_; 
v_fst_1431_ = lean_ctor_get(v_x2_1430_, 0);
v___x_1432_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x1_1429_, v_fst_1431_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = 1;
return v___x_1433_;
}
else
{
uint8_t v___x_1434_; 
v___x_1434_ = 0;
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x1_1435_, lean_object* v_x2_1436_){
_start:
{
uint8_t v_res_1437_; lean_object* v_r_1438_; 
v_res_1437_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x1_1435_, v_x2_1436_);
lean_dec_ref(v_x2_1436_);
lean_dec_ref(v_x1_1435_);
v_r_1438_ = lean_box(v_res_1437_);
return v_r_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_f_1439_, lean_object* v_keys_1440_, lean_object* v_vals_1441_, lean_object* v_i_1442_, lean_object* v_acc_1443_){
_start:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_array_get_size(v_keys_1440_);
v___x_1445_ = lean_nat_dec_lt(v_i_1442_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec(v_i_1442_);
lean_dec(v_f_1439_);
return v_acc_1443_;
}
else
{
lean_object* v_k_1446_; lean_object* v_v_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_k_1446_ = lean_array_fget_borrowed(v_keys_1440_, v_i_1442_);
v_v_1447_ = lean_array_fget_borrowed(v_vals_1441_, v_i_1442_);
lean_inc(v_f_1439_);
lean_inc(v_v_1447_);
lean_inc(v_k_1446_);
v___x_1448_ = lean_apply_3(v_f_1439_, v_acc_1443_, v_k_1446_, v_v_1447_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_i_1442_, v___x_1449_);
lean_dec(v_i_1442_);
v_i_1442_ = v___x_1450_;
v_acc_1443_ = v___x_1448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_f_1452_, lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_i_1455_, lean_object* v_acc_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1452_, v_keys_1453_, v_vals_1454_, v_i_1455_, v_acc_1456_);
lean_dec_ref(v_vals_1454_);
lean_dec_ref(v_keys_1453_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1458_, lean_object* v_as_1459_, size_t v_i_1460_, size_t v_stop_1461_, lean_object* v_b_1462_){
_start:
{
lean_object* v___y_1464_; uint8_t v___x_1468_; 
v___x_1468_ = lean_usize_dec_eq(v_i_1460_, v_stop_1461_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_array_uget_borrowed(v_as_1459_, v_i_1460_);
switch(lean_obj_tag(v___x_1469_))
{
case 0:
{
lean_object* v_key_1470_; lean_object* v_val_1471_; lean_object* v___x_1472_; 
v_key_1470_ = lean_ctor_get(v___x_1469_, 0);
v_val_1471_ = lean_ctor_get(v___x_1469_, 1);
lean_inc(v_f_1458_);
lean_inc(v_val_1471_);
lean_inc(v_key_1470_);
v___x_1472_ = lean_apply_3(v_f_1458_, v_b_1462_, v_key_1470_, v_val_1471_);
v___y_1464_ = v___x_1472_;
goto v___jp_1463_;
}
case 1:
{
lean_object* v_node_1473_; lean_object* v___x_1474_; 
v_node_1473_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_f_1458_);
v___x_1474_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1458_, v_node_1473_, v_b_1462_);
v___y_1464_ = v___x_1474_;
goto v___jp_1463_;
}
default: 
{
v___y_1464_ = v_b_1462_;
goto v___jp_1463_;
}
}
}
else
{
lean_dec(v_f_1458_);
return v_b_1462_;
}
v___jp_1463_:
{
size_t v___x_1465_; size_t v___x_1466_; 
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_add(v_i_1460_, v___x_1465_);
v_i_1460_ = v___x_1466_;
v_b_1462_ = v___y_1464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1476_) == 0)
{
lean_object* v_es_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_es_1478_ = lean_ctor_get(v_x_1476_, 0);
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = lean_array_get_size(v_es_1478_);
v___x_1481_ = lean_nat_dec_lt(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_dec(v_f_1475_);
return v_x_1477_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1480_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1475_, v_es_1478_, v___x_1482_, v___x_1483_, v_x_1477_);
return v___x_1484_;
}
}
else
{
lean_object* v_ks_1485_; lean_object* v_vs_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_ks_1485_ = lean_ctor_get(v_x_1476_, 0);
v_vs_1486_ = lean_ctor_get(v_x_1476_, 1);
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_1475_, v_ks_1485_, v_vs_1486_, v___x_1487_, v_x_1477_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1489_, v_x_1490_, v_x_1491_);
lean_dec_ref(v_x_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1493_, lean_object* v_as_1494_, lean_object* v_i_1495_, lean_object* v_stop_1496_, lean_object* v_b_1497_){
_start:
{
size_t v_i_boxed_1498_; size_t v_stop_boxed_1499_; lean_object* v_res_1500_; 
v_i_boxed_1498_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_stop_boxed_1499_ = lean_unbox_usize(v_stop_1496_);
lean_dec(v_stop_1496_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1493_, v_as_1494_, v_i_boxed_1498_, v_stop_boxed_1499_, v_b_1497_);
lean_dec_ref(v_as_1494_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1501_, lean_object* v_x1_1502_, lean_object* v_x2_1503_, lean_object* v_x3_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_apply_3(v_f_1501_, v_x1_1502_, v_x2_1503_, v_x3_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1506_, lean_object* v_f_1507_, lean_object* v_init_1508_){
_start:
{
lean_object* v___f_1509_; lean_object* v___x_1510_; 
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1509_, 0, v_f_1507_);
v___x_1510_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1509_, v_map_1506_, v_init_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1511_, lean_object* v_f_1512_, lean_object* v_init_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1511_, v_f_1512_, v_init_1513_);
lean_dec_ref(v_map_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1515_, lean_object* v_k_1516_, lean_object* v_v_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_k_1516_);
lean_ctor_set(v___x_1518_, 1, v_v_1517_);
v___x_1519_ = lean_array_push(v_ps_1515_, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1523_){
_start:
{
lean_object* v___f_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___f_1524_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1525_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1526_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1523_, v___f_1524_, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1527_);
lean_dec_ref(v_m_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_fst_1531_; lean_object* v_fst_1532_; uint8_t v___x_1533_; 
v_fst_1531_ = lean_ctor_get(v___y_1529_, 0);
v_fst_1532_ = lean_ctor_get(v___y_1530_, 0);
v___x_1533_ = l_Lean_Name_quickLt(v_fst_1531_, v_fst_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1534_, v___y_1535_);
lean_dec_ref(v___y_1535_);
lean_dec_ref(v___y_1534_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_hi_1538_, lean_object* v_pivot_1539_, lean_object* v_as_1540_, lean_object* v_i_1541_, lean_object* v_k_1542_){
_start:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_nat_dec_lt(v_k_1542_, v_hi_1538_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_k_1542_);
v___x_1544_ = lean_array_fswap(v_as_1540_, v_i_1541_, v_hi_1538_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_i_1541_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; lean_object* v_fst_1547_; lean_object* v_fst_1548_; uint8_t v___x_1549_; 
v___x_1546_ = lean_array_fget_borrowed(v_as_1540_, v_k_1542_);
v_fst_1547_ = lean_ctor_get(v___x_1546_, 0);
v_fst_1548_ = lean_ctor_get(v_pivot_1539_, 0);
v___x_1549_ = l_Lean_Name_quickLt(v_fst_1547_, v_fst_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_k_1542_, v___x_1550_);
lean_dec(v_k_1542_);
v_k_1542_ = v___x_1551_;
goto _start;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_array_fswap(v_as_1540_, v_i_1541_, v_k_1542_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_i_1541_, v___x_1554_);
lean_dec(v_i_1541_);
v___x_1556_ = lean_nat_add(v_k_1542_, v___x_1554_);
lean_dec(v_k_1542_);
v_as_1540_ = v___x_1553_;
v_i_1541_ = v___x_1555_;
v_k_1542_ = v___x_1556_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_hi_1558_, lean_object* v_pivot_1559_, lean_object* v_as_1560_, lean_object* v_i_1561_, lean_object* v_k_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1558_, v_pivot_1559_, v_as_1560_, v_i_1561_, v_k_1562_);
lean_dec_ref(v_pivot_1559_);
lean_dec(v_hi_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_1564_, lean_object* v_as_1565_, lean_object* v_lo_1566_, lean_object* v_hi_1567_){
_start:
{
lean_object* v___y_1569_; uint8_t v___x_1579_; 
v___x_1579_ = lean_nat_dec_lt(v_lo_1566_, v_hi_1567_);
if (v___x_1579_ == 0)
{
lean_dec(v_lo_1566_);
return v_as_1565_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_mid_1582_; lean_object* v___y_1584_; lean_object* v___y_1590_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1580_ = lean_nat_add(v_lo_1566_, v_hi_1567_);
v___x_1581_ = lean_unsigned_to_nat(1u);
v_mid_1582_ = lean_nat_shiftr(v___x_1580_, v___x_1581_);
lean_dec(v___x_1580_);
v___x_1595_ = lean_array_fget_borrowed(v_as_1565_, v_mid_1582_);
v___x_1596_ = lean_array_fget_borrowed(v_as_1565_, v_lo_1566_);
v___x_1597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
v___y_1590_ = v_as_1565_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_array_fswap(v_as_1565_, v_lo_1566_, v_mid_1582_);
v___y_1590_ = v___x_1598_;
goto v___jp_1589_;
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_array_fget_borrowed(v___y_1584_, v_mid_1582_);
v___x_1586_ = lean_array_fget_borrowed(v___y_1584_, v_hi_1567_);
v___x_1587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_dec(v_mid_1582_);
v___y_1569_ = v___y_1584_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_array_fswap(v___y_1584_, v_mid_1582_, v_hi_1567_);
lean_dec(v_mid_1582_);
v___y_1569_ = v___x_1588_;
goto v___jp_1568_;
}
}
v___jp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_array_fget_borrowed(v___y_1590_, v_hi_1567_);
v___x_1592_ = lean_array_fget_borrowed(v___y_1590_, v_lo_1566_);
v___x_1593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___lam__0(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
v___y_1584_ = v___y_1590_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_array_fswap(v___y_1590_, v_lo_1566_, v_hi_1567_);
v___y_1584_ = v___x_1594_;
goto v___jp_1583_;
}
}
}
v___jp_1568_:
{
lean_object* v_pivot_1570_; lean_object* v___x_1571_; lean_object* v_fst_1572_; lean_object* v_snd_1573_; uint8_t v___x_1574_; 
v_pivot_1570_ = lean_array_fget(v___y_1569_, v_hi_1567_);
lean_inc_n(v_lo_1566_, 2);
v___x_1571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1567_, v_pivot_1570_, v___y_1569_, v_lo_1566_, v_lo_1566_);
lean_dec(v_pivot_1570_);
v_fst_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_fst_1572_);
v_snd_1573_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_snd_1573_);
lean_dec_ref(v___x_1571_);
v___x_1574_ = lean_nat_dec_le(v_hi_1567_, v_fst_1572_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1564_, v_snd_1573_, v_lo_1566_, v_fst_1572_);
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_add(v_fst_1572_, v___x_1576_);
lean_dec(v_fst_1572_);
v_as_1565_ = v___x_1575_;
v_lo_1566_ = v___x_1577_;
goto _start;
}
else
{
lean_dec(v_fst_1572_);
lean_dec(v_lo_1566_);
return v_snd_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_1599_, lean_object* v_as_1600_, lean_object* v_lo_1601_, lean_object* v_hi_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1599_, v_as_1600_, v_lo_1601_, v_hi_1602_);
lean_dec(v_hi_1602_);
lean_dec(v_n_1599_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1606_, lean_object* v_s_1607_, lean_object* v_x_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___x_1618_; 
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1611_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_s_1607_);
v___x_1612_ = lean_array_get_size(v___x_1611_);
v___x_1618_ = lean_nat_dec_eq(v___x_1612_, v___x_1609_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___y_1622_; uint8_t v___x_1624_; 
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_sub(v___x_1612_, v___x_1619_);
v___x_1624_ = lean_nat_dec_le(v___x_1609_, v___x_1620_);
if (v___x_1624_ == 0)
{
lean_inc(v___x_1620_);
v___y_1622_ = v___x_1620_;
goto v___jp_1621_;
}
else
{
v___y_1622_ = v___x_1609_;
goto v___jp_1621_;
}
v___jp_1621_:
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_nat_dec_le(v___y_1622_, v___x_1620_);
if (v___x_1623_ == 0)
{
lean_dec(v___x_1620_);
lean_inc(v___y_1622_);
v___y_1614_ = v___y_1622_;
v___y_1615_ = v___y_1622_;
goto v___jp_1613_;
}
else
{
v___y_1614_ = v___y_1622_;
v___y_1615_ = v___x_1620_;
goto v___jp_1613_;
}
}
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1610_);
lean_ctor_set(v___x_1625_, 1, v___x_1610_);
lean_ctor_set(v___x_1625_, 2, v___x_1611_);
return v___x_1625_;
}
v___jp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v___x_1612_, v___x_1611_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
v___x_1617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1610_);
lean_ctor_set(v___x_1617_, 1, v___x_1610_);
lean_ctor_set(v___x_1617_, 2, v___x_1616_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1626_, lean_object* v_s_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1626_, v_s_1627_, v_x_1628_);
lean_dec(v_x_1628_);
lean_dec_ref(v_s_1627_);
lean_dec_ref(v_x_1626_);
return v_res_1629_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1630_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_x_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(v_x_1635_);
lean_dec_ref(v_x_1635_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v_ks_1641_; lean_object* v_vs_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1666_; 
v_ks_1641_ = lean_ctor_get(v_x_1637_, 0);
v_vs_1642_ = lean_ctor_get(v_x_1637_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1644_ = v_x_1637_;
v_isShared_1645_ = v_isSharedCheck_1666_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_vs_1642_);
lean_inc(v_ks_1641_);
lean_dec(v_x_1637_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1666_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = lean_array_get_size(v_ks_1641_);
v___x_1647_ = lean_nat_dec_lt(v_x_1638_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
lean_dec(v_x_1638_);
v___x_1648_ = lean_array_push(v_ks_1641_, v_x_1639_);
v___x_1649_ = lean_array_push(v_vs_1642_, v_x_1640_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___x_1649_);
lean_ctor_set(v___x_1644_, 0, v___x_1648_);
v___x_1651_ = v___x_1644_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
else
{
lean_object* v_k_x27_1653_; uint8_t v___x_1654_; 
v_k_x27_1653_ = lean_array_fget_borrowed(v_ks_1641_, v_x_1638_);
v___x_1654_ = lean_name_eq(v_x_1639_, v_k_x27_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1656_; 
if (v_isShared_1645_ == 0)
{
v___x_1656_ = v___x_1644_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_ks_1641_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_vs_1642_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_nat_add(v_x_1638_, v___x_1657_);
lean_dec(v_x_1638_);
v_x_1637_ = v___x_1656_;
v_x_1638_ = v___x_1658_;
goto _start;
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1661_ = lean_array_fset(v_ks_1641_, v_x_1638_, v_x_1639_);
v___x_1662_ = lean_array_fset(v_vs_1642_, v_x_1638_, v_x_1640_);
lean_dec(v_x_1638_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___x_1662_);
lean_ctor_set(v___x_1644_, 0, v___x_1661_);
v___x_1664_ = v___x_1644_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_n_1667_, lean_object* v_k_1668_, lean_object* v_v_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_n_1667_, v___x_1670_, v_k_1668_, v_v_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_x_1673_, size_t v_x_1674_, size_t v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1673_) == 0)
{
lean_object* v_es_1678_; size_t v___x_1679_; size_t v___x_1680_; lean_object* v_j_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_es_1678_ = lean_ctor_get(v_x_1673_, 0);
v___x_1679_ = ((size_t)31ULL);
v___x_1680_ = lean_usize_land(v_x_1674_, v___x_1679_);
v_j_1681_ = lean_usize_to_nat(v___x_1680_);
v___x_1682_ = lean_array_get_size(v_es_1678_);
v___x_1683_ = lean_nat_dec_lt(v_j_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_dec(v_j_1681_);
lean_dec(v_x_1677_);
lean_dec(v_x_1676_);
return v_x_1673_;
}
else
{
lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1722_; 
lean_inc_ref(v_es_1678_);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_x_1673_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v_x_1673_, 0);
lean_dec(v_unused_1723_);
v___x_1685_ = v_x_1673_;
v_isShared_1686_ = v_isSharedCheck_1722_;
goto v_resetjp_1684_;
}
else
{
lean_dec(v_x_1673_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1722_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_v_1687_; lean_object* v___x_1688_; lean_object* v_xs_x27_1689_; lean_object* v___y_1691_; 
v_v_1687_ = lean_array_fget(v_es_1678_, v_j_1681_);
v___x_1688_ = lean_box(0);
v_xs_x27_1689_ = lean_array_fset(v_es_1678_, v_j_1681_, v___x_1688_);
switch(lean_obj_tag(v_v_1687_))
{
case 0:
{
lean_object* v_key_1696_; lean_object* v_val_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1707_; 
v_key_1696_ = lean_ctor_get(v_v_1687_, 0);
v_val_1697_ = lean_ctor_get(v_v_1687_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_v_1687_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1699_ = v_v_1687_;
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_val_1697_);
lean_inc(v_key_1696_);
lean_dec(v_v_1687_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_name_eq(v_x_1676_, v_key_1696_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_del_object(v___x_1699_);
v___x_1702_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1696_, v_val_1697_, v_x_1676_, v_x_1677_);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
v___y_1691_ = v___x_1703_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1705_; 
lean_dec(v_val_1697_);
lean_dec(v_key_1696_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v_x_1677_);
lean_ctor_set(v___x_1699_, 0, v_x_1676_);
v___x_1705_ = v___x_1699_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_x_1676_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_x_1677_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
v___y_1691_ = v___x_1705_;
goto v___jp_1690_;
}
}
}
}
case 1:
{
lean_object* v_node_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1720_; 
v_node_1708_ = lean_ctor_get(v_v_1687_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_v_1687_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1710_ = v_v_1687_;
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_node_1708_);
lean_dec(v_v_1687_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
size_t v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1712_ = ((size_t)5ULL);
v___x_1713_ = lean_usize_shift_right(v_x_1674_, v___x_1712_);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_x_1675_, v___x_1714_);
v___x_1716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_node_1708_, v___x_1713_, v___x_1715_, v_x_1676_, v_x_1677_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1716_);
v___x_1718_ = v___x_1710_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v___y_1691_ = v___x_1718_;
goto v___jp_1690_;
}
}
}
default: 
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_x_1676_);
lean_ctor_set(v___x_1721_, 1, v_x_1677_);
v___y_1691_ = v___x_1721_;
goto v___jp_1690_;
}
}
v___jp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_array_fset(v_xs_x27_1689_, v_j_1681_, v___y_1691_);
lean_dec(v_j_1681_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1692_);
v___x_1694_ = v___x_1685_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v_ks_1724_; lean_object* v_vs_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1743_; 
v_ks_1724_ = lean_ctor_get(v_x_1673_, 0);
v_vs_1725_ = lean_ctor_get(v_x_1673_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_x_1673_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1727_ = v_x_1673_;
v_isShared_1728_ = v_isSharedCheck_1743_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_vs_1725_);
lean_inc(v_ks_1724_);
lean_dec(v_x_1673_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1743_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_ks_1724_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_vs_1725_);
v___x_1730_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v_newNode_1731_; size_t v___x_1732_; uint8_t v___x_1733_; 
v_newNode_1731_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v___x_1730_, v_x_1676_, v_x_1677_);
v___x_1732_ = ((size_t)7ULL);
v___x_1733_ = lean_usize_dec_le(v___x_1732_, v_x_1675_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1734_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1731_);
v___x_1735_ = lean_unsigned_to_nat(4u);
v___x_1736_ = lean_nat_dec_lt(v___x_1734_, v___x_1735_);
lean_dec(v___x_1734_);
if (v___x_1736_ == 0)
{
lean_object* v_ks_1737_; lean_object* v_vs_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_ks_1737_ = lean_ctor_get(v_newNode_1731_, 0);
lean_inc_ref(v_ks_1737_);
v_vs_1738_ = lean_ctor_get(v_newNode_1731_, 1);
lean_inc_ref(v_vs_1738_);
lean_dec_ref(v_newNode_1731_);
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___closed__0);
v___x_1741_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_x_1675_, v_ks_1737_, v_vs_1738_, v___x_1739_, v___x_1740_);
lean_dec_ref(v_vs_1738_);
lean_dec_ref(v_ks_1737_);
return v___x_1741_;
}
else
{
return v_newNode_1731_;
}
}
else
{
return v_newNode_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(size_t v_depth_1744_, lean_object* v_keys_1745_, lean_object* v_vals_1746_, lean_object* v_i_1747_, lean_object* v_entries_1748_){
_start:
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = lean_array_get_size(v_keys_1745_);
v___x_1750_ = lean_nat_dec_lt(v_i_1747_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec(v_i_1747_);
return v_entries_1748_;
}
else
{
lean_object* v_k_1751_; lean_object* v_v_1752_; uint64_t v___y_1754_; 
v_k_1751_ = lean_array_fget_borrowed(v_keys_1745_, v_i_1747_);
v_v_1752_ = lean_array_fget_borrowed(v_vals_1746_, v_i_1747_);
if (lean_obj_tag(v_k_1751_) == 0)
{
uint64_t v___x_1765_; 
v___x_1765_ = 1723ULL;
v___y_1754_ = v___x_1765_;
goto v___jp_1753_;
}
else
{
uint64_t v_hash_1766_; 
v_hash_1766_ = lean_ctor_get_uint64(v_k_1751_, sizeof(void*)*2);
v___y_1754_ = v_hash_1766_;
goto v___jp_1753_;
}
v___jp_1753_:
{
size_t v_h_1755_; size_t v___x_1756_; lean_object* v___x_1757_; size_t v___x_1758_; size_t v___x_1759_; size_t v___x_1760_; size_t v_h_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_h_1755_ = lean_uint64_to_usize(v___y_1754_);
v___x_1756_ = ((size_t)5ULL);
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_sub(v_depth_1744_, v___x_1758_);
v___x_1760_ = lean_usize_mul(v___x_1756_, v___x_1759_);
v_h_1761_ = lean_usize_shift_right(v_h_1755_, v___x_1760_);
v___x_1762_ = lean_nat_add(v_i_1747_, v___x_1757_);
lean_dec(v_i_1747_);
lean_inc(v_v_1752_);
lean_inc(v_k_1751_);
v___x_1763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_entries_1748_, v_h_1761_, v_depth_1744_, v_k_1751_, v_v_1752_);
v_i_1747_ = v___x_1762_;
v_entries_1748_ = v___x_1763_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_1767_, lean_object* v_keys_1768_, lean_object* v_vals_1769_, lean_object* v_i_1770_, lean_object* v_entries_1771_){
_start:
{
size_t v_depth_boxed_1772_; lean_object* v_res_1773_; 
v_depth_boxed_1772_ = lean_unbox_usize(v_depth_1767_);
lean_dec(v_depth_1767_);
v_res_1773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_boxed_1772_, v_keys_1768_, v_vals_1769_, v_i_1770_, v_entries_1771_);
lean_dec_ref(v_vals_1769_);
lean_dec_ref(v_keys_1768_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_x_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
size_t v_x_1539__boxed_1779_; size_t v_x_1540__boxed_1780_; lean_object* v_res_1781_; 
v_x_1539__boxed_1779_ = lean_unbox_usize(v_x_1775_);
lean_dec(v_x_1775_);
v_x_1540__boxed_1780_ = lean_unbox_usize(v_x_1776_);
lean_dec(v_x_1776_);
v_res_1781_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1774_, v_x_1539__boxed_1779_, v_x_1540__boxed_1780_, v_x_1777_, v_x_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_){
_start:
{
uint64_t v___y_1786_; 
if (lean_obj_tag(v_x_1783_) == 0)
{
uint64_t v___x_1790_; 
v___x_1790_ = 1723ULL;
v___y_1786_ = v___x_1790_;
goto v___jp_1785_;
}
else
{
uint64_t v_hash_1791_; 
v_hash_1791_ = lean_ctor_get_uint64(v_x_1783_, sizeof(void*)*2);
v___y_1786_ = v_hash_1791_;
goto v___jp_1785_;
}
v___jp_1785_:
{
size_t v___x_1787_; size_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = lean_uint64_to_usize(v___y_1786_);
v___x_1788_ = ((size_t)1ULL);
v___x_1789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1782_, v___x_1787_, v___x_1788_, v_x_1783_, v_x_1784_);
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(lean_object* v_s_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v_fst_1794_; lean_object* v_snd_1795_; lean_object* v___x_1796_; 
v_fst_1794_ = lean_ctor_get(v_x_1793_, 0);
lean_inc(v_fst_1794_);
v_snd_1795_ = lean_ctor_get(v_x_1793_, 1);
lean_inc(v_snd_1795_);
lean_dec_ref(v_x_1793_);
v___x_1796_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_s_1792_, v_fst_1794_, v_snd_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_));
v___x_1831_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2____boxed(lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_();
return v_res_1833_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___redArg(v_x_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
uint8_t v_res_1841_; lean_object* v_r_1842_; 
v_res_1841_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0(v_00_u03b2_1838_, v_x_1839_, v_x_1840_);
lean_dec(v_x_1840_);
lean_dec_ref(v_x_1839_);
v_r_1842_ = lean_box(v_res_1841_);
return v_r_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1843_, lean_object* v_m_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___redArg(v_m_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1846_, lean_object* v_m_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1(v_00_u03b2_1846_, v_m_1847_);
lean_dec_ref(v_m_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(lean_object* v_n_1849_, lean_object* v_as_1850_, lean_object* v_lo_1851_, lean_object* v_hi_1852_, lean_object* v_w_1853_, lean_object* v_hlo_1854_, lean_object* v_hhi_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___redArg(v_n_1849_, v_as_1850_, v_lo_1851_, v_hi_1852_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1857_, lean_object* v_as_1858_, lean_object* v_lo_1859_, lean_object* v_hi_1860_, lean_object* v_w_1861_, lean_object* v_hlo_1862_, lean_object* v_hhi_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2(v_n_1857_, v_as_1858_, v_lo_1859_, v_hi_1860_, v_w_1861_, v_hlo_1862_, v_hhi_1863_);
lean_dec(v_hi_1860_);
lean_dec(v_n_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3___redArg(v_x_1866_, v_x_1867_, v_x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, size_t v_x_1872_, lean_object* v_x_1873_){
_start:
{
uint8_t v___x_1874_; 
v___x_1874_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1871_, v_x_1872_, v_x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
size_t v_x_1842__boxed_1879_; uint8_t v_res_1880_; lean_object* v_r_1881_; 
v_x_1842__boxed_1879_ = lean_unbox_usize(v_x_1877_);
lean_dec(v_x_1877_);
v_res_1880_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1875_, v_x_1876_, v_x_1842__boxed_1879_, v_x_1878_);
lean_dec(v_x_1878_);
lean_dec_ref(v_x_1876_);
v_r_1881_ = lean_box(v_res_1880_);
return v_r_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_map_1884_, lean_object* v_f_1885_, lean_object* v_init_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1884_, v_f_1885_, v_init_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_map_1890_, lean_object* v_f_1891_, lean_object* v_init_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1888_, v_00_u03b2_1889_, v_map_1890_, v_f_1891_, v_init_1892_);
lean_dec_ref(v_map_1890_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_n_1894_, lean_object* v_lo_1895_, lean_object* v_hi_1896_, lean_object* v_hhi_1897_, lean_object* v_pivot_1898_, lean_object* v_as_1899_, lean_object* v_i_1900_, lean_object* v_k_1901_, lean_object* v_ilo_1902_, lean_object* v_ik_1903_, lean_object* v_w_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___redArg(v_hi_1896_, v_pivot_1898_, v_as_1899_, v_i_1900_, v_k_1901_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_n_1906_, lean_object* v_lo_1907_, lean_object* v_hi_1908_, lean_object* v_hhi_1909_, lean_object* v_pivot_1910_, lean_object* v_as_1911_, lean_object* v_i_1912_, lean_object* v_k_1913_, lean_object* v_ilo_1914_, lean_object* v_ik_1915_, lean_object* v_w_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__2_spec__4(v_n_1906_, v_lo_1907_, v_hi_1908_, v_hhi_1909_, v_pivot_1910_, v_as_1911_, v_i_1912_, v_k_1913_, v_ilo_1914_, v_ik_1915_, v_w_1916_);
lean_dec_ref(v_pivot_1910_);
lean_dec(v_hi_1908_);
lean_dec(v_lo_1907_);
lean_dec(v_n_1906_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1918_, lean_object* v_x_1919_, size_t v_x_1920_, size_t v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1919_, v_x_1920_, v_x_1921_, v_x_1922_, v_x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1925_, lean_object* v_x_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
size_t v_x_1857__boxed_1931_; size_t v_x_1858__boxed_1932_; lean_object* v_res_1933_; 
v_x_1857__boxed_1931_ = lean_unbox_usize(v_x_1927_);
lean_dec(v_x_1927_);
v_x_1858__boxed_1932_ = lean_unbox_usize(v_x_1928_);
lean_dec(v_x_1928_);
v_res_1933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1925_, v_x_1926_, v_x_1857__boxed_1931_, v_x_1858__boxed_1932_, v_x_1929_, v_x_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1934_, lean_object* v_keys_1935_, lean_object* v_vals_1936_, lean_object* v_heq_1937_, lean_object* v_i_1938_, lean_object* v_k_1939_){
_start:
{
uint8_t v___x_1940_; 
v___x_1940_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1935_, v_i_1938_, v_k_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1941_, lean_object* v_keys_1942_, lean_object* v_vals_1943_, lean_object* v_heq_1944_, lean_object* v_i_1945_, lean_object* v_k_1946_){
_start:
{
uint8_t v_res_1947_; lean_object* v_r_1948_; 
v_res_1947_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1941_, v_keys_1942_, v_vals_1943_, v_heq_1944_, v_i_1945_, v_k_1946_);
lean_dec(v_k_1946_);
lean_dec_ref(v_vals_1943_);
lean_dec_ref(v_keys_1942_);
v_r_1948_ = lean_box(v_res_1947_);
return v_r_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1949_, lean_object* v_f_1950_, lean_object* v_init_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1950_, v_map_1949_, v_init_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1953_, lean_object* v_f_1954_, lean_object* v_init_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1953_, v_f_1954_, v_init_1955_);
lean_dec_ref(v_map_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1957_, lean_object* v_00_u03b2_1958_, lean_object* v_map_1959_, lean_object* v_f_1960_, lean_object* v_init_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1960_, v_map_1959_, v_init_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1963_, lean_object* v_00_u03b2_1964_, lean_object* v_map_1965_, lean_object* v_f_1966_, lean_object* v_init_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1963_, v_00_u03b2_1964_, v_map_1965_, v_f_1966_, v_init_1967_);
lean_dec_ref(v_map_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1969_, lean_object* v_n_1970_, lean_object* v_k_1971_, lean_object* v_v_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_n_1970_, v_k_1971_, v_v_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1974_, size_t v_depth_1975_, lean_object* v_keys_1976_, lean_object* v_vals_1977_, lean_object* v_heq_1978_, lean_object* v_i_1979_, lean_object* v_entries_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___redArg(v_depth_1975_, v_keys_1976_, v_vals_1977_, v_i_1979_, v_entries_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1982_, lean_object* v_depth_1983_, lean_object* v_keys_1984_, lean_object* v_vals_1985_, lean_object* v_heq_1986_, lean_object* v_i_1987_, lean_object* v_entries_1988_){
_start:
{
size_t v_depth_boxed_1989_; lean_object* v_res_1990_; 
v_depth_boxed_1989_ = lean_unbox_usize(v_depth_1983_);
lean_dec(v_depth_1983_);
v_res_1990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__10(v_00_u03b2_1982_, v_depth_boxed_1989_, v_keys_1984_, v_vals_1985_, v_heq_1986_, v_i_1987_, v_entries_1988_);
lean_dec_ref(v_vals_1985_);
lean_dec_ref(v_keys_1984_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_1991_, lean_object* v_00_u03b1_1992_, lean_object* v_00_u03b2_1993_, lean_object* v_f_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1994_, v_x_1995_, v_x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_1998_, lean_object* v_00_u03b1_1999_, lean_object* v_00_u03b2_2000_, lean_object* v_f_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_1998_, v_00_u03b1_1999_, v_00_u03b2_2000_, v_f_2001_, v_x_2002_, v_x_2003_);
lean_dec_ref(v_x_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6_spec__9_spec__11___redArg(v_x_2006_, v_x_2007_, v_x_2008_, v_x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_2011_, lean_object* v_00_u03b2_2012_, lean_object* v_00_u03c3_2013_, lean_object* v_f_2014_, lean_object* v_as_2015_, size_t v_i_2016_, size_t v_stop_2017_, lean_object* v_b_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_2014_, v_as_2015_, v_i_2016_, v_stop_2017_, v_b_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_00_u03b2_2021_, lean_object* v_00_u03c3_2022_, lean_object* v_f_2023_, lean_object* v_as_2024_, lean_object* v_i_2025_, lean_object* v_stop_2026_, lean_object* v_b_2027_){
_start:
{
size_t v_i_boxed_2028_; size_t v_stop_boxed_2029_; lean_object* v_res_2030_; 
v_i_boxed_2028_ = lean_unbox_usize(v_i_2025_);
lean_dec(v_i_2025_);
v_stop_boxed_2029_ = lean_unbox_usize(v_stop_2026_);
lean_dec(v_stop_2026_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03b1_2020_, v_00_u03b2_2021_, v_00_u03c3_2022_, v_f_2023_, v_as_2024_, v_i_boxed_2028_, v_stop_boxed_2029_, v_b_2027_);
lean_dec_ref(v_as_2024_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03c3_2031_, lean_object* v_00_u03b1_2032_, lean_object* v_00_u03b2_2033_, lean_object* v_f_2034_, lean_object* v_keys_2035_, lean_object* v_vals_2036_, lean_object* v_heq_2037_, lean_object* v_i_2038_, lean_object* v_acc_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___redArg(v_f_2034_, v_keys_2035_, v_vals_2036_, v_i_2038_, v_acc_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03c3_2041_, lean_object* v_00_u03b1_2042_, lean_object* v_00_u03b2_2043_, lean_object* v_f_2044_, lean_object* v_keys_2045_, lean_object* v_vals_2046_, lean_object* v_heq_2047_, lean_object* v_i_2048_, lean_object* v_acc_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__11(v_00_u03c3_2041_, v_00_u03b1_2042_, v_00_u03b2_2043_, v_f_2044_, v_keys_2045_, v_vals_2046_, v_heq_2047_, v_i_2048_, v_acc_2049_);
lean_dec_ref(v_vals_2046_);
lean_dec_ref(v_keys_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary___lam__0(lean_object* v_addEntryFn_2051_, lean_object* v___x_2052_, lean_object* v_s_2053_){
_start:
{
lean_object* v_importedEntries_2054_; lean_object* v_state_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2063_; 
v_importedEntries_2054_ = lean_ctor_get(v_s_2053_, 0);
v_state_2055_ = lean_ctor_get(v_s_2053_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_s_2053_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2057_ = v_s_2053_;
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_state_2055_);
lean_inc(v_importedEntries_2054_);
lean_dec(v_s_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_state_2059_; lean_object* v___x_2061_; 
v_state_2059_ = lean_apply_2(v_addEntryFn_2051_, v_state_2055_, v___x_2052_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v_state_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_importedEntries_2054_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_state_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2064_, lean_object* v_fid_2065_, lean_object* v_v_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v_toEnvExtension_2068_; lean_object* v_addEntryFn_2069_; lean_object* v_asyncMode_2070_; uint8_t v_logWrites_2071_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2067_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2068_ = lean_ctor_get(v___x_2067_, 0);
v_addEntryFn_2069_ = lean_ctor_get(v___x_2067_, 3);
v_asyncMode_2070_ = lean_ctor_get(v_toEnvExtension_2068_, 2);
v_logWrites_2071_ = lean_ctor_get_uint8(v_toEnvExtension_2068_, sizeof(void*)*6);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v_fid_2065_);
lean_ctor_set(v___x_2072_, 1, v_v_2066_);
lean_inc(v_addEntryFn_2069_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary___lam__0), 3, 2);
lean_closure_set(v___f_2073_, 0, v_addEntryFn_2069_);
lean_closure_set(v___f_2073_, 1, v___x_2072_);
v___x_2074_ = lean_box(0);
v___x_2075_ = 1;
if (v_logWrites_2071_ == 0)
{
lean_object* v___x_2076_; 
lean_inc_ref(v_toEnvExtension_2068_);
v___x_2076_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2068_, v_env_2064_, v___f_2073_, v_asyncMode_2070_, v___x_2074_, v___x_2075_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_inc_ref_n(v_toEnvExtension_2068_, 2);
v___x_2077_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2068_, v_env_2064_);
lean_dec_ref(v_env_2064_);
v___x_2078_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2068_, v___x_2077_, v___f_2073_, v_asyncMode_2070_, v___x_2074_, v___x_2075_);
return v___x_2078_;
}
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
size_t v_x_402__boxed_2124_; lean_object* v_res_2125_; 
v_x_402__boxed_2124_ = lean_unbox_usize(v_x_2122_);
lean_dec(v_x_2122_);
v_res_2125_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2121_, v_x_402__boxed_2124_, v_x_2123_);
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
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0(void){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0);
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___x_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2168_, lean_object* v_fid_2169_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2180_; 
v___x_2170_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1);
v___x_2171_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2180_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2168_, v_fid_2169_);
if (lean_obj_tag(v___x_2180_) == 0)
{
goto v___jp_2172_;
}
else
{
lean_object* v_val_2181_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_val_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2203_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_2170_, v___x_2171_, v_env_2168_, v_val_2181_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_array_get_size(v___x_2203_);
v___x_2206_ = lean_nat_dec_lt(v___x_2204_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_dec_ref(v___x_2203_);
goto v___jp_2182_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_sub(v___x_2205_, v___x_2207_);
v___x_2209_ = lean_nat_dec_le(v___x_2204_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_dec(v___x_2208_);
lean_dec_ref(v___x_2203_);
goto v___jp_2182_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_box(0);
lean_inc(v_fid_2169_);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_fid_2169_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2203_, v___x_2211_, v___x_2204_, v___x_2208_);
lean_dec_ref_known(v___x_2211_, 2);
lean_dec_ref(v___x_2203_);
if (lean_obj_tag(v___x_2212_) == 0)
{
goto v___jp_2182_;
}
else
{
lean_object* v_val_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_val_2181_);
lean_dec(v_fid_2169_);
lean_dec_ref(v_env_2168_);
v_val_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_val_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v_snd_2217_; lean_object* v___x_2219_; 
v_snd_2217_ = lean_ctor_get(v_val_2213_, 1);
lean_inc(v_snd_2217_);
lean_dec(v_val_2213_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v_snd_2217_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_snd_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
v___jp_2182_:
{
uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2183_ = 0;
v___x_2184_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2170_, v___x_2171_, v_env_2168_, v_val_2181_, v___x_2183_);
lean_dec(v_val_2181_);
v___x_2185_ = lean_unsigned_to_nat(0u);
v___x_2186_ = lean_array_get_size(v___x_2184_);
v___x_2187_ = lean_nat_dec_lt(v___x_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_dec_ref(v___x_2184_);
goto v___jp_2172_;
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_sub(v___x_2186_, v___x_2188_);
v___x_2190_ = lean_nat_dec_le(v___x_2185_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_dec(v___x_2189_);
lean_dec_ref(v___x_2184_);
goto v___jp_2172_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_box(0);
lean_inc(v_fid_2169_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_fid_2169_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2184_, v___x_2192_, v___x_2185_, v___x_2189_);
lean_dec_ref_known(v___x_2192_, 2);
lean_dec_ref(v___x_2184_);
if (lean_obj_tag(v___x_2193_) == 0)
{
goto v___jp_2172_;
}
else
{
lean_object* v_val_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_fid_2169_);
lean_dec_ref(v_env_2168_);
v_val_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_val_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_snd_2198_; lean_object* v___x_2200_; 
v_snd_2198_ = lean_ctor_get(v_val_2194_, 1);
lean_inc(v_snd_2198_);
lean_dec(v_val_2194_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_snd_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_snd_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
}
v___jp_2172_:
{
lean_object* v_toEnvExtension_2173_; lean_object* v_asyncMode_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; lean_object* v_snd_2178_; lean_object* v___x_2179_; 
v_toEnvExtension_2173_ = lean_ctor_get(v___x_2171_, 0);
v_asyncMode_2174_ = lean_ctor_get(v_toEnvExtension_2173_, 2);
v___x_2175_ = lean_box(0);
v___x_2176_ = 0;
v___x_2177_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2170_, v___x_2171_, v_env_2168_, v_asyncMode_2174_, v___x_2175_, v___x_2176_);
v_snd_2178_ = lean_ctor_get(v___x_2177_, 1);
lean_inc(v_snd_2178_);
lean_dec(v___x_2177_);
v___x_2179_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2178_, v_fid_2169_);
lean_dec(v_fid_2169_);
lean_dec(v_snd_2178_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2223_, v_x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2226_, v_x_2227_, v_x_2228_);
lean_dec(v_x_2228_);
lean_dec_ref(v_x_2227_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2230_, lean_object* v_k_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2230_, v_k_2231_, v_x_2232_, v_x_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2236_, lean_object* v_k_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2236_, v_k_2237_, v_x_2238_, v_x_2239_, v_x_2240_);
lean_dec_ref(v_k_2237_);
lean_dec_ref(v_as_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2242_, lean_object* v_x_2243_, size_t v_x_2244_, lean_object* v_x_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2243_, v_x_2244_, v_x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2247_, lean_object* v_x_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_){
_start:
{
size_t v_x_628__boxed_2251_; lean_object* v_res_2252_; 
v_x_628__boxed_2251_ = lean_unbox_usize(v_x_2249_);
lean_dec(v_x_2249_);
v_res_2252_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2247_, v_x_2248_, v_x_628__boxed_2251_, v_x_2250_);
lean_dec(v_x_2250_);
lean_dec_ref(v_x_2248_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2253_, lean_object* v_keys_2254_, lean_object* v_vals_2255_, lean_object* v_heq_2256_, lean_object* v_i_2257_, lean_object* v_k_2258_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2254_, v_vals_2255_, v_i_2257_, v_k_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2260_, lean_object* v_keys_2261_, lean_object* v_vals_2262_, lean_object* v_heq_2263_, lean_object* v_i_2264_, lean_object* v_k_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2260_, v_keys_2261_, v_vals_2262_, v_heq_2263_, v_i_2264_, v_k_2265_);
lean_dec(v_k_2265_);
lean_dec_ref(v_vals_2262_);
lean_dec_ref(v_keys_2261_);
return v_res_2266_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0(void){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v_assignments_2273_; lean_object* v_currFnIdx_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2271_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0);
v___x_2272_ = lean_st_ref_get(v_a_2269_);
v_assignments_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc_ref(v_assignments_2273_);
lean_dec(v___x_2272_);
v_currFnIdx_2274_ = lean_ctor_get(v_a_2268_, 1);
v___x_2275_ = lean_array_get(v___x_2271_, v_assignments_2273_, v_currFnIdx_2274_);
lean_dec_ref(v_assignments_2273_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2281_, v_a_2282_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v_funVals_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2300_ = lean_box(0);
v___x_2301_ = lean_st_ref_get(v_a_2298_);
v_funVals_2302_ = lean_ctor_get(v___x_2301_, 1);
lean_inc_ref(v_funVals_2302_);
lean_dec(v___x_2301_);
v___x_2303_ = lean_array_get(v___x_2300_, v_funVals_2302_, v_funIdx_2297_);
lean_dec_ref(v_funVals_2302_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec(v_funIdx_2305_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2309_, v_a_2311_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_funIdx_2318_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2327_, lean_object* v_as_2328_, lean_object* v_j_2329_){
_start:
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_array_get_size(v_as_2328_);
v___x_2331_ = lean_nat_dec_lt(v_j_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_dec(v_j_2329_);
v___x_2332_ = lean_box(0);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; lean_object* v_toSignature_2334_; lean_object* v_name_2335_; uint8_t v___x_2336_; 
v___x_2333_ = lean_array_fget_borrowed(v_as_2328_, v_j_2329_);
v_toSignature_2334_ = lean_ctor_get(v___x_2333_, 0);
v_name_2335_ = lean_ctor_get(v_toSignature_2334_, 0);
v___x_2336_ = lean_name_eq(v_name_2335_, v_declName_2327_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_unsigned_to_nat(1u);
v___x_2338_ = lean_nat_add(v_j_2329_, v___x_2337_);
lean_dec(v_j_2329_);
v_j_2329_ = v___x_2338_;
goto _start;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2340_, 0, v_j_2329_);
return v___x_2340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2341_, lean_object* v_as_2342_, lean_object* v_j_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2341_, v_as_2342_, v_j_2343_);
lean_dec_ref(v_as_2342_);
lean_dec(v_declName_2341_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_decls_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_decls_2349_ = lean_ctor_get(v_a_2346_, 0);
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2345_, v_decls_2349_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
else
{
lean_object* v_val_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2370_; 
v_val_2354_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2356_ = v___x_2351_;
v_isShared_2357_ = v_isSharedCheck_2370_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_val_2354_);
lean_dec(v___x_2351_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2370_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2369_; 
v___x_2358_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2354_, v_a_2347_);
lean_dec(v_val_2354_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2369_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2369_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v_a_2359_);
v___x_2364_ = v___x_2356_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2364_);
v___x_2366_ = v___x_2361_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2371_, v_a_2372_, v_a_2373_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_declName_2371_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2376_, v_a_2377_, v_a_2378_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_declName_2385_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_currFnIdx_2398_; lean_object* v___x_2399_; lean_object* v_assignments_2400_; lean_object* v_funVals_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2419_; 
v_currFnIdx_2398_ = lean_ctor_get(v_a_2395_, 1);
v___x_2399_ = lean_st_ref_take(v_a_2396_);
v_assignments_2400_ = lean_ctor_get(v___x_2399_, 0);
v_funVals_2401_ = lean_ctor_get(v___x_2399_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2403_ = v___x_2399_;
v_isShared_2404_ = v_isSharedCheck_2419_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_funVals_2401_);
lean_inc(v_assignments_2400_);
lean_dec(v___x_2399_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2419_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___y_2407_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2405_ = lean_box(0);
v___x_2413_ = lean_array_get_size(v_assignments_2400_);
v___x_2414_ = lean_nat_dec_lt(v_currFnIdx_2398_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_dec_ref(v_f_2394_);
v___y_2407_ = v_assignments_2400_;
goto v___jp_2406_;
}
else
{
lean_object* v_v_2415_; lean_object* v_xs_x27_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_v_2415_ = lean_array_fget(v_assignments_2400_, v_currFnIdx_2398_);
v_xs_x27_2416_ = lean_array_fset(v_assignments_2400_, v_currFnIdx_2398_, v___x_2405_);
v___x_2417_ = lean_apply_1(v_f_2394_, v_v_2415_);
v___x_2418_ = lean_array_fset(v_xs_x27_2416_, v_currFnIdx_2398_, v___x_2417_);
v___y_2407_ = v___x_2418_;
goto v___jp_2406_;
}
v___jp_2406_:
{
lean_object* v___x_2409_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___y_2407_);
v___x_2409_ = v___x_2403_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___y_2407_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_funVals_2401_);
v___x_2409_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_st_ref_put(v_a_2396_, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2405_);
return v___x_2411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2425_, v_a_2426_, v_a_2427_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2443_, lean_object* v_fallback_2444_, lean_object* v_x_2445_){
_start:
{
if (lean_obj_tag(v_x_2445_) == 0)
{
lean_inc(v_fallback_2444_);
return v_fallback_2444_;
}
else
{
lean_object* v_key_2446_; lean_object* v_value_2447_; lean_object* v_tail_2448_; uint8_t v___x_2449_; 
v_key_2446_ = lean_ctor_get(v_x_2445_, 0);
v_value_2447_ = lean_ctor_get(v_x_2445_, 1);
v_tail_2448_ = lean_ctor_get(v_x_2445_, 2);
v___x_2449_ = l_Lean_instBEqFVarId_beq(v_key_2446_, v_a_2443_);
if (v___x_2449_ == 0)
{
v_x_2445_ = v_tail_2448_;
goto _start;
}
else
{
lean_inc(v_value_2447_);
return v_value_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2451_, lean_object* v_fallback_2452_, lean_object* v_x_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2451_, v_fallback_2452_, v_x_2453_);
lean_dec(v_x_2453_);
lean_dec(v_fallback_2452_);
lean_dec(v_a_2451_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2455_, lean_object* v_a_2456_, lean_object* v_fallback_2457_){
_start:
{
lean_object* v_buckets_2458_; lean_object* v___x_2459_; uint64_t v___x_2460_; uint64_t v___x_2461_; uint64_t v___x_2462_; uint64_t v_fold_2463_; uint64_t v___x_2464_; uint64_t v___x_2465_; uint64_t v___x_2466_; size_t v___x_2467_; size_t v___x_2468_; size_t v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_buckets_2458_ = lean_ctor_get(v_m_2455_, 1);
v___x_2459_ = lean_array_get_size(v_buckets_2458_);
v___x_2460_ = l_Lean_instHashableFVarId_hash(v_a_2456_);
v___x_2461_ = 32ULL;
v___x_2462_ = lean_uint64_shift_right(v___x_2460_, v___x_2461_);
v_fold_2463_ = lean_uint64_xor(v___x_2460_, v___x_2462_);
v___x_2464_ = 16ULL;
v___x_2465_ = lean_uint64_shift_right(v_fold_2463_, v___x_2464_);
v___x_2466_ = lean_uint64_xor(v_fold_2463_, v___x_2465_);
v___x_2467_ = lean_uint64_to_usize(v___x_2466_);
v___x_2468_ = lean_usize_of_nat(v___x_2459_);
v___x_2469_ = ((size_t)1ULL);
v___x_2470_ = lean_usize_sub(v___x_2468_, v___x_2469_);
v___x_2471_ = lean_usize_land(v___x_2467_, v___x_2470_);
v___x_2472_ = lean_array_uget_borrowed(v_buckets_2458_, v___x_2471_);
v___x_2473_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2456_, v_fallback_2457_, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2474_, lean_object* v_a_2475_, lean_object* v_fallback_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2474_, v_a_2475_, v_fallback_2476_);
lean_dec(v_fallback_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_m_2474_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v___x_2482_; lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2492_; 
v___x_2482_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2479_, v_a_2480_);
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2487_ = lean_box(0);
v___x_2488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2483_, v_var_2478_, v___x_2487_);
lean_dec(v_a_2483_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2488_);
v___x_2490_ = v___x_2485_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_var_2493_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2498_, v_a_2499_, v_a_2500_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_var_2507_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2516_, lean_object* v_m_2517_, lean_object* v_a_2518_, lean_object* v_fallback_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2517_, v_a_2518_, v_fallback_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2521_, lean_object* v_m_2522_, lean_object* v_a_2523_, lean_object* v_fallback_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2521_, v_m_2522_, v_a_2523_, v_fallback_2524_);
lean_dec(v_fallback_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_m_2522_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2526_, lean_object* v_a_2527_, lean_object* v_fallback_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2527_, v_fallback_2528_, v_x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2531_, lean_object* v_a_2532_, lean_object* v_fallback_2533_, lean_object* v_x_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2531_, v_a_2532_, v_fallback_2533_, v_x_2534_);
lean_dec(v_x_2534_);
lean_dec(v_fallback_2533_);
lean_dec(v_a_2532_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
if (lean_obj_tag(v_arg_2536_) == 1)
{
lean_object* v_fvarId_2540_; lean_object* v___x_2541_; 
v_fvarId_2540_ = lean_ctor_get(v_arg_2536_, 0);
v___x_2541_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2540_, v_a_2537_, v_a_2538_);
return v___x_2541_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_box(1);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_arg_2544_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2549_, v_a_2550_, v_a_2551_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_arg_2558_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2567_, lean_object* v_b_2568_, lean_object* v_x_2569_){
_start:
{
if (lean_obj_tag(v_x_2569_) == 0)
{
lean_dec(v_b_2568_);
lean_dec(v_a_2567_);
return v_x_2569_;
}
else
{
lean_object* v_key_2570_; lean_object* v_value_2571_; lean_object* v_tail_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2584_; 
v_key_2570_ = lean_ctor_get(v_x_2569_, 0);
v_value_2571_ = lean_ctor_get(v_x_2569_, 1);
v_tail_2572_ = lean_ctor_get(v_x_2569_, 2);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2569_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2574_ = v_x_2569_;
v_isShared_2575_ = v_isSharedCheck_2584_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_tail_2572_);
lean_inc(v_value_2571_);
lean_inc(v_key_2570_);
lean_dec(v_x_2569_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2584_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
uint8_t v___x_2576_; 
v___x_2576_ = l_Lean_instBEqFVarId_beq(v_key_2570_, v_a_2567_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2567_, v_b_2568_, v_tail_2572_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 2, v___x_2577_);
v___x_2579_ = v___x_2574_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_key_2570_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_value_2571_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
else
{
lean_object* v___x_2582_; 
lean_dec(v_value_2571_);
lean_dec(v_key_2570_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v_b_2568_);
lean_ctor_set(v___x_2574_, 0, v_a_2567_);
v___x_2582_ = v___x_2574_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2567_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_b_2568_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_tail_2572_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
if (lean_obj_tag(v_x_2586_) == 0)
{
return v_x_2585_;
}
else
{
lean_object* v_key_2587_; lean_object* v_value_2588_; lean_object* v_tail_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2612_; 
v_key_2587_ = lean_ctor_get(v_x_2586_, 0);
v_value_2588_ = lean_ctor_get(v_x_2586_, 1);
v_tail_2589_ = lean_ctor_get(v_x_2586_, 2);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_x_2586_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2591_ = v_x_2586_;
v_isShared_2592_ = v_isSharedCheck_2612_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_tail_2589_);
lean_inc(v_value_2588_);
lean_inc(v_key_2587_);
lean_dec(v_x_2586_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2612_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; uint64_t v___x_2594_; uint64_t v___x_2595_; uint64_t v___x_2596_; uint64_t v_fold_2597_; uint64_t v___x_2598_; uint64_t v___x_2599_; uint64_t v___x_2600_; size_t v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2593_ = lean_array_get_size(v_x_2585_);
v___x_2594_ = l_Lean_instHashableFVarId_hash(v_key_2587_);
v___x_2595_ = 32ULL;
v___x_2596_ = lean_uint64_shift_right(v___x_2594_, v___x_2595_);
v_fold_2597_ = lean_uint64_xor(v___x_2594_, v___x_2596_);
v___x_2598_ = 16ULL;
v___x_2599_ = lean_uint64_shift_right(v_fold_2597_, v___x_2598_);
v___x_2600_ = lean_uint64_xor(v_fold_2597_, v___x_2599_);
v___x_2601_ = lean_uint64_to_usize(v___x_2600_);
v___x_2602_ = lean_usize_of_nat(v___x_2593_);
v___x_2603_ = ((size_t)1ULL);
v___x_2604_ = lean_usize_sub(v___x_2602_, v___x_2603_);
v___x_2605_ = lean_usize_land(v___x_2601_, v___x_2604_);
v___x_2606_ = lean_array_uget_borrowed(v_x_2585_, v___x_2605_);
lean_inc(v___x_2606_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 2, v___x_2606_);
v___x_2608_ = v___x_2591_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_key_2587_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_value_2588_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_array_uset(v_x_2585_, v___x_2605_, v___x_2608_);
v_x_2585_ = v___x_2609_;
v_x_2586_ = v_tail_2589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2613_, lean_object* v_source_2614_, lean_object* v_target_2615_){
_start:
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = lean_array_get_size(v_source_2614_);
v___x_2617_ = lean_nat_dec_lt(v_i_2613_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_dec_ref(v_source_2614_);
lean_dec(v_i_2613_);
return v_target_2615_;
}
else
{
lean_object* v_es_2618_; lean_object* v___x_2619_; lean_object* v_source_2620_; lean_object* v_target_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_es_2618_ = lean_array_fget(v_source_2614_, v_i_2613_);
v___x_2619_ = lean_box(0);
v_source_2620_ = lean_array_fset(v_source_2614_, v_i_2613_, v___x_2619_);
v_target_2621_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2615_, v_es_2618_);
v___x_2622_ = lean_unsigned_to_nat(1u);
v___x_2623_ = lean_nat_add(v_i_2613_, v___x_2622_);
lean_dec(v_i_2613_);
v_i_2613_ = v___x_2623_;
v_source_2614_ = v_source_2620_;
v_target_2615_ = v_target_2621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_nbuckets_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2626_ = lean_array_get_size(v_data_2625_);
v___x_2627_ = lean_unsigned_to_nat(2u);
v_nbuckets_2628_ = lean_nat_mul(v___x_2626_, v___x_2627_);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_box(0);
v___x_2631_ = lean_mk_array(v_nbuckets_2628_, v___x_2630_);
v___x_2632_ = lean_array_propagate_mark(v_data_2625_, v___x_2631_);
v___x_2633_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2629_, v_data_2625_, v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2634_, lean_object* v_x_2635_){
_start:
{
if (lean_obj_tag(v_x_2635_) == 0)
{
uint8_t v___x_2636_; 
v___x_2636_ = 0;
return v___x_2636_;
}
else
{
lean_object* v_key_2637_; lean_object* v_tail_2638_; uint8_t v___x_2639_; 
v_key_2637_ = lean_ctor_get(v_x_2635_, 0);
v_tail_2638_ = lean_ctor_get(v_x_2635_, 2);
v___x_2639_ = l_Lean_instBEqFVarId_beq(v_key_2637_, v_a_2634_);
if (v___x_2639_ == 0)
{
v_x_2635_ = v_tail_2638_;
goto _start;
}
else
{
return v___x_2639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2641_, lean_object* v_x_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2641_, v_x_2642_);
lean_dec(v_x_2642_);
lean_dec(v_a_2641_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2645_, lean_object* v_a_2646_, lean_object* v_b_2647_){
_start:
{
lean_object* v_size_2648_; lean_object* v_buckets_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2692_; 
v_size_2648_ = lean_ctor_get(v_m_2645_, 0);
v_buckets_2649_ = lean_ctor_get(v_m_2645_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_m_2645_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2651_ = v_m_2645_;
v_isShared_2652_ = v_isSharedCheck_2692_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_buckets_2649_);
lean_inc(v_size_2648_);
lean_dec(v_m_2645_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2692_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; uint64_t v___x_2654_; uint64_t v___x_2655_; uint64_t v___x_2656_; uint64_t v_fold_2657_; uint64_t v___x_2658_; uint64_t v___x_2659_; uint64_t v___x_2660_; size_t v___x_2661_; size_t v___x_2662_; size_t v___x_2663_; size_t v___x_2664_; size_t v___x_2665_; lean_object* v_bkt_2666_; uint8_t v___x_2667_; 
v___x_2653_ = lean_array_get_size(v_buckets_2649_);
v___x_2654_ = l_Lean_instHashableFVarId_hash(v_a_2646_);
v___x_2655_ = 32ULL;
v___x_2656_ = lean_uint64_shift_right(v___x_2654_, v___x_2655_);
v_fold_2657_ = lean_uint64_xor(v___x_2654_, v___x_2656_);
v___x_2658_ = 16ULL;
v___x_2659_ = lean_uint64_shift_right(v_fold_2657_, v___x_2658_);
v___x_2660_ = lean_uint64_xor(v_fold_2657_, v___x_2659_);
v___x_2661_ = lean_uint64_to_usize(v___x_2660_);
v___x_2662_ = lean_usize_of_nat(v___x_2653_);
v___x_2663_ = ((size_t)1ULL);
v___x_2664_ = lean_usize_sub(v___x_2662_, v___x_2663_);
v___x_2665_ = lean_usize_land(v___x_2661_, v___x_2664_);
v_bkt_2666_ = lean_array_uget_borrowed(v_buckets_2649_, v___x_2665_);
v___x_2667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2646_, v_bkt_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v_size_x27_2669_; lean_object* v___x_2670_; lean_object* v_buckets_x27_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2668_ = lean_unsigned_to_nat(1u);
v_size_x27_2669_ = lean_nat_add(v_size_2648_, v___x_2668_);
lean_dec(v_size_2648_);
lean_inc(v_bkt_2666_);
v___x_2670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2670_, 0, v_a_2646_);
lean_ctor_set(v___x_2670_, 1, v_b_2647_);
lean_ctor_set(v___x_2670_, 2, v_bkt_2666_);
v_buckets_x27_2671_ = lean_array_uset(v_buckets_2649_, v___x_2665_, v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(4u);
v___x_2673_ = lean_nat_mul(v_size_x27_2669_, v___x_2672_);
v___x_2674_ = lean_unsigned_to_nat(3u);
v___x_2675_ = lean_nat_div(v___x_2673_, v___x_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_array_get_size(v_buckets_x27_2671_);
v___x_2677_ = lean_nat_dec_le(v___x_2675_, v___x_2676_);
lean_dec(v___x_2675_);
if (v___x_2677_ == 0)
{
lean_object* v_val_2678_; lean_object* v___x_2680_; 
v_val_2678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2671_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v_val_2678_);
lean_ctor_set(v___x_2651_, 0, v_size_x27_2669_);
v___x_2680_ = v___x_2651_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_size_x27_2669_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_val_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
else
{
lean_object* v___x_2683_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v_buckets_x27_2671_);
lean_ctor_set(v___x_2651_, 0, v_size_x27_2669_);
v___x_2683_ = v___x_2651_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_size_x27_2669_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_buckets_x27_2671_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_object* v___x_2685_; lean_object* v_buckets_x27_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_inc(v_bkt_2666_);
v___x_2685_ = lean_box(0);
v_buckets_x27_2686_ = lean_array_uset(v_buckets_2649_, v___x_2665_, v___x_2685_);
v___x_2687_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2646_, v_b_2647_, v_bkt_2666_);
v___x_2688_ = lean_array_uset(v_buckets_x27_2686_, v___x_2665_, v___x_2687_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2688_);
v___x_2690_ = v___x_2651_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_size_2648_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2693_, lean_object* v___x_2694_, lean_object* v_x_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2695_, v_var_2693_, v___x_2694_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2697_, lean_object* v_newVal_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v_env_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_st_ref_get(v_a_2701_);
v_env_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc_ref(v_env_2704_);
lean_dec(v___x_2703_);
v___x_2705_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2697_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2704_, v_a_2706_, v_newVal_2698_);
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2708_, 0, v_var_2697_);
lean_closure_set(v___f_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2708_, v_a_2699_, v_a_2700_);
return v___x_2709_;
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v_env_2704_);
lean_dec(v_newVal_2698_);
lean_dec(v_var_2697_);
v_a_2710_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2705_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2705_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2718_, lean_object* v_newVal_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2718_, v_newVal_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2725_, lean_object* v_newVal_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2725_, v_newVal_2726_, v_a_2727_, v_a_2728_, v_a_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2735_, lean_object* v_newVal_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2735_, v_newVal_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2745_, lean_object* v_m_2746_, lean_object* v_a_2747_, lean_object* v_b_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2746_, v_a_2747_, v_b_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2750_, lean_object* v_a_2751_, lean_object* v_x_2752_){
_start:
{
uint8_t v___x_2753_; 
v___x_2753_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2751_, v_x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2754_, lean_object* v_a_2755_, lean_object* v_x_2756_){
_start:
{
uint8_t v_res_2757_; lean_object* v_r_2758_; 
v_res_2757_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2754_, v_a_2755_, v_x_2756_);
lean_dec(v_x_2756_);
lean_dec(v_a_2755_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2759_, lean_object* v_data_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2762_, lean_object* v_a_2763_, lean_object* v_b_2764_, lean_object* v_x_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2763_, v_b_2764_, v_x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2767_, lean_object* v_i_2768_, lean_object* v_source_2769_, lean_object* v_target_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2768_, v_source_2769_, v_target_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2772_, lean_object* v_x_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2773_, v_x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2776_, lean_object* v_x_2777_){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_box(0);
v___x_2779_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2777_, v_var_2776_, v___x_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___f_2784_; lean_object* v___x_2785_; 
v___f_2784_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2784_, 0, v_var_2780_);
v___x_2785_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2784_, v_a_2781_, v_a_2782_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2791_, v_a_2792_, v_a_2793_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v_env_2815_; lean_object* v_currFnIdx_2816_; lean_object* v___x_2817_; lean_object* v_fst_2819_; lean_object* v_snd_2820_; lean_object* v_assignments_2823_; lean_object* v_funVals_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2814_ = lean_st_ref_get(v_a_2812_);
v_env_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc_ref(v_env_2815_);
lean_dec(v___x_2814_);
v_currFnIdx_2816_ = lean_ctor_get(v_a_2810_, 1);
v___x_2817_ = lean_st_ref_take(v_a_2811_);
v_assignments_2823_ = lean_ctor_get(v___x_2817_, 0);
v_funVals_2824_ = lean_ctor_get(v___x_2817_, 1);
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_array_get_size(v_funVals_2824_);
v___x_2827_ = lean_nat_dec_lt(v_currFnIdx_2816_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_dec_ref(v_env_2815_);
lean_dec(v_v_2809_);
v_fst_2819_ = v___x_2825_;
v_snd_2820_ = v___x_2817_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2838_; 
lean_inc_ref(v_funVals_2824_);
lean_inc_ref(v_assignments_2823_);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; lean_object* v_unused_2840_; 
v_unused_2839_ = lean_ctor_get(v___x_2817_, 1);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v___x_2817_, 0);
lean_dec(v_unused_2840_);
v___x_2829_ = v___x_2817_;
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v___x_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_v_2831_; lean_object* v_xs_x27_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v_v_2831_ = lean_array_fget(v_funVals_2824_, v_currFnIdx_2816_);
v_xs_x27_2832_ = lean_array_fset(v_funVals_2824_, v_currFnIdx_2816_, v___x_2825_);
v___x_2833_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2815_, v_v_2809_, v_v_2831_);
v___x_2834_ = lean_array_fset(v_xs_x27_2832_, v_currFnIdx_2816_, v___x_2833_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v___x_2834_);
v___x_2836_ = v___x_2829_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_assignments_2823_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
v_fst_2819_ = v___x_2825_;
v_snd_2820_ = v___x_2836_;
goto v___jp_2818_;
}
}
}
v___jp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = lean_st_ref_put(v_a_2811_, v_snd_2820_);
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v_fst_2819_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
lean_dec(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2847_, v_a_2848_, v_a_2849_, v_a_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2865_, uint8_t v_b_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_array_2871_; lean_object* v_start_2872_; lean_object* v_stop_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2910_; 
v_array_2871_ = lean_ctor_get(v_a_2865_, 0);
v_start_2872_ = lean_ctor_get(v_a_2865_, 1);
v_stop_2873_ = lean_ctor_get(v_a_2865_, 2);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_a_2865_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2875_ = v_a_2865_;
v_isShared_2876_ = v_isSharedCheck_2910_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_stop_2873_);
lean_inc(v_start_2872_);
lean_inc(v_array_2871_);
lean_dec(v_a_2865_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2910_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_nat_dec_lt(v_start_2872_, v_stop_2873_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_del_object(v___x_2875_);
lean_dec(v_stop_2873_);
lean_dec(v_start_2872_);
lean_dec_ref(v_array_2871_);
v___x_2878_ = lean_box(v_b_2866_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; lean_object* v_fvarId_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2880_ = lean_array_fget_borrowed(v_array_2871_, v_start_2872_);
v_fvarId_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_fvarId_2881_);
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = lean_nat_add(v_start_2872_, v___x_2882_);
lean_dec(v_start_2872_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___x_2883_);
v___x_2885_ = v___x_2875_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_array_2871_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_stop_2873_);
v___x_2885_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2881_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___x_2888_ = lean_box(0);
v___x_2889_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2887_, v___x_2888_);
lean_dec(v_a_2887_);
v___x_2890_ = lean_box(1);
v___x_2891_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2881_, v___x_2890_, v___y_2867_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_dec_ref_known(v___x_2891_, 1);
v_a_2865_ = v___x_2885_;
v_b_2866_ = v___x_2889_;
goto _start;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v___x_2885_);
v_a_2893_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2891_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2891_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___x_2885_);
lean_dec(v_fvarId_2881_);
v_a_2901_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2886_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2886_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2911_, lean_object* v_b_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v_b_boxed_2917_; lean_object* v_res_2918_; 
v_b_boxed_2917_ = lean_unbox(v_b_2912_);
v_res_2918_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2911_, v_b_boxed_2917_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2919_, lean_object* v___x_2920_, lean_object* v_x_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2921_, v_fvarId_2919_, v___x_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2923_, lean_object* v_as_2924_, size_t v_sz_2925_, size_t v_i_2926_, lean_object* v_b_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_a_2932_; uint8_t v___x_2936_; 
v___x_2936_ = lean_usize_dec_lt(v_i_2926_, v_sz_2925_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; 
lean_dec_ref(v___x_2923_);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_b_2927_);
return v___x_2937_;
}
else
{
lean_object* v_snd_2938_; lean_object* v_fst_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3005_; 
v_snd_2938_ = lean_ctor_get(v_b_2927_, 1);
v_fst_2939_ = lean_ctor_get(v_b_2927_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_b_2927_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2941_ = v_b_2927_;
v_isShared_2942_ = v_isSharedCheck_3005_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_snd_2938_);
lean_inc(v_fst_2939_);
lean_dec(v_b_2927_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3005_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_array_2943_; lean_object* v_start_2944_; lean_object* v_stop_2945_; uint8_t v___x_2946_; 
v_array_2943_ = lean_ctor_get(v_snd_2938_, 0);
v_start_2944_ = lean_ctor_get(v_snd_2938_, 1);
v_stop_2945_ = lean_ctor_get(v_snd_2938_, 2);
v___x_2946_ = lean_nat_dec_lt(v_start_2944_, v_stop_2945_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref(v___x_2923_);
if (v_isShared_2942_ == 0)
{
v___x_2948_ = v___x_2941_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_snd_2938_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
}
else
{
lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3001_; 
lean_inc(v_stop_2945_);
lean_inc(v_start_2944_);
lean_inc_ref(v_array_2943_);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_snd_2938_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; lean_object* v_unused_3003_; lean_object* v_unused_3004_; 
v_unused_3002_ = lean_ctor_get(v_snd_2938_, 2);
lean_dec(v_unused_3002_);
v_unused_3003_ = lean_ctor_get(v_snd_2938_, 1);
lean_dec(v_unused_3003_);
v_unused_3004_ = lean_ctor_get(v_snd_2938_, 0);
lean_dec(v_unused_3004_);
v___x_2952_ = v_snd_2938_;
v_isShared_2953_ = v_isSharedCheck_3001_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v_snd_2938_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3001_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_a_2954_; lean_object* v_fvarId_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v_a_2954_ = lean_array_uget_borrowed(v_as_2924_, v_i_2926_);
v_fvarId_2955_ = lean_ctor_get(v_a_2954_, 0);
v___x_2956_ = lean_array_fget(v_array_2943_, v_start_2944_);
v___x_2957_ = lean_unsigned_to_nat(1u);
v___x_2958_ = lean_nat_add(v_start_2944_, v___x_2957_);
lean_dec(v_start_2944_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_2958_);
v___x_2960_ = v___x_2952_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_array_2943_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v_stop_2945_);
v___x_2960_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2955_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v___x_2963_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2956_, v___y_2928_, v___y_2929_);
lean_dec(v___x_2956_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
lean_inc(v_a_2962_);
lean_inc_ref(v___x_2923_);
v___x_2965_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2923_, v_a_2962_, v_a_2964_);
v___x_2966_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2965_, v_a_2962_);
lean_dec(v_a_2962_);
if (v___x_2966_ == 0)
{
lean_object* v___f_2967_; lean_object* v___x_2968_; 
lean_dec(v_fst_2939_);
lean_inc(v_fvarId_2955_);
v___f_2967_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2967_, 0, v_fvarId_2955_);
lean_closure_set(v___f_2967_, 1, v___x_2965_);
v___x_2968_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2967_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec_ref_known(v___x_2968_, 1);
v___x_2969_ = lean_box(v___x_2946_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2960_);
lean_ctor_set(v___x_2941_, 0, v___x_2969_);
v___x_2971_ = v___x_2941_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___x_2960_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
v_a_2932_ = v___x_2971_;
goto v___jp_2931_;
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v___x_2960_);
lean_del_object(v___x_2941_);
lean_dec_ref(v___x_2923_);
v_a_2973_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2968_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2968_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v___x_2982_; 
lean_dec(v___x_2965_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2960_);
v___x_2982_ = v___x_2941_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2960_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
v_a_2932_ = v___x_2982_;
goto v___jp_2931_;
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2962_);
lean_dec_ref(v___x_2960_);
lean_del_object(v___x_2941_);
lean_dec(v_fst_2939_);
lean_dec_ref(v___x_2923_);
v_a_2984_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2963_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2963_);
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
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v___x_2960_);
lean_dec(v___x_2956_);
lean_del_object(v___x_2941_);
lean_dec(v_fst_2939_);
lean_dec_ref(v___x_2923_);
v_a_2992_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2961_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2961_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
}
v___jp_2931_:
{
size_t v___x_2933_; size_t v___x_2934_; 
v___x_2933_ = ((size_t)1ULL);
v___x_2934_ = lean_usize_add(v_i_2926_, v___x_2933_);
v_i_2926_ = v___x_2934_;
v_b_2927_ = v_a_2932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3006_, lean_object* v_as_3007_, lean_object* v_sz_3008_, lean_object* v_i_3009_, lean_object* v_b_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
size_t v_sz_boxed_3014_; size_t v_i_boxed_3015_; lean_object* v_res_3016_; 
v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3008_);
lean_dec(v_sz_3008_);
v_i_boxed_3015_ = lean_unbox_usize(v_i_3009_);
lean_dec(v_i_3009_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3006_, v_as_3007_, v_sz_boxed_3014_, v_i_boxed_3015_, v_b_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec_ref(v_as_3007_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3017_, lean_object* v_args_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
uint8_t v_ret_3026_; lean_object* v___x_3027_; lean_object* v_env_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; size_t v_sz_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v_ret_3026_ = 0;
v___x_3027_ = lean_st_ref_get(v_a_3024_);
v_env_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc_ref(v_env_3028_);
lean_dec(v___x_3027_);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_array_get_size(v_args_3018_);
v___x_3031_ = l_Array_toSubarray___redArg(v_args_3018_, v___x_3029_, v___x_3030_);
v___x_3032_ = lean_box(v_ret_3026_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
v_sz_3034_ = lean_array_size(v_params_3017_);
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3028_, v_params_3017_, v_sz_3034_, v___x_3035_, v___x_3033_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3054_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3054_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3054_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_fst_3041_; lean_object* v_lower_3043_; lean_object* v_upper_3044_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v_fst_3041_ = lean_ctor_get(v_a_3037_, 0);
lean_inc(v_fst_3041_);
lean_dec(v_a_3037_);
v___x_3048_ = lean_array_get_size(v_params_3017_);
v___x_3049_ = lean_nat_dec_eq(v___x_3048_, v___x_3030_);
if (v___x_3049_ == 0)
{
uint8_t v___x_3050_; 
lean_del_object(v___x_3039_);
v___x_3050_ = lean_nat_dec_le(v___x_3030_, v___x_3029_);
if (v___x_3050_ == 0)
{
v_lower_3043_ = v___x_3030_;
v_upper_3044_ = v___x_3048_;
goto v___jp_3042_;
}
else
{
v_lower_3043_ = v___x_3029_;
v_upper_3044_ = v___x_3048_;
goto v___jp_3042_;
}
}
else
{
lean_object* v___x_3052_; 
lean_dec_ref(v_params_3017_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v_fst_3041_);
v___x_3052_ = v___x_3039_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_fst_3041_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
v___jp_3042_:
{
lean_object* v___x_3045_; uint8_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = l_Array_toSubarray___redArg(v_params_3017_, v_lower_3043_, v_upper_3044_);
v___x_3046_ = lean_unbox(v_fst_3041_);
lean_dec(v_fst_3041_);
v___x_3047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3045_, v___x_3046_, v_a_3019_, v_a_3020_, v_a_3024_);
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v_params_3017_);
v_a_3055_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3036_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3036_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3063_, lean_object* v_args_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3063_, v_args_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3073_, lean_object* v_as_3074_, size_t v_sz_3075_, size_t v_i_3076_, lean_object* v_b_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3073_, v_as_3074_, v_sz_3075_, v_i_3076_, v_b_3077_, v___y_3078_, v___y_3079_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3086_, lean_object* v_as_3087_, lean_object* v_sz_3088_, lean_object* v_i_3089_, lean_object* v_b_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
size_t v_sz_boxed_3098_; size_t v_i_boxed_3099_; lean_object* v_res_3100_; 
v_sz_boxed_3098_ = lean_unbox_usize(v_sz_3088_);
lean_dec(v_sz_3088_);
v_i_boxed_3099_ = lean_unbox_usize(v_i_3089_);
lean_dec(v_i_3089_);
v_res_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3086_, v_as_3087_, v_sz_boxed_3098_, v_i_boxed_3099_, v_b_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec_ref(v_as_3087_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3101_, lean_object* v_R_3102_, lean_object* v_a_3103_, uint8_t v_b_3104_, lean_object* v_c_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3103_, v_b_3104_, v___y_3106_, v___y_3107_, v___y_3111_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3114_, lean_object* v_R_3115_, lean_object* v_a_3116_, lean_object* v_b_3117_, lean_object* v_c_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
uint8_t v_b_boxed_3126_; lean_object* v_res_3127_; 
v_b_boxed_3126_ = lean_unbox(v_b_3117_);
v_res_3127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3114_, v_R_3115_, v_a_3116_, v_b_boxed_3126_, v_c_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3128_, size_t v_sz_3129_, size_t v_i_3130_, uint8_t v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
uint8_t v_a_3136_; uint8_t v___x_3140_; 
v___x_3140_ = lean_usize_dec_lt(v_i_3130_, v_sz_3129_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_box(v_b_3131_);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
else
{
lean_object* v_a_3143_; lean_object* v_fvarId_3144_; lean_object* v___x_3145_; 
v_a_3143_ = lean_array_uget_borrowed(v_as_3128_, v_i_3130_);
v_fvarId_3144_ = lean_ctor_get(v_a_3143_, 0);
v___x_3145_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3144_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___x_3145_, 1);
v___x_3147_ = lean_box(1);
v___x_3148_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3147_, v_a_3146_);
lean_dec(v_a_3146_);
if (v___x_3148_ == 0)
{
lean_object* v___f_3149_; lean_object* v___x_3150_; 
lean_inc(v_fvarId_3144_);
v___f_3149_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3149_, 0, v_fvarId_3144_);
lean_closure_set(v___f_3149_, 1, v___x_3147_);
v___x_3150_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3149_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_dec_ref_known(v___x_3150_, 1);
v_a_3136_ = v___x_3140_;
goto v___jp_3135_;
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
else
{
v_a_3136_ = v_b_3131_;
goto v___jp_3135_;
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_a_3159_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3145_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3145_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
v___jp_3135_:
{
size_t v___x_3137_; size_t v___x_3138_; 
v___x_3137_ = ((size_t)1ULL);
v___x_3138_ = lean_usize_add(v_i_3130_, v___x_3137_);
v_i_3130_ = v___x_3138_;
v_b_3131_ = v_a_3136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3167_, lean_object* v_sz_3168_, lean_object* v_i_3169_, lean_object* v_b_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
size_t v_sz_boxed_3174_; size_t v_i_boxed_3175_; uint8_t v_b_boxed_3176_; lean_object* v_res_3177_; 
v_sz_boxed_3174_ = lean_unbox_usize(v_sz_3168_);
lean_dec(v_sz_3168_);
v_i_boxed_3175_ = lean_unbox_usize(v_i_3169_);
lean_dec(v_i_3169_);
v_b_boxed_3176_ = lean_unbox(v_b_3170_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3167_, v_sz_boxed_3174_, v_i_boxed_3175_, v_b_boxed_3176_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v_as_3167_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
uint8_t v_ret_3186_; size_t v_sz_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v_ret_3186_ = 0;
v_sz_3187_ = lean_array_size(v_params_3178_);
v___x_3188_ = ((size_t)0ULL);
v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3178_, v_sz_3187_, v___x_3188_, v_ret_3186_, v_a_3179_, v_a_3180_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec_ref(v_params_3190_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3199_, size_t v_sz_3200_, size_t v_i_3201_, uint8_t v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3199_, v_sz_3200_, v_i_3201_, v_b_3202_, v___y_3203_, v___y_3204_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3211_, lean_object* v_sz_3212_, lean_object* v_i_3213_, lean_object* v_b_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
size_t v_sz_boxed_3222_; size_t v_i_boxed_3223_; uint8_t v_b_boxed_3224_; lean_object* v_res_3225_; 
v_sz_boxed_3222_ = lean_unbox_usize(v_sz_3212_);
lean_dec(v_sz_3212_);
v_i_boxed_3223_ = lean_unbox_usize(v_i_3213_);
lean_dec(v_i_3213_);
v_b_boxed_3224_ = lean_unbox(v_b_3214_);
v_res_3225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3211_, v_sz_boxed_3222_, v_i_boxed_3223_, v_b_boxed_3224_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec_ref(v_as_3211_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3226_, size_t v_i_3227_, size_t v_stop_3228_, lean_object* v_b_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
uint8_t v___x_3233_; 
v___x_3233_ = lean_usize_dec_eq(v_i_3227_, v_stop_3228_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v_fvarId_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_array_uget_borrowed(v_as_3226_, v_i_3227_);
v_fvarId_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_fvarId_3235_);
v___x_3236_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3235_, v___y_3230_, v___y_3231_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; size_t v___x_3238_; size_t v___x_3239_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v___x_3238_ = ((size_t)1ULL);
v___x_3239_ = lean_usize_add(v_i_3227_, v___x_3238_);
v_i_3227_ = v___x_3239_;
v_b_3229_ = v_a_3237_;
goto _start;
}
else
{
return v___x_3236_;
}
}
else
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v_b_3229_);
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3242_, lean_object* v_i_3243_, lean_object* v_stop_3244_, lean_object* v_b_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
size_t v_i_boxed_3249_; size_t v_stop_boxed_3250_; lean_object* v_res_3251_; 
v_i_boxed_3249_ = lean_unbox_usize(v_i_3243_);
lean_dec(v_i_3243_);
v_stop_boxed_3250_ = lean_unbox_usize(v_stop_3244_);
lean_dec(v_stop_3244_);
v_res_3251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3242_, v_i_boxed_3249_, v_stop_boxed_3250_, v_b_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v_as_3242_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_decl_3261_; lean_object* v_k_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; 
switch(lean_obj_tag(v_x_3252_))
{
case 0:
{
lean_object* v_k_3279_; 
v_k_3279_ = lean_ctor_get(v_x_3252_, 1);
lean_inc_ref(v_k_3279_);
lean_dec_ref_known(v_x_3252_, 2);
v_x_3252_ = v_k_3279_;
goto _start;
}
case 3:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec_ref_known(v_x_3252_, 2);
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
return v___x_3282_;
}
case 4:
{
lean_object* v_cases_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3298_; 
v_cases_3283_ = lean_ctor_get(v_x_3252_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_x_3252_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3285_ = v_x_3252_;
v_isShared_3286_ = v_isSharedCheck_3298_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_cases_3283_);
lean_dec(v_x_3252_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3298_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_alts_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v_alts_3287_ = lean_ctor_get(v_cases_3283_, 3);
lean_inc_ref(v_alts_3287_);
lean_dec_ref(v_cases_3283_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_array_get_size(v_alts_3287_);
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_nat_dec_lt(v___x_3288_, v___x_3289_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3293_; 
lean_dec_ref(v_alts_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3290_);
v___x_3293_ = v___x_3285_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3290_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
else
{
size_t v___x_3295_; size_t v___x_3296_; lean_object* v___x_3297_; 
lean_del_object(v___x_3285_);
v___x_3295_ = ((size_t)0ULL);
v___x_3296_ = lean_usize_of_nat(v___x_3289_);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3287_, v___x_3295_, v___x_3296_, v___x_3290_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
lean_dec_ref(v_alts_3287_);
return v___x_3297_;
}
}
}
case 5:
{
lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3306_; 
v_isSharedCheck_3306_ = !lean_is_exclusive(v_x_3252_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v_x_3252_, 0);
lean_dec(v_unused_3307_);
v___x_3300_ = v_x_3252_;
v_isShared_3301_ = v_isSharedCheck_3306_;
goto v_resetjp_3299_;
}
else
{
lean_dec(v_x_3252_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3306_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3302_ = lean_box(0);
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3302_);
v___x_3304_ = v___x_3300_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
case 6:
{
lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3315_; 
v_isSharedCheck_3315_ = !lean_is_exclusive(v_x_3252_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v_x_3252_, 0);
lean_dec(v_unused_3316_);
v___x_3309_ = v_x_3252_;
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
else
{
lean_dec(v_x_3252_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_box(0);
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
default: 
{
lean_object* v_decl_3317_; lean_object* v_k_3318_; 
v_decl_3317_ = lean_ctor_get(v_x_3252_, 0);
lean_inc_ref(v_decl_3317_);
v_k_3318_ = lean_ctor_get(v_x_3252_, 1);
lean_inc_ref(v_k_3318_);
lean_dec_ref(v_x_3252_);
v_decl_3261_ = v_decl_3317_;
v_k_3262_ = v_k_3318_;
v___y_3263_ = v_a_3253_;
v___y_3264_ = v_a_3254_;
v___y_3265_ = v_a_3255_;
v___y_3266_ = v_a_3256_;
v___y_3267_ = v_a_3257_;
v___y_3268_ = v_a_3258_;
goto v___jp_3260_;
}
}
v___jp_3260_:
{
lean_object* v_params_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
v_params_3269_ = lean_ctor_get(v_decl_3261_, 2);
lean_inc_ref(v_params_3269_);
lean_dec_ref(v_decl_3261_);
v___x_3270_ = lean_unsigned_to_nat(0u);
v___x_3271_ = lean_array_get_size(v_params_3269_);
v___x_3272_ = lean_nat_dec_lt(v___x_3270_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_dec_ref(v_params_3269_);
v_x_3252_ = v_k_3262_;
v_a_3253_ = v___y_3263_;
v_a_3254_ = v___y_3264_;
v_a_3255_ = v___y_3265_;
v_a_3256_ = v___y_3266_;
v_a_3257_ = v___y_3267_;
v_a_3258_ = v___y_3268_;
goto _start;
}
else
{
lean_object* v___x_3274_; size_t v___x_3275_; size_t v___x_3276_; lean_object* v___x_3277_; 
v___x_3274_ = lean_box(0);
v___x_3275_ = ((size_t)0ULL);
v___x_3276_ = lean_usize_of_nat(v___x_3271_);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3269_, v___x_3275_, v___x_3276_, v___x_3274_, v___y_3263_, v___y_3264_);
lean_dec_ref(v_params_3269_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_dec_ref_known(v___x_3277_, 1);
v_x_3252_ = v_k_3262_;
v_a_3253_ = v___y_3263_;
v_a_3254_ = v___y_3264_;
v_a_3255_ = v___y_3265_;
v_a_3256_ = v___y_3266_;
v_a_3257_ = v___y_3267_;
v_a_3258_ = v___y_3268_;
goto _start;
}
else
{
lean_dec_ref(v_k_3262_);
return v___x_3277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3319_, size_t v_i_3320_, size_t v_stop_3321_, lean_object* v_b_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___y_3331_; uint8_t v___x_3337_; 
v___x_3337_ = lean_usize_dec_eq(v_i_3320_, v_stop_3321_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_array_uget_borrowed(v_as_3319_, v_i_3320_);
switch(lean_obj_tag(v___x_3338_))
{
case 0:
{
lean_object* v_code_3339_; 
v_code_3339_ = lean_ctor_get(v___x_3338_, 2);
lean_inc_ref(v_code_3339_);
v___y_3331_ = v_code_3339_;
goto v___jp_3330_;
}
case 1:
{
lean_object* v_code_3340_; 
v_code_3340_ = lean_ctor_get(v___x_3338_, 1);
lean_inc_ref(v_code_3340_);
v___y_3331_ = v_code_3340_;
goto v___jp_3330_;
}
default: 
{
lean_object* v_code_3341_; 
v_code_3341_ = lean_ctor_get(v___x_3338_, 0);
lean_inc_ref(v_code_3341_);
v___y_3331_ = v_code_3341_;
goto v___jp_3330_;
}
}
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v_b_3322_);
return v___x_3342_;
}
v___jp_3330_:
{
lean_object* v___x_3332_; 
v___x_3332_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3331_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; size_t v___x_3334_; size_t v___x_3335_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___x_3334_ = ((size_t)1ULL);
v___x_3335_ = lean_usize_add(v_i_3320_, v___x_3334_);
v_i_3320_ = v___x_3335_;
v_b_3322_ = v_a_3333_;
goto _start;
}
else
{
return v___x_3332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3343_, lean_object* v_i_3344_, lean_object* v_stop_3345_, lean_object* v_b_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
size_t v_i_boxed_3354_; size_t v_stop_boxed_3355_; lean_object* v_res_3356_; 
v_i_boxed_3354_ = lean_unbox_usize(v_i_3344_);
lean_dec(v_i_3344_);
v_stop_boxed_3355_ = lean_unbox_usize(v_stop_3345_);
lean_dec(v_stop_3345_);
v_res_3356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3343_, v_i_boxed_3354_, v_stop_boxed_3355_, v_b_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec_ref(v_as_3343_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3366_, size_t v_i_3367_, size_t v_stop_3368_, lean_object* v_b_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3366_, v_i_3367_, v_stop_3368_, v_b_3369_, v___y_3370_, v___y_3371_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3378_, lean_object* v_i_3379_, lean_object* v_stop_3380_, lean_object* v_b_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
size_t v_i_boxed_3389_; size_t v_stop_boxed_3390_; lean_object* v_res_3391_; 
v_i_boxed_3389_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3390_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3378_, v_i_boxed_3389_, v_stop_boxed_3390_, v_b_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3392_, lean_object* v_b_3393_){
_start:
{
lean_object* v_array_3394_; lean_object* v_start_3395_; lean_object* v_stop_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3409_; 
v_array_3394_ = lean_ctor_get(v_a_3392_, 0);
v_start_3395_ = lean_ctor_get(v_a_3392_, 1);
v_stop_3396_ = lean_ctor_get(v_a_3392_, 2);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3392_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3398_ = v_a_3392_;
v_isShared_3399_ = v_isSharedCheck_3409_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_stop_3396_);
lean_inc(v_start_3395_);
lean_inc(v_array_3394_);
lean_dec(v_a_3392_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3409_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_nat_dec_lt(v_start_3395_, v_stop_3396_);
if (v___x_3400_ == 0)
{
lean_del_object(v___x_3398_);
lean_dec(v_stop_3396_);
lean_dec(v_start_3395_);
lean_dec_ref(v_array_3394_);
return v_b_3393_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3401_ = lean_unsigned_to_nat(1u);
v___x_3402_ = lean_nat_add(v_start_3395_, v___x_3401_);
lean_inc_ref(v_array_3394_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 1, v___x_3402_);
v___x_3404_ = v___x_3398_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_array_3394_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3408_, 2, v_stop_3396_);
v___x_3404_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = lean_array_fget(v_array_3394_, v_start_3395_);
lean_dec(v_start_3395_);
lean_dec_ref(v_array_3394_);
v___x_3406_ = lean_array_push(v_b_3393_, v___x_3405_);
v_a_3392_ = v___x_3404_;
v_b_3393_ = v___x_3406_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3410_, size_t v_i_3411_, lean_object* v_bs_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_lt(v_i_3411_, v_sz_3410_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_bs_3412_);
return v___x_3417_;
}
else
{
lean_object* v_v_3418_; lean_object* v___x_3419_; lean_object* v_bs_x27_3420_; lean_object* v___x_3421_; 
v_v_3418_ = lean_array_uget(v_bs_3412_, v_i_3411_);
v___x_3419_ = lean_unsigned_to_nat(0u);
v_bs_x27_3420_ = lean_array_uset(v_bs_3412_, v_i_3411_, v___x_3419_);
v___x_3421_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3418_, v___y_3413_, v___y_3414_);
lean_dec(v_v_3418_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; size_t v___x_3423_; size_t v___x_3424_; lean_object* v___x_3425_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = ((size_t)1ULL);
v___x_3424_ = lean_usize_add(v_i_3411_, v___x_3423_);
v___x_3425_ = lean_array_uset(v_bs_x27_3420_, v_i_3411_, v_a_3422_);
v_i_3411_ = v___x_3424_;
v_bs_3412_ = v___x_3425_;
goto _start;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v_bs_x27_3420_);
v_a_3427_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3421_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3421_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3435_, lean_object* v_i_3436_, lean_object* v_bs_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
size_t v_sz_boxed_3441_; size_t v_i_boxed_3442_; lean_object* v_res_3443_; 
v_sz_boxed_3441_ = lean_unbox_usize(v_sz_3435_);
lean_dec(v_sz_3435_);
v_i_boxed_3442_ = lean_unbox_usize(v_i_3436_);
lean_dec(v_i_3436_);
v_res_3443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3441_, v_i_boxed_3442_, v_bs_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3444_, size_t v_i_3445_, size_t v_stop_3446_, lean_object* v_b_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
uint8_t v___x_3452_; 
v___x_3452_ = lean_usize_dec_eq(v_i_3445_, v_stop_3446_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v_fvarId_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3453_ = lean_array_uget_borrowed(v_as_3444_, v_i_3445_);
v_fvarId_3454_ = lean_ctor_get(v___x_3453_, 0);
v___x_3455_ = lean_box(1);
lean_inc(v_fvarId_3454_);
v___x_3456_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3454_, v___x_3455_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; size_t v___x_3458_; size_t v___x_3459_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3445_, v___x_3458_);
v_i_3445_ = v___x_3459_;
v_b_3447_ = v_a_3457_;
goto _start;
}
else
{
return v___x_3456_;
}
}
else
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v_b_3447_);
return v___x_3461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3462_, lean_object* v_i_3463_, lean_object* v_stop_3464_, lean_object* v_b_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
size_t v_i_boxed_3470_; size_t v_stop_boxed_3471_; lean_object* v_res_3472_; 
v_i_boxed_3470_ = lean_unbox_usize(v_i_3463_);
lean_dec(v_i_3463_);
v_stop_boxed_3471_ = lean_unbox_usize(v_stop_3464_);
lean_dec(v_stop_3464_);
v_res_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3462_, v_i_boxed_3470_, v_stop_boxed_3471_, v_b_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v_as_3462_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3473_, size_t v_i_3474_, size_t v_stop_3475_, lean_object* v_b_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
uint8_t v___x_3481_; 
v___x_3481_ = lean_usize_dec_eq(v_i_3474_, v_stop_3475_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v_fvarId_3485_; lean_object* v___x_3486_; 
v___x_3482_ = lean_array_uget_borrowed(v_as_3473_, v_i_3474_);
v_fst_3483_ = lean_ctor_get(v___x_3482_, 0);
v_snd_3484_ = lean_ctor_get(v___x_3482_, 1);
v_fvarId_3485_ = lean_ctor_get(v_fst_3483_, 0);
lean_inc(v_snd_3484_);
lean_inc(v_fvarId_3485_);
v___x_3486_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3485_, v_snd_3484_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; size_t v___x_3488_; size_t v___x_3489_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = ((size_t)1ULL);
v___x_3489_ = lean_usize_add(v_i_3474_, v___x_3488_);
v_i_3474_ = v___x_3489_;
v_b_3476_ = v_a_3487_;
goto _start;
}
else
{
return v___x_3486_;
}
}
else
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_b_3476_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3492_, lean_object* v_i_3493_, lean_object* v_stop_3494_, lean_object* v_b_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
size_t v_i_boxed_3500_; size_t v_stop_boxed_3501_; lean_object* v_res_3502_; 
v_i_boxed_3500_ = lean_unbox_usize(v_i_3493_);
lean_dec(v_i_3493_);
v_stop_boxed_3501_ = lean_unbox_usize(v_stop_3494_);
lean_dec(v_stop_3494_);
v_res_3502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3492_, v_i_boxed_3500_, v_stop_boxed_3501_, v_b_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v_as_3492_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3505_, size_t v_i_3506_, size_t v_stop_3507_, lean_object* v_b_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_eq(v_i_3506_, v_stop_3507_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_array_uget_borrowed(v_as_3505_, v_i_3506_);
v___x_3518_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3517_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
switch(lean_obj_tag(v_letVal_3524_))
{
case 0:
{
lean_object* v_value_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3546_; 
v_value_3538_ = lean_ctor_get(v_letVal_3524_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_letVal_3524_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3540_ = v_letVal_3524_;
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_value_3538_);
lean_dec(v_letVal_3524_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3542_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3538_);
lean_dec_ref(v_value_3538_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v___x_3542_);
v___x_3544_ = v___x_3540_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
case 1:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_box(1);
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
return v___x_3548_;
}
case 2:
{
lean_object* v_idx_3549_; lean_object* v_struct_3550_; lean_object* v___x_3551_; lean_object* v_env_3552_; lean_object* v___x_3553_; 
v_idx_3549_ = lean_ctor_get(v_letVal_3524_, 1);
lean_inc(v_idx_3549_);
v_struct_3550_ = lean_ctor_get(v_letVal_3524_, 2);
lean_inc(v_struct_3550_);
lean_dec_ref_known(v_letVal_3524_, 3);
v___x_3551_ = lean_st_ref_get(v_a_3530_);
v_env_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc_ref(v_env_3552_);
lean_dec(v___x_3551_);
v___x_3553_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3550_, v_a_3525_, v_a_3526_);
lean_dec(v_struct_3550_);
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
v___x_3558_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3552_, v_a_3554_, v_idx_3549_);
lean_dec(v_idx_3549_);
lean_dec(v_a_3554_);
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
lean_dec_ref(v_env_3552_);
lean_dec(v_idx_3549_);
return v___x_3553_;
}
}
case 3:
{
lean_object* v_declName_3563_; lean_object* v_args_3564_; lean_object* v___x_3565_; lean_object* v_env_3566_; lean_object* v___x_3567_; lean_object* v_numFields_3569_; lean_object* v_lower_3570_; lean_object* v_upper_3571_; lean_object* v___x_3599_; uint8_t v___x_3667_; 
v_declName_3563_ = lean_ctor_get(v_letVal_3524_, 0);
lean_inc(v_declName_3563_);
v_args_3564_ = lean_ctor_get(v_letVal_3524_, 2);
lean_inc_ref(v_args_3564_);
lean_dec_ref_known(v_letVal_3524_, 3);
v___x_3565_ = lean_st_ref_get(v_a_3530_);
v_env_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc_ref(v_env_3566_);
lean_dec(v___x_3565_);
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3599_ = lean_array_get_size(v_args_3564_);
v___x_3667_ = lean_nat_dec_lt(v___x_3567_, v___x_3599_);
if (v___x_3667_ == 0)
{
goto v___jp_3600_;
}
else
{
lean_object* v___x_3668_; size_t v___x_3669_; size_t v___x_3670_; lean_object* v___x_3671_; 
v___x_3668_ = lean_box(0);
v___x_3669_ = ((size_t)0ULL);
v___x_3670_ = lean_usize_of_nat(v___x_3599_);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3564_, v___x_3669_, v___x_3670_, v___x_3668_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_dec_ref_known(v___x_3671_, 1);
goto v___jp_3600_;
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec_ref(v_env_3566_);
lean_dec_ref(v_args_3564_);
lean_dec(v_declName_3563_);
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
v___jp_3568_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3572_ = l_Array_toSubarray___redArg(v_args_3564_, v_lower_3570_, v_upper_3571_);
v___x_3573_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3574_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3572_, v___x_3573_);
v___x_3575_ = lean_array_get_size(v___x_3574_);
v___x_3576_ = lean_nat_dec_eq(v_numFields_3569_, v___x_3575_);
lean_dec(v_numFields_3569_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec_ref(v___x_3574_);
lean_dec(v_declName_3563_);
v___x_3577_ = lean_box(1);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
else
{
size_t v_sz_3579_; size_t v___x_3580_; lean_object* v___x_3581_; 
v_sz_3579_ = lean_array_size(v___x_3574_);
v___x_3580_ = ((size_t)0ULL);
v___x_3581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3579_, v___x_3580_, v___x_3574_, v_a_3525_, v_a_3526_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3590_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3590_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3590_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3586_, 0, v_declName_3563_);
lean_ctor_set(v___x_3586_, 1, v_a_3582_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3586_);
v___x_3588_ = v___x_3584_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v_declName_3563_);
v_a_3591_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3581_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3581_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
v___jp_3600_:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3527_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
v___x_3603_ = lean_unbox(v_a_3602_);
lean_dec(v_a_3602_);
lean_inc(v_declName_3563_);
v___x_3604_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3563_, v___x_3603_, v_a_3529_, v_a_3530_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3650_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3650_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3650_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
if (lean_obj_tag(v_a_3605_) == 1)
{
lean_object* v_val_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
lean_dec_ref(v_args_3564_);
v_val_3609_ = lean_ctor_get(v_a_3605_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v_a_3605_, 1);
v___x_3610_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3609_);
lean_dec(v_val_3609_);
v___x_3611_ = lean_nat_dec_eq(v___x_3610_, v___x_3599_);
lean_dec(v___x_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_dec_ref(v_env_3566_);
lean_dec(v_declName_3563_);
v___x_3612_ = lean_box(1);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3612_);
v___x_3614_ = v___x_3607_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
else
{
lean_object* v___x_3616_; 
lean_inc(v_declName_3563_);
v___x_3616_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3566_, v_declName_3563_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v___x_3617_; 
lean_del_object(v___x_3607_);
v___x_3617_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3563_, v_a_3525_, v_a_3526_);
lean_dec(v_declName_3563_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3630_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3630_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3630_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
if (lean_obj_tag(v_a_3618_) == 0)
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3622_ = lean_box(1);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v___x_3622_);
v___x_3624_ = v___x_3620_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
else
{
lean_object* v_val_3626_; lean_object* v___x_3628_; 
v_val_3626_ = lean_ctor_get(v_a_3618_, 0);
lean_inc(v_val_3626_);
lean_dec_ref_known(v_a_3618_, 1);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v_val_3626_);
v___x_3628_ = v___x_3620_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_val_3626_);
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
v_a_3631_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3617_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3617_);
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
else
{
lean_object* v_val_3639_; lean_object* v___x_3641_; 
lean_dec(v_declName_3563_);
v_val_3639_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_val_3639_);
lean_dec_ref_known(v___x_3616_, 1);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v_val_3639_);
v___x_3641_ = v___x_3607_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_val_3639_);
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
else
{
uint8_t v___x_3643_; lean_object* v___x_3644_; 
lean_del_object(v___x_3607_);
lean_dec(v_a_3605_);
v___x_3643_ = 0;
lean_inc(v_declName_3563_);
v___x_3644_ = l_Lean_Environment_find_x3f(v_env_3566_, v_declName_3563_, v___x_3643_);
if (lean_obj_tag(v___x_3644_) == 1)
{
lean_object* v_val_3645_; 
v_val_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_val_3645_);
lean_dec_ref_known(v___x_3644_, 1);
if (lean_obj_tag(v_val_3645_) == 6)
{
lean_object* v_val_3646_; lean_object* v_numParams_3647_; lean_object* v_numFields_3648_; uint8_t v___x_3649_; 
v_val_3646_ = lean_ctor_get(v_val_3645_, 0);
lean_inc_ref(v_val_3646_);
lean_dec_ref_known(v_val_3645_, 1);
v_numParams_3647_ = lean_ctor_get(v_val_3646_, 3);
lean_inc(v_numParams_3647_);
v_numFields_3648_ = lean_ctor_get(v_val_3646_, 4);
lean_inc(v_numFields_3648_);
lean_dec_ref(v_val_3646_);
v___x_3649_ = lean_nat_dec_le(v_numParams_3647_, v___x_3567_);
if (v___x_3649_ == 0)
{
v_numFields_3569_ = v_numFields_3648_;
v_lower_3570_ = v_numParams_3647_;
v_upper_3571_ = v___x_3599_;
goto v___jp_3568_;
}
else
{
lean_dec(v_numParams_3647_);
v_numFields_3569_ = v_numFields_3648_;
v_lower_3570_ = v___x_3567_;
v_upper_3571_ = v___x_3599_;
goto v___jp_3568_;
}
}
else
{
lean_dec(v_val_3645_);
lean_dec_ref(v_args_3564_);
lean_dec(v_declName_3563_);
goto v___jp_3532_;
}
}
else
{
lean_dec(v___x_3644_);
lean_dec_ref(v_args_3564_);
lean_dec(v_declName_3563_);
goto v___jp_3532_;
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v_env_3566_);
lean_dec_ref(v_args_3564_);
lean_dec(v_declName_3563_);
v_a_3651_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3604_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3604_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref(v_env_3566_);
lean_dec_ref(v_args_3564_);
lean_dec(v_declName_3563_);
v_a_3659_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3601_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3601_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
default: 
{
lean_object* v_args_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v_args_3680_ = lean_ctor_get(v_letVal_3524_, 1);
lean_inc_ref(v_args_3680_);
lean_dec_ref_known(v_letVal_3524_, 2);
v___x_3681_ = lean_unsigned_to_nat(0u);
v___x_3682_ = lean_array_get_size(v_args_3680_);
v___x_3683_ = lean_nat_dec_lt(v___x_3681_, v___x_3682_);
if (v___x_3683_ == 0)
{
lean_dec_ref(v_args_3680_);
goto v___jp_3535_;
}
else
{
lean_object* v___x_3684_; size_t v___x_3685_; size_t v___x_3686_; lean_object* v___x_3687_; 
v___x_3684_ = lean_box(0);
v___x_3685_ = ((size_t)0ULL);
v___x_3686_ = lean_usize_of_nat(v___x_3682_);
v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3680_, v___x_3685_, v___x_3686_, v___x_3684_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
lean_dec_ref(v_args_3680_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_dec_ref_known(v___x_3687_, 1);
goto v___jp_3535_;
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3687_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3687_);
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
}
}
v___jp_3532_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_box(1);
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
v___jp_3535_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = lean_box(1);
v___x_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3696_, lean_object* v_args_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_params_3705_; lean_object* v_value_3706_; lean_object* v___x_3707_; 
v_params_3705_ = lean_ctor_get(v_funDecl_3696_, 2);
lean_inc_ref(v_params_3705_);
v_value_3706_ = lean_ctor_get(v_funDecl_3696_, 4);
lean_inc_ref(v_value_3706_);
lean_dec_ref(v_funDecl_3696_);
v___x_3707_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3705_, v_args_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3719_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3719_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3719_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
uint8_t v___x_3712_; 
v___x_3712_ = lean_unbox(v_a_3708_);
lean_dec(v_a_3708_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
lean_dec_ref(v_value_3706_);
v___x_3713_ = lean_box(0);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3713_);
v___x_3715_ = v___x_3710_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
else
{
lean_object* v___x_3717_; 
lean_del_object(v___x_3710_);
lean_inc_ref(v_value_3706_);
v___x_3717_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3706_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v___x_3718_; 
lean_dec_ref_known(v___x_3717_, 1);
v___x_3718_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3706_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
return v___x_3718_;
}
else
{
lean_dec_ref(v_value_3706_);
return v___x_3717_;
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v_value_3706_);
v_a_3720_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3707_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3707_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3728_, lean_object* v_as_3729_, size_t v_sz_3730_, size_t v_i_3731_, lean_object* v_b_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_a_3741_; uint8_t v___x_3745_; 
v___x_3745_ = lean_usize_dec_lt(v_i_3731_, v_sz_3730_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3746_, 0, v_b_3732_);
return v___x_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v_a_3748_; 
v___x_3747_ = lean_box(0);
v_a_3748_ = lean_array_uget_borrowed(v_as_3729_, v_i_3731_);
if (lean_obj_tag(v_a_3748_) == 0)
{
lean_object* v_ctorName_3749_; lean_object* v_params_3750_; lean_object* v_code_3751_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___x_3760_; 
v_ctorName_3749_ = lean_ctor_get(v_a_3748_, 0);
v_params_3750_ = lean_ctor_get(v_a_3748_, 1);
v_code_3751_ = lean_ctor_get(v_a_3748_, 2);
v___x_3760_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3728_, v_ctorName_3749_);
if (lean_obj_tag(v___x_3760_) == 1)
{
lean_object* v_val_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v_val_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_val_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3762_ = l_Array_zip___redArg(v_params_3750_, v_val_3761_);
lean_dec(v_val_3761_);
v___x_3763_ = lean_unsigned_to_nat(0u);
v___x_3764_ = lean_array_get_size(v___x_3762_);
v___x_3765_ = lean_nat_dec_lt(v___x_3763_, v___x_3764_);
if (v___x_3765_ == 0)
{
lean_dec_ref(v___x_3762_);
v___y_3753_ = v___y_3733_;
v___y_3754_ = v___y_3734_;
v___y_3755_ = v___y_3735_;
v___y_3756_ = v___y_3736_;
v___y_3757_ = v___y_3737_;
v___y_3758_ = v___y_3738_;
goto v___jp_3752_;
}
else
{
size_t v___x_3766_; size_t v___x_3767_; lean_object* v___x_3768_; 
v___x_3766_ = ((size_t)0ULL);
v___x_3767_ = lean_usize_of_nat(v___x_3764_);
v___x_3768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3762_, v___x_3766_, v___x_3767_, v___x_3747_, v___y_3733_, v___y_3734_, v___y_3738_);
lean_dec_ref(v___x_3762_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_dec_ref_known(v___x_3768_, 1);
v___y_3753_ = v___y_3733_;
v___y_3754_ = v___y_3734_;
v___y_3755_ = v___y_3735_;
v___y_3756_ = v___y_3736_;
v___y_3757_ = v___y_3737_;
v___y_3758_ = v___y_3738_;
goto v___jp_3752_;
}
else
{
return v___x_3768_;
}
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
lean_dec(v___x_3760_);
v___x_3769_ = lean_unsigned_to_nat(0u);
v___x_3770_ = lean_array_get_size(v_params_3750_);
v___x_3771_ = lean_nat_dec_lt(v___x_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
v___y_3753_ = v___y_3733_;
v___y_3754_ = v___y_3734_;
v___y_3755_ = v___y_3735_;
v___y_3756_ = v___y_3736_;
v___y_3757_ = v___y_3737_;
v___y_3758_ = v___y_3738_;
goto v___jp_3752_;
}
else
{
size_t v___x_3772_; size_t v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = ((size_t)0ULL);
v___x_3773_ = lean_usize_of_nat(v___x_3770_);
v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3750_, v___x_3772_, v___x_3773_, v___x_3747_, v___y_3733_, v___y_3734_, v___y_3738_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_dec_ref_known(v___x_3774_, 1);
v___y_3753_ = v___y_3733_;
v___y_3754_ = v___y_3734_;
v___y_3755_ = v___y_3735_;
v___y_3756_ = v___y_3736_;
v___y_3757_ = v___y_3737_;
v___y_3758_ = v___y_3738_;
goto v___jp_3752_;
}
else
{
return v___x_3774_;
}
}
}
v___jp_3752_:
{
lean_object* v___x_3759_; 
lean_inc_ref(v_code_3751_);
v___x_3759_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3751_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_dec_ref_known(v___x_3759_, 1);
v_a_3741_ = v___x_3747_;
goto v___jp_3740_;
}
else
{
return v___x_3759_;
}
}
}
else
{
lean_object* v_code_3775_; lean_object* v___x_3776_; 
v_code_3775_ = lean_ctor_get(v_a_3748_, 0);
lean_inc_ref(v_code_3775_);
v___x_3776_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3775_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_dec_ref_known(v___x_3776_, 1);
v_a_3741_ = v___x_3747_;
goto v___jp_3740_;
}
else
{
return v___x_3776_;
}
}
}
v___jp_3740_:
{
size_t v___x_3742_; size_t v___x_3743_; 
v___x_3742_ = ((size_t)1ULL);
v___x_3743_ = lean_usize_add(v_i_3731_, v___x_3742_);
v_i_3731_ = v___x_3743_;
v_b_3732_ = v_a_3741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v_decl_3786_; lean_object* v_k_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; 
switch(lean_obj_tag(v_x_3777_))
{
case 0:
{
lean_object* v_decl_3797_; lean_object* v_k_3798_; lean_object* v_fvarId_3799_; lean_object* v_value_3800_; lean_object* v___x_3801_; 
v_decl_3797_ = lean_ctor_get(v_x_3777_, 0);
lean_inc_ref(v_decl_3797_);
v_k_3798_ = lean_ctor_get(v_x_3777_, 1);
lean_inc_ref(v_k_3798_);
lean_dec_ref_known(v_x_3777_, 2);
v_fvarId_3799_ = lean_ctor_get(v_decl_3797_, 0);
lean_inc(v_fvarId_3799_);
v_value_3800_ = lean_ctor_get(v_decl_3797_, 3);
lean_inc_n(v_value_3800_, 2);
lean_dec_ref(v_decl_3797_);
v___x_3801_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3800_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3803_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3803_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3799_, v_a_3802_, v_a_3778_, v_a_3779_, v_a_3783_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_dec_ref_known(v___x_3803_, 1);
if (lean_obj_tag(v_value_3800_) == 4)
{
lean_object* v_fvarId_3804_; lean_object* v_args_3805_; uint8_t v___x_3806_; lean_object* v___x_3807_; 
v_fvarId_3804_ = lean_ctor_get(v_value_3800_, 0);
lean_inc(v_fvarId_3804_);
v_args_3805_ = lean_ctor_get(v_value_3800_, 1);
lean_inc_ref(v_args_3805_);
lean_dec_ref_known(v_value_3800_, 2);
v___x_3806_ = 0;
v___x_3807_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3806_, v_fvarId_3804_, v_a_3781_);
lean_dec(v_fvarId_3804_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
if (lean_obj_tag(v_a_3808_) == 1)
{
lean_object* v_val_3809_; lean_object* v___x_3810_; 
v_val_3809_ = lean_ctor_get(v_a_3808_, 0);
lean_inc(v_val_3809_);
lean_dec_ref_known(v_a_3808_, 1);
v___x_3810_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3809_, v_args_3805_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_dec_ref_known(v___x_3810_, 1);
v_x_3777_ = v_k_3798_;
goto _start;
}
else
{
lean_dec_ref(v_k_3798_);
return v___x_3810_;
}
}
else
{
lean_dec(v_a_3808_);
lean_dec_ref(v_args_3805_);
v_x_3777_ = v_k_3798_;
goto _start;
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v_args_3805_);
lean_dec_ref(v_k_3798_);
v_a_3813_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3807_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3807_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_dec(v_value_3800_);
v_x_3777_ = v_k_3798_;
goto _start;
}
}
else
{
lean_dec(v_value_3800_);
lean_dec_ref(v_k_3798_);
return v___x_3803_;
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec(v_value_3800_);
lean_dec(v_fvarId_3799_);
lean_dec_ref(v_k_3798_);
v_a_3822_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3801_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3801_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3830_; lean_object* v_args_3831_; uint8_t v___x_3832_; lean_object* v___x_3833_; 
v_fvarId_3830_ = lean_ctor_get(v_x_3777_, 0);
lean_inc(v_fvarId_3830_);
v_args_3831_ = lean_ctor_get(v_x_3777_, 1);
lean_inc_ref(v_args_3831_);
lean_dec_ref_known(v_x_3777_, 2);
v___x_3832_ = 0;
v___x_3833_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3832_, v_fvarId_3830_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = lean_array_get_size(v_args_3831_);
v___x_3837_ = lean_nat_dec_lt(v___x_3835_, v___x_3836_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; 
v___x_3838_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3834_, v_args_3831_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = ((size_t)0ULL);
v___x_3841_ = lean_usize_of_nat(v___x_3836_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3831_, v___x_3840_, v___x_3841_, v___x_3839_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v___x_3843_; 
lean_dec_ref_known(v___x_3842_, 1);
v___x_3843_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3834_, v_args_3831_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
return v___x_3843_;
}
else
{
lean_dec(v_a_3834_);
lean_dec_ref(v_args_3831_);
return v___x_3842_;
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v_args_3831_);
v_a_3844_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3833_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3833_);
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
case 4:
{
lean_object* v_cases_3852_; lean_object* v_discr_3853_; lean_object* v_alts_3854_; lean_object* v___x_3855_; 
v_cases_3852_ = lean_ctor_get(v_x_3777_, 0);
lean_inc_ref(v_cases_3852_);
lean_dec_ref_known(v_x_3777_, 1);
v_discr_3853_ = lean_ctor_get(v_cases_3852_, 2);
lean_inc(v_discr_3853_);
v_alts_3854_ = lean_ctor_get(v_cases_3852_, 3);
lean_inc_ref(v_alts_3854_);
lean_dec_ref(v_cases_3852_);
v___x_3855_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3853_, v_a_3778_, v_a_3779_);
lean_dec(v_discr_3853_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3857_; size_t v_sz_3858_; size_t v___x_3859_; lean_object* v___x_3860_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___x_3857_ = lean_box(0);
v_sz_3858_ = lean_array_size(v_alts_3854_);
v___x_3859_ = ((size_t)0ULL);
v___x_3860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3856_, v_alts_3854_, v_sz_3858_, v___x_3859_, v___x_3857_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
lean_dec_ref(v_alts_3854_);
lean_dec(v_a_3856_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; 
v_unused_3868_ = lean_ctor_get(v___x_3860_, 0);
lean_dec(v_unused_3868_);
v___x_3862_ = v___x_3860_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_dec(v___x_3860_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3857_);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3857_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
else
{
return v___x_3860_;
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_dec_ref(v_alts_3854_);
v_a_3869_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3855_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3855_);
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
case 5:
{
lean_object* v_fvarId_3877_; lean_object* v___x_3878_; 
v_fvarId_3877_ = lean_ctor_get(v_x_3777_, 0);
lean_inc(v_fvarId_3877_);
lean_dec_ref_known(v_x_3777_, 1);
v___x_3878_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3877_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v___x_3879_; 
lean_dec_ref_known(v___x_3878_, 1);
v___x_3879_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3877_, v_a_3778_, v_a_3779_);
lean_dec(v_fvarId_3877_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3880_, v_a_3778_, v_a_3779_, v_a_3783_);
return v___x_3881_;
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3879_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3879_);
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
else
{
lean_dec(v_fvarId_3877_);
return v___x_3878_;
}
}
case 6:
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3897_; 
v_isSharedCheck_3897_ = !lean_is_exclusive(v_x_3777_);
if (v_isSharedCheck_3897_ == 0)
{
lean_object* v_unused_3898_; 
v_unused_3898_ = lean_ctor_get(v_x_3777_, 0);
lean_dec(v_unused_3898_);
v___x_3891_ = v_x_3777_;
v_isShared_3892_ = v_isSharedCheck_3897_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v_x_3777_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3897_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = lean_box(0);
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3895_ = v___x_3891_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
default: 
{
lean_object* v_decl_3899_; lean_object* v_k_3900_; 
v_decl_3899_ = lean_ctor_get(v_x_3777_, 0);
lean_inc_ref(v_decl_3899_);
v_k_3900_ = lean_ctor_get(v_x_3777_, 1);
lean_inc_ref(v_k_3900_);
lean_dec_ref(v_x_3777_);
v_decl_3786_ = v_decl_3899_;
v_k_3787_ = v_k_3900_;
v___y_3788_ = v_a_3778_;
v___y_3789_ = v_a_3779_;
v___y_3790_ = v_a_3780_;
v___y_3791_ = v_a_3781_;
v___y_3792_ = v_a_3782_;
v___y_3793_ = v_a_3783_;
goto v___jp_3785_;
}
}
v___jp_3785_:
{
lean_object* v_value_3794_; lean_object* v___x_3795_; 
v_value_3794_ = lean_ctor_get(v_decl_3786_, 4);
lean_inc_ref(v_value_3794_);
lean_dec_ref(v_decl_3786_);
v___x_3795_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3794_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_dec_ref_known(v___x_3795_, 1);
v_x_3777_ = v_k_3787_;
v_a_3778_ = v___y_3788_;
v_a_3779_ = v___y_3789_;
v_a_3780_ = v___y_3790_;
v_a_3781_ = v___y_3791_;
v_a_3782_ = v___y_3792_;
v_a_3783_ = v___y_3793_;
goto _start;
}
else
{
lean_dec_ref(v_k_3787_);
return v___x_3795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
uint8_t v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = 0;
v___x_3910_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3909_, v_var_3901_, v_a_3905_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3943_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3943_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3943_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
if (lean_obj_tag(v_a_3911_) == 1)
{
lean_object* v_val_3915_; lean_object* v_params_3916_; lean_object* v_value_3917_; lean_object* v___x_3918_; 
lean_del_object(v___x_3913_);
v_val_3915_ = lean_ctor_get(v_a_3911_, 0);
lean_inc(v_val_3915_);
lean_dec_ref_known(v_a_3911_, 1);
v_params_3916_ = lean_ctor_get(v_val_3915_, 2);
lean_inc_ref(v_params_3916_);
v_value_3917_ = lean_ctor_get(v_val_3915_, 4);
lean_inc_ref(v_value_3917_);
lean_dec(v_val_3915_);
v___x_3918_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3916_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_);
lean_dec_ref(v_params_3916_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3930_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3921_ = v___x_3918_;
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
uint8_t v___x_3923_; 
v___x_3923_ = lean_unbox(v_a_3919_);
lean_dec(v_a_3919_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_dec_ref(v_value_3917_);
v___x_3924_ = lean_box(0);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3924_);
v___x_3926_ = v___x_3921_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
else
{
lean_object* v___x_3928_; 
lean_del_object(v___x_3921_);
lean_inc_ref(v_value_3917_);
v___x_3928_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3917_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v___x_3929_; 
lean_dec_ref_known(v___x_3928_, 1);
v___x_3929_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3917_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_);
return v___x_3929_;
}
else
{
lean_dec_ref(v_value_3917_);
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v_value_3917_);
v_a_3931_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3918_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3918_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
lean_dec(v_a_3911_);
v___x_3939_ = lean_box(0);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3939_);
v___x_3941_ = v___x_3913_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
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
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
v_a_3944_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3910_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3910_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
if (lean_obj_tag(v_arg_3952_) == 1)
{
lean_object* v_fvarId_3960_; lean_object* v___x_3961_; 
v_fvarId_3960_ = lean_ctor_get(v_arg_3952_, 0);
v___x_3961_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3960_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_box(0);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_arg_3964_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_3973_, lean_object* v_i_3974_, lean_object* v_stop_3975_, lean_object* v_b_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
size_t v_i_boxed_3984_; size_t v_stop_boxed_3985_; lean_object* v_res_3986_; 
v_i_boxed_3984_ = lean_unbox_usize(v_i_3974_);
lean_dec(v_i_3974_);
v_stop_boxed_3985_ = lean_unbox_usize(v_stop_3975_);
lean_dec(v_stop_3975_);
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_3973_, v_i_boxed_3984_, v_stop_boxed_3985_, v_b_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v_as_3973_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_3987_, lean_object* v_args_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_3987_, v_args_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_var_3997_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4006_, lean_object* v_as_4007_, lean_object* v_sz_4008_, lean_object* v_i_4009_, lean_object* v_b_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
size_t v_sz_boxed_4018_; size_t v_i_boxed_4019_; lean_object* v_res_4020_; 
v_sz_boxed_4018_ = lean_unbox_usize(v_sz_4008_);
lean_dec(v_sz_4008_);
v_i_boxed_4019_ = lean_unbox_usize(v_i_4009_);
lean_dec(v_i_4009_);
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4006_, v_as_4007_, v_sz_boxed_4018_, v_i_boxed_4019_, v_b_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec_ref(v_as_4007_);
lean_dec(v_a_4006_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4039_, lean_object* v_R_4040_, lean_object* v_a_4041_, lean_object* v_b_4042_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4041_, v_b_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4044_, size_t v_i_4045_, lean_object* v_bs_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4044_, v_i_4045_, v_bs_4046_, v___y_4047_, v___y_4048_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4055_, lean_object* v_i_4056_, lean_object* v_bs_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
size_t v_sz_boxed_4065_; size_t v_i_boxed_4066_; lean_object* v_res_4067_; 
v_sz_boxed_4065_ = lean_unbox_usize(v_sz_4055_);
lean_dec(v_sz_4055_);
v_i_boxed_4066_ = lean_unbox_usize(v_i_4056_);
lean_dec(v_i_4056_);
v_res_4067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4065_, v_i_boxed_4066_, v_bs_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4068_, size_t v_i_4069_, size_t v_stop_4070_, lean_object* v_b_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4068_, v_i_4069_, v_stop_4070_, v_b_4071_, v___y_4072_, v___y_4073_, v___y_4077_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4080_, lean_object* v_i_4081_, lean_object* v_stop_4082_, lean_object* v_b_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
size_t v_i_boxed_4091_; size_t v_stop_boxed_4092_; lean_object* v_res_4093_; 
v_i_boxed_4091_ = lean_unbox_usize(v_i_4081_);
lean_dec(v_i_4081_);
v_stop_boxed_4092_ = lean_unbox_usize(v_stop_4082_);
lean_dec(v_stop_4082_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4080_, v_i_boxed_4091_, v_stop_boxed_4092_, v_b_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec_ref(v_as_4080_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4094_, size_t v_i_4095_, size_t v_stop_4096_, lean_object* v_b_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4094_, v_i_4095_, v_stop_4096_, v_b_4097_, v___y_4098_, v___y_4099_, v___y_4103_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4106_, lean_object* v_i_4107_, lean_object* v_stop_4108_, lean_object* v_b_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
size_t v_i_boxed_4117_; size_t v_stop_boxed_4118_; lean_object* v_res_4119_; 
v_i_boxed_4117_ = lean_unbox_usize(v_i_4107_);
lean_dec(v_i_4107_);
v_stop_boxed_4118_ = lean_unbox_usize(v_stop_4108_);
lean_dec(v_stop_4108_);
v_res_4119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4106_, v_i_boxed_4117_, v_stop_boxed_4118_, v_b_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec_ref(v_as_4106_);
return v_res_4119_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4120_ = lean_unsigned_to_nat(32u);
v___x_4121_ = lean_mk_empty_array_with_capacity(v___x_4120_);
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4123_ = ((size_t)5ULL);
v___x_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = lean_unsigned_to_nat(32u);
v___x_4126_ = lean_mk_empty_array_with_capacity(v___x_4125_);
v___x_4127_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4128_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set(v___x_4128_, 1, v___x_4126_);
lean_ctor_set(v___x_4128_, 2, v___x_4124_);
lean_ctor_set(v___x_4128_, 3, v___x_4124_);
lean_ctor_set_usize(v___x_4128_, 4, v___x_4123_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4129_){
_start:
{
lean_object* v___x_4131_; lean_object* v_traceState_4132_; lean_object* v_traces_4133_; lean_object* v___x_4134_; lean_object* v_traceState_4135_; lean_object* v_env_4136_; lean_object* v_nextMacroScope_4137_; lean_object* v_ngen_4138_; lean_object* v_auxDeclNGen_4139_; lean_object* v_cache_4140_; lean_object* v_recordedDeps_4141_; lean_object* v_messages_4142_; lean_object* v_infoState_4143_; lean_object* v_snapshotTasks_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4163_; 
v___x_4131_ = lean_st_ref_get(v___y_4129_);
v_traceState_4132_ = lean_ctor_get(v___x_4131_, 4);
lean_inc_ref(v_traceState_4132_);
lean_dec(v___x_4131_);
v_traces_4133_ = lean_ctor_get(v_traceState_4132_, 0);
lean_inc_ref(v_traces_4133_);
lean_dec_ref(v_traceState_4132_);
v___x_4134_ = lean_st_ref_take(v___y_4129_);
v_traceState_4135_ = lean_ctor_get(v___x_4134_, 4);
v_env_4136_ = lean_ctor_get(v___x_4134_, 0);
v_nextMacroScope_4137_ = lean_ctor_get(v___x_4134_, 1);
v_ngen_4138_ = lean_ctor_get(v___x_4134_, 2);
v_auxDeclNGen_4139_ = lean_ctor_get(v___x_4134_, 3);
v_cache_4140_ = lean_ctor_get(v___x_4134_, 5);
v_recordedDeps_4141_ = lean_ctor_get(v___x_4134_, 6);
v_messages_4142_ = lean_ctor_get(v___x_4134_, 7);
v_infoState_4143_ = lean_ctor_get(v___x_4134_, 8);
v_snapshotTasks_4144_ = lean_ctor_get(v___x_4134_, 9);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4146_ = v___x_4134_;
v_isShared_4147_ = v_isSharedCheck_4163_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_snapshotTasks_4144_);
lean_inc(v_infoState_4143_);
lean_inc(v_messages_4142_);
lean_inc(v_recordedDeps_4141_);
lean_inc(v_cache_4140_);
lean_inc(v_traceState_4135_);
lean_inc(v_auxDeclNGen_4139_);
lean_inc(v_ngen_4138_);
lean_inc(v_nextMacroScope_4137_);
lean_inc(v_env_4136_);
lean_dec(v___x_4134_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4163_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
uint64_t v_tid_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4161_; 
v_tid_4148_ = lean_ctor_get_uint64(v_traceState_4135_, sizeof(void*)*1);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_traceState_4135_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; 
v_unused_4162_ = lean_ctor_get(v_traceState_4135_, 0);
lean_dec(v_unused_4162_);
v___x_4150_ = v_traceState_4135_;
v_isShared_4151_ = v_isSharedCheck_4161_;
goto v_resetjp_4149_;
}
else
{
lean_dec(v_traceState_4135_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4161_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; lean_object* v___x_4154_; 
v___x_4152_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v___x_4152_);
v___x_4154_ = v___x_4150_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4152_);
lean_ctor_set_uint64(v_reuseFailAlloc_4160_, sizeof(void*)*1, v_tid_4148_);
v___x_4154_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4156_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 4, v___x_4154_);
v___x_4156_ = v___x_4146_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_env_4136_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_nextMacroScope_4137_);
lean_ctor_set(v_reuseFailAlloc_4159_, 2, v_ngen_4138_);
lean_ctor_set(v_reuseFailAlloc_4159_, 3, v_auxDeclNGen_4139_);
lean_ctor_set(v_reuseFailAlloc_4159_, 4, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4159_, 5, v_cache_4140_);
lean_ctor_set(v_reuseFailAlloc_4159_, 6, v_recordedDeps_4141_);
lean_ctor_set(v_reuseFailAlloc_4159_, 7, v_messages_4142_);
lean_ctor_set(v_reuseFailAlloc_4159_, 8, v_infoState_4143_);
lean_ctor_set(v_reuseFailAlloc_4159_, 9, v_snapshotTasks_4144_);
v___x_4156_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = lean_st_ref_put(v___y_4129_, v___x_4156_);
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v_traces_4133_);
return v___x_4158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4164_);
lean_dec(v___y_4164_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4172_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
return v_res_4182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4183_, lean_object* v_opt_4184_){
_start:
{
lean_object* v_name_4185_; lean_object* v_defValue_4186_; lean_object* v_map_4187_; lean_object* v___x_4188_; 
v_name_4185_ = lean_ctor_get(v_opt_4184_, 0);
v_defValue_4186_ = lean_ctor_get(v_opt_4184_, 1);
v_map_4187_ = lean_ctor_get(v_opts_4183_, 0);
v___x_4188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4187_, v_name_4185_);
if (lean_obj_tag(v___x_4188_) == 0)
{
uint8_t v___x_4189_; 
v___x_4189_ = lean_unbox(v_defValue_4186_);
return v___x_4189_;
}
else
{
lean_object* v_val_4190_; 
v_val_4190_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_val_4190_);
lean_dec_ref_known(v___x_4188_, 1);
if (lean_obj_tag(v_val_4190_) == 1)
{
uint8_t v_v_4191_; 
v_v_4191_ = lean_ctor_get_uint8(v_val_4190_, 0);
lean_dec_ref_known(v_val_4190_, 0);
return v_v_4191_;
}
else
{
uint8_t v___x_4192_; 
lean_dec(v_val_4190_);
v___x_4192_ = lean_unbox(v_defValue_4186_);
return v___x_4192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4193_, lean_object* v_opt_4194_){
_start:
{
uint8_t v_res_4195_; lean_object* v_r_4196_; 
v_res_4195_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4193_, v_opt_4194_);
lean_dec_ref(v_opt_4194_);
lean_dec_ref(v_opts_4193_);
v_r_4196_ = lean_box(v_res_4195_);
return v_r_4196_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4199_ = l_Lean_stringToMessageData(v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4200_, lean_object* v_x_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4209_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4210_ = l_Lean_MessageData_ofName(v_name_4200_);
v___x_4211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4213_, lean_object* v_x_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4213_, v_x_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec_ref(v_x_4214_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4223_, lean_object* v_opt_4224_){
_start:
{
lean_object* v_name_4225_; lean_object* v_defValue_4226_; lean_object* v_map_4227_; lean_object* v___x_4228_; 
v_name_4225_ = lean_ctor_get(v_opt_4224_, 0);
v_defValue_4226_ = lean_ctor_get(v_opt_4224_, 1);
v_map_4227_ = lean_ctor_get(v_opts_4223_, 0);
v___x_4228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4227_, v_name_4225_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_inc(v_defValue_4226_);
return v_defValue_4226_;
}
else
{
lean_object* v_val_4229_; 
v_val_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_val_4229_);
lean_dec_ref_known(v___x_4228_, 1);
if (lean_obj_tag(v_val_4229_) == 3)
{
lean_object* v_v_4230_; 
v_v_4230_ = lean_ctor_get(v_val_4229_, 0);
lean_inc(v_v_4230_);
lean_dec_ref_known(v_val_4229_, 1);
return v_v_4230_;
}
else
{
lean_dec(v_val_4229_);
lean_inc(v_defValue_4226_);
return v_defValue_4226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4231_, lean_object* v_opt_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4231_, v_opt_4232_);
lean_dec_ref(v_opt_4232_);
lean_dec_ref(v_opts_4231_);
return v_res_4233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4234_){
_start:
{
if (lean_obj_tag(v_e_4234_) == 0)
{
uint8_t v___x_4235_; 
v___x_4235_ = 2;
return v___x_4235_;
}
else
{
uint8_t v___x_4236_; 
v___x_4236_ = 0;
return v___x_4236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4237_){
_start:
{
uint8_t v_res_4238_; lean_object* v_r_4239_; 
v_res_4238_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4237_);
lean_dec_ref(v_e_4237_);
v_r_4239_ = lean_box(v_res_4238_);
return v_r_4239_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4240_){
_start:
{
if (lean_obj_tag(v_x_4240_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_a_4242_ = lean_ctor_get(v_x_4240_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_x_4240_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v_x_4240_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v_x_4240_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 1);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
v_a_4250_ = lean_ctor_get(v_x_4240_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_x_4240_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v_x_4240_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v_x_4240_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
lean_ctor_set_tag(v___x_4252_, 0);
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4258_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4261_, size_t v_i_4262_, lean_object* v_bs_4263_){
_start:
{
uint8_t v___x_4264_; 
v___x_4264_ = lean_usize_dec_lt(v_i_4262_, v_sz_4261_);
if (v___x_4264_ == 0)
{
return v_bs_4263_;
}
else
{
lean_object* v_v_4265_; lean_object* v_msg_4266_; lean_object* v___x_4267_; lean_object* v_bs_x27_4268_; size_t v___x_4269_; size_t v___x_4270_; lean_object* v___x_4271_; 
v_v_4265_ = lean_array_uget_borrowed(v_bs_4263_, v_i_4262_);
v_msg_4266_ = lean_ctor_get(v_v_4265_, 1);
lean_inc_ref(v_msg_4266_);
v___x_4267_ = lean_unsigned_to_nat(0u);
v_bs_x27_4268_ = lean_array_uset(v_bs_4263_, v_i_4262_, v___x_4267_);
v___x_4269_ = ((size_t)1ULL);
v___x_4270_ = lean_usize_add(v_i_4262_, v___x_4269_);
v___x_4271_ = lean_array_uset(v_bs_x27_4268_, v_i_4262_, v_msg_4266_);
v_i_4262_ = v___x_4270_;
v_bs_4263_ = v___x_4271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4273_, lean_object* v_i_4274_, lean_object* v_bs_4275_){
_start:
{
size_t v_sz_boxed_4276_; size_t v_i_boxed_4277_; lean_object* v_res_4278_; 
v_sz_boxed_4276_ = lean_unbox_usize(v_sz_4273_);
lean_dec(v_sz_4273_);
v_i_boxed_4277_ = lean_unbox_usize(v_i_4274_);
lean_dec(v_i_4274_);
v_res_4278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4276_, v_i_boxed_4277_, v_bs_4275_);
return v_res_4278_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4281_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4282_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4283_ = lean_unsigned_to_nat(0u);
v___x_4284_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4283_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
lean_ctor_set(v___x_4284_, 2, v___x_4283_);
lean_ctor_set(v___x_4284_, 3, v___x_4283_);
lean_ctor_set(v___x_4284_, 4, v___x_4282_);
lean_ctor_set(v___x_4284_, 5, v___x_4282_);
lean_ctor_set(v___x_4284_, 6, v___x_4282_);
lean_ctor_set(v___x_4284_, 7, v___x_4282_);
lean_ctor_set(v___x_4284_, 8, v___x_4282_);
lean_ctor_set(v___x_4284_, 9, v___x_4282_);
lean_ctor_set(v___x_4284_, 10, v___x_4282_);
lean_ctor_set(v___x_4284_, 11, v___x_4281_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4285_, lean_object* v_data_4286_, lean_object* v_ref_4287_, lean_object* v_msg_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_toCold_4294_; lean_object* v_currRecDepth_4295_; lean_object* v_ref_4296_; uint16_t v_optionFlags_4297_; uint8_t v_suppressElabErrors_4298_; uint8_t v_checkDeprecated_4299_; uint8_t v_isRecordingDeps_4300_; lean_object* v_ref_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v_traceState_4304_; lean_object* v_traces_4305_; lean_object* v___x_4306_; size_t v_sz_4307_; size_t v___x_4308_; lean_object* v___x_4309_; lean_object* v_msg_4310_; lean_object* v___x_4311_; lean_object* v_env_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_toCold_4294_ = lean_ctor_get(v___y_4291_, 0);
v_currRecDepth_4295_ = lean_ctor_get(v___y_4291_, 1);
v_ref_4296_ = lean_ctor_get(v___y_4291_, 2);
v_optionFlags_4297_ = lean_ctor_get_uint16(v___y_4291_, sizeof(void*)*3);
v_suppressElabErrors_4298_ = lean_ctor_get_uint8(v___y_4291_, sizeof(void*)*3 + 2);
v_checkDeprecated_4299_ = lean_ctor_get_uint8(v___y_4291_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4300_ = lean_ctor_get_uint8(v___y_4291_, sizeof(void*)*3 + 4);
v_ref_4301_ = l_Lean_replaceRef(v_ref_4287_, v_ref_4296_);
lean_inc(v_currRecDepth_4295_);
lean_inc_ref(v_toCold_4294_);
v___x_4302_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4302_, 0, v_toCold_4294_);
lean_ctor_set(v___x_4302_, 1, v_currRecDepth_4295_);
lean_ctor_set(v___x_4302_, 2, v_ref_4301_);
lean_ctor_set_uint16(v___x_4302_, sizeof(void*)*3, v_optionFlags_4297_);
lean_ctor_set_uint8(v___x_4302_, sizeof(void*)*3 + 2, v_suppressElabErrors_4298_);
lean_ctor_set_uint8(v___x_4302_, sizeof(void*)*3 + 3, v_checkDeprecated_4299_);
lean_ctor_set_uint8(v___x_4302_, sizeof(void*)*3 + 4, v_isRecordingDeps_4300_);
v___x_4303_ = lean_st_ref_get(v___y_4292_);
v_traceState_4304_ = lean_ctor_get(v___x_4303_, 4);
lean_inc_ref(v_traceState_4304_);
lean_dec(v___x_4303_);
v_traces_4305_ = lean_ctor_get(v_traceState_4304_, 0);
lean_inc_ref(v_traces_4305_);
lean_dec_ref(v_traceState_4304_);
v___x_4306_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4305_);
lean_dec_ref(v_traces_4305_);
v_sz_4307_ = lean_array_size(v___x_4306_);
v___x_4308_ = ((size_t)0ULL);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4307_, v___x_4308_, v___x_4306_);
v_msg_4310_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4310_, 0, v_data_4286_);
lean_ctor_set(v_msg_4310_, 1, v_msg_4288_);
lean_ctor_set(v_msg_4310_, 2, v___x_4309_);
v___x_4311_ = lean_st_ref_get(v___y_4292_);
v_env_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc_ref(v_env_4312_);
lean_dec(v___x_4311_);
v___x_4313_ = lean_st_ref_get(v___y_4290_);
v___x_4314_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4289_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4367_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4367_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4367_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v_lctx_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4365_; 
v_lctx_4319_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; 
v_unused_4366_ = lean_ctor_get(v___x_4313_, 1);
lean_dec(v_unused_4366_);
v___x_4321_ = v___x_4313_;
v_isShared_4322_ = v_isSharedCheck_4365_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_lctx_4319_);
lean_dec(v___x_4313_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4365_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
uint8_t v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4329_; 
v___x_4323_ = lean_unbox(v_a_4315_);
lean_dec(v_a_4315_);
v___x_4324_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4319_, v___x_4323_);
lean_dec_ref(v_lctx_4319_);
v___x_4325_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___x_4302_);
lean_dec_ref_known(v___x_4302_, 3);
v___x_4326_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4327_, 0, v_env_4312_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
lean_ctor_set(v___x_4327_, 2, v___x_4324_);
lean_ctor_set(v___x_4327_, 3, v___x_4325_);
if (v_isShared_4322_ == 0)
{
lean_ctor_set_tag(v___x_4321_, 3);
lean_ctor_set(v___x_4321_, 1, v_msg_4310_);
lean_ctor_set(v___x_4321_, 0, v___x_4327_);
v___x_4329_ = v___x_4321_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v_msg_4310_);
v___x_4329_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4330_; lean_object* v_traceState_4331_; lean_object* v_env_4332_; lean_object* v_nextMacroScope_4333_; lean_object* v_ngen_4334_; lean_object* v_auxDeclNGen_4335_; lean_object* v_cache_4336_; lean_object* v_recordedDeps_4337_; lean_object* v_messages_4338_; lean_object* v_infoState_4339_; lean_object* v_snapshotTasks_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4363_; 
v___x_4330_ = lean_st_ref_take(v___y_4292_);
v_traceState_4331_ = lean_ctor_get(v___x_4330_, 4);
v_env_4332_ = lean_ctor_get(v___x_4330_, 0);
v_nextMacroScope_4333_ = lean_ctor_get(v___x_4330_, 1);
v_ngen_4334_ = lean_ctor_get(v___x_4330_, 2);
v_auxDeclNGen_4335_ = lean_ctor_get(v___x_4330_, 3);
v_cache_4336_ = lean_ctor_get(v___x_4330_, 5);
v_recordedDeps_4337_ = lean_ctor_get(v___x_4330_, 6);
v_messages_4338_ = lean_ctor_get(v___x_4330_, 7);
v_infoState_4339_ = lean_ctor_get(v___x_4330_, 8);
v_snapshotTasks_4340_ = lean_ctor_get(v___x_4330_, 9);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4342_ = v___x_4330_;
v_isShared_4343_ = v_isSharedCheck_4363_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_snapshotTasks_4340_);
lean_inc(v_infoState_4339_);
lean_inc(v_messages_4338_);
lean_inc(v_recordedDeps_4337_);
lean_inc(v_cache_4336_);
lean_inc(v_traceState_4331_);
lean_inc(v_auxDeclNGen_4335_);
lean_inc(v_ngen_4334_);
lean_inc(v_nextMacroScope_4333_);
lean_inc(v_env_4332_);
lean_dec(v___x_4330_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4363_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
uint64_t v_tid_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4361_; 
v_tid_4344_ = lean_ctor_get_uint64(v_traceState_4331_, sizeof(void*)*1);
v_isSharedCheck_4361_ = !lean_is_exclusive(v_traceState_4331_);
if (v_isSharedCheck_4361_ == 0)
{
lean_object* v_unused_4362_; 
v_unused_4362_ = lean_ctor_get(v_traceState_4331_, 0);
lean_dec(v_unused_4362_);
v___x_4346_ = v_traceState_4331_;
v_isShared_4347_ = v_isSharedCheck_4361_;
goto v_resetjp_4345_;
}
else
{
lean_dec(v_traceState_4331_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4361_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4352_; 
v___x_4348_ = lean_box(0);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v_ref_4287_);
lean_ctor_set(v___x_4349_, 1, v___x_4329_);
v___x_4350_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4285_, v___x_4349_);
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 0, v___x_4350_);
v___x_4352_ = v___x_4346_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4350_);
lean_ctor_set_uint64(v_reuseFailAlloc_4360_, sizeof(void*)*1, v_tid_4344_);
v___x_4352_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
lean_object* v___x_4354_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 4, v___x_4352_);
v___x_4354_ = v___x_4342_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_env_4332_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_nextMacroScope_4333_);
lean_ctor_set(v_reuseFailAlloc_4359_, 2, v_ngen_4334_);
lean_ctor_set(v_reuseFailAlloc_4359_, 3, v_auxDeclNGen_4335_);
lean_ctor_set(v_reuseFailAlloc_4359_, 4, v___x_4352_);
lean_ctor_set(v_reuseFailAlloc_4359_, 5, v_cache_4336_);
lean_ctor_set(v_reuseFailAlloc_4359_, 6, v_recordedDeps_4337_);
lean_ctor_set(v_reuseFailAlloc_4359_, 7, v_messages_4338_);
lean_ctor_set(v_reuseFailAlloc_4359_, 8, v_infoState_4339_);
lean_ctor_set(v_reuseFailAlloc_4359_, 9, v_snapshotTasks_4340_);
v___x_4354_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4355_ = lean_st_ref_put(v___y_4292_, v___x_4354_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 0, v___x_4348_);
v___x_4357_ = v___x_4317_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4348_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
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
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec(v___x_4313_);
lean_dec_ref(v_env_4312_);
lean_dec_ref_known(v_msg_4310_, 3);
lean_dec_ref_known(v___x_4302_, 3);
lean_dec(v_ref_4287_);
lean_dec_ref(v_oldTraces_4285_);
v_a_4368_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4314_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4314_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4376_, lean_object* v_data_4377_, lean_object* v_ref_4378_, lean_object* v_msg_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4376_, v_data_4377_, v_ref_4378_, v_msg_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
return v_res_4385_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4386_; double v___x_4387_; 
v___x_4386_ = lean_unsigned_to_nat(0u);
v___x_4387_ = lean_float_of_nat(v___x_4386_);
return v___x_4387_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4390_ = l_Lean_stringToMessageData(v___x_4389_);
return v___x_4390_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4391_; double v___x_4392_; 
v___x_4391_ = lean_unsigned_to_nat(1000u);
v___x_4392_ = lean_float_of_nat(v___x_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4393_, uint8_t v_collapsed_4394_, lean_object* v_tag_4395_, lean_object* v_opts_4396_, uint8_t v_clsEnabled_4397_, lean_object* v_oldTraces_4398_, lean_object* v_msg_4399_, lean_object* v_resStartStop_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v_fst_4408_; lean_object* v_snd_4409_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v_data_4413_; lean_object* v_fst_4416_; lean_object* v_snd_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; lean_object* v___y_4421_; lean_object* v_a_4422_; uint8_t v___y_4437_; double v___y_4469_; 
v_fst_4408_ = lean_ctor_get(v_resStartStop_4400_, 0);
lean_inc(v_fst_4408_);
v_snd_4409_ = lean_ctor_get(v_resStartStop_4400_, 1);
lean_inc(v_snd_4409_);
lean_dec_ref(v_resStartStop_4400_);
v_fst_4416_ = lean_ctor_get(v_snd_4409_, 0);
lean_inc(v_fst_4416_);
v_snd_4417_ = lean_ctor_get(v_snd_4409_, 1);
lean_inc(v_snd_4417_);
lean_dec(v_snd_4409_);
v___x_4418_ = l_Lean_trace_profiler;
v___x_4419_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4396_, v___x_4418_);
if (v___x_4419_ == 0)
{
v___y_4437_ = v___x_4419_;
goto v___jp_4436_;
}
else
{
lean_object* v___x_4474_; uint8_t v___x_4475_; 
v___x_4474_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4475_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4396_, v___x_4474_);
if (v___x_4475_ == 0)
{
lean_object* v___x_4476_; lean_object* v___x_4477_; double v___x_4478_; double v___x_4479_; double v___x_4480_; 
v___x_4476_ = l_Lean_trace_profiler_threshold;
v___x_4477_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4396_, v___x_4476_);
v___x_4478_ = lean_float_of_nat(v___x_4477_);
v___x_4479_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4480_ = lean_float_div(v___x_4478_, v___x_4479_);
v___y_4469_ = v___x_4480_;
goto v___jp_4468_;
}
else
{
lean_object* v___x_4481_; lean_object* v___x_4482_; double v___x_4483_; 
v___x_4481_ = l_Lean_trace_profiler_threshold;
v___x_4482_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4396_, v___x_4481_);
v___x_4483_ = lean_float_of_nat(v___x_4482_);
v___y_4469_ = v___x_4483_;
goto v___jp_4468_;
}
}
v___jp_4410_:
{
lean_object* v___x_4414_; 
lean_inc(v___y_4411_);
v___x_4414_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4398_, v_data_4413_, v___y_4411_, v___y_4412_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v___x_4415_; 
lean_dec_ref_known(v___x_4414_, 1);
v___x_4415_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4408_);
return v___x_4415_;
}
else
{
lean_dec(v_fst_4408_);
return v___x_4414_;
}
}
v___jp_4420_:
{
uint8_t v_result_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; double v___x_4426_; lean_object* v_data_4427_; 
v_result_4423_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4408_);
v___x_4424_ = lean_box(v_result_4423_);
v___x_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
v___x_4426_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4395_);
lean_inc_ref(v___x_4425_);
lean_inc(v_cls_4393_);
v_data_4427_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4427_, 0, v_cls_4393_);
lean_ctor_set(v_data_4427_, 1, v___x_4425_);
lean_ctor_set(v_data_4427_, 2, v_tag_4395_);
lean_ctor_set_float(v_data_4427_, sizeof(void*)*3, v___x_4426_);
lean_ctor_set_float(v_data_4427_, sizeof(void*)*3 + 8, v___x_4426_);
lean_ctor_set_uint8(v_data_4427_, sizeof(void*)*3 + 16, v_collapsed_4394_);
if (v___x_4419_ == 0)
{
lean_dec_ref_known(v___x_4425_, 1);
lean_dec(v_snd_4417_);
lean_dec(v_fst_4416_);
lean_dec_ref(v_tag_4395_);
lean_dec(v_cls_4393_);
v___y_4411_ = v___y_4421_;
v___y_4412_ = v_a_4422_;
v_data_4413_ = v_data_4427_;
goto v___jp_4410_;
}
else
{
lean_object* v_data_4428_; double v___x_4429_; double v___x_4430_; 
lean_dec_ref_known(v_data_4427_, 3);
v_data_4428_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4428_, 0, v_cls_4393_);
lean_ctor_set(v_data_4428_, 1, v___x_4425_);
lean_ctor_set(v_data_4428_, 2, v_tag_4395_);
v___x_4429_ = lean_unbox_float(v_fst_4416_);
lean_dec(v_fst_4416_);
lean_ctor_set_float(v_data_4428_, sizeof(void*)*3, v___x_4429_);
v___x_4430_ = lean_unbox_float(v_snd_4417_);
lean_dec(v_snd_4417_);
lean_ctor_set_float(v_data_4428_, sizeof(void*)*3 + 8, v___x_4430_);
lean_ctor_set_uint8(v_data_4428_, sizeof(void*)*3 + 16, v_collapsed_4394_);
v___y_4411_ = v___y_4421_;
v___y_4412_ = v_a_4422_;
v_data_4413_ = v_data_4428_;
goto v___jp_4410_;
}
}
v___jp_4431_:
{
lean_object* v_ref_4432_; lean_object* v___x_4433_; 
v_ref_4432_ = lean_ctor_get(v___y_4405_, 2);
lean_inc(v___y_4406_);
lean_inc_ref(v___y_4405_);
lean_inc(v___y_4404_);
lean_inc_ref(v___y_4403_);
lean_inc(v___y_4402_);
lean_inc_ref(v___y_4401_);
lean_inc(v_fst_4408_);
v___x_4433_ = lean_apply_8(v_msg_4399_, v_fst_4408_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, lean_box(0));
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___y_4421_ = v_ref_4432_;
v_a_4422_ = v_a_4434_;
goto v___jp_4420_;
}
else
{
lean_object* v___x_4435_; 
lean_dec_ref_known(v___x_4433_, 1);
v___x_4435_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4421_ = v_ref_4432_;
v_a_4422_ = v___x_4435_;
goto v___jp_4420_;
}
}
v___jp_4436_:
{
if (v_clsEnabled_4397_ == 0)
{
if (v___y_4437_ == 0)
{
lean_object* v___x_4438_; lean_object* v_traceState_4439_; lean_object* v_env_4440_; lean_object* v_nextMacroScope_4441_; lean_object* v_ngen_4442_; lean_object* v_auxDeclNGen_4443_; lean_object* v_cache_4444_; lean_object* v_recordedDeps_4445_; lean_object* v_messages_4446_; lean_object* v_infoState_4447_; lean_object* v_snapshotTasks_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4467_; 
lean_dec(v_snd_4417_);
lean_dec(v_fst_4416_);
lean_dec_ref(v_msg_4399_);
lean_dec_ref(v_tag_4395_);
lean_dec(v_cls_4393_);
v___x_4438_ = lean_st_ref_take(v___y_4406_);
v_traceState_4439_ = lean_ctor_get(v___x_4438_, 4);
v_env_4440_ = lean_ctor_get(v___x_4438_, 0);
v_nextMacroScope_4441_ = lean_ctor_get(v___x_4438_, 1);
v_ngen_4442_ = lean_ctor_get(v___x_4438_, 2);
v_auxDeclNGen_4443_ = lean_ctor_get(v___x_4438_, 3);
v_cache_4444_ = lean_ctor_get(v___x_4438_, 5);
v_recordedDeps_4445_ = lean_ctor_get(v___x_4438_, 6);
v_messages_4446_ = lean_ctor_get(v___x_4438_, 7);
v_infoState_4447_ = lean_ctor_get(v___x_4438_, 8);
v_snapshotTasks_4448_ = lean_ctor_get(v___x_4438_, 9);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4450_ = v___x_4438_;
v_isShared_4451_ = v_isSharedCheck_4467_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_snapshotTasks_4448_);
lean_inc(v_infoState_4447_);
lean_inc(v_messages_4446_);
lean_inc(v_recordedDeps_4445_);
lean_inc(v_cache_4444_);
lean_inc(v_traceState_4439_);
lean_inc(v_auxDeclNGen_4443_);
lean_inc(v_ngen_4442_);
lean_inc(v_nextMacroScope_4441_);
lean_inc(v_env_4440_);
lean_dec(v___x_4438_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4467_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
uint64_t v_tid_4452_; lean_object* v_traces_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4466_; 
v_tid_4452_ = lean_ctor_get_uint64(v_traceState_4439_, sizeof(void*)*1);
v_traces_4453_ = lean_ctor_get(v_traceState_4439_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_traceState_4439_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4455_ = v_traceState_4439_;
v_isShared_4456_ = v_isSharedCheck_4466_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_traces_4453_);
lean_dec(v_traceState_4439_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4466_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4457_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4398_, v_traces_4453_);
lean_dec_ref(v_traces_4453_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4457_);
v___x_4459_ = v___x_4455_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4457_);
lean_ctor_set_uint64(v_reuseFailAlloc_4465_, sizeof(void*)*1, v_tid_4452_);
v___x_4459_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4461_; 
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 4, v___x_4459_);
v___x_4461_ = v___x_4450_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_env_4440_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_nextMacroScope_4441_);
lean_ctor_set(v_reuseFailAlloc_4464_, 2, v_ngen_4442_);
lean_ctor_set(v_reuseFailAlloc_4464_, 3, v_auxDeclNGen_4443_);
lean_ctor_set(v_reuseFailAlloc_4464_, 4, v___x_4459_);
lean_ctor_set(v_reuseFailAlloc_4464_, 5, v_cache_4444_);
lean_ctor_set(v_reuseFailAlloc_4464_, 6, v_recordedDeps_4445_);
lean_ctor_set(v_reuseFailAlloc_4464_, 7, v_messages_4446_);
lean_ctor_set(v_reuseFailAlloc_4464_, 8, v_infoState_4447_);
lean_ctor_set(v_reuseFailAlloc_4464_, 9, v_snapshotTasks_4448_);
v___x_4461_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = lean_st_ref_put(v___y_4406_, v___x_4461_);
v___x_4463_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4408_);
return v___x_4463_;
}
}
}
}
}
else
{
goto v___jp_4431_;
}
}
else
{
goto v___jp_4431_;
}
}
v___jp_4468_:
{
double v___x_4470_; double v___x_4471_; double v___x_4472_; uint8_t v___x_4473_; 
v___x_4470_ = lean_unbox_float(v_snd_4417_);
v___x_4471_ = lean_unbox_float(v_fst_4416_);
v___x_4472_ = lean_float_sub(v___x_4470_, v___x_4471_);
v___x_4473_ = lean_float_decLt(v___y_4469_, v___x_4472_);
v___y_4437_ = v___x_4473_;
goto v___jp_4436_;
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
lean_object* v___f_4544_; lean_object* v___x_4545_; 
lean_inc(v_name_4539_);
v___f_4544_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4544_, 0, v_name_4539_);
v___x_4545_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4520_, v___y_4523_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v___y_4548_; lean_object* v_decls_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; uint8_t v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v_a_4589_; uint8_t v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v_a_4608_; uint8_t v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; uint8_t v___x_4688_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v___x_4545_, 1);
v_decls_4578_ = lean_ctor_get(v___y_4522_, 0);
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = lean_array_get_size(v_params_4540_);
lean_inc(v_a_4520_);
lean_inc_ref(v_decls_4578_);
v___x_4581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4581_, 0, v_decls_4578_);
lean_ctor_set(v___x_4581_, 1, v_a_4520_);
v___x_4688_ = lean_nat_dec_lt(v___x_4579_, v___x_4580_);
if (v___x_4688_ == 0)
{
goto v___jp_4671_;
}
else
{
size_t v___x_4689_; size_t v___x_4690_; lean_object* v___x_4691_; 
v___x_4689_ = ((size_t)0ULL);
v___x_4690_ = lean_usize_of_nat(v___x_4580_);
v___x_4691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4540_, v___x_4689_, v___x_4690_, v___x_4542_, v___x_4581_, v___y_4523_, v___y_4527_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_dec_ref_known(v___x_4691_, 1);
goto v___jp_4671_;
}
else
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
lean_dec_ref_known(v___x_4581_, 2);
lean_dec(v_a_4546_);
lean_dec_ref(v___f_4544_);
lean_dec(v_a_4520_);
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4691_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4691_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
v___jp_4547_:
{
if (lean_obj_tag(v___y_4548_) == 0)
{
lean_object* v___x_4549_; 
lean_dec_ref_known(v___y_4548_, 1);
v___x_4549_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4520_, v___y_4523_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4561_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4552_ = v___x_4549_;
v_isShared_4553_ = v_isSharedCheck_4561_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4549_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4561_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
uint8_t v___x_4554_; 
v___x_4554_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4546_, v_a_4550_);
lean_dec(v_a_4550_);
lean_dec(v_a_4546_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4559_; 
lean_dec(v_a_4520_);
v___x_4555_ = lean_box(v___x_4534_);
v___x_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
v___x_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
lean_ctor_set(v___x_4557_, 1, v___x_4542_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4557_);
v___x_4559_ = v___x_4552_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
else
{
lean_del_object(v___x_4552_);
v_a_4530_ = v___x_4543_;
goto v___jp_4529_;
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec(v_a_4546_);
lean_dec(v_a_4520_);
v_a_4562_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4549_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4549_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec(v_a_4546_);
lean_dec(v_a_4520_);
v_a_4570_ = lean_ctor_get(v___y_4548_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___y_4548_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___y_4548_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___y_4548_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
v___jp_4582_:
{
lean_object* v___x_4590_; double v___x_4591_; double v___x_4592_; double v___x_4593_; double v___x_4594_; double v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4590_ = lean_io_mono_nanos_now();
v___x_4591_ = lean_float_of_nat(v___y_4584_);
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
lean_inc_ref(v___y_4586_);
lean_inc(v___y_4585_);
v___x_4600_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4585_, v___x_4534_, v___y_4586_, v___y_4587_, v___y_4583_, v___y_4588_, v___f_4544_, v___x_4599_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref_known(v___x_4581_, 2);
v___y_4548_ = v___x_4600_;
goto v___jp_4547_;
}
v___jp_4601_:
{
lean_object* v___x_4609_; double v___x_4610_; double v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4609_ = lean_io_get_num_heartbeats();
v___x_4610_ = lean_float_of_nat(v___y_4603_);
v___x_4611_ = lean_float_of_nat(v___x_4609_);
v___x_4612_ = lean_box_float(v___x_4610_);
v___x_4613_ = lean_box_float(v___x_4611_);
v___x_4614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4612_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4615_, 0, v_a_4608_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
lean_inc_ref(v___y_4605_);
lean_inc(v___y_4604_);
v___x_4616_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4604_, v___x_4534_, v___y_4605_, v___y_4606_, v___y_4602_, v___y_4607_, v___f_4544_, v___x_4615_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref_known(v___x_4581_, 2);
v___y_4548_ = v___x_4616_;
goto v___jp_4547_;
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
lean_dec_ref_known(v___x_4623_, 1);
v___x_4625_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4626_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4622_, v___x_4625_);
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
v___y_4583_ = v___y_4618_;
v___y_4584_ = v___x_4627_;
v___y_4585_ = v___y_4620_;
v___y_4586_ = v___y_4621_;
v___y_4587_ = v___y_4622_;
v___y_4588_ = v_a_4624_;
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
v___y_4583_ = v___y_4618_;
v___y_4584_ = v___x_4627_;
v___y_4585_ = v___y_4620_;
v___y_4586_ = v___y_4621_;
v___y_4587_ = v___y_4622_;
v___y_4588_ = v_a_4624_;
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
v___y_4602_ = v___y_4618_;
v___y_4603_ = v___x_4645_;
v___y_4604_ = v___y_4620_;
v___y_4605_ = v___y_4621_;
v___y_4606_ = v___y_4622_;
v___y_4607_ = v_a_4624_;
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
v___y_4602_ = v___y_4618_;
v___y_4603_ = v___x_4645_;
v___y_4604_ = v___y_4620_;
v___y_4605_ = v___y_4621_;
v___y_4606_ = v___y_4622_;
v___y_4607_ = v_a_4624_;
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
lean_dec_ref_known(v___x_4581_, 2);
lean_dec(v_a_4546_);
lean_dec_ref(v___f_4544_);
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
lean_object* v_toCold_4672_; lean_object* v_options_4673_; uint8_t v_hasTrace_4674_; 
v_toCold_4672_ = lean_ctor_get(v___y_4526_, 0);
v_options_4673_ = lean_ctor_get(v_toCold_4672_, 2);
v_hasTrace_4674_ = lean_ctor_get_uint8(v_options_4673_, sizeof(void*)*1);
if (v_hasTrace_4674_ == 0)
{
lean_object* v_code_4675_; lean_object* v___x_4676_; 
lean_dec_ref(v___f_4544_);
v_code_4675_ = lean_ctor_get(v_value_4538_, 0);
lean_inc_ref(v_code_4675_);
v___x_4676_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4675_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref_known(v___x_4581_, 2);
v___y_4548_ = v___x_4676_;
goto v___jp_4547_;
}
else
{
lean_object* v_code_4677_; lean_object* v_inheritedTraceOptions_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; 
v_code_4677_ = lean_ctor_get(v_value_4538_, 0);
v_inheritedTraceOptions_4678_ = lean_ctor_get(v_toCold_4672_, 11);
v___x_4679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4681_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4678_, v_options_4673_, v___x_4681_);
if (v___x_4682_ == 0)
{
lean_object* v___x_4683_; uint8_t v___x_4684_; 
v___x_4683_ = l_Lean_trace_profiler;
v___x_4684_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4673_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; 
lean_dec_ref(v___f_4544_);
lean_inc_ref(v_code_4677_);
v___x_4685_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4677_, v___x_4581_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec_ref_known(v___x_4581_, 2);
v___y_4548_ = v___x_4685_;
goto v___jp_4547_;
}
else
{
lean_inc_ref(v_code_4677_);
v___y_4618_ = v___x_4682_;
v___y_4619_ = v_code_4677_;
v___y_4620_ = v___x_4679_;
v___y_4621_ = v___x_4680_;
v___y_4622_ = v_options_4673_;
goto v___jp_4617_;
}
}
else
{
lean_inc_ref(v_code_4677_);
v___y_4618_ = v___x_4682_;
v___y_4619_ = v_code_4677_;
v___y_4620_ = v___x_4679_;
v___y_4621_ = v___x_4680_;
v___y_4622_ = v_options_4673_;
goto v___jp_4617_;
}
}
}
else
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
lean_dec_ref(v___f_4544_);
v___x_4686_ = lean_box(1);
v___x_4687_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4686_, v___x_4581_, v___y_4523_, v___y_4527_);
lean_dec_ref_known(v___x_4581_, 2);
v___y_4548_ = v___x_4687_;
goto v___jp_4547_;
}
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
lean_dec_ref(v___f_4544_);
lean_dec(v_a_4520_);
v_a_4700_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4545_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4545_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4708_, lean_object* v___x_4709_, lean_object* v_a_4710_, lean_object* v_b_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4708_, v___x_4709_, v_a_4710_, v_b_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec_ref(v___x_4709_);
lean_dec(v_upperBound_4708_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_decls_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v_decls_4727_ = lean_ctor_get(v_a_4720_, 0);
v___x_4728_ = lean_array_get_size(v_decls_4727_);
v___x_4729_ = lean_unsigned_to_nat(0u);
v___x_4730_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4728_, v_decls_4727_, v___x_4729_, v___x_4730_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4746_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4746_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4746_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v_fst_4736_; 
v_fst_4736_ = lean_ctor_get(v_a_4732_, 0);
lean_inc(v_fst_4736_);
lean_dec(v_a_4732_);
if (lean_obj_tag(v_fst_4736_) == 0)
{
uint8_t v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4737_ = 0;
v___x_4738_ = lean_box(v___x_4737_);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v___x_4738_);
v___x_4740_ = v___x_4734_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
else
{
lean_object* v_val_4742_; lean_object* v___x_4744_; 
v_val_4742_ = lean_ctor_get(v_fst_4736_, 0);
lean_inc(v_val_4742_);
lean_dec_ref_known(v_fst_4736_, 1);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v_val_4742_);
v___x_4744_ = v___x_4734_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_val_4742_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
v_a_4747_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4731_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4731_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4763_, lean_object* v_x_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v___x_4772_; 
v___x_4772_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4764_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4773_, lean_object* v_x_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4773_, v_x_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4783_, lean_object* v___x_4784_, lean_object* v_inst_4785_, lean_object* v_R_4786_, lean_object* v_a_4787_, lean_object* v_b_4788_, lean_object* v_c_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4783_, v___x_4784_, v_a_4787_, v_b_4788_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4798_, lean_object* v___x_4799_, lean_object* v_inst_4800_, lean_object* v_R_4801_, lean_object* v_a_4802_, lean_object* v_b_4803_, lean_object* v_c_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4798_, v___x_4799_, v_inst_4800_, v_R_4801_, v_a_4802_, v_b_4803_, v_c_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec_ref(v___x_4799_);
lean_dec(v_upperBound_4798_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4813_, lean_object* v_data_4814_, lean_object* v_ref_4815_, lean_object* v_msg_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4813_, v_data_4814_, v_ref_4815_, v_msg_4816_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4825_, lean_object* v_data_4826_, lean_object* v_ref_4827_, lean_object* v_msg_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4825_, v_data_4826_, v_ref_4827_, v_msg_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4839_, lean_object* v_msg_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v_ref_4846_; lean_object* v___x_4847_; lean_object* v_env_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v_ref_4846_ = lean_ctor_get(v___y_4843_, 2);
v___x_4847_ = lean_st_ref_get(v___y_4844_);
v_env_4848_ = lean_ctor_get(v___x_4847_, 0);
lean_inc_ref(v_env_4848_);
lean_dec(v___x_4847_);
v___x_4849_ = lean_st_ref_get(v___y_4842_);
v___x_4850_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4841_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4910_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4853_ = v___x_4850_;
v_isShared_4854_ = v_isSharedCheck_4910_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4850_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4910_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v_lctx_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4908_; 
v_lctx_4855_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4908_ == 0)
{
lean_object* v_unused_4909_; 
v_unused_4909_ = lean_ctor_get(v___x_4849_, 1);
lean_dec(v_unused_4909_);
v___x_4857_ = v___x_4849_;
v_isShared_4858_ = v_isSharedCheck_4908_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_lctx_4855_);
lean_dec(v___x_4849_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4908_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
uint8_t v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4859_ = lean_unbox(v_a_4851_);
lean_dec(v_a_4851_);
v___x_4860_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4855_, v___x_4859_);
lean_dec_ref(v_lctx_4855_);
v___x_4861_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4843_);
v___x_4862_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_4863_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4863_, 0, v_env_4848_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
lean_ctor_set(v___x_4863_, 2, v___x_4860_);
lean_ctor_set(v___x_4863_, 3, v___x_4861_);
if (v_isShared_4858_ == 0)
{
lean_ctor_set_tag(v___x_4857_, 3);
lean_ctor_set(v___x_4857_, 1, v_msg_4840_);
lean_ctor_set(v___x_4857_, 0, v___x_4863_);
v___x_4865_ = v___x_4857_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4907_, 1, v_msg_4840_);
v___x_4865_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4866_; lean_object* v_traceState_4867_; lean_object* v_env_4868_; lean_object* v_nextMacroScope_4869_; lean_object* v_ngen_4870_; lean_object* v_auxDeclNGen_4871_; lean_object* v_cache_4872_; lean_object* v_recordedDeps_4873_; lean_object* v_messages_4874_; lean_object* v_infoState_4875_; lean_object* v_snapshotTasks_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4906_; 
v___x_4866_ = lean_st_ref_take(v___y_4844_);
v_traceState_4867_ = lean_ctor_get(v___x_4866_, 4);
v_env_4868_ = lean_ctor_get(v___x_4866_, 0);
v_nextMacroScope_4869_ = lean_ctor_get(v___x_4866_, 1);
v_ngen_4870_ = lean_ctor_get(v___x_4866_, 2);
v_auxDeclNGen_4871_ = lean_ctor_get(v___x_4866_, 3);
v_cache_4872_ = lean_ctor_get(v___x_4866_, 5);
v_recordedDeps_4873_ = lean_ctor_get(v___x_4866_, 6);
v_messages_4874_ = lean_ctor_get(v___x_4866_, 7);
v_infoState_4875_ = lean_ctor_get(v___x_4866_, 8);
v_snapshotTasks_4876_ = lean_ctor_get(v___x_4866_, 9);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4878_ = v___x_4866_;
v_isShared_4879_ = v_isSharedCheck_4906_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_snapshotTasks_4876_);
lean_inc(v_infoState_4875_);
lean_inc(v_messages_4874_);
lean_inc(v_recordedDeps_4873_);
lean_inc(v_cache_4872_);
lean_inc(v_traceState_4867_);
lean_inc(v_auxDeclNGen_4871_);
lean_inc(v_ngen_4870_);
lean_inc(v_nextMacroScope_4869_);
lean_inc(v_env_4868_);
lean_dec(v___x_4866_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4906_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
uint64_t v_tid_4880_; lean_object* v_traces_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4905_; 
v_tid_4880_ = lean_ctor_get_uint64(v_traceState_4867_, sizeof(void*)*1);
v_traces_4881_ = lean_ctor_get(v_traceState_4867_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v_traceState_4867_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4883_ = v_traceState_4867_;
v_isShared_4884_ = v_isSharedCheck_4905_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_traces_4881_);
lean_dec(v_traceState_4867_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4905_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; double v___x_4887_; uint8_t v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4885_ = lean_box(0);
v___x_4886_ = lean_box(0);
v___x_4887_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4888_ = 0;
v___x_4889_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4890_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4890_, 0, v_cls_4839_);
lean_ctor_set(v___x_4890_, 1, v___x_4886_);
lean_ctor_set(v___x_4890_, 2, v___x_4889_);
lean_ctor_set_float(v___x_4890_, sizeof(void*)*3, v___x_4887_);
lean_ctor_set_float(v___x_4890_, sizeof(void*)*3 + 8, v___x_4887_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*3 + 16, v___x_4888_);
v___x_4891_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4892_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4890_);
lean_ctor_set(v___x_4892_, 1, v___x_4865_);
lean_ctor_set(v___x_4892_, 2, v___x_4891_);
lean_inc(v_ref_4846_);
v___x_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4893_, 0, v_ref_4846_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
v___x_4894_ = l_Lean_PersistentArray_push___redArg(v_traces_4881_, v___x_4893_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4894_);
v___x_4896_ = v___x_4883_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4894_);
lean_ctor_set_uint64(v_reuseFailAlloc_4904_, sizeof(void*)*1, v_tid_4880_);
v___x_4896_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
lean_object* v___x_4898_; 
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 4, v___x_4896_);
v___x_4898_ = v___x_4878_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_env_4868_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_nextMacroScope_4869_);
lean_ctor_set(v_reuseFailAlloc_4903_, 2, v_ngen_4870_);
lean_ctor_set(v_reuseFailAlloc_4903_, 3, v_auxDeclNGen_4871_);
lean_ctor_set(v_reuseFailAlloc_4903_, 4, v___x_4896_);
lean_ctor_set(v_reuseFailAlloc_4903_, 5, v_cache_4872_);
lean_ctor_set(v_reuseFailAlloc_4903_, 6, v_recordedDeps_4873_);
lean_ctor_set(v_reuseFailAlloc_4903_, 7, v_messages_4874_);
lean_ctor_set(v_reuseFailAlloc_4903_, 8, v_infoState_4875_);
lean_ctor_set(v_reuseFailAlloc_4903_, 9, v_snapshotTasks_4876_);
v___x_4898_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
lean_object* v___x_4899_; lean_object* v___x_4901_; 
v___x_4899_ = lean_st_ref_put(v___y_4844_, v___x_4898_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 0, v___x_4885_);
v___x_4901_ = v___x_4853_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4885_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
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
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
lean_dec(v___x_4849_);
lean_dec_ref(v_env_4848_);
lean_dec_ref(v_msg_4840_);
lean_dec(v_cls_4839_);
v_a_4911_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4913_ = v___x_4850_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4850_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4919_, lean_object* v_msg_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4919_, v_msg_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4927_, lean_object* v_msg_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4927_, v_msg_4928_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4937_, lean_object* v_msg_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4937_, v_msg_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v___y_4940_);
lean_dec_ref(v___y_4939_);
return v_res_4946_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4947_ = lean_box(0);
v___x_4948_ = lean_unsigned_to_nat(16u);
v___x_4949_ = lean_mk_array(v___x_4948_, v___x_4947_);
return v___x_4949_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_4951_ = lean_unsigned_to_nat(0u);
v___x_4952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
lean_ctor_set(v___x_4952_, 1, v___x_4950_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_4953_, size_t v_i_4954_, lean_object* v_bs_4955_){
_start:
{
uint8_t v___x_4956_; 
v___x_4956_ = lean_usize_dec_lt(v_i_4954_, v_sz_4953_);
if (v___x_4956_ == 0)
{
return v_bs_4955_;
}
else
{
lean_object* v___x_4957_; lean_object* v_bs_x27_4958_; lean_object* v___x_4959_; size_t v___x_4960_; size_t v___x_4961_; lean_object* v___x_4962_; 
v___x_4957_ = lean_unsigned_to_nat(0u);
v_bs_x27_4958_ = lean_array_uset(v_bs_4955_, v_i_4954_, v___x_4957_);
v___x_4959_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_4960_ = ((size_t)1ULL);
v___x_4961_ = lean_usize_add(v_i_4954_, v___x_4960_);
v___x_4962_ = lean_array_uset(v_bs_x27_4958_, v_i_4954_, v___x_4959_);
v_i_4954_ = v___x_4961_;
v_bs_4955_ = v___x_4962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_4964_, lean_object* v_i_4965_, lean_object* v_bs_4966_){
_start:
{
size_t v_sz_boxed_4967_; size_t v_i_boxed_4968_; lean_object* v_res_4969_; 
v_sz_boxed_4967_ = lean_unbox_usize(v_sz_4964_);
lean_dec(v_sz_4964_);
v_i_boxed_4968_ = lean_unbox_usize(v_i_4965_);
lean_dec(v_i_4965_);
v_res_4969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_4967_, v_i_boxed_4968_, v_bs_4966_);
return v_res_4969_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_4972_ = l_Lean_stringToMessageData(v___x_4971_);
return v___x_4972_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4974_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_4975_ = l_Lean_stringToMessageData(v___x_4974_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v___x_4987_; lean_object* v_decls_4988_; lean_object* v_funVals_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_5029_; 
v___x_4987_ = lean_st_ref_take(v_a_4978_);
v_decls_4988_ = lean_ctor_get(v_a_4977_, 0);
v_funVals_4989_ = lean_ctor_get(v___x_4987_, 1);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_5029_ == 0)
{
lean_object* v_unused_5030_; 
v_unused_5030_ = lean_ctor_get(v___x_4987_, 0);
lean_dec(v_unused_5030_);
v___x_4991_ = v___x_4987_;
v_isShared_4992_ = v_isSharedCheck_5029_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_funVals_4989_);
lean_dec(v___x_4987_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_5029_;
goto v_resetjp_4990_;
}
v___jp_4984_:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = lean_box(0);
v___x_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4985_);
return v___x_4986_;
}
v_resetjp_4990_:
{
size_t v_sz_4993_; size_t v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4997_; 
v_sz_4993_ = lean_array_size(v_decls_4988_);
v___x_4994_ = ((size_t)0ULL);
lean_inc_ref(v_decls_4988_);
v___x_4995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_4993_, v___x_4994_, v_decls_4988_);
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 0, v___x_4995_);
v___x_4997_ = v___x_4991_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_4995_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v_funVals_4989_);
v___x_4997_ = v_reuseFailAlloc_5028_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = lean_st_ref_put(v_a_4978_, v___x_4997_);
v___x_4999_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; uint8_t v___x_5001_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref_known(v___x_4999_, 1);
v___x_5001_ = lean_unbox(v_a_5000_);
lean_dec(v_a_5000_);
if (v___x_5001_ == 0)
{
lean_object* v_toCold_5002_; lean_object* v_options_5003_; uint8_t v_hasTrace_5004_; 
v_toCold_5002_ = lean_ctor_get(v_a_4981_, 0);
v_options_5003_ = lean_ctor_get(v_toCold_5002_, 2);
v_hasTrace_5004_ = lean_ctor_get_uint8(v_options_5003_, sizeof(void*)*1);
if (v_hasTrace_5004_ == 0)
{
lean_dec(v_n_4976_);
goto v___jp_4984_;
}
else
{
lean_object* v_inheritedTraceOptions_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
v_inheritedTraceOptions_5005_ = lean_ctor_get(v_toCold_5002_, 11);
v___x_5006_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5007_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5005_, v_options_5003_, v___x_5007_);
if (v___x_5008_ == 0)
{
lean_dec(v_n_4976_);
goto v___jp_4984_;
}
else
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5009_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5010_ = l_Nat_reprFast(v_n_4976_);
v___x_5011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5010_);
v___x_5012_ = l_Lean_MessageData_ofFormat(v___x_5011_);
v___x_5013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5009_);
lean_ctor_set(v___x_5013_, 1, v___x_5012_);
v___x_5014_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5013_);
lean_ctor_set(v___x_5015_, 1, v___x_5014_);
v___x_5016_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5006_, v___x_5015_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_dec_ref_known(v___x_5016_, 1);
goto v___jp_4984_;
}
else
{
return v___x_5016_;
}
}
}
}
else
{
lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5017_ = lean_unsigned_to_nat(1u);
v___x_5018_ = lean_nat_add(v_n_4976_, v___x_5017_);
lean_dec(v_n_4976_);
v_n_4976_ = v___x_5018_;
goto _start;
}
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec(v_n_4976_);
v_a_5020_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_4999_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_4999_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
lean_dec(v_a_5037_);
lean_dec_ref(v_a_5036_);
lean_dec(v_a_5035_);
lean_dec_ref(v_a_5034_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
return v_res_5039_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5040_; 
v___x_5040_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5041_){
_start:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5042_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5043_ = lean_panic_fn_borrowed(v___x_5042_, v_msg_5041_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5044_, lean_object* v_msg_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v_ref_5051_; lean_object* v___x_5052_; lean_object* v_env_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v_ref_5051_ = lean_ctor_get(v___y_5048_, 2);
v___x_5052_ = lean_st_ref_get(v___y_5049_);
v_env_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc_ref(v_env_5053_);
lean_dec(v___x_5052_);
v___x_5054_ = lean_st_ref_get(v___y_5047_);
v___x_5055_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5046_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5115_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5058_ = v___x_5055_;
v_isShared_5059_ = v_isSharedCheck_5115_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5055_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5115_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v_lctx_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5113_; 
v_lctx_5060_ = lean_ctor_get(v___x_5054_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5113_ == 0)
{
lean_object* v_unused_5114_; 
v_unused_5114_ = lean_ctor_get(v___x_5054_, 1);
lean_dec(v_unused_5114_);
v___x_5062_ = v___x_5054_;
v_isShared_5063_ = v_isSharedCheck_5113_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_lctx_5060_);
lean_dec(v___x_5054_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5113_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
uint8_t v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5064_ = lean_unbox(v_a_5056_);
lean_dec(v_a_5056_);
v___x_5065_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5060_, v___x_5064_);
lean_dec_ref(v_lctx_5060_);
v___x_5066_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5048_);
v___x_5067_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
v___x_5068_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5068_, 0, v_env_5053_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
lean_ctor_set(v___x_5068_, 2, v___x_5065_);
lean_ctor_set(v___x_5068_, 3, v___x_5066_);
if (v_isShared_5063_ == 0)
{
lean_ctor_set_tag(v___x_5062_, 3);
lean_ctor_set(v___x_5062_, 1, v_msg_5045_);
lean_ctor_set(v___x_5062_, 0, v___x_5068_);
v___x_5070_ = v___x_5062_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v_msg_5045_);
v___x_5070_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5071_; lean_object* v_traceState_5072_; lean_object* v_env_5073_; lean_object* v_nextMacroScope_5074_; lean_object* v_ngen_5075_; lean_object* v_auxDeclNGen_5076_; lean_object* v_cache_5077_; lean_object* v_recordedDeps_5078_; lean_object* v_messages_5079_; lean_object* v_infoState_5080_; lean_object* v_snapshotTasks_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5111_; 
v___x_5071_ = lean_st_ref_take(v___y_5049_);
v_traceState_5072_ = lean_ctor_get(v___x_5071_, 4);
v_env_5073_ = lean_ctor_get(v___x_5071_, 0);
v_nextMacroScope_5074_ = lean_ctor_get(v___x_5071_, 1);
v_ngen_5075_ = lean_ctor_get(v___x_5071_, 2);
v_auxDeclNGen_5076_ = lean_ctor_get(v___x_5071_, 3);
v_cache_5077_ = lean_ctor_get(v___x_5071_, 5);
v_recordedDeps_5078_ = lean_ctor_get(v___x_5071_, 6);
v_messages_5079_ = lean_ctor_get(v___x_5071_, 7);
v_infoState_5080_ = lean_ctor_get(v___x_5071_, 8);
v_snapshotTasks_5081_ = lean_ctor_get(v___x_5071_, 9);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5083_ = v___x_5071_;
v_isShared_5084_ = v_isSharedCheck_5111_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_snapshotTasks_5081_);
lean_inc(v_infoState_5080_);
lean_inc(v_messages_5079_);
lean_inc(v_recordedDeps_5078_);
lean_inc(v_cache_5077_);
lean_inc(v_traceState_5072_);
lean_inc(v_auxDeclNGen_5076_);
lean_inc(v_ngen_5075_);
lean_inc(v_nextMacroScope_5074_);
lean_inc(v_env_5073_);
lean_dec(v___x_5071_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5111_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
uint64_t v_tid_5085_; lean_object* v_traces_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5110_; 
v_tid_5085_ = lean_ctor_get_uint64(v_traceState_5072_, sizeof(void*)*1);
v_traces_5086_ = lean_ctor_get(v_traceState_5072_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v_traceState_5072_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5088_ = v_traceState_5072_;
v_isShared_5089_ = v_isSharedCheck_5110_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_traces_5086_);
lean_dec(v_traceState_5072_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5110_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; double v___x_5092_; uint8_t v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5101_; 
v___x_5090_ = lean_box(0);
v___x_5091_ = lean_box(0);
v___x_5092_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5093_ = 0;
v___x_5094_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5095_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5095_, 0, v_cls_5044_);
lean_ctor_set(v___x_5095_, 1, v___x_5091_);
lean_ctor_set(v___x_5095_, 2, v___x_5094_);
lean_ctor_set_float(v___x_5095_, sizeof(void*)*3, v___x_5092_);
lean_ctor_set_float(v___x_5095_, sizeof(void*)*3 + 8, v___x_5092_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*3 + 16, v___x_5093_);
v___x_5096_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5097_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5095_);
lean_ctor_set(v___x_5097_, 1, v___x_5070_);
lean_ctor_set(v___x_5097_, 2, v___x_5096_);
lean_inc(v_ref_5051_);
v___x_5098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5098_, 0, v_ref_5051_);
lean_ctor_set(v___x_5098_, 1, v___x_5097_);
v___x_5099_ = l_Lean_PersistentArray_push___redArg(v_traces_5086_, v___x_5098_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 0, v___x_5099_);
v___x_5101_ = v___x_5088_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5099_);
lean_ctor_set_uint64(v_reuseFailAlloc_5109_, sizeof(void*)*1, v_tid_5085_);
v___x_5101_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_object* v___x_5103_; 
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 4, v___x_5101_);
v___x_5103_ = v___x_5083_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_env_5073_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v_nextMacroScope_5074_);
lean_ctor_set(v_reuseFailAlloc_5108_, 2, v_ngen_5075_);
lean_ctor_set(v_reuseFailAlloc_5108_, 3, v_auxDeclNGen_5076_);
lean_ctor_set(v_reuseFailAlloc_5108_, 4, v___x_5101_);
lean_ctor_set(v_reuseFailAlloc_5108_, 5, v_cache_5077_);
lean_ctor_set(v_reuseFailAlloc_5108_, 6, v_recordedDeps_5078_);
lean_ctor_set(v_reuseFailAlloc_5108_, 7, v_messages_5079_);
lean_ctor_set(v_reuseFailAlloc_5108_, 8, v_infoState_5080_);
lean_ctor_set(v_reuseFailAlloc_5108_, 9, v_snapshotTasks_5081_);
v___x_5103_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___x_5104_; lean_object* v___x_5106_; 
v___x_5104_ = lean_st_ref_put(v___y_5049_, v___x_5103_);
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5090_);
v___x_5106_ = v___x_5058_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5090_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
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
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec(v___x_5054_);
lean_dec_ref(v_env_5053_);
lean_dec_ref(v_msg_5045_);
lean_dec(v_cls_5044_);
v_a_5116_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5055_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5055_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5124_, lean_object* v_msg_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5124_, v_msg_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
lean_dec(v___y_5127_);
lean_dec_ref(v___y_5126_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5132_, size_t v_i_5133_, size_t v_stop_5134_, lean_object* v_b_5135_){
_start:
{
uint8_t v___x_5137_; 
v___x_5137_ = lean_usize_dec_eq(v_i_5133_, v_stop_5134_);
if (v___x_5137_ == 0)
{
lean_object* v_fst_5138_; lean_object* v_snd_5139_; lean_object* v___x_5140_; lean_object* v_snd_5141_; lean_object* v_fst_5142_; lean_object* v_fst_5143_; lean_object* v_snd_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5158_; 
v_fst_5138_ = lean_ctor_get(v_b_5135_, 0);
lean_inc(v_fst_5138_);
v_snd_5139_ = lean_ctor_get(v_b_5135_, 1);
lean_inc(v_snd_5139_);
lean_dec_ref(v_b_5135_);
v___x_5140_ = lean_array_uget_borrowed(v_as_5132_, v_i_5133_);
v_snd_5141_ = lean_ctor_get(v___x_5140_, 1);
lean_inc(v_snd_5141_);
v_fst_5142_ = lean_ctor_get(v___x_5140_, 0);
v_fst_5143_ = lean_ctor_get(v_snd_5141_, 0);
v_snd_5144_ = lean_ctor_get(v_snd_5141_, 1);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_snd_5141_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5146_ = v_snd_5141_;
v_isShared_5147_ = v_isSharedCheck_5158_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_snd_5144_);
lean_inc(v_fst_5143_);
lean_dec(v_snd_5141_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5158_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v_fvarId_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5153_; 
v_fvarId_5148_ = lean_ctor_get(v_fst_5142_, 0);
v___x_5149_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_5143_, v_fst_5138_);
lean_dec(v_fst_5143_);
v___x_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5150_, 0, v_snd_5144_);
lean_inc(v_fvarId_5148_);
v___x_5151_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5139_, v_fvarId_5148_, v___x_5150_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 1, v___x_5151_);
lean_ctor_set(v___x_5146_, 0, v___x_5149_);
v___x_5153_ = v___x_5146_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5149_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v___x_5151_);
v___x_5153_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
size_t v___x_5154_; size_t v___x_5155_; 
v___x_5154_ = ((size_t)1ULL);
v___x_5155_ = lean_usize_add(v_i_5133_, v___x_5154_);
v_i_5133_ = v___x_5155_;
v_b_5135_ = v___x_5153_;
goto _start;
}
}
}
else
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5159_, 0, v_b_5135_);
return v___x_5159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5160_, lean_object* v_i_5161_, lean_object* v_stop_5162_, lean_object* v_b_5163_, lean_object* v___y_5164_){
_start:
{
size_t v_i_boxed_5165_; size_t v_stop_boxed_5166_; lean_object* v_res_5167_; 
v_i_boxed_5165_ = lean_unbox_usize(v_i_5161_);
lean_dec(v_i_5161_);
v_stop_boxed_5166_ = lean_unbox_usize(v_stop_5162_);
lean_dec(v_stop_5162_);
v_res_5167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5160_, v_i_boxed_5165_, v_stop_boxed_5166_, v_b_5163_);
lean_dec_ref(v_as_5160_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5168_, lean_object* v_x_5169_){
_start:
{
if (lean_obj_tag(v_x_5169_) == 0)
{
lean_object* v___x_5170_; 
v___x_5170_ = lean_box(0);
return v___x_5170_;
}
else
{
lean_object* v_key_5171_; lean_object* v_value_5172_; lean_object* v_tail_5173_; uint8_t v___x_5174_; 
v_key_5171_ = lean_ctor_get(v_x_5169_, 0);
v_value_5172_ = lean_ctor_get(v_x_5169_, 1);
v_tail_5173_ = lean_ctor_get(v_x_5169_, 2);
v___x_5174_ = l_Lean_instBEqFVarId_beq(v_key_5171_, v_a_5168_);
if (v___x_5174_ == 0)
{
v_x_5169_ = v_tail_5173_;
goto _start;
}
else
{
lean_object* v___x_5176_; 
lean_inc(v_value_5172_);
v___x_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5176_, 0, v_value_5172_);
return v___x_5176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5177_, lean_object* v_x_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5177_, v_x_5178_);
lean_dec(v_x_5178_);
lean_dec(v_a_5177_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5180_, lean_object* v_a_5181_){
_start:
{
lean_object* v_buckets_5182_; lean_object* v___x_5183_; uint64_t v___x_5184_; uint64_t v___x_5185_; uint64_t v___x_5186_; uint64_t v_fold_5187_; uint64_t v___x_5188_; uint64_t v___x_5189_; uint64_t v___x_5190_; size_t v___x_5191_; size_t v___x_5192_; size_t v___x_5193_; size_t v___x_5194_; size_t v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
v_buckets_5182_ = lean_ctor_get(v_m_5180_, 1);
v___x_5183_ = lean_array_get_size(v_buckets_5182_);
v___x_5184_ = l_Lean_instHashableFVarId_hash(v_a_5181_);
v___x_5185_ = 32ULL;
v___x_5186_ = lean_uint64_shift_right(v___x_5184_, v___x_5185_);
v_fold_5187_ = lean_uint64_xor(v___x_5184_, v___x_5186_);
v___x_5188_ = 16ULL;
v___x_5189_ = lean_uint64_shift_right(v_fold_5187_, v___x_5188_);
v___x_5190_ = lean_uint64_xor(v_fold_5187_, v___x_5189_);
v___x_5191_ = lean_uint64_to_usize(v___x_5190_);
v___x_5192_ = lean_usize_of_nat(v___x_5183_);
v___x_5193_ = ((size_t)1ULL);
v___x_5194_ = lean_usize_sub(v___x_5192_, v___x_5193_);
v___x_5195_ = lean_usize_land(v___x_5191_, v___x_5194_);
v___x_5196_ = lean_array_uget_borrowed(v_buckets_5182_, v___x_5195_);
v___x_5197_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5181_, v___x_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5198_, v_a_5199_);
lean_dec(v_a_5199_);
lean_dec_ref(v_m_5198_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5201_, lean_object* v_as_5202_, size_t v_i_5203_, size_t v_stop_5204_, lean_object* v_b_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v_a_5212_; uint8_t v___x_5216_; 
v___x_5216_ = lean_usize_dec_eq(v_i_5203_, v_stop_5204_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; lean_object* v_fvarId_5218_; lean_object* v___x_5219_; 
v___x_5217_ = lean_array_uget_borrowed(v_as_5202_, v_i_5203_);
v_fvarId_5218_ = lean_ctor_get(v___x_5217_, 0);
v___x_5219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5201_, v_fvarId_5218_);
if (lean_obj_tag(v___x_5219_) == 1)
{
lean_object* v_val_5220_; lean_object* v___x_5221_; 
v_val_5220_ = lean_ctor_get(v___x_5219_, 0);
lean_inc(v_val_5220_);
lean_dec_ref_known(v___x_5219_, 1);
v___x_5221_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5220_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v_a_5222_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_a_5222_);
lean_dec_ref_known(v___x_5221_, 1);
if (lean_obj_tag(v_a_5222_) == 1)
{
lean_object* v_val_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v_val_5223_ = lean_ctor_get(v_a_5222_, 0);
lean_inc(v_val_5223_);
lean_dec_ref_known(v_a_5222_, 1);
lean_inc(v___x_5217_);
v___x_5224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5217_);
lean_ctor_set(v___x_5224_, 1, v_val_5223_);
v___x_5225_ = lean_array_push(v_b_5205_, v___x_5224_);
v_a_5212_ = v___x_5225_;
goto v___jp_5211_;
}
else
{
lean_dec(v_a_5222_);
v_a_5212_ = v_b_5205_;
goto v___jp_5211_;
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
lean_dec_ref(v_b_5205_);
v_a_5226_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5221_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5221_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
else
{
lean_dec(v___x_5219_);
v_a_5212_ = v_b_5205_;
goto v___jp_5211_;
}
}
else
{
lean_object* v___x_5234_; 
v___x_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5234_, 0, v_b_5205_);
return v___x_5234_;
}
v___jp_5211_:
{
size_t v___x_5213_; size_t v___x_5214_; 
v___x_5213_ = ((size_t)1ULL);
v___x_5214_ = lean_usize_add(v_i_5203_, v___x_5213_);
v_i_5203_ = v___x_5214_;
v_b_5205_ = v_a_5212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5235_, lean_object* v_as_5236_, lean_object* v_i_5237_, lean_object* v_stop_5238_, lean_object* v_b_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
size_t v_i_boxed_5245_; size_t v_stop_boxed_5246_; lean_object* v_res_5247_; 
v_i_boxed_5245_ = lean_unbox_usize(v_i_5237_);
lean_dec(v_i_5237_);
v_stop_boxed_5246_ = lean_unbox_usize(v_stop_5238_);
lean_dec(v_stop_5238_);
v_res_5247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5235_, v_as_5236_, v_i_boxed_5245_, v_stop_boxed_5246_, v_b_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec_ref(v_as_5236_);
lean_dec_ref(v_assignment_5235_);
return v_res_5247_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5250_, lean_object* v_as_5251_, lean_object* v_start_5252_, lean_object* v_stop_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v___x_5259_; uint8_t v___x_5260_; 
v___x_5259_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5260_ = lean_nat_dec_lt(v_start_5252_, v_stop_5253_);
if (v___x_5260_ == 0)
{
lean_object* v___x_5261_; 
v___x_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5259_);
return v___x_5261_;
}
else
{
lean_object* v___x_5262_; uint8_t v___x_5263_; 
v___x_5262_ = lean_array_get_size(v_as_5251_);
v___x_5263_ = lean_nat_dec_le(v_stop_5253_, v___x_5262_);
if (v___x_5263_ == 0)
{
uint8_t v___x_5264_; 
v___x_5264_ = lean_nat_dec_lt(v_start_5252_, v___x_5262_);
if (v___x_5264_ == 0)
{
lean_object* v___x_5265_; 
v___x_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5259_);
return v___x_5265_;
}
else
{
size_t v___x_5266_; size_t v___x_5267_; lean_object* v___x_5268_; 
v___x_5266_ = lean_usize_of_nat(v_start_5252_);
v___x_5267_ = lean_usize_of_nat(v___x_5262_);
v___x_5268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5250_, v_as_5251_, v___x_5266_, v___x_5267_, v___x_5259_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
return v___x_5268_;
}
}
else
{
size_t v___x_5269_; size_t v___x_5270_; lean_object* v___x_5271_; 
v___x_5269_ = lean_usize_of_nat(v_start_5252_);
v___x_5270_ = lean_usize_of_nat(v_stop_5253_);
v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5250_, v_as_5251_, v___x_5269_, v___x_5270_, v___x_5259_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
return v___x_5271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5272_, lean_object* v_as_5273_, lean_object* v_start_5274_, lean_object* v_stop_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5272_, v_as_5273_, v_start_5274_, v_stop_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v_stop_5275_);
lean_dec(v_start_5274_);
lean_dec_ref(v_as_5273_);
lean_dec_ref(v_assignment_5272_);
return v_res_5281_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5284_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5285_ = lean_unsigned_to_nat(9u);
v___x_5286_ = lean_unsigned_to_nat(650u);
v___x_5287_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5288_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5289_ = l_mkPanicMessageWithDecl(v___x_5288_, v___x_5287_, v___x_5286_, v___x_5285_, v___x_5284_);
return v___x_5289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5292_, lean_object* v_discrVal_5293_, lean_object* v_discr_5294_, lean_object* v_assignment_5295_, lean_object* v_i_5296_, lean_object* v_as_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_){
_start:
{
lean_object* v___x_5303_; uint8_t v___x_5304_; 
v___x_5303_ = lean_array_get_size(v_as_5297_);
v___x_5304_ = lean_nat_dec_lt(v_i_5296_, v___x_5303_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; 
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v___x_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5305_, 0, v_as_5297_);
return v___x_5305_;
}
else
{
lean_object* v_a_5306_; lean_object* v_a_5308_; 
v_a_5306_ = lean_array_fget_borrowed(v_as_5297_, v_i_5296_);
if (lean_obj_tag(v_a_5306_) == 0)
{
lean_object* v_ctorName_5319_; lean_object* v_params_5320_; lean_object* v_code_5321_; uint8_t v___x_5322_; lean_object* v___y_5324_; lean_object* v___y_5325_; uint8_t v___x_5337_; 
v_ctorName_5319_ = lean_ctor_get(v_a_5306_, 0);
v_params_5320_ = lean_ctor_get(v_a_5306_, 1);
v_code_5321_ = lean_ctor_get(v_a_5306_, 2);
v___x_5322_ = 0;
v___x_5337_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5293_, v_ctorName_5319_);
if (v___x_5337_ == 0)
{
lean_object* v_toCold_5338_; lean_object* v_options_5339_; uint8_t v_hasTrace_5340_; 
v_toCold_5338_ = lean_ctor_get(v___y_5300_, 0);
v_options_5339_ = lean_ctor_get(v_toCold_5338_, 2);
v_hasTrace_5340_ = lean_ctor_get_uint8(v_options_5339_, sizeof(void*)*1);
if (v_hasTrace_5340_ == 0)
{
lean_inc_ref(v_code_5321_);
v___y_5324_ = v___y_5299_;
v___y_5325_ = v_code_5321_;
goto v___jp_5323_;
}
else
{
lean_object* v_inheritedTraceOptions_5341_; lean_object* v_cls_5342_; lean_object* v___x_5343_; uint8_t v___x_5344_; 
v_inheritedTraceOptions_5341_ = lean_ctor_get(v_toCold_5338_, 11);
v_cls_5342_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5343_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5344_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5341_, v_options_5339_, v___x_5343_);
if (v___x_5344_ == 0)
{
lean_inc_ref(v_code_5321_);
v___y_5324_ = v___y_5299_;
v___y_5325_ = v_code_5321_;
goto v___jp_5323_;
}
else
{
lean_object* v___x_5345_; 
lean_inc(v_discr_5294_);
v___x_5345_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5294_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
lean_inc(v_a_5346_);
lean_dec_ref_known(v___x_5345_, 1);
v___x_5347_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5348_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5346_, v___x_5344_);
v___x_5349_ = lean_string_append(v___x_5347_, v___x_5348_);
lean_dec_ref(v___x_5348_);
v___x_5350_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5351_ = lean_string_append(v___x_5349_, v___x_5350_);
lean_inc(v_ctorName_5319_);
v___x_5352_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5319_, v___x_5344_);
v___x_5353_ = lean_string_append(v___x_5351_, v___x_5352_);
lean_dec_ref(v___x_5352_);
v___x_5354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5354_, 0, v___x_5353_);
v___x_5355_ = l_Lean_MessageData_ofFormat(v___x_5354_);
v___x_5356_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5342_, v___x_5355_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_dec_ref_known(v___x_5356_, 1);
lean_inc_ref(v_code_5321_);
v___y_5324_ = v___y_5299_;
v___y_5325_ = v_code_5321_;
goto v___jp_5323_;
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5356_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5356_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5365_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5345_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5345_);
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
}
}
else
{
lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5373_ = lean_unsigned_to_nat(0u);
v___x_5374_ = lean_array_get_size(v_params_5320_);
v___x_5375_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5295_, v_params_5320_, v___x_5373_, v___x_5374_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5375_) == 0)
{
lean_object* v_a_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; lean_object* v_fst_5380_; lean_object* v_snd_5381_; 
v_a_5376_ = lean_ctor_get(v___x_5375_, 0);
lean_inc(v_a_5376_);
lean_dec_ref_known(v___x_5375_, 1);
v___x_5377_ = lean_array_get_size(v_a_5376_);
v___x_5378_ = lean_nat_dec_eq(v___x_5377_, v___x_5373_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5393_; 
lean_inc_ref(v_code_5321_);
v___x_5393_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5295_, v_code_5321_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v_a_5394_; lean_object* v___x_5395_; uint8_t v___x_5396_; 
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5394_);
lean_dec_ref_known(v___x_5393_, 1);
v___x_5395_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5396_ = lean_nat_dec_lt(v___x_5373_, v___x_5377_);
if (v___x_5396_ == 0)
{
lean_dec(v_a_5376_);
v_fst_5380_ = v_a_5394_;
v_snd_5381_ = v___x_5395_;
goto v___jp_5379_;
}
else
{
lean_object* v___x_5397_; size_t v___x_5398_; size_t v___x_5399_; lean_object* v___x_5400_; 
v___x_5397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5397_, 0, v_a_5394_);
lean_ctor_set(v___x_5397_, 1, v___x_5395_);
v___x_5398_ = ((size_t)0ULL);
v___x_5399_ = lean_usize_of_nat(v___x_5377_);
v___x_5400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5376_, v___x_5398_, v___x_5399_, v___x_5397_);
lean_dec(v_a_5376_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v_a_5401_; lean_object* v_fst_5402_; lean_object* v_snd_5403_; 
v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
lean_inc(v_a_5401_);
lean_dec_ref_known(v___x_5400_, 1);
v_fst_5402_ = lean_ctor_get(v_a_5401_, 0);
lean_inc(v_fst_5402_);
v_snd_5403_ = lean_ctor_get(v_a_5401_, 1);
lean_inc(v_snd_5403_);
lean_dec(v_a_5401_);
v_fst_5380_ = v_fst_5402_;
v_snd_5381_ = v_snd_5403_;
goto v___jp_5379_;
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5404_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5400_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5400_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
else
{
lean_object* v_a_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5419_; 
lean_dec(v_a_5376_);
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5412_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5414_ = v___x_5393_;
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_a_5412_);
lean_dec(v___x_5393_);
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
lean_object* v___x_5420_; 
lean_dec(v_a_5376_);
lean_inc_ref(v_code_5321_);
v___x_5420_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5295_, v_code_5321_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; lean_object* v___x_5422_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref_known(v___x_5420_, 1);
lean_inc_ref(v_a_5306_);
v___x_5422_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5306_, v_a_5421_);
v_a_5308_ = v___x_5422_;
goto v___jp_5307_;
}
else
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5430_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5423_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5425_ = v___x_5420_;
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v___x_5420_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5423_);
v___x_5428_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
return v___x_5428_;
}
}
}
}
v___jp_5379_:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5322_, v_fst_5380_, v_snd_5381_, v___x_5378_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
lean_dec_ref(v_snd_5381_);
if (lean_obj_tag(v___x_5382_) == 0)
{
lean_object* v_a_5383_; lean_object* v___x_5384_; 
v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
lean_inc(v_a_5383_);
lean_dec_ref_known(v___x_5382_, 1);
lean_inc_ref(v_a_5306_);
v___x_5384_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5306_, v_a_5383_);
v_a_5308_ = v___x_5384_;
goto v___jp_5307_;
}
else
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5385_ = lean_ctor_get(v___x_5382_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5382_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5382_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5382_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
}
else
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5438_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5431_ = lean_ctor_get(v___x_5375_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5375_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5433_ = v___x_5375_;
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5375_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5436_; 
if (v_isShared_5434_ == 0)
{
v___x_5436_ = v___x_5433_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
}
v___jp_5323_:
{
lean_object* v___x_5326_; 
v___x_5326_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5322_, v___y_5325_, v___y_5324_);
lean_dec_ref(v___y_5325_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v___x_5327_; lean_object* v___x_5328_; 
lean_dec_ref_known(v___x_5326_, 1);
lean_inc_ref(v_resultType_5292_);
v___x_5327_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5327_, 0, v_resultType_5292_);
lean_inc_ref(v_a_5306_);
v___x_5328_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5306_, v___x_5327_);
v_a_5308_ = v___x_5328_;
goto v___jp_5307_;
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
v_a_5329_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5326_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5326_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
}
else
{
lean_object* v_code_5439_; lean_object* v___x_5440_; 
v_code_5439_ = lean_ctor_get(v_a_5306_, 0);
lean_inc_ref(v_code_5439_);
v___x_5440_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5295_, v_code_5439_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v___x_5442_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v___x_5440_, 1);
lean_inc_ref(v_a_5306_);
v___x_5442_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5306_, v_a_5441_);
v_a_5308_ = v___x_5442_;
goto v___jp_5307_;
}
else
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5450_; 
lean_dec_ref(v_as_5297_);
lean_dec(v_i_5296_);
lean_dec(v_discr_5294_);
lean_dec_ref(v_resultType_5292_);
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
v___jp_5307_:
{
size_t v___x_5309_; size_t v___x_5310_; uint8_t v___x_5311_; 
v___x_5309_ = lean_ptr_addr(v_a_5306_);
v___x_5310_ = lean_ptr_addr(v_a_5308_);
v___x_5311_ = lean_usize_dec_eq(v___x_5309_, v___x_5310_);
if (v___x_5311_ == 0)
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5312_ = lean_unsigned_to_nat(1u);
v___x_5313_ = lean_nat_add(v_i_5296_, v___x_5312_);
v___x_5314_ = lean_array_fset(v_as_5297_, v_i_5296_, v_a_5308_);
lean_dec(v_i_5296_);
v_i_5296_ = v___x_5313_;
v_as_5297_ = v___x_5314_;
goto _start;
}
else
{
lean_object* v___x_5316_; lean_object* v___x_5317_; 
lean_dec_ref(v_a_5308_);
v___x_5316_ = lean_unsigned_to_nat(1u);
v___x_5317_ = lean_nat_add(v_i_5296_, v___x_5316_);
lean_dec(v_i_5296_);
v_i_5296_ = v___x_5317_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5451_, lean_object* v_code_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v_decl_5459_; lean_object* v_k_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___y_5464_; 
switch(lean_obj_tag(v_code_5452_))
{
case 0:
{
lean_object* v_decl_5572_; lean_object* v_k_5573_; lean_object* v___x_5574_; 
v_decl_5572_ = lean_ctor_get(v_code_5452_, 0);
v_k_5573_ = lean_ctor_get(v_code_5452_, 1);
lean_inc_ref(v_k_5573_);
v___x_5574_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5451_, v_k_5573_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5611_; 
v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5577_ = v___x_5574_;
v_isShared_5578_ = v_isSharedCheck_5611_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5574_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5611_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
size_t v___x_5579_; size_t v___x_5580_; uint8_t v___x_5581_; 
v___x_5579_ = lean_ptr_addr(v_k_5573_);
v___x_5580_ = lean_ptr_addr(v_a_5575_);
v___x_5581_ = lean_usize_dec_eq(v___x_5579_, v___x_5580_);
if (v___x_5581_ == 0)
{
lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5591_; 
lean_inc_ref(v_decl_5572_);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_code_5452_);
if (v_isSharedCheck_5591_ == 0)
{
lean_object* v_unused_5592_; lean_object* v_unused_5593_; 
v_unused_5592_ = lean_ctor_get(v_code_5452_, 1);
lean_dec(v_unused_5592_);
v_unused_5593_ = lean_ctor_get(v_code_5452_, 0);
lean_dec(v_unused_5593_);
v___x_5583_ = v_code_5452_;
v_isShared_5584_ = v_isSharedCheck_5591_;
goto v_resetjp_5582_;
}
else
{
lean_dec(v_code_5452_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5591_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5584_ == 0)
{
lean_ctor_set(v___x_5583_, 1, v_a_5575_);
v___x_5586_ = v___x_5583_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_decl_5572_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v_a_5575_);
v___x_5586_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
lean_object* v___x_5588_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 0, v___x_5586_);
v___x_5588_ = v___x_5577_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5586_);
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
else
{
size_t v___x_5594_; uint8_t v___x_5595_; 
v___x_5594_ = lean_ptr_addr(v_decl_5572_);
v___x_5595_ = lean_usize_dec_eq(v___x_5594_, v___x_5594_);
if (v___x_5595_ == 0)
{
lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5605_; 
lean_inc_ref(v_decl_5572_);
v_isSharedCheck_5605_ = !lean_is_exclusive(v_code_5452_);
if (v_isSharedCheck_5605_ == 0)
{
lean_object* v_unused_5606_; lean_object* v_unused_5607_; 
v_unused_5606_ = lean_ctor_get(v_code_5452_, 1);
lean_dec(v_unused_5606_);
v_unused_5607_ = lean_ctor_get(v_code_5452_, 0);
lean_dec(v_unused_5607_);
v___x_5597_ = v_code_5452_;
v_isShared_5598_ = v_isSharedCheck_5605_;
goto v_resetjp_5596_;
}
else
{
lean_dec(v_code_5452_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5605_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v___x_5600_; 
if (v_isShared_5598_ == 0)
{
lean_ctor_set(v___x_5597_, 1, v_a_5575_);
v___x_5600_ = v___x_5597_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_decl_5572_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v_a_5575_);
v___x_5600_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
lean_object* v___x_5602_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 0, v___x_5600_);
v___x_5602_ = v___x_5577_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5600_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
else
{
lean_object* v___x_5609_; 
lean_dec(v_a_5575_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 0, v_code_5452_);
v___x_5609_ = v___x_5577_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_code_5452_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_5452_, 2);
return v___x_5574_;
}
}
case 1:
{
lean_object* v_decl_5612_; lean_object* v_k_5613_; 
v_decl_5612_ = lean_ctor_get(v_code_5452_, 0);
v_k_5613_ = lean_ctor_get(v_code_5452_, 1);
lean_inc_ref(v_k_5613_);
lean_inc_ref(v_decl_5612_);
v_decl_5459_ = v_decl_5612_;
v_k_5460_ = v_k_5613_;
v___y_5461_ = v_a_5453_;
v___y_5462_ = v_a_5454_;
v___y_5463_ = v_a_5455_;
v___y_5464_ = v_a_5456_;
goto v___jp_5458_;
}
case 2:
{
lean_object* v_decl_5614_; lean_object* v_k_5615_; 
v_decl_5614_ = lean_ctor_get(v_code_5452_, 0);
v_k_5615_ = lean_ctor_get(v_code_5452_, 1);
lean_inc_ref(v_k_5615_);
lean_inc_ref(v_decl_5614_);
v_decl_5459_ = v_decl_5614_;
v_k_5460_ = v_k_5615_;
v___y_5461_ = v_a_5453_;
v___y_5462_ = v_a_5454_;
v___y_5463_ = v_a_5455_;
v___y_5464_ = v_a_5456_;
goto v___jp_5458_;
}
case 4:
{
lean_object* v_cases_5616_; lean_object* v_typeName_5617_; lean_object* v_resultType_5618_; lean_object* v_discr_5619_; lean_object* v_alts_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5661_; 
v_cases_5616_ = lean_ctor_get(v_code_5452_, 0);
lean_inc_ref(v_cases_5616_);
v_typeName_5617_ = lean_ctor_get(v_cases_5616_, 0);
v_resultType_5618_ = lean_ctor_get(v_cases_5616_, 1);
v_discr_5619_ = lean_ctor_get(v_cases_5616_, 2);
v_alts_5620_ = lean_ctor_get(v_cases_5616_, 3);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_cases_5616_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5622_ = v_cases_5616_;
v_isShared_5623_ = v_isSharedCheck_5661_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_alts_5620_);
lean_inc(v_discr_5619_);
lean_inc(v_resultType_5618_);
lean_inc(v_typeName_5617_);
lean_dec(v_cases_5616_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5661_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5624_; lean_object* v_discrVal_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v___x_5624_ = lean_box(0);
v_discrVal_5625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5451_, v_discr_5619_, v___x_5624_);
v___x_5626_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5620_);
lean_inc(v_discr_5619_);
lean_inc_ref(v_resultType_5618_);
v___x_5627_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5618_, v_discrVal_5625_, v_discr_5619_, v_assignment_5451_, v___x_5626_, v_alts_5620_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_);
lean_dec(v_discrVal_5625_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5652_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5630_ = v___x_5627_;
v_isShared_5631_ = v_isSharedCheck_5652_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_a_5628_);
lean_dec(v___x_5627_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5652_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
size_t v___x_5632_; size_t v___x_5633_; uint8_t v___x_5634_; 
v___x_5632_ = lean_ptr_addr(v_alts_5620_);
lean_dec_ref(v_alts_5620_);
v___x_5633_ = lean_ptr_addr(v_a_5628_);
v___x_5634_ = lean_usize_dec_eq(v___x_5632_, v___x_5633_);
if (v___x_5634_ == 0)
{
lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5647_; 
v_isSharedCheck_5647_ = !lean_is_exclusive(v_code_5452_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; 
v_unused_5648_ = lean_ctor_get(v_code_5452_, 0);
lean_dec(v_unused_5648_);
v___x_5636_ = v_code_5452_;
v_isShared_5637_ = v_isSharedCheck_5647_;
goto v_resetjp_5635_;
}
else
{
lean_dec(v_code_5452_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5647_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5639_; 
if (v_isShared_5623_ == 0)
{
lean_ctor_set(v___x_5622_, 3, v_a_5628_);
v___x_5639_ = v___x_5622_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_typeName_5617_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_resultType_5618_);
lean_ctor_set(v_reuseFailAlloc_5646_, 2, v_discr_5619_);
lean_ctor_set(v_reuseFailAlloc_5646_, 3, v_a_5628_);
v___x_5639_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
lean_object* v___x_5641_; 
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 0, v___x_5639_);
v___x_5641_ = v___x_5636_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v___x_5639_);
v___x_5641_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
lean_object* v___x_5643_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v___x_5641_);
v___x_5643_ = v___x_5630_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5641_);
v___x_5643_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
return v___x_5643_;
}
}
}
}
}
else
{
lean_object* v___x_5650_; 
lean_dec(v_a_5628_);
lean_del_object(v___x_5622_);
lean_dec(v_discr_5619_);
lean_dec_ref(v_resultType_5618_);
lean_dec(v_typeName_5617_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v_code_5452_);
v___x_5650_ = v___x_5630_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_code_5452_);
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
lean_object* v_a_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5660_; 
lean_del_object(v___x_5622_);
lean_dec_ref(v_alts_5620_);
lean_dec(v_discr_5619_);
lean_dec_ref(v_resultType_5618_);
lean_dec(v_typeName_5617_);
lean_dec_ref_known(v_code_5452_, 1);
v_a_5653_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5660_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5660_ == 0)
{
v___x_5655_ = v___x_5627_;
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_a_5653_);
lean_dec(v___x_5627_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5658_; 
if (v_isShared_5656_ == 0)
{
v___x_5658_ = v___x_5655_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
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
}
default: 
{
lean_object* v___x_5662_; 
v___x_5662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5662_, 0, v_code_5452_);
return v___x_5662_;
}
}
v___jp_5458_:
{
lean_object* v_params_5465_; lean_object* v_type_5466_; lean_object* v_value_5467_; uint8_t v___x_5468_; lean_object* v___x_5469_; 
v_params_5465_ = lean_ctor_get(v_decl_5459_, 2);
lean_inc_ref(v_params_5465_);
v_type_5466_ = lean_ctor_get(v_decl_5459_, 3);
lean_inc_ref(v_type_5466_);
v_value_5467_ = lean_ctor_get(v_decl_5459_, 4);
v___x_5468_ = 0;
lean_inc_ref(v_value_5467_);
v___x_5469_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5451_, v_value_5467_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5471_; 
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
lean_inc(v_a_5470_);
lean_dec_ref_known(v___x_5469_, 1);
v___x_5471_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5468_, v_decl_5459_, v_type_5466_, v_params_5465_, v_a_5470_, v___y_5462_);
if (lean_obj_tag(v___x_5471_) == 0)
{
lean_object* v_a_5472_; lean_object* v___x_5473_; 
v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v_a_5472_);
lean_dec_ref_known(v___x_5471_, 1);
v___x_5473_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5451_, v_k_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
if (lean_obj_tag(v___x_5473_) == 0)
{
switch(lean_obj_tag(v_code_5452_))
{
case 1:
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5513_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5476_ = v___x_5473_;
v_isShared_5477_ = v_isSharedCheck_5513_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5473_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5513_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v_decl_5478_; lean_object* v_k_5479_; size_t v___x_5480_; size_t v___x_5481_; uint8_t v___x_5482_; 
v_decl_5478_ = lean_ctor_get(v_code_5452_, 0);
v_k_5479_ = lean_ctor_get(v_code_5452_, 1);
v___x_5480_ = lean_ptr_addr(v_k_5479_);
v___x_5481_ = lean_ptr_addr(v_a_5474_);
v___x_5482_ = lean_usize_dec_eq(v___x_5480_, v___x_5481_);
if (v___x_5482_ == 0)
{
lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5492_; 
v_isSharedCheck_5492_ = !lean_is_exclusive(v_code_5452_);
if (v_isSharedCheck_5492_ == 0)
{
lean_object* v_unused_5493_; lean_object* v_unused_5494_; 
v_unused_5493_ = lean_ctor_get(v_code_5452_, 1);
lean_dec(v_unused_5493_);
v_unused_5494_ = lean_ctor_get(v_code_5452_, 0);
lean_dec(v_unused_5494_);
v___x_5484_ = v_code_5452_;
v_isShared_5485_ = v_isSharedCheck_5492_;
goto v_resetjp_5483_;
}
else
{
lean_dec(v_code_5452_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5492_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5487_; 
if (v_isShared_5485_ == 0)
{
lean_ctor_set(v___x_5484_, 1, v_a_5474_);
lean_ctor_set(v___x_5484_, 0, v_a_5472_);
v___x_5487_ = v___x_5484_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5472_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v_a_5474_);
v___x_5487_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
lean_object* v___x_5489_; 
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v___x_5487_);
v___x_5489_ = v___x_5476_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5487_);
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
else
{
size_t v___x_5495_; size_t v___x_5496_; uint8_t v___x_5497_; 
v___x_5495_ = lean_ptr_addr(v_decl_5478_);
v___x_5496_ = lean_ptr_addr(v_a_5472_);
v___x_5497_ = lean_usize_dec_eq(v___x_5495_, v___x_5496_);
if (v___x_5497_ == 0)
{
lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5507_; 
v_isSharedCheck_5507_ = !lean_is_exclusive(v_code_5452_);
if (v_isSharedCheck_5507_ == 0)
{
lean_object* v_unused_5508_; lean_object* v_unused_5509_; 
v_unused_5508_ = lean_ctor_get(v_code_5452_, 1);
lean_dec(v_unused_5508_);
v_unused_5509_ = lean_ctor_get(v_code_5452_, 0);
lean_dec(v_unused_5509_);
v___x_5499_ = v_code_5452_;
v_isShared_5500_ = v_isSharedCheck_5507_;
goto v_resetjp_5498_;
}
else
{
lean_dec(v_code_5452_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5507_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5502_; 
if (v_isShared_5500_ == 0)
{
lean_ctor_set(v___x_5499_, 1, v_a_5474_);
lean_ctor_set(v___x_5499_, 0, v_a_5472_);
v___x_5502_ = v___x_5499_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5472_);
lean_ctor_set(v_reuseFailAlloc_5506_, 1, v_a_5474_);
v___x_5502_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5504_; 
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v___x_5502_);
v___x_5504_ = v___x_5476_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
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
else
{
lean_object* v___x_5511_; 
lean_dec(v_a_5474_);
lean_dec(v_a_5472_);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v_code_5452_);
v___x_5511_ = v___x_5476_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_code_5452_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
}
case 2:
{
lean_object* v_a_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5553_; 
v_a_5514_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5516_ = v___x_5473_;
v_isShared_5517_ = v_isSharedCheck_5553_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_a_5514_);
lean_dec(v___x_5473_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5553_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v_decl_5518_; lean_object* v_k_5519_; size_t v___x_5520_; size_t v___x_5521_; uint8_t v___x_5522_; 
v_decl_5518_ = lean_ctor_get(v_code_5452_, 0);
v_k_5519_ = lean_ctor_get(v_code_5452_, 1);
v___x_5520_ = lean_ptr_addr(v_k_5519_);
v___x_5521_ = lean_ptr_addr(v_a_5514_);
v___x_5522_ = lean_usize_dec_eq(v___x_5520_, v___x_5521_);
if (v___x_5522_ == 0)
{
lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5532_; 
v_isSharedCheck_5532_ = !lean_is_exclusive(v_code_5452_);
if (v_isSharedCheck_5532_ == 0)
{
lean_object* v_unused_5533_; lean_object* v_unused_5534_; 
v_unused_5533_ = lean_ctor_get(v_code_5452_, 1);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_code_5452_, 0);
lean_dec(v_unused_5534_);
v___x_5524_ = v_code_5452_;
v_isShared_5525_ = v_isSharedCheck_5532_;
goto v_resetjp_5523_;
}
else
{
lean_dec(v_code_5452_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5532_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5527_; 
if (v_isShared_5525_ == 0)
{
lean_ctor_set(v___x_5524_, 1, v_a_5514_);
lean_ctor_set(v___x_5524_, 0, v_a_5472_);
v___x_5527_ = v___x_5524_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_a_5472_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v_a_5514_);
v___x_5527_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
lean_object* v___x_5529_; 
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 0, v___x_5527_);
v___x_5529_ = v___x_5516_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5527_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
else
{
size_t v___x_5535_; size_t v___x_5536_; uint8_t v___x_5537_; 
v___x_5535_ = lean_ptr_addr(v_decl_5518_);
v___x_5536_ = lean_ptr_addr(v_a_5472_);
v___x_5537_ = lean_usize_dec_eq(v___x_5535_, v___x_5536_);
if (v___x_5537_ == 0)
{
lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5547_; 
v_isSharedCheck_5547_ = !lean_is_exclusive(v_code_5452_);
if (v_isSharedCheck_5547_ == 0)
{
lean_object* v_unused_5548_; lean_object* v_unused_5549_; 
v_unused_5548_ = lean_ctor_get(v_code_5452_, 1);
lean_dec(v_unused_5548_);
v_unused_5549_ = lean_ctor_get(v_code_5452_, 0);
lean_dec(v_unused_5549_);
v___x_5539_ = v_code_5452_;
v_isShared_5540_ = v_isSharedCheck_5547_;
goto v_resetjp_5538_;
}
else
{
lean_dec(v_code_5452_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5547_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5542_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 1, v_a_5514_);
lean_ctor_set(v___x_5539_, 0, v_a_5472_);
v___x_5542_ = v___x_5539_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5472_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v_a_5514_);
v___x_5542_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5544_; 
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 0, v___x_5542_);
v___x_5544_ = v___x_5516_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v___x_5542_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
lean_object* v___x_5551_; 
lean_dec(v_a_5514_);
lean_dec(v_a_5472_);
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 0, v_code_5452_);
v___x_5551_ = v___x_5516_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_code_5452_);
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
}
default: 
{
lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5562_; 
lean_dec(v_a_5472_);
lean_dec_ref(v_code_5452_);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5562_ == 0)
{
lean_object* v_unused_5563_; 
v_unused_5563_ = lean_ctor_get(v___x_5473_, 0);
lean_dec(v_unused_5563_);
v___x_5555_ = v___x_5473_;
v_isShared_5556_ = v_isSharedCheck_5562_;
goto v_resetjp_5554_;
}
else
{
lean_dec(v___x_5473_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5562_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5560_; 
v___x_5557_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5558_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5557_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 0, v___x_5558_);
v___x_5560_ = v___x_5555_;
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
}
else
{
lean_dec(v_a_5472_);
lean_dec_ref(v_code_5452_);
return v___x_5473_;
}
}
else
{
lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5571_; 
lean_dec_ref(v_k_5460_);
lean_dec_ref(v_code_5452_);
v_a_5564_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5571_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5571_ == 0)
{
v___x_5566_ = v___x_5471_;
v_isShared_5567_ = v_isSharedCheck_5571_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_dec(v___x_5471_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5571_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5569_; 
if (v_isShared_5567_ == 0)
{
v___x_5569_ = v___x_5566_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5564_);
v___x_5569_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
return v___x_5569_;
}
}
}
}
else
{
lean_dec_ref(v_type_5466_);
lean_dec_ref(v_params_5465_);
lean_dec_ref(v_k_5460_);
lean_dec_ref(v_decl_5459_);
lean_dec_ref(v_code_5452_);
return v___x_5469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5663_, lean_object* v_code_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5663_, v_code_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
lean_dec(v_a_5668_);
lean_dec_ref(v_a_5667_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
lean_dec_ref(v_assignment_5663_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5671_, lean_object* v_discrVal_5672_, lean_object* v_discr_5673_, lean_object* v_assignment_5674_, lean_object* v_i_5675_, lean_object* v_as_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
lean_object* v_res_5682_; 
v_res_5682_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5671_, v_discrVal_5672_, v_discr_5673_, v_assignment_5674_, v_i_5675_, v_as_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec_ref(v_assignment_5674_);
lean_dec(v_discrVal_5672_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5683_, lean_object* v_m_5684_, lean_object* v_a_5685_){
_start:
{
lean_object* v___x_5686_; 
v___x_5686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5684_, v_a_5685_);
return v___x_5686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5687_, lean_object* v_m_5688_, lean_object* v_a_5689_){
_start:
{
lean_object* v_res_5690_; 
v_res_5690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5687_, v_m_5688_, v_a_5689_);
lean_dec(v_a_5689_);
lean_dec_ref(v_m_5688_);
return v_res_5690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5691_, size_t v_i_5692_, size_t v_stop_5693_, lean_object* v_b_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_){
_start:
{
lean_object* v___x_5700_; 
v___x_5700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5691_, v_i_5692_, v_stop_5693_, v_b_5694_);
return v___x_5700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5701_, lean_object* v_i_5702_, lean_object* v_stop_5703_, lean_object* v_b_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
size_t v_i_boxed_5710_; size_t v_stop_boxed_5711_; lean_object* v_res_5712_; 
v_i_boxed_5710_ = lean_unbox_usize(v_i_5702_);
lean_dec(v_i_5702_);
v_stop_boxed_5711_ = lean_unbox_usize(v_stop_5703_);
lean_dec(v_stop_5703_);
v_res_5712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5701_, v_i_boxed_5710_, v_stop_boxed_5711_, v_b_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec(v___y_5706_);
lean_dec_ref(v___y_5705_);
lean_dec_ref(v_as_5701_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5713_, lean_object* v_a_5714_, lean_object* v_x_5715_){
_start:
{
lean_object* v___x_5716_; 
v___x_5716_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5714_, v_x_5715_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5717_, lean_object* v_a_5718_, lean_object* v_x_5719_){
_start:
{
lean_object* v_res_5720_; 
v_res_5720_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5717_, v_a_5718_, v_x_5719_);
lean_dec(v_x_5719_);
lean_dec(v_a_5718_);
return v_res_5720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5721_, lean_object* v_v_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
if (lean_obj_tag(v_v_5722_) == 0)
{
lean_object* v_code_5728_; lean_object* v___x_5730_; uint8_t v_isShared_5731_; uint8_t v_isSharedCheck_5752_; 
v_code_5728_ = lean_ctor_get(v_v_5722_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v_v_5722_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5730_ = v_v_5722_;
v_isShared_5731_ = v_isSharedCheck_5752_;
goto v_resetjp_5729_;
}
else
{
lean_inc(v_code_5728_);
lean_dec(v_v_5722_);
v___x_5730_ = lean_box(0);
v_isShared_5731_ = v_isSharedCheck_5752_;
goto v_resetjp_5729_;
}
v_resetjp_5729_:
{
lean_object* v___x_5732_; 
lean_inc(v___y_5726_);
lean_inc_ref(v___y_5725_);
lean_inc(v___y_5724_);
lean_inc_ref(v___y_5723_);
v___x_5732_ = lean_apply_6(v_f_5721_, v_code_5728_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, lean_box(0));
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5743_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5743_ == 0)
{
v___x_5735_ = v___x_5732_;
v_isShared_5736_ = v_isSharedCheck_5743_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5732_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5743_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 0, v_a_5733_);
v___x_5738_ = v___x_5730_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
lean_object* v___x_5740_; 
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 0, v___x_5738_);
v___x_5740_ = v___x_5735_;
goto v_reusejp_5739_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5738_);
v___x_5740_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5739_;
}
v_reusejp_5739_:
{
return v___x_5740_;
}
}
}
}
else
{
lean_object* v_a_5744_; lean_object* v___x_5746_; uint8_t v_isShared_5747_; uint8_t v_isSharedCheck_5751_; 
lean_del_object(v___x_5730_);
v_a_5744_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5746_ = v___x_5732_;
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
else
{
lean_inc(v_a_5744_);
lean_dec(v___x_5732_);
v___x_5746_ = lean_box(0);
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
v_resetjp_5745_:
{
lean_object* v___x_5749_; 
if (v_isShared_5747_ == 0)
{
v___x_5749_ = v___x_5746_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_a_5744_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
}
}
else
{
lean_object* v___x_5753_; 
lean_dec_ref(v_f_5721_);
v___x_5753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5753_, 0, v_v_5722_);
return v___x_5753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5754_, lean_object* v_v_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v_res_5761_; 
v_res_5761_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5754_, v_v_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
lean_dec(v___y_5759_);
lean_dec_ref(v___y_5758_);
lean_dec(v___y_5757_);
lean_dec_ref(v___y_5756_);
return v_res_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5762_, lean_object* v_f_5763_, lean_object* v_v_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_){
_start:
{
lean_object* v___x_5770_; 
v___x_5770_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5763_, v_v_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_);
return v___x_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5771_, lean_object* v_f_5772_, lean_object* v_v_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_){
_start:
{
uint8_t v_pu_boxed_5779_; lean_object* v_res_5780_; 
v_pu_boxed_5779_ = lean_unbox(v_pu_5771_);
v_res_5780_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5779_, v_f_5772_, v_v_5773_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_);
lean_dec(v___y_5777_);
lean_dec_ref(v___y_5776_);
lean_dec(v___y_5775_);
lean_dec_ref(v___y_5774_);
return v_res_5780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5781_, lean_object* v_x_5782_){
_start:
{
if (lean_obj_tag(v_x_5782_) == 0)
{
return v_x_5781_;
}
else
{
lean_object* v_key_5783_; lean_object* v_value_5784_; lean_object* v_tail_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; 
v_key_5783_ = lean_ctor_get(v_x_5782_, 0);
v_value_5784_ = lean_ctor_get(v_x_5782_, 1);
v_tail_5785_ = lean_ctor_get(v_x_5782_, 2);
lean_inc(v_value_5784_);
lean_inc(v_key_5783_);
v___x_5786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5786_, 0, v_key_5783_);
lean_ctor_set(v___x_5786_, 1, v_value_5784_);
v___x_5787_ = lean_array_push(v_x_5781_, v___x_5786_);
v_x_5781_ = v___x_5787_;
v_x_5782_ = v_tail_5785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5789_, lean_object* v_x_5790_){
_start:
{
lean_object* v_res_5791_; 
v_res_5791_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5789_, v_x_5790_);
lean_dec(v_x_5790_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5792_, size_t v_i_5793_, size_t v_stop_5794_, lean_object* v_b_5795_){
_start:
{
uint8_t v___x_5796_; 
v___x_5796_ = lean_usize_dec_eq(v_i_5793_, v_stop_5794_);
if (v___x_5796_ == 0)
{
lean_object* v___x_5797_; lean_object* v___x_5798_; size_t v___x_5799_; size_t v___x_5800_; 
v___x_5797_ = lean_array_uget_borrowed(v_as_5792_, v_i_5793_);
v___x_5798_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5795_, v___x_5797_);
v___x_5799_ = ((size_t)1ULL);
v___x_5800_ = lean_usize_add(v_i_5793_, v___x_5799_);
v_i_5793_ = v___x_5800_;
v_b_5795_ = v___x_5798_;
goto _start;
}
else
{
return v_b_5795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5802_, lean_object* v_i_5803_, lean_object* v_stop_5804_, lean_object* v_b_5805_){
_start:
{
size_t v_i_boxed_5806_; size_t v_stop_boxed_5807_; lean_object* v_res_5808_; 
v_i_boxed_5806_ = lean_unbox_usize(v_i_5803_);
lean_dec(v_i_5803_);
v_stop_boxed_5807_ = lean_unbox_usize(v_stop_5804_);
lean_dec(v_stop_5804_);
v_res_5808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5802_, v_i_boxed_5806_, v_stop_boxed_5807_, v_b_5805_);
lean_dec_ref(v_as_5802_);
return v_res_5808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5809_, size_t v_sz_5810_, size_t v_i_5811_, lean_object* v_bs_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_){
_start:
{
uint8_t v___x_5818_; 
v___x_5818_ = lean_usize_dec_lt(v_i_5811_, v_sz_5810_);
if (v___x_5818_ == 0)
{
lean_object* v___x_5819_; 
v___x_5819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5819_, 0, v_bs_5812_);
return v___x_5819_;
}
else
{
lean_object* v_v_5820_; lean_object* v_fst_5821_; lean_object* v_snd_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5846_; 
v_v_5820_ = lean_array_uget(v_bs_5812_, v_i_5811_);
v_fst_5821_ = lean_ctor_get(v_v_5820_, 0);
v_snd_5822_ = lean_ctor_get(v_v_5820_, 1);
v_isSharedCheck_5846_ = !lean_is_exclusive(v_v_5820_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5824_ = v_v_5820_;
v_isShared_5825_ = v_isSharedCheck_5846_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_snd_5822_);
lean_inc(v_fst_5821_);
lean_dec(v_v_5820_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5846_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5826_; lean_object* v_bs_x27_5827_; lean_object* v___x_5828_; 
v___x_5826_ = lean_unsigned_to_nat(0u);
v_bs_x27_5827_ = lean_array_uset(v_bs_5812_, v_i_5811_, v___x_5826_);
v___x_5828_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5821_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_);
if (lean_obj_tag(v___x_5828_) == 0)
{
lean_object* v_a_5829_; lean_object* v___x_5830_; lean_object* v___x_5832_; 
v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5829_);
lean_dec_ref_known(v___x_5828_, 1);
v___x_5830_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5829_, v_a_5809_);
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 0, v___x_5830_);
v___x_5832_ = v___x_5824_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5830_);
lean_ctor_set(v_reuseFailAlloc_5837_, 1, v_snd_5822_);
v___x_5832_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
size_t v___x_5833_; size_t v___x_5834_; lean_object* v___x_5835_; 
v___x_5833_ = ((size_t)1ULL);
v___x_5834_ = lean_usize_add(v_i_5811_, v___x_5833_);
v___x_5835_ = lean_array_uset(v_bs_x27_5827_, v_i_5811_, v___x_5832_);
v_i_5811_ = v___x_5834_;
v_bs_5812_ = v___x_5835_;
goto _start;
}
}
else
{
lean_object* v_a_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5845_; 
lean_dec_ref(v_bs_x27_5827_);
lean_del_object(v___x_5824_);
lean_dec(v_snd_5822_);
v_a_5838_ = lean_ctor_get(v___x_5828_, 0);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5828_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5840_ = v___x_5828_;
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_a_5838_);
lean_dec(v___x_5828_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5847_, lean_object* v_sz_5848_, lean_object* v_i_5849_, lean_object* v_bs_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_){
_start:
{
uint8_t v_a_2418__boxed_5856_; size_t v_sz_boxed_5857_; size_t v_i_boxed_5858_; lean_object* v_res_5859_; 
v_a_2418__boxed_5856_ = lean_unbox(v_a_5847_);
v_sz_boxed_5857_ = lean_unbox_usize(v_sz_5848_);
lean_dec(v_sz_5848_);
v_i_boxed_5858_ = lean_unbox_usize(v_i_5849_);
lean_dec(v_i_5849_);
v_res_5859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2418__boxed_5856_, v_sz_boxed_5857_, v_i_boxed_5858_, v_bs_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5860_){
_start:
{
lean_object* v_fst_5861_; lean_object* v_snd_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5885_; 
v_fst_5861_ = lean_ctor_get(v_x_5860_, 0);
v_snd_5862_ = lean_ctor_get(v_x_5860_, 1);
v_isSharedCheck_5885_ = !lean_is_exclusive(v_x_5860_);
if (v_isSharedCheck_5885_ == 0)
{
v___x_5864_ = v_x_5860_;
v_isShared_5865_ = v_isSharedCheck_5885_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_snd_5862_);
lean_inc(v_fst_5861_);
lean_dec(v_x_5860_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5885_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5870_; 
v___x_5866_ = l_String_quote(v_fst_5861_);
v___x_5867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5867_, 0, v___x_5866_);
v___x_5868_ = lean_box(0);
if (v_isShared_5865_ == 0)
{
lean_ctor_set_tag(v___x_5864_, 1);
lean_ctor_set(v___x_5864_, 1, v___x_5868_);
lean_ctor_set(v___x_5864_, 0, v___x_5867_);
v___x_5870_ = v___x_5864_;
goto v_reusejp_5869_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5867_);
lean_ctor_set(v_reuseFailAlloc_5884_, 1, v___x_5868_);
v___x_5870_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5869_;
}
v_reusejp_5869_:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; uint8_t v___x_5882_; lean_object* v___x_5883_; 
v___x_5871_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5862_);
v___x_5872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
lean_ctor_set(v___x_5872_, 1, v___x_5870_);
v___x_5873_ = l_List_reverse___redArg(v___x_5872_);
v___x_5874_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5875_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5873_, v___x_5874_);
v___x_5876_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5877_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5877_);
lean_ctor_set(v___x_5878_, 1, v___x_5875_);
v___x_5879_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5880_, 0, v___x_5878_);
lean_ctor_set(v___x_5880_, 1, v___x_5879_);
v___x_5881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5876_);
lean_ctor_set(v___x_5881_, 1, v___x_5880_);
v___x_5882_ = 0;
v___x_5883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5883_, 0, v___x_5881_);
lean_ctor_set_uint8(v___x_5883_, sizeof(void*)*1, v___x_5882_);
return v___x_5883_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5886_, lean_object* v_x_5887_, lean_object* v_x_5888_){
_start:
{
if (lean_obj_tag(v_x_5888_) == 0)
{
lean_dec(v_x_5886_);
return v_x_5887_;
}
else
{
lean_object* v_head_5889_; lean_object* v_tail_5890_; lean_object* v___x_5892_; uint8_t v_isShared_5893_; uint8_t v_isSharedCheck_5900_; 
v_head_5889_ = lean_ctor_get(v_x_5888_, 0);
v_tail_5890_ = lean_ctor_get(v_x_5888_, 1);
v_isSharedCheck_5900_ = !lean_is_exclusive(v_x_5888_);
if (v_isSharedCheck_5900_ == 0)
{
v___x_5892_ = v_x_5888_;
v_isShared_5893_ = v_isSharedCheck_5900_;
goto v_resetjp_5891_;
}
else
{
lean_inc(v_tail_5890_);
lean_inc(v_head_5889_);
lean_dec(v_x_5888_);
v___x_5892_ = lean_box(0);
v_isShared_5893_ = v_isSharedCheck_5900_;
goto v_resetjp_5891_;
}
v_resetjp_5891_:
{
lean_object* v___x_5895_; 
lean_inc(v_x_5886_);
if (v_isShared_5893_ == 0)
{
lean_ctor_set_tag(v___x_5892_, 5);
lean_ctor_set(v___x_5892_, 1, v_x_5886_);
lean_ctor_set(v___x_5892_, 0, v_x_5887_);
v___x_5895_ = v___x_5892_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_x_5887_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v_x_5886_);
v___x_5895_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5896_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5889_);
v___x_5897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5895_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
v_x_5887_ = v___x_5897_;
v_x_5888_ = v_tail_5890_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5901_, lean_object* v_x_5902_, lean_object* v_x_5903_){
_start:
{
if (lean_obj_tag(v_x_5903_) == 0)
{
lean_dec(v_x_5901_);
return v_x_5902_;
}
else
{
lean_object* v_head_5904_; lean_object* v_tail_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5915_; 
v_head_5904_ = lean_ctor_get(v_x_5903_, 0);
v_tail_5905_ = lean_ctor_get(v_x_5903_, 1);
v_isSharedCheck_5915_ = !lean_is_exclusive(v_x_5903_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5907_ = v_x_5903_;
v_isShared_5908_ = v_isSharedCheck_5915_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_tail_5905_);
lean_inc(v_head_5904_);
lean_dec(v_x_5903_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5915_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
lean_inc(v_x_5901_);
if (v_isShared_5908_ == 0)
{
lean_ctor_set_tag(v___x_5907_, 5);
lean_ctor_set(v___x_5907_, 1, v_x_5901_);
lean_ctor_set(v___x_5907_, 0, v_x_5902_);
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v_x_5902_);
lean_ctor_set(v_reuseFailAlloc_5914_, 1, v_x_5901_);
v___x_5910_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5911_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5904_);
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5910_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5901_, v___x_5912_, v_tail_5905_);
return v___x_5913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5916_, lean_object* v_x_5917_){
_start:
{
if (lean_obj_tag(v_x_5916_) == 0)
{
lean_object* v___x_5918_; 
lean_dec(v_x_5917_);
v___x_5918_ = lean_box(0);
return v___x_5918_;
}
else
{
lean_object* v_tail_5919_; 
v_tail_5919_ = lean_ctor_get(v_x_5916_, 1);
if (lean_obj_tag(v_tail_5919_) == 0)
{
lean_object* v_head_5920_; lean_object* v___x_5921_; 
lean_dec(v_x_5917_);
v_head_5920_ = lean_ctor_get(v_x_5916_, 0);
lean_inc(v_head_5920_);
lean_dec_ref_known(v_x_5916_, 2);
v___x_5921_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5920_);
return v___x_5921_;
}
else
{
lean_object* v_head_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; 
lean_inc(v_tail_5919_);
v_head_5922_ = lean_ctor_get(v_x_5916_, 0);
lean_inc(v_head_5922_);
lean_dec_ref_known(v_x_5916_, 2);
v___x_5923_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5922_);
v___x_5924_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5917_, v___x_5923_, v_tail_5919_);
return v___x_5924_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5926_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5927_ = lean_string_length(v___x_5926_);
return v___x_5927_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5928_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5929_ = lean_nat_to_int(v___x_5928_);
return v___x_5929_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5935_){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; uint8_t v___x_5938_; 
v___x_5936_ = lean_array_get_size(v_xs_5935_);
v___x_5937_ = lean_unsigned_to_nat(0u);
v___x_5938_ = lean_nat_dec_eq(v___x_5936_, v___x_5937_);
if (v___x_5938_ == 0)
{
lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; 
v___x_5939_ = lean_array_to_list(v_xs_5935_);
v___x_5940_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5941_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5939_, v___x_5940_);
v___x_5942_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5943_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5943_);
lean_ctor_set(v___x_5944_, 1, v___x_5941_);
v___x_5945_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5944_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
v___x_5947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5942_);
lean_ctor_set(v___x_5947_, 1, v___x_5946_);
v___x_5948_ = l_Std_Format_fill(v___x_5947_);
return v___x_5948_;
}
else
{
lean_object* v___x_5949_; 
lean_dec_ref(v_xs_5935_);
v___x_5949_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_5949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_5952_, lean_object* v_decl_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_){
_start:
{
lean_object* v___y_5960_; lean_object* v___y_5961_; lean_object* v___y_5962_; lean_object* v___y_5963_; lean_object* v_toCold_5993_; lean_object* v_options_5994_; uint8_t v_hasTrace_5995_; 
v_toCold_5993_ = lean_ctor_get(v_a_5956_, 0);
v_options_5994_ = lean_ctor_get(v_toCold_5993_, 2);
v_hasTrace_5995_ = lean_ctor_get_uint8(v_options_5994_, sizeof(void*)*1);
if (v_hasTrace_5995_ == 0)
{
v___y_5960_ = v_a_5954_;
v___y_5961_ = v_a_5955_;
v___y_5962_ = v_a_5956_;
v___y_5963_ = v_a_5957_;
goto v___jp_5959_;
}
else
{
lean_object* v_inheritedTraceOptions_5996_; lean_object* v_cls_5997_; uint8_t v___y_5999_; lean_object* v___y_6000_; lean_object* v___x_6036_; uint8_t v___x_6037_; 
v_inheritedTraceOptions_5996_ = lean_ctor_get(v_toCold_5993_, 11);
v_cls_5997_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6036_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5996_, v_options_5994_, v___x_6036_);
if (v___x_6037_ == 0)
{
v___y_5960_ = v_a_5954_;
v___y_5961_ = v_a_5955_;
v___y_5962_ = v_a_5956_;
v___y_5963_ = v_a_5957_;
goto v___jp_5959_;
}
else
{
lean_object* v_size_6038_; lean_object* v_buckets_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; uint8_t v___x_6043_; 
v_size_6038_ = lean_ctor_get(v_assignment_5952_, 0);
v_buckets_6039_ = lean_ctor_get(v_assignment_5952_, 1);
v___x_6040_ = lean_mk_empty_array_with_capacity(v_size_6038_);
v___x_6041_ = lean_unsigned_to_nat(0u);
v___x_6042_ = lean_array_get_size(v_buckets_6039_);
v___x_6043_ = lean_nat_dec_lt(v___x_6041_, v___x_6042_);
if (v___x_6043_ == 0)
{
v___y_5999_ = v___x_6037_;
v___y_6000_ = v___x_6040_;
goto v___jp_5998_;
}
else
{
size_t v___x_6044_; size_t v___x_6045_; lean_object* v___x_6046_; 
v___x_6044_ = ((size_t)0ULL);
v___x_6045_ = lean_usize_of_nat(v___x_6042_);
v___x_6046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6039_, v___x_6044_, v___x_6045_, v___x_6040_);
v___y_5999_ = v___x_6037_;
v___y_6000_ = v___x_6046_;
goto v___jp_5998_;
}
}
v___jp_5998_:
{
size_t v_sz_6001_; size_t v___x_6002_; lean_object* v___x_6003_; 
v_sz_6001_ = lean_array_size(v___y_6000_);
v___x_6002_ = ((size_t)0ULL);
v___x_6003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_5999_, v_sz_6001_, v___x_6002_, v___y_6000_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_);
if (lean_obj_tag(v___x_6003_) == 0)
{
lean_object* v_toSignature_6004_; lean_object* v_a_6005_; lean_object* v_name_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; 
v_toSignature_6004_ = lean_ctor_get(v_decl_5953_, 0);
v_a_6005_ = lean_ctor_get(v___x_6003_, 0);
lean_inc(v_a_6005_);
lean_dec_ref_known(v___x_6003_, 1);
v_name_6006_ = lean_ctor_get(v_toSignature_6004_, 0);
v___x_6007_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6006_);
v___x_6008_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6006_, v___y_5999_);
v___x_6009_ = lean_string_append(v___x_6007_, v___x_6008_);
lean_dec_ref(v___x_6008_);
v___x_6010_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6011_ = lean_string_append(v___x_6009_, v___x_6010_);
v___x_6012_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6005_);
v___x_6013_ = l_Std_Format_defWidth;
v___x_6014_ = lean_unsigned_to_nat(0u);
v___x_6015_ = l_Std_Format_pretty(v___x_6012_, v___x_6013_, v___x_6014_, v___x_6014_);
v___x_6016_ = lean_string_append(v___x_6011_, v___x_6015_);
lean_dec_ref(v___x_6015_);
v___x_6017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
v___x_6018_ = l_Lean_MessageData_ofFormat(v___x_6017_);
v___x_6019_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5997_, v___x_6018_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_);
if (lean_obj_tag(v___x_6019_) == 0)
{
lean_dec_ref_known(v___x_6019_, 1);
v___y_5960_ = v_a_5954_;
v___y_5961_ = v_a_5955_;
v___y_5962_ = v_a_5956_;
v___y_5963_ = v_a_5957_;
goto v___jp_5959_;
}
else
{
lean_object* v_a_6020_; lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6027_; 
lean_dec_ref(v_decl_5953_);
lean_dec_ref(v_assignment_5952_);
v_a_6020_ = lean_ctor_get(v___x_6019_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v___x_6019_);
if (v_isSharedCheck_6027_ == 0)
{
v___x_6022_ = v___x_6019_;
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
else
{
lean_inc(v_a_6020_);
lean_dec(v___x_6019_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v___x_6025_; 
if (v_isShared_6023_ == 0)
{
v___x_6025_ = v___x_6022_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_a_6020_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
}
else
{
lean_object* v_a_6028_; lean_object* v___x_6030_; uint8_t v_isShared_6031_; uint8_t v_isSharedCheck_6035_; 
lean_dec_ref(v_decl_5953_);
lean_dec_ref(v_assignment_5952_);
v_a_6028_ = lean_ctor_get(v___x_6003_, 0);
v_isSharedCheck_6035_ = !lean_is_exclusive(v___x_6003_);
if (v_isSharedCheck_6035_ == 0)
{
v___x_6030_ = v___x_6003_;
v_isShared_6031_ = v_isSharedCheck_6035_;
goto v_resetjp_6029_;
}
else
{
lean_inc(v_a_6028_);
lean_dec(v___x_6003_);
v___x_6030_ = lean_box(0);
v_isShared_6031_ = v_isSharedCheck_6035_;
goto v_resetjp_6029_;
}
v_resetjp_6029_:
{
lean_object* v___x_6033_; 
if (v_isShared_6031_ == 0)
{
v___x_6033_ = v___x_6030_;
goto v_reusejp_6032_;
}
else
{
lean_object* v_reuseFailAlloc_6034_; 
v_reuseFailAlloc_6034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_a_6028_);
v___x_6033_ = v_reuseFailAlloc_6034_;
goto v_reusejp_6032_;
}
v_reusejp_6032_:
{
return v___x_6033_;
}
}
}
}
}
v___jp_5959_:
{
lean_object* v_toSignature_5964_; lean_object* v_value_5965_; uint8_t v_recursive_5966_; lean_object* v_inlineAttr_x3f_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5992_; 
v_toSignature_5964_ = lean_ctor_get(v_decl_5953_, 0);
v_value_5965_ = lean_ctor_get(v_decl_5953_, 1);
v_recursive_5966_ = lean_ctor_get_uint8(v_decl_5953_, sizeof(void*)*3);
v_inlineAttr_x3f_5967_ = lean_ctor_get(v_decl_5953_, 2);
v_isSharedCheck_5992_ = !lean_is_exclusive(v_decl_5953_);
if (v_isSharedCheck_5992_ == 0)
{
v___x_5969_ = v_decl_5953_;
v_isShared_5970_ = v_isSharedCheck_5992_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_inlineAttr_x3f_5967_);
lean_inc(v_value_5965_);
lean_inc(v_toSignature_5964_);
lean_dec(v_decl_5953_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5992_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5971_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_5971_, 0, v_assignment_5952_);
v___x_5972_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_5971_, v_value_5965_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_);
if (lean_obj_tag(v___x_5972_) == 0)
{
lean_object* v_a_5973_; lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_5983_; 
v_a_5973_ = lean_ctor_get(v___x_5972_, 0);
v_isSharedCheck_5983_ = !lean_is_exclusive(v___x_5972_);
if (v_isSharedCheck_5983_ == 0)
{
v___x_5975_ = v___x_5972_;
v_isShared_5976_ = v_isSharedCheck_5983_;
goto v_resetjp_5974_;
}
else
{
lean_inc(v_a_5973_);
lean_dec(v___x_5972_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_5983_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5978_; 
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 1, v_a_5973_);
v___x_5978_ = v___x_5969_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_toSignature_5964_);
lean_ctor_set(v_reuseFailAlloc_5982_, 1, v_a_5973_);
lean_ctor_set(v_reuseFailAlloc_5982_, 2, v_inlineAttr_x3f_5967_);
lean_ctor_set_uint8(v_reuseFailAlloc_5982_, sizeof(void*)*3, v_recursive_5966_);
v___x_5978_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
lean_object* v___x_5980_; 
if (v_isShared_5976_ == 0)
{
lean_ctor_set(v___x_5975_, 0, v___x_5978_);
v___x_5980_ = v___x_5975_;
goto v_reusejp_5979_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5978_);
v___x_5980_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5979_;
}
v_reusejp_5979_:
{
return v___x_5980_;
}
}
}
}
else
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5991_; 
lean_del_object(v___x_5969_);
lean_dec(v_inlineAttr_x3f_5967_);
lean_dec_ref(v_toSignature_5964_);
v_a_5984_ = lean_ctor_get(v___x_5972_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5972_);
if (v_isSharedCheck_5991_ == 0)
{
v___x_5986_ = v___x_5972_;
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v___x_5972_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6047_, lean_object* v_decl_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_){
_start:
{
lean_object* v_res_6054_; 
v_res_6054_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6047_, v_decl_6048_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_);
lean_dec(v_a_6052_);
lean_dec_ref(v_a_6051_);
lean_dec(v_a_6050_);
lean_dec_ref(v_a_6049_);
return v_res_6054_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6055_, lean_object* v_x_6056_){
_start:
{
lean_object* v___x_6057_; 
v___x_6057_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6055_);
return v___x_6057_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6058_, lean_object* v_x_6059_){
_start:
{
lean_object* v_res_6060_; 
v_res_6060_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6058_, v_x_6059_);
lean_dec(v_x_6059_);
return v_res_6060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6061_, size_t v_i_6062_, lean_object* v_bs_6063_){
_start:
{
uint8_t v___x_6064_; 
v___x_6064_ = lean_usize_dec_lt(v_i_6062_, v_sz_6061_);
if (v___x_6064_ == 0)
{
return v_bs_6063_;
}
else
{
lean_object* v_v_6065_; lean_object* v_toSignature_6066_; lean_object* v_name_6067_; lean_object* v___x_6068_; lean_object* v_bs_x27_6069_; size_t v___x_6070_; size_t v___x_6071_; lean_object* v___x_6072_; 
v_v_6065_ = lean_array_uget_borrowed(v_bs_6063_, v_i_6062_);
v_toSignature_6066_ = lean_ctor_get(v_v_6065_, 0);
v_name_6067_ = lean_ctor_get(v_toSignature_6066_, 0);
lean_inc(v_name_6067_);
v___x_6068_ = lean_unsigned_to_nat(0u);
v_bs_x27_6069_ = lean_array_uset(v_bs_6063_, v_i_6062_, v___x_6068_);
v___x_6070_ = ((size_t)1ULL);
v___x_6071_ = lean_usize_add(v_i_6062_, v___x_6070_);
v___x_6072_ = lean_array_uset(v_bs_x27_6069_, v_i_6062_, v_name_6067_);
v_i_6062_ = v___x_6071_;
v_bs_6063_ = v___x_6072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6074_, lean_object* v_i_6075_, lean_object* v_bs_6076_){
_start:
{
size_t v_sz_boxed_6077_; size_t v_i_boxed_6078_; lean_object* v_res_6079_; 
v_sz_boxed_6077_ = lean_unbox_usize(v_sz_6074_);
lean_dec(v_sz_6074_);
v_i_boxed_6078_ = lean_unbox_usize(v_i_6075_);
lean_dec(v_i_6075_);
v_res_6079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6077_, v_i_boxed_6078_, v_bs_6076_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6080_, lean_object* v_a_6081_){
_start:
{
if (lean_obj_tag(v_a_6080_) == 0)
{
lean_object* v___x_6082_; 
v___x_6082_ = l_List_reverse___redArg(v_a_6081_);
return v___x_6082_;
}
else
{
lean_object* v_head_6083_; lean_object* v_tail_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6093_; 
v_head_6083_ = lean_ctor_get(v_a_6080_, 0);
v_tail_6084_ = lean_ctor_get(v_a_6080_, 1);
v_isSharedCheck_6093_ = !lean_is_exclusive(v_a_6080_);
if (v_isSharedCheck_6093_ == 0)
{
v___x_6086_ = v_a_6080_;
v_isShared_6087_ = v_isSharedCheck_6093_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_tail_6084_);
lean_inc(v_head_6083_);
lean_dec(v_a_6080_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6093_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v___x_6088_; lean_object* v___x_6090_; 
v___x_6088_ = l_Lean_MessageData_ofName(v_head_6083_);
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 1, v_a_6081_);
lean_ctor_set(v___x_6086_, 0, v___x_6088_);
v___x_6090_ = v___x_6086_;
goto v_reusejp_6089_;
}
else
{
lean_object* v_reuseFailAlloc_6092_; 
v_reuseFailAlloc_6092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6092_, 0, v___x_6088_);
lean_ctor_set(v_reuseFailAlloc_6092_, 1, v_a_6081_);
v___x_6090_ = v_reuseFailAlloc_6092_;
goto v_reusejp_6089_;
}
v_reusejp_6089_:
{
v_a_6080_ = v_tail_6084_;
v_a_6081_ = v___x_6090_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6095_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6096_ = l_Lean_stringToMessageData(v___x_6095_);
return v___x_6096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6097_, lean_object* v_x_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_){
_start:
{
lean_object* v___x_6106_; size_t v_sz_6107_; size_t v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6106_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6107_ = lean_array_size(v___y_6097_);
v___x_6108_ = ((size_t)0ULL);
v___x_6109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6107_, v___x_6108_, v___y_6097_);
v___x_6110_ = lean_array_to_list(v___x_6109_);
v___x_6111_ = lean_box(0);
v___x_6112_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6110_, v___x_6111_);
v___x_6113_ = l_Lean_MessageData_ofList(v___x_6112_);
v___x_6114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6106_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v___x_6115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
return v___x_6115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6116_, lean_object* v_x_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_){
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6116_, v_x_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec(v___y_6121_);
lean_dec_ref(v___y_6120_);
lean_dec(v___y_6119_);
lean_dec_ref(v___y_6118_);
lean_dec_ref(v_x_6117_);
return v_res_6125_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_6126_; 
v___x_6126_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default___redArg();
return v___x_6126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6127_, lean_object* v_n_6128_, lean_object* v_j_6129_, lean_object* v_a_6130_){
_start:
{
lean_object* v_zero_6131_; uint8_t v_isZero_6132_; 
v_zero_6131_ = lean_unsigned_to_nat(0u);
v_isZero_6132_ = lean_nat_dec_eq(v_j_6129_, v_zero_6131_);
if (v_isZero_6132_ == 1)
{
lean_dec(v_j_6129_);
return v_a_6130_;
}
else
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v_toSignature_6136_; uint8_t v_safe_6137_; lean_object* v_one_6138_; lean_object* v_n_6139_; 
v___x_6133_ = lean_nat_sub(v_n_6128_, v_j_6129_);
v___x_6134_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6135_ = lean_array_get_borrowed(v___x_6134_, v___y_6127_, v___x_6133_);
lean_dec(v___x_6133_);
v_toSignature_6136_ = lean_ctor_get(v___x_6135_, 0);
v_safe_6137_ = lean_ctor_get_uint8(v_toSignature_6136_, sizeof(void*)*4);
v_one_6138_ = lean_unsigned_to_nat(1u);
v_n_6139_ = lean_nat_sub(v_j_6129_, v_one_6138_);
lean_dec(v_j_6129_);
if (v_safe_6137_ == 0)
{
lean_object* v___x_6140_; lean_object* v___x_6141_; 
v___x_6140_ = lean_box(1);
v___x_6141_ = lean_array_push(v_a_6130_, v___x_6140_);
v_j_6129_ = v_n_6139_;
v_a_6130_ = v___x_6141_;
goto _start;
}
else
{
lean_object* v___x_6143_; lean_object* v___x_6144_; 
v___x_6143_ = lean_box(0);
v___x_6144_ = lean_array_push(v_a_6130_, v___x_6143_);
v_j_6129_ = v_n_6139_;
v_a_6130_ = v___x_6144_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6146_, lean_object* v_n_6147_, lean_object* v_j_6148_, lean_object* v_a_6149_){
_start:
{
lean_object* v_res_6150_; 
v_res_6150_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6146_, v_n_6147_, v_j_6148_, v_a_6149_);
lean_dec(v_n_6147_);
lean_dec_ref(v___y_6146_);
return v_res_6150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6151_, size_t v_sz_6152_, size_t v_i_6153_, lean_object* v_bs_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_){
_start:
{
uint8_t v___x_6160_; 
v___x_6160_ = lean_usize_dec_lt(v_i_6153_, v_sz_6152_);
if (v___x_6160_ == 0)
{
lean_object* v___x_6161_; 
v___x_6161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6161_, 0, v_bs_6154_);
return v___x_6161_;
}
else
{
lean_object* v_v_6162_; lean_object* v_toSignature_6163_; uint8_t v_safe_6164_; lean_object* v___x_6165_; lean_object* v_bs_x27_6166_; lean_object* v_a_6168_; 
v_v_6162_ = lean_array_uget(v_bs_6154_, v_i_6153_);
v_toSignature_6163_ = lean_ctor_get(v_v_6162_, 0);
v_safe_6164_ = lean_ctor_get_uint8(v_toSignature_6163_, sizeof(void*)*4);
v___x_6165_ = lean_unsigned_to_nat(0u);
v_bs_x27_6166_ = lean_array_uset(v_bs_6154_, v_i_6153_, v___x_6165_);
if (v_safe_6164_ == 0)
{
v_a_6168_ = v_v_6162_;
goto v___jp_6167_;
}
else
{
lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; 
v___x_6173_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0);
v___x_6174_ = lean_usize_to_nat(v_i_6153_);
v___x_6175_ = lean_array_get_borrowed(v___x_6173_, v___x_6151_, v___x_6174_);
lean_dec(v___x_6174_);
lean_inc(v___x_6175_);
v___x_6176_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6175_, v_v_6162_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_);
if (lean_obj_tag(v___x_6176_) == 0)
{
lean_object* v_a_6177_; 
v_a_6177_ = lean_ctor_get(v___x_6176_, 0);
lean_inc(v_a_6177_);
lean_dec_ref_known(v___x_6176_, 1);
v_a_6168_ = v_a_6177_;
goto v___jp_6167_;
}
else
{
lean_object* v_a_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6185_; 
lean_dec_ref(v_bs_x27_6166_);
v_a_6178_ = lean_ctor_get(v___x_6176_, 0);
v_isSharedCheck_6185_ = !lean_is_exclusive(v___x_6176_);
if (v_isSharedCheck_6185_ == 0)
{
v___x_6180_ = v___x_6176_;
v_isShared_6181_ = v_isSharedCheck_6185_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_a_6178_);
lean_dec(v___x_6176_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6185_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v___x_6183_; 
if (v_isShared_6181_ == 0)
{
v___x_6183_ = v___x_6180_;
goto v_reusejp_6182_;
}
else
{
lean_object* v_reuseFailAlloc_6184_; 
v_reuseFailAlloc_6184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_a_6178_);
v___x_6183_ = v_reuseFailAlloc_6184_;
goto v_reusejp_6182_;
}
v_reusejp_6182_:
{
return v___x_6183_;
}
}
}
}
v___jp_6167_:
{
size_t v___x_6169_; size_t v___x_6170_; lean_object* v___x_6171_; 
v___x_6169_ = ((size_t)1ULL);
v___x_6170_ = lean_usize_add(v_i_6153_, v___x_6169_);
v___x_6171_ = lean_array_uset(v_bs_x27_6166_, v_i_6153_, v_a_6168_);
v_i_6153_ = v___x_6170_;
v_bs_6154_ = v___x_6171_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6186_, lean_object* v_sz_6187_, lean_object* v_i_6188_, lean_object* v_bs_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
size_t v_sz_boxed_6195_; size_t v_i_boxed_6196_; lean_object* v_res_6197_; 
v_sz_boxed_6195_ = lean_unbox_usize(v_sz_6187_);
lean_dec(v_sz_6187_);
v_i_boxed_6196_ = lean_unbox_usize(v_i_6188_);
lean_dec(v_i_6188_);
v_res_6197_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6186_, v_sz_boxed_6195_, v_i_boxed_6196_, v_bs_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6191_);
lean_dec_ref(v___y_6190_);
lean_dec_ref(v___x_6186_);
return v_res_6197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6200_, lean_object* v_pivot_6201_, lean_object* v_as_6202_, lean_object* v_i_6203_, lean_object* v_k_6204_){
_start:
{
uint8_t v___x_6205_; 
v___x_6205_ = lean_nat_dec_lt(v_k_6204_, v_hi_6200_);
if (v___x_6205_ == 0)
{
lean_object* v___x_6206_; lean_object* v___x_6207_; 
lean_dec(v_k_6204_);
lean_dec_ref(v_pivot_6201_);
v___x_6206_ = lean_array_fswap(v_as_6202_, v_i_6203_, v_hi_6200_);
v___x_6207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6207_, 0, v_i_6203_);
lean_ctor_set(v___x_6207_, 1, v___x_6206_);
return v___x_6207_;
}
else
{
lean_object* v___x_6208_; lean_object* v_toSignature_6209_; lean_object* v_toSignature_6210_; lean_object* v_name_6211_; lean_object* v_name_6212_; uint8_t v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; uint8_t v___x_6223_; 
v___x_6208_ = lean_array_fget_borrowed(v_as_6202_, v_k_6204_);
v_toSignature_6209_ = lean_ctor_get(v___x_6208_, 0);
v_toSignature_6210_ = lean_ctor_get(v_pivot_6201_, 0);
v_name_6211_ = lean_ctor_get(v_toSignature_6209_, 0);
v_name_6212_ = lean_ctor_get(v_toSignature_6210_, 0);
v___x_6213_ = 0;
v___x_6214_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6213_, v___x_6208_);
v___x_6215_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6216_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6217_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6211_);
v___x_6218_ = l_Lean_Name_toString(v_name_6211_, v___x_6205_);
v___x_6219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6214_);
lean_ctor_set(v___x_6219_, 1, v___x_6218_);
v___x_6220_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6213_, v_pivot_6201_);
lean_inc(v_name_6212_);
v___x_6221_ = l_Lean_Name_toString(v_name_6212_, v___x_6205_);
v___x_6222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6222_, 0, v___x_6220_);
lean_ctor_set(v___x_6222_, 1, v___x_6221_);
v___x_6223_ = l_Prod_lexLtDec___redArg(v___x_6215_, v___x_6216_, v___x_6217_, v___x_6219_, v___x_6222_);
if (v___x_6223_ == 0)
{
lean_object* v___x_6224_; lean_object* v___x_6225_; 
v___x_6224_ = lean_unsigned_to_nat(1u);
v___x_6225_ = lean_nat_add(v_k_6204_, v___x_6224_);
lean_dec(v_k_6204_);
v_k_6204_ = v___x_6225_;
goto _start;
}
else
{
lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; 
v___x_6227_ = lean_array_fswap(v_as_6202_, v_i_6203_, v_k_6204_);
v___x_6228_ = lean_unsigned_to_nat(1u);
v___x_6229_ = lean_nat_add(v_i_6203_, v___x_6228_);
lean_dec(v_i_6203_);
v___x_6230_ = lean_nat_add(v_k_6204_, v___x_6228_);
lean_dec(v_k_6204_);
v_as_6202_ = v___x_6227_;
v_i_6203_ = v___x_6229_;
v_k_6204_ = v___x_6230_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6232_, lean_object* v_pivot_6233_, lean_object* v_as_6234_, lean_object* v_i_6235_, lean_object* v_k_6236_){
_start:
{
lean_object* v_res_6237_; 
v_res_6237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6232_, v_pivot_6233_, v_as_6234_, v_i_6235_, v_k_6236_);
lean_dec(v_hi_6232_);
return v_res_6237_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6238_, lean_object* v_l_6239_, lean_object* v_r_6240_){
_start:
{
lean_object* v_toSignature_6241_; lean_object* v_toSignature_6242_; lean_object* v_name_6243_; lean_object* v_name_6244_; uint8_t v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; uint8_t v___x_6255_; 
v_toSignature_6241_ = lean_ctor_get(v_l_6239_, 0);
v_toSignature_6242_ = lean_ctor_get(v_r_6240_, 0);
v_name_6243_ = lean_ctor_get(v_toSignature_6241_, 0);
lean_inc(v_name_6243_);
v_name_6244_ = lean_ctor_get(v_toSignature_6242_, 0);
lean_inc(v_name_6244_);
v___x_6245_ = 0;
v___x_6246_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6245_, v_l_6239_);
lean_dec_ref(v_l_6239_);
v___x_6247_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6248_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6249_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6250_ = l_Lean_Name_toString(v_name_6243_, v___x_6238_);
v___x_6251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6251_, 0, v___x_6246_);
lean_ctor_set(v___x_6251_, 1, v___x_6250_);
v___x_6252_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6245_, v_r_6240_);
lean_dec_ref(v_r_6240_);
v___x_6253_ = l_Lean_Name_toString(v_name_6244_, v___x_6238_);
v___x_6254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6254_, 0, v___x_6252_);
lean_ctor_set(v___x_6254_, 1, v___x_6253_);
v___x_6255_ = l_Prod_lexLtDec___redArg(v___x_6247_, v___x_6248_, v___x_6249_, v___x_6251_, v___x_6254_);
return v___x_6255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6256_, lean_object* v_l_6257_, lean_object* v_r_6258_){
_start:
{
uint8_t v___x_13221__boxed_6259_; uint8_t v_res_6260_; lean_object* v_r_6261_; 
v___x_13221__boxed_6259_ = lean_unbox(v___x_6256_);
v_res_6260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13221__boxed_6259_, v_l_6257_, v_r_6258_);
v_r_6261_ = lean_box(v_res_6260_);
return v_r_6261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6262_, lean_object* v_as_6263_, lean_object* v_lo_6264_, lean_object* v_hi_6265_){
_start:
{
lean_object* v___y_6267_; uint8_t v___x_6277_; 
v___x_6277_ = lean_nat_dec_lt(v_lo_6264_, v_hi_6265_);
if (v___x_6277_ == 0)
{
lean_dec(v_lo_6264_);
return v_as_6263_;
}
else
{
lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v_mid_6280_; lean_object* v___y_6282_; lean_object* v___y_6288_; lean_object* v___x_6293_; lean_object* v___x_6294_; uint8_t v___x_6295_; 
v___x_6278_ = lean_nat_add(v_lo_6264_, v_hi_6265_);
v___x_6279_ = lean_unsigned_to_nat(1u);
v_mid_6280_ = lean_nat_shiftr(v___x_6278_, v___x_6279_);
lean_dec(v___x_6278_);
v___x_6293_ = lean_array_fget_borrowed(v_as_6263_, v_mid_6280_);
v___x_6294_ = lean_array_fget_borrowed(v_as_6263_, v_lo_6264_);
lean_inc(v___x_6294_);
lean_inc(v___x_6293_);
v___x_6295_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6277_, v___x_6293_, v___x_6294_);
if (v___x_6295_ == 0)
{
v___y_6288_ = v_as_6263_;
goto v___jp_6287_;
}
else
{
lean_object* v___x_6296_; 
v___x_6296_ = lean_array_fswap(v_as_6263_, v_lo_6264_, v_mid_6280_);
v___y_6288_ = v___x_6296_;
goto v___jp_6287_;
}
v___jp_6281_:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; uint8_t v___x_6285_; 
v___x_6283_ = lean_array_fget_borrowed(v___y_6282_, v_mid_6280_);
v___x_6284_ = lean_array_fget_borrowed(v___y_6282_, v_hi_6265_);
lean_inc(v___x_6284_);
lean_inc(v___x_6283_);
v___x_6285_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6277_, v___x_6283_, v___x_6284_);
if (v___x_6285_ == 0)
{
lean_dec(v_mid_6280_);
v___y_6267_ = v___y_6282_;
goto v___jp_6266_;
}
else
{
lean_object* v___x_6286_; 
v___x_6286_ = lean_array_fswap(v___y_6282_, v_mid_6280_, v_hi_6265_);
lean_dec(v_mid_6280_);
v___y_6267_ = v___x_6286_;
goto v___jp_6266_;
}
}
v___jp_6287_:
{
lean_object* v___x_6289_; lean_object* v___x_6290_; uint8_t v___x_6291_; 
v___x_6289_ = lean_array_fget_borrowed(v___y_6288_, v_hi_6265_);
v___x_6290_ = lean_array_fget_borrowed(v___y_6288_, v_lo_6264_);
lean_inc(v___x_6290_);
lean_inc(v___x_6289_);
v___x_6291_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6277_, v___x_6289_, v___x_6290_);
if (v___x_6291_ == 0)
{
v___y_6282_ = v___y_6288_;
goto v___jp_6281_;
}
else
{
lean_object* v___x_6292_; 
v___x_6292_ = lean_array_fswap(v___y_6288_, v_lo_6264_, v_hi_6265_);
v___y_6282_ = v___x_6292_;
goto v___jp_6281_;
}
}
}
v___jp_6266_:
{
lean_object* v_pivot_6268_; lean_object* v___x_6269_; lean_object* v_fst_6270_; lean_object* v_snd_6271_; uint8_t v___x_6272_; 
v_pivot_6268_ = lean_array_fget(v___y_6267_, v_hi_6265_);
lean_inc_n(v_lo_6264_, 2);
v___x_6269_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6265_, v_pivot_6268_, v___y_6267_, v_lo_6264_, v_lo_6264_);
v_fst_6270_ = lean_ctor_get(v___x_6269_, 0);
lean_inc(v_fst_6270_);
v_snd_6271_ = lean_ctor_get(v___x_6269_, 1);
lean_inc(v_snd_6271_);
lean_dec_ref(v___x_6269_);
v___x_6272_ = lean_nat_dec_le(v_hi_6265_, v_fst_6270_);
if (v___x_6272_ == 0)
{
lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v___x_6273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6262_, v_snd_6271_, v_lo_6264_, v_fst_6270_);
v___x_6274_ = lean_unsigned_to_nat(1u);
v___x_6275_ = lean_nat_add(v_fst_6270_, v___x_6274_);
lean_dec(v_fst_6270_);
v_as_6263_ = v___x_6273_;
v_lo_6264_ = v___x_6275_;
goto _start;
}
else
{
lean_dec(v_fst_6270_);
lean_dec(v_lo_6264_);
return v_snd_6271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6297_, lean_object* v_as_6298_, lean_object* v_lo_6299_, lean_object* v_hi_6300_){
_start:
{
lean_object* v_res_6301_; 
v_res_6301_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6297_, v_as_6298_, v_lo_6299_, v_hi_6300_);
lean_dec(v_hi_6300_);
lean_dec(v_n_6297_);
return v_res_6301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6302_, lean_object* v___x_6303_, lean_object* v_n_6304_, lean_object* v_j_6305_, lean_object* v_a_6306_){
_start:
{
lean_object* v_zero_6307_; uint8_t v_isZero_6308_; 
v_zero_6307_ = lean_unsigned_to_nat(0u);
v_isZero_6308_ = lean_nat_dec_eq(v_j_6305_, v_zero_6307_);
if (v_isZero_6308_ == 1)
{
lean_dec(v_j_6305_);
return v_a_6306_;
}
else
{
lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v_toSignature_6311_; lean_object* v_name_6312_; lean_object* v___x_6313_; lean_object* v_one_6314_; lean_object* v_n_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6309_ = lean_nat_sub(v_n_6304_, v_j_6305_);
v___x_6310_ = lean_array_fget_borrowed(v___y_6302_, v___x_6309_);
v_toSignature_6311_ = lean_ctor_get(v___x_6310_, 0);
v_name_6312_ = lean_ctor_get(v_toSignature_6311_, 0);
v___x_6313_ = lean_box(0);
v_one_6314_ = lean_unsigned_to_nat(1u);
v_n_6315_ = lean_nat_sub(v_j_6305_, v_one_6314_);
lean_dec(v_j_6305_);
v___x_6316_ = lean_array_get_borrowed(v___x_6313_, v___x_6303_, v___x_6309_);
lean_dec(v___x_6309_);
lean_inc(v___x_6316_);
lean_inc(v_name_6312_);
v___x_6317_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6306_, v_name_6312_, v___x_6316_);
v_j_6305_ = v_n_6315_;
v_a_6306_ = v___x_6317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6319_, lean_object* v___x_6320_, lean_object* v_n_6321_, lean_object* v_j_6322_, lean_object* v_a_6323_){
_start:
{
lean_object* v_res_6324_; 
v_res_6324_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6319_, v___x_6320_, v_n_6321_, v_j_6322_, v_a_6323_);
lean_dec(v_n_6321_);
lean_dec_ref(v___x_6320_);
lean_dec_ref(v___y_6319_);
return v_res_6324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6325_; lean_object* v___x_6326_; 
v___x_6325_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_6326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6326_, 0, v___x_6325_);
return v___x_6326_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6327_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6328_, 0, v___x_6327_);
lean_ctor_set(v___x_6328_, 1, v___x_6327_);
return v___x_6328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_){
_start:
{
lean_object* v___y_6338_; size_t v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; size_t v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6378_; lean_object* v___y_6379_; lean_object* v___y_6380_; lean_object* v___y_6381_; lean_object* v___y_6382_; lean_object* v___y_6383_; uint8_t v___y_6384_; lean_object* v___y_6385_; size_t v___y_6386_; uint8_t v___y_6387_; lean_object* v___y_6388_; lean_object* v___y_6389_; lean_object* v___y_6390_; size_t v___y_6391_; lean_object* v_a_6392_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v___y_6404_; lean_object* v___y_6405_; lean_object* v___y_6406_; lean_object* v___y_6407_; lean_object* v___y_6408_; uint8_t v___y_6409_; size_t v___y_6410_; uint8_t v___y_6411_; lean_object* v___y_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; size_t v___y_6415_; lean_object* v_a_6416_; lean_object* v___x_6428_; lean_object* v___y_6430_; lean_object* v___y_6431_; lean_object* v___y_6432_; lean_object* v___y_6433_; lean_object* v___y_6434_; lean_object* v___y_6435_; uint8_t v___y_6436_; size_t v___y_6437_; uint8_t v___y_6438_; lean_object* v___y_6439_; lean_object* v___y_6440_; size_t v___y_6441_; lean_object* v___y_6483_; lean_object* v___x_6507_; lean_object* v___y_6509_; lean_object* v___y_6510_; uint8_t v___x_6512_; 
v___x_6428_ = lean_unsigned_to_nat(0u);
v___x_6507_ = lean_array_get_size(v_decls_6331_);
v___x_6512_ = lean_nat_dec_eq(v___x_6507_, v___x_6428_);
if (v___x_6512_ == 0)
{
lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___y_6516_; uint8_t v___x_6518_; 
v___x_6513_ = lean_unsigned_to_nat(1u);
v___x_6514_ = lean_nat_sub(v___x_6507_, v___x_6513_);
v___x_6518_ = lean_nat_dec_le(v___x_6428_, v___x_6514_);
if (v___x_6518_ == 0)
{
lean_inc(v___x_6514_);
v___y_6516_ = v___x_6514_;
goto v___jp_6515_;
}
else
{
v___y_6516_ = v___x_6428_;
goto v___jp_6515_;
}
v___jp_6515_:
{
uint8_t v___x_6517_; 
v___x_6517_ = lean_nat_dec_le(v___y_6516_, v___x_6514_);
if (v___x_6517_ == 0)
{
lean_dec(v___x_6514_);
lean_inc(v___y_6516_);
v___y_6509_ = v___y_6516_;
v___y_6510_ = v___y_6516_;
goto v___jp_6508_;
}
else
{
v___y_6509_ = v___y_6516_;
v___y_6510_ = v___x_6514_;
goto v___jp_6508_;
}
}
}
else
{
v___y_6483_ = v_decls_6331_;
goto v___jp_6482_;
}
v___jp_6337_:
{
if (lean_obj_tag(v___y_6343_) == 0)
{
lean_object* v___x_6344_; lean_object* v_assignments_6345_; lean_object* v_funVals_6346_; lean_object* v___x_6347_; lean_object* v_env_6348_; lean_object* v_nextMacroScope_6349_; lean_object* v_ngen_6350_; lean_object* v_auxDeclNGen_6351_; lean_object* v_traceState_6352_; lean_object* v_recordedDeps_6353_; lean_object* v_messages_6354_; lean_object* v_infoState_6355_; lean_object* v_snapshotTasks_6356_; lean_object* v___x_6358_; uint8_t v_isShared_6359_; uint8_t v_isSharedCheck_6367_; 
lean_dec_ref_known(v___y_6343_, 1);
v___x_6344_ = lean_st_ref_get(v___y_6341_);
lean_dec(v___y_6341_);
v_assignments_6345_ = lean_ctor_get(v___x_6344_, 0);
lean_inc_ref(v_assignments_6345_);
v_funVals_6346_ = lean_ctor_get(v___x_6344_, 1);
lean_inc_ref(v_funVals_6346_);
lean_dec(v___x_6344_);
v___x_6347_ = lean_st_ref_take(v_a_6335_);
v_env_6348_ = lean_ctor_get(v___x_6347_, 0);
v_nextMacroScope_6349_ = lean_ctor_get(v___x_6347_, 1);
v_ngen_6350_ = lean_ctor_get(v___x_6347_, 2);
v_auxDeclNGen_6351_ = lean_ctor_get(v___x_6347_, 3);
v_traceState_6352_ = lean_ctor_get(v___x_6347_, 4);
v_recordedDeps_6353_ = lean_ctor_get(v___x_6347_, 6);
v_messages_6354_ = lean_ctor_get(v___x_6347_, 7);
v_infoState_6355_ = lean_ctor_get(v___x_6347_, 8);
v_snapshotTasks_6356_ = lean_ctor_get(v___x_6347_, 9);
v_isSharedCheck_6367_ = !lean_is_exclusive(v___x_6347_);
if (v_isSharedCheck_6367_ == 0)
{
lean_object* v_unused_6368_; 
v_unused_6368_ = lean_ctor_get(v___x_6347_, 5);
lean_dec(v_unused_6368_);
v___x_6358_ = v___x_6347_;
v_isShared_6359_ = v_isSharedCheck_6367_;
goto v_resetjp_6357_;
}
else
{
lean_inc(v_snapshotTasks_6356_);
lean_inc(v_infoState_6355_);
lean_inc(v_messages_6354_);
lean_inc(v_recordedDeps_6353_);
lean_inc(v_traceState_6352_);
lean_inc(v_auxDeclNGen_6351_);
lean_inc(v_ngen_6350_);
lean_inc(v_nextMacroScope_6349_);
lean_inc(v_env_6348_);
lean_dec(v___x_6347_);
v___x_6358_ = lean_box(0);
v_isShared_6359_ = v_isSharedCheck_6367_;
goto v_resetjp_6357_;
}
v_resetjp_6357_:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6363_; 
lean_inc(v___y_6340_);
v___x_6360_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6338_, v_funVals_6346_, v___y_6340_, v___y_6340_, v_env_6348_);
lean_dec(v___y_6340_);
lean_dec_ref(v_funVals_6346_);
v___x_6361_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
if (v_isShared_6359_ == 0)
{
lean_ctor_set(v___x_6358_, 5, v___x_6361_);
lean_ctor_set(v___x_6358_, 0, v___x_6360_);
v___x_6363_ = v___x_6358_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6366_; 
v_reuseFailAlloc_6366_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6366_, 0, v___x_6360_);
lean_ctor_set(v_reuseFailAlloc_6366_, 1, v_nextMacroScope_6349_);
lean_ctor_set(v_reuseFailAlloc_6366_, 2, v_ngen_6350_);
lean_ctor_set(v_reuseFailAlloc_6366_, 3, v_auxDeclNGen_6351_);
lean_ctor_set(v_reuseFailAlloc_6366_, 4, v_traceState_6352_);
lean_ctor_set(v_reuseFailAlloc_6366_, 5, v___x_6361_);
lean_ctor_set(v_reuseFailAlloc_6366_, 6, v_recordedDeps_6353_);
lean_ctor_set(v_reuseFailAlloc_6366_, 7, v_messages_6354_);
lean_ctor_set(v_reuseFailAlloc_6366_, 8, v_infoState_6355_);
lean_ctor_set(v_reuseFailAlloc_6366_, 9, v_snapshotTasks_6356_);
v___x_6363_ = v_reuseFailAlloc_6366_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; 
v___x_6364_ = lean_st_ref_put(v_a_6335_, v___x_6363_);
v___x_6365_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6345_, v___y_6339_, v___y_6342_, v___y_6338_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
lean_dec_ref(v_assignments_6345_);
return v___x_6365_;
}
}
}
else
{
lean_object* v_a_6369_; lean_object* v___x_6371_; uint8_t v_isShared_6372_; uint8_t v_isSharedCheck_6376_; 
lean_dec(v___y_6341_);
lean_dec(v___y_6340_);
lean_dec_ref(v___y_6338_);
v_a_6369_ = lean_ctor_get(v___y_6343_, 0);
v_isSharedCheck_6376_ = !lean_is_exclusive(v___y_6343_);
if (v_isSharedCheck_6376_ == 0)
{
v___x_6371_ = v___y_6343_;
v_isShared_6372_ = v_isSharedCheck_6376_;
goto v_resetjp_6370_;
}
else
{
lean_inc(v_a_6369_);
lean_dec(v___y_6343_);
v___x_6371_ = lean_box(0);
v_isShared_6372_ = v_isSharedCheck_6376_;
goto v_resetjp_6370_;
}
v_resetjp_6370_:
{
lean_object* v___x_6374_; 
if (v_isShared_6372_ == 0)
{
v___x_6374_ = v___x_6371_;
goto v_reusejp_6373_;
}
else
{
lean_object* v_reuseFailAlloc_6375_; 
v_reuseFailAlloc_6375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6375_, 0, v_a_6369_);
v___x_6374_ = v_reuseFailAlloc_6375_;
goto v_reusejp_6373_;
}
v_reusejp_6373_:
{
return v___x_6374_;
}
}
}
}
v___jp_6377_:
{
lean_object* v___x_6393_; double v___x_6394_; double v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; 
v___x_6393_ = lean_io_get_num_heartbeats();
v___x_6394_ = lean_float_of_nat(v___y_6385_);
v___x_6395_ = lean_float_of_nat(v___x_6393_);
v___x_6396_ = lean_box_float(v___x_6394_);
v___x_6397_ = lean_box_float(v___x_6395_);
v___x_6398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6398_, 0, v___x_6396_);
lean_ctor_set(v___x_6398_, 1, v___x_6397_);
v___x_6399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6399_, 0, v_a_6392_);
lean_ctor_set(v___x_6399_, 1, v___x_6398_);
lean_inc_ref(v___y_6379_);
lean_inc(v___y_6381_);
v___x_6400_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6381_, v___y_6387_, v___y_6379_, v___y_6389_, v___y_6384_, v___y_6388_, v___y_6383_, v___x_6399_, v___y_6378_, v___y_6382_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
lean_dec_ref(v___y_6378_);
v___y_6338_ = v___y_6380_;
v___y_6339_ = v___y_6386_;
v___y_6340_ = v___y_6390_;
v___y_6341_ = v___y_6382_;
v___y_6342_ = v___y_6391_;
v___y_6343_ = v___x_6400_;
goto v___jp_6337_;
}
v___jp_6401_:
{
lean_object* v___x_6417_; double v___x_6418_; double v___x_6419_; double v___x_6420_; double v___x_6421_; double v___x_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6417_ = lean_io_mono_nanos_now();
v___x_6418_ = lean_float_of_nat(v___y_6403_);
v___x_6419_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6420_ = lean_float_div(v___x_6418_, v___x_6419_);
v___x_6421_ = lean_float_of_nat(v___x_6417_);
v___x_6422_ = lean_float_div(v___x_6421_, v___x_6419_);
v___x_6423_ = lean_box_float(v___x_6420_);
v___x_6424_ = lean_box_float(v___x_6422_);
v___x_6425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6425_, 0, v___x_6423_);
lean_ctor_set(v___x_6425_, 1, v___x_6424_);
v___x_6426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6426_, 0, v_a_6416_);
lean_ctor_set(v___x_6426_, 1, v___x_6425_);
lean_inc_ref(v___y_6404_);
lean_inc(v___y_6406_);
v___x_6427_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6406_, v___y_6411_, v___y_6404_, v___y_6413_, v___y_6409_, v___y_6412_, v___y_6408_, v___x_6426_, v___y_6402_, v___y_6407_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
lean_dec_ref(v___y_6402_);
v___y_6338_ = v___y_6405_;
v___y_6339_ = v___y_6410_;
v___y_6340_ = v___y_6414_;
v___y_6341_ = v___y_6407_;
v___y_6342_ = v___y_6415_;
v___y_6343_ = v___x_6427_;
goto v___jp_6337_;
}
v___jp_6429_:
{
lean_object* v___x_6442_; lean_object* v_a_6443_; lean_object* v___x_6444_; uint8_t v___x_6445_; 
v___x_6442_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6335_);
v_a_6443_ = lean_ctor_get(v___x_6442_, 0);
lean_inc(v_a_6443_);
lean_dec_ref(v___x_6442_);
v___x_6444_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6445_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6439_, v___x_6444_);
if (v___x_6445_ == 0)
{
lean_object* v___x_6446_; lean_object* v___x_6447_; 
v___x_6446_ = lean_io_mono_nanos_now();
v___x_6447_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6428_, v___y_6430_, v___y_6434_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
if (lean_obj_tag(v___x_6447_) == 0)
{
lean_object* v_a_6448_; lean_object* v___x_6450_; uint8_t v_isShared_6451_; uint8_t v_isSharedCheck_6455_; 
v_a_6448_ = lean_ctor_get(v___x_6447_, 0);
v_isSharedCheck_6455_ = !lean_is_exclusive(v___x_6447_);
if (v_isSharedCheck_6455_ == 0)
{
v___x_6450_ = v___x_6447_;
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
else
{
lean_inc(v_a_6448_);
lean_dec(v___x_6447_);
v___x_6450_ = lean_box(0);
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
v_resetjp_6449_:
{
lean_object* v___x_6453_; 
if (v_isShared_6451_ == 0)
{
lean_ctor_set_tag(v___x_6450_, 1);
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
v___y_6402_ = v___y_6430_;
v___y_6403_ = v___x_6446_;
v___y_6404_ = v___y_6431_;
v___y_6405_ = v___y_6432_;
v___y_6406_ = v___y_6433_;
v___y_6407_ = v___y_6434_;
v___y_6408_ = v___y_6435_;
v___y_6409_ = v___y_6436_;
v___y_6410_ = v___y_6437_;
v___y_6411_ = v___y_6438_;
v___y_6412_ = v_a_6443_;
v___y_6413_ = v___y_6439_;
v___y_6414_ = v___y_6440_;
v___y_6415_ = v___y_6441_;
v_a_6416_ = v___x_6453_;
goto v___jp_6401_;
}
}
}
else
{
lean_object* v_a_6456_; lean_object* v___x_6458_; uint8_t v_isShared_6459_; uint8_t v_isSharedCheck_6463_; 
v_a_6456_ = lean_ctor_get(v___x_6447_, 0);
v_isSharedCheck_6463_ = !lean_is_exclusive(v___x_6447_);
if (v_isSharedCheck_6463_ == 0)
{
v___x_6458_ = v___x_6447_;
v_isShared_6459_ = v_isSharedCheck_6463_;
goto v_resetjp_6457_;
}
else
{
lean_inc(v_a_6456_);
lean_dec(v___x_6447_);
v___x_6458_ = lean_box(0);
v_isShared_6459_ = v_isSharedCheck_6463_;
goto v_resetjp_6457_;
}
v_resetjp_6457_:
{
lean_object* v___x_6461_; 
if (v_isShared_6459_ == 0)
{
lean_ctor_set_tag(v___x_6458_, 0);
v___x_6461_ = v___x_6458_;
goto v_reusejp_6460_;
}
else
{
lean_object* v_reuseFailAlloc_6462_; 
v_reuseFailAlloc_6462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6462_, 0, v_a_6456_);
v___x_6461_ = v_reuseFailAlloc_6462_;
goto v_reusejp_6460_;
}
v_reusejp_6460_:
{
v___y_6402_ = v___y_6430_;
v___y_6403_ = v___x_6446_;
v___y_6404_ = v___y_6431_;
v___y_6405_ = v___y_6432_;
v___y_6406_ = v___y_6433_;
v___y_6407_ = v___y_6434_;
v___y_6408_ = v___y_6435_;
v___y_6409_ = v___y_6436_;
v___y_6410_ = v___y_6437_;
v___y_6411_ = v___y_6438_;
v___y_6412_ = v_a_6443_;
v___y_6413_ = v___y_6439_;
v___y_6414_ = v___y_6440_;
v___y_6415_ = v___y_6441_;
v_a_6416_ = v___x_6461_;
goto v___jp_6401_;
}
}
}
}
else
{
lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6464_ = lean_io_get_num_heartbeats();
v___x_6465_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6428_, v___y_6430_, v___y_6434_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
if (lean_obj_tag(v___x_6465_) == 0)
{
lean_object* v_a_6466_; lean_object* v___x_6468_; uint8_t v_isShared_6469_; uint8_t v_isSharedCheck_6473_; 
v_a_6466_ = lean_ctor_get(v___x_6465_, 0);
v_isSharedCheck_6473_ = !lean_is_exclusive(v___x_6465_);
if (v_isSharedCheck_6473_ == 0)
{
v___x_6468_ = v___x_6465_;
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
else
{
lean_inc(v_a_6466_);
lean_dec(v___x_6465_);
v___x_6468_ = lean_box(0);
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
v_resetjp_6467_:
{
lean_object* v___x_6471_; 
if (v_isShared_6469_ == 0)
{
lean_ctor_set_tag(v___x_6468_, 1);
v___x_6471_ = v___x_6468_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_a_6466_);
v___x_6471_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
v___y_6378_ = v___y_6430_;
v___y_6379_ = v___y_6431_;
v___y_6380_ = v___y_6432_;
v___y_6381_ = v___y_6433_;
v___y_6382_ = v___y_6434_;
v___y_6383_ = v___y_6435_;
v___y_6384_ = v___y_6436_;
v___y_6385_ = v___x_6464_;
v___y_6386_ = v___y_6437_;
v___y_6387_ = v___y_6438_;
v___y_6388_ = v_a_6443_;
v___y_6389_ = v___y_6439_;
v___y_6390_ = v___y_6440_;
v___y_6391_ = v___y_6441_;
v_a_6392_ = v___x_6471_;
goto v___jp_6377_;
}
}
}
else
{
lean_object* v_a_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6481_; 
v_a_6474_ = lean_ctor_get(v___x_6465_, 0);
v_isSharedCheck_6481_ = !lean_is_exclusive(v___x_6465_);
if (v_isSharedCheck_6481_ == 0)
{
v___x_6476_ = v___x_6465_;
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_a_6474_);
lean_dec(v___x_6465_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v___x_6479_; 
if (v_isShared_6477_ == 0)
{
lean_ctor_set_tag(v___x_6476_, 0);
v___x_6479_ = v___x_6476_;
goto v_reusejp_6478_;
}
else
{
lean_object* v_reuseFailAlloc_6480_; 
v_reuseFailAlloc_6480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6480_, 0, v_a_6474_);
v___x_6479_ = v_reuseFailAlloc_6480_;
goto v_reusejp_6478_;
}
v_reusejp_6478_:
{
v___y_6378_ = v___y_6430_;
v___y_6379_ = v___y_6431_;
v___y_6380_ = v___y_6432_;
v___y_6381_ = v___y_6433_;
v___y_6382_ = v___y_6434_;
v___y_6383_ = v___y_6435_;
v___y_6384_ = v___y_6436_;
v___y_6385_ = v___x_6464_;
v___y_6386_ = v___y_6437_;
v___y_6387_ = v___y_6438_;
v___y_6388_ = v_a_6443_;
v___y_6389_ = v___y_6439_;
v___y_6390_ = v___y_6440_;
v___y_6391_ = v___y_6441_;
v_a_6392_ = v___x_6479_;
goto v___jp_6377_;
}
}
}
}
}
v___jp_6482_:
{
lean_object* v___f_6484_; size_t v_sz_6485_; size_t v___x_6486_; lean_object* v_assignments_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v_funVals_6490_; lean_object* v_ctx_6491_; lean_object* v_state_6492_; lean_object* v___x_6493_; uint8_t v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v_toCold_6497_; lean_object* v_options_6498_; uint8_t v_hasTrace_6499_; 
lean_inc_ref_n(v___y_6483_, 3);
v___f_6484_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6484_, 0, v___y_6483_);
v_sz_6485_ = lean_array_size(v___y_6483_);
v___x_6486_ = ((size_t)0ULL);
v_assignments_6487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6485_, v___x_6486_, v___y_6483_);
v___x_6488_ = lean_array_get_size(v___y_6483_);
v___x_6489_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2));
v_funVals_6490_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6483_, v___x_6488_, v___x_6488_, v___x_6489_);
v_ctx_6491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6491_, 0, v___y_6483_);
lean_ctor_set(v_ctx_6491_, 1, v___x_6428_);
v_state_6492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6492_, 0, v_assignments_6487_);
lean_ctor_set(v_state_6492_, 1, v_funVals_6490_);
v___x_6493_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6494_ = 1;
v___x_6495_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6496_ = lean_st_mk_ref(v_state_6492_);
v_toCold_6497_ = lean_ctor_get(v_a_6334_, 0);
v_options_6498_ = lean_ctor_get(v_toCold_6497_, 2);
v_hasTrace_6499_ = lean_ctor_get_uint8(v_options_6498_, sizeof(void*)*1);
if (v_hasTrace_6499_ == 0)
{
lean_object* v___x_6500_; 
lean_dec_ref(v___f_6484_);
v___x_6500_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6428_, v_ctx_6491_, v___x_6496_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
lean_dec_ref_known(v_ctx_6491_, 2);
v___y_6338_ = v___y_6483_;
v___y_6339_ = v_sz_6485_;
v___y_6340_ = v___x_6488_;
v___y_6341_ = v___x_6496_;
v___y_6342_ = v___x_6486_;
v___y_6343_ = v___x_6500_;
goto v___jp_6337_;
}
else
{
lean_object* v_inheritedTraceOptions_6501_; lean_object* v___x_6502_; uint8_t v___x_6503_; 
v_inheritedTraceOptions_6501_ = lean_ctor_get(v_toCold_6497_, 11);
v___x_6502_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6501_, v_options_6498_, v___x_6502_);
if (v___x_6503_ == 0)
{
lean_object* v___x_6504_; uint8_t v___x_6505_; 
v___x_6504_ = l_Lean_trace_profiler;
v___x_6505_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6498_, v___x_6504_);
if (v___x_6505_ == 0)
{
lean_object* v___x_6506_; 
lean_dec_ref(v___f_6484_);
v___x_6506_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6428_, v_ctx_6491_, v___x_6496_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
lean_dec_ref_known(v_ctx_6491_, 2);
v___y_6338_ = v___y_6483_;
v___y_6339_ = v_sz_6485_;
v___y_6340_ = v___x_6488_;
v___y_6341_ = v___x_6496_;
v___y_6342_ = v___x_6486_;
v___y_6343_ = v___x_6506_;
goto v___jp_6337_;
}
else
{
v___y_6430_ = v_ctx_6491_;
v___y_6431_ = v___x_6495_;
v___y_6432_ = v___y_6483_;
v___y_6433_ = v___x_6493_;
v___y_6434_ = v___x_6496_;
v___y_6435_ = v___f_6484_;
v___y_6436_ = v___x_6503_;
v___y_6437_ = v_sz_6485_;
v___y_6438_ = v___x_6494_;
v___y_6439_ = v_options_6498_;
v___y_6440_ = v___x_6488_;
v___y_6441_ = v___x_6486_;
goto v___jp_6429_;
}
}
else
{
v___y_6430_ = v_ctx_6491_;
v___y_6431_ = v___x_6495_;
v___y_6432_ = v___y_6483_;
v___y_6433_ = v___x_6493_;
v___y_6434_ = v___x_6496_;
v___y_6435_ = v___f_6484_;
v___y_6436_ = v___x_6503_;
v___y_6437_ = v_sz_6485_;
v___y_6438_ = v___x_6494_;
v___y_6439_ = v_options_6498_;
v___y_6440_ = v___x_6488_;
v___y_6441_ = v___x_6486_;
goto v___jp_6429_;
}
}
}
v___jp_6508_:
{
lean_object* v___x_6511_; 
v___x_6511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6507_, v_decls_6331_, v___y_6509_, v___y_6510_);
lean_dec(v___y_6510_);
v___y_6483_ = v___x_6511_;
goto v___jp_6482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6519_, lean_object* v_a_6520_, lean_object* v_a_6521_, lean_object* v_a_6522_, lean_object* v_a_6523_, lean_object* v_a_6524_){
_start:
{
lean_object* v_res_6525_; 
v_res_6525_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6519_, v_a_6520_, v_a_6521_, v_a_6522_, v_a_6523_);
lean_dec(v_a_6523_);
lean_dec_ref(v_a_6522_);
lean_dec(v_a_6521_);
lean_dec_ref(v_a_6520_);
return v_res_6525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6526_, lean_object* v_n_6527_, lean_object* v_j_6528_, lean_object* v_a_6529_, lean_object* v_a_6530_){
_start:
{
lean_object* v___x_6531_; 
v___x_6531_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6526_, v_n_6527_, v_j_6528_, v_a_6530_);
return v___x_6531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6532_, lean_object* v_n_6533_, lean_object* v_j_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_){
_start:
{
lean_object* v_res_6537_; 
v_res_6537_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6532_, v_n_6533_, v_j_6534_, v_a_6535_, v_a_6536_);
lean_dec(v_n_6533_);
lean_dec_ref(v___y_6532_);
return v_res_6537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6538_, lean_object* v___x_6539_, lean_object* v_n_6540_, lean_object* v_j_6541_, lean_object* v_a_6542_, lean_object* v_a_6543_){
_start:
{
lean_object* v___x_6544_; 
v___x_6544_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6538_, v___x_6539_, v_n_6540_, v_j_6541_, v_a_6543_);
return v___x_6544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6545_, lean_object* v___x_6546_, lean_object* v_n_6547_, lean_object* v_j_6548_, lean_object* v_a_6549_, lean_object* v_a_6550_){
_start:
{
lean_object* v_res_6551_; 
v_res_6551_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6545_, v___x_6546_, v_n_6547_, v_j_6548_, v_a_6549_, v_a_6550_);
lean_dec(v_n_6547_);
lean_dec_ref(v___x_6546_);
lean_dec_ref(v___y_6545_);
return v_res_6551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6552_, lean_object* v_as_6553_, size_t v_sz_6554_, size_t v_i_6555_, lean_object* v_bs_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_){
_start:
{
lean_object* v___x_6562_; 
v___x_6562_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6552_, v_sz_6554_, v_i_6555_, v_bs_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
return v___x_6562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6563_, lean_object* v_as_6564_, lean_object* v_sz_6565_, lean_object* v_i_6566_, lean_object* v_bs_6567_, lean_object* v___y_6568_, lean_object* v___y_6569_, lean_object* v___y_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_){
_start:
{
size_t v_sz_boxed_6573_; size_t v_i_boxed_6574_; lean_object* v_res_6575_; 
v_sz_boxed_6573_ = lean_unbox_usize(v_sz_6565_);
lean_dec(v_sz_6565_);
v_i_boxed_6574_ = lean_unbox_usize(v_i_6566_);
lean_dec(v_i_6566_);
v_res_6575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6563_, v_as_6564_, v_sz_boxed_6573_, v_i_boxed_6574_, v_bs_6567_, v___y_6568_, v___y_6569_, v___y_6570_, v___y_6571_);
lean_dec(v___y_6571_);
lean_dec_ref(v___y_6570_);
lean_dec(v___y_6569_);
lean_dec_ref(v___y_6568_);
lean_dec_ref(v_as_6564_);
lean_dec_ref(v___x_6563_);
return v_res_6575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6576_, lean_object* v_as_6577_, lean_object* v_lo_6578_, lean_object* v_hi_6579_, lean_object* v_w_6580_, lean_object* v_hlo_6581_, lean_object* v_hhi_6582_){
_start:
{
lean_object* v___x_6583_; 
v___x_6583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6576_, v_as_6577_, v_lo_6578_, v_hi_6579_);
return v___x_6583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6584_, lean_object* v_as_6585_, lean_object* v_lo_6586_, lean_object* v_hi_6587_, lean_object* v_w_6588_, lean_object* v_hlo_6589_, lean_object* v_hhi_6590_){
_start:
{
lean_object* v_res_6591_; 
v_res_6591_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6584_, v_as_6585_, v_lo_6586_, v_hi_6587_, v_w_6588_, v_hlo_6589_, v_hhi_6590_);
lean_dec(v_hi_6587_);
lean_dec(v_n_6584_);
return v_res_6591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6592_, lean_object* v_lo_6593_, lean_object* v_hi_6594_, lean_object* v_hhi_6595_, lean_object* v_pivot_6596_, lean_object* v_as_6597_, lean_object* v_i_6598_, lean_object* v_k_6599_, lean_object* v_ilo_6600_, lean_object* v_ik_6601_, lean_object* v_w_6602_){
_start:
{
lean_object* v___x_6603_; 
v___x_6603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6594_, v_pivot_6596_, v_as_6597_, v_i_6598_, v_k_6599_);
return v___x_6603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6604_, lean_object* v_lo_6605_, lean_object* v_hi_6606_, lean_object* v_hhi_6607_, lean_object* v_pivot_6608_, lean_object* v_as_6609_, lean_object* v_i_6610_, lean_object* v_k_6611_, lean_object* v_ilo_6612_, lean_object* v_ik_6613_, lean_object* v_w_6614_){
_start:
{
lean_object* v_res_6615_; 
v_res_6615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6604_, v_lo_6605_, v_hi_6606_, v_hhi_6607_, v_pivot_6608_, v_as_6609_, v_i_6610_, v_k_6611_, v_ilo_6612_, v_ik_6613_, v_w_6614_);
lean_dec(v_hi_6606_);
lean_dec(v_lo_6605_);
lean_dec(v_n_6604_);
return v_res_6615_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; 
v___x_6675_ = lean_unsigned_to_nat(3955956072u);
v___x_6676_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6677_ = l_Lean_Name_num___override(v___x_6676_, v___x_6675_);
return v___x_6677_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; 
v___x_6679_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6680_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6681_ = l_Lean_Name_str___override(v___x_6680_, v___x_6679_);
return v___x_6681_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; 
v___x_6683_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6684_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6685_ = l_Lean_Name_str___override(v___x_6684_, v___x_6683_);
return v___x_6685_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; 
v___x_6686_ = lean_unsigned_to_nat(2u);
v___x_6687_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6688_ = l_Lean_Name_num___override(v___x_6687_, v___x_6686_);
return v___x_6688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6690_; uint8_t v___x_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; 
v___x_6690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6691_ = 1;
v___x_6692_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6693_ = l_Lean_registerTraceClass(v___x_6690_, v___x_6691_, v___x_6692_);
return v___x_6693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6694_){
_start:
{
lean_object* v_res_6695_; 
v_res_6695_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6695_;
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
