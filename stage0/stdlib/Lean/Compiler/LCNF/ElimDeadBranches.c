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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_983_ = l_instMonadEIO___redArg();
return v___x_983_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go_spec__0___closed__3(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Array_instInhabited___redArg();
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
lean_object* v_v_1281_; lean_object* v___x_1282_; lean_object* v_bs_x27_1283_; lean_object* v___x_1284_; 
v_v_1281_ = lean_array_uget(v_bs_1273_, v_i_1272_);
v___x_1282_ = lean_unsigned_to_nat(0u);
v_bs_x27_1283_ = lean_array_uset(v_bs_1273_, v_i_1272_, v___x_1282_);
v___x_1284_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral_go(v_v_1281_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = ((size_t)1ULL);
v___x_1287_ = lean_usize_add(v_i_1272_, v___x_1286_);
v___x_1288_ = lean_array_uset(v_bs_x27_1283_, v_i_1272_, v_a_1285_);
v_i_1272_ = v___x_1287_;
v_bs_1273_ = v___x_1288_;
goto _start;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_bs_x27_1283_);
v_a_1290_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1284_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1284_);
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
size_t v_x_1144__boxed_1428_; uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_x_1144__boxed_1428_ = lean_unbox_usize(v_x_1426_);
lean_dec(v_x_1426_);
v_res_1429_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1425_, v_x_1144__boxed_1428_, v_x_1427_);
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
v___x_1644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_1686_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_1538__boxed_1793_; size_t v_x_1539__boxed_1794_; lean_object* v_res_1795_; 
v_x_1538__boxed_1793_ = lean_unbox_usize(v_x_1789_);
lean_dec(v_x_1789_);
v_x_1539__boxed_1794_ = lean_unbox_usize(v_x_1790_);
lean_dec(v_x_1790_);
v_res_1795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6___redArg(v_x_1788_, v_x_1538__boxed_1793_, v_x_1539__boxed_1794_, v_x_1791_, v_x_1792_);
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
size_t v_x_1838__boxed_1892_; uint8_t v_res_1893_; lean_object* v_r_1894_; 
v_x_1838__boxed_1892_ = lean_unbox_usize(v_x_1890_);
lean_dec(v_x_1890_);
v_res_1893_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1888_, v_x_1889_, v_x_1838__boxed_1892_, v_x_1891_);
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
size_t v_x_1853__boxed_1944_; size_t v_x_1854__boxed_1945_; lean_object* v_res_1946_; 
v_x_1853__boxed_1944_ = lean_unbox_usize(v_x_1940_);
lean_dec(v_x_1940_);
v_x_1854__boxed_1945_ = lean_unbox_usize(v_x_1941_);
lean_dec(v_x_1941_);
v_res_1946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1938_, v_x_1939_, v_x_1853__boxed_1944_, v_x_1854__boxed_1945_, v_x_1942_, v_x_1943_);
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
size_t v_x_412__boxed_2118_; lean_object* v_res_2119_; 
v_x_412__boxed_2118_ = lean_unbox_usize(v_x_2116_);
lean_dec(v_x_2116_);
v_res_2119_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2115_, v_x_412__boxed_2118_, v_x_2117_);
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
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0(void){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0);
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2163_, lean_object* v_fid_2164_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2174_; 
v___x_2165_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1);
v___x_2166_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2174_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2163_, v_fid_2164_);
if (lean_obj_tag(v___x_2174_) == 0)
{
goto v___jp_2167_;
}
else
{
lean_object* v_val_2175_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_val_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2197_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_2165_, v___x_2166_, v_env_2163_, v_val_2175_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_array_get_size(v___x_2197_);
v___x_2200_ = lean_nat_dec_lt(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_dec_ref(v___x_2197_);
goto v___jp_2176_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_sub(v___x_2199_, v___x_2201_);
v___x_2203_ = lean_nat_dec_le(v___x_2198_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_dec(v___x_2202_);
lean_dec_ref(v___x_2197_);
goto v___jp_2176_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_box(0);
lean_inc(v_fid_2164_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_fid_2164_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2197_, v___x_2205_, v___x_2198_, v___x_2202_);
lean_dec_ref_known(v___x_2205_, 2);
lean_dec_ref(v___x_2197_);
if (lean_obj_tag(v___x_2206_) == 0)
{
goto v___jp_2176_;
}
else
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_val_2175_);
lean_dec(v_fid_2164_);
lean_dec_ref(v_env_2163_);
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_snd_2211_; lean_object* v___x_2213_; 
v_snd_2211_ = lean_ctor_get(v_val_2207_, 1);
lean_inc(v_snd_2211_);
lean_dec(v_val_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_snd_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_snd_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
v___jp_2176_:
{
uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2177_ = 0;
v___x_2178_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2165_, v___x_2166_, v_env_2163_, v_val_2175_, v___x_2177_);
lean_dec(v_val_2175_);
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_array_get_size(v___x_2178_);
v___x_2181_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_dec_ref(v___x_2178_);
goto v___jp_2167_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_nat_sub(v___x_2180_, v___x_2182_);
v___x_2184_ = lean_nat_dec_le(v___x_2179_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2178_);
goto v___jp_2167_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = lean_box(0);
lean_inc(v_fid_2164_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_fid_2164_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2178_, v___x_2186_, v___x_2179_, v___x_2183_);
lean_dec_ref_known(v___x_2186_, 2);
lean_dec_ref(v___x_2178_);
if (lean_obj_tag(v___x_2187_) == 0)
{
goto v___jp_2167_;
}
else
{
lean_object* v_val_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_fid_2164_);
lean_dec_ref(v_env_2163_);
v_val_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_val_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v_snd_2192_; lean_object* v___x_2194_; 
v_snd_2192_ = lean_ctor_get(v_val_2188_, 1);
lean_inc(v_snd_2192_);
lean_dec(v_val_2188_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v_snd_2192_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_snd_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
}
v___jp_2167_:
{
lean_object* v_toEnvExtension_2168_; lean_object* v_asyncMode_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v_snd_2172_; lean_object* v___x_2173_; 
v_toEnvExtension_2168_ = lean_ctor_get(v___x_2166_, 0);
v_asyncMode_2169_ = lean_ctor_get(v_toEnvExtension_2168_, 2);
v___x_2170_ = lean_box(0);
v___x_2171_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2165_, v___x_2166_, v_env_2163_, v_asyncMode_2169_, v___x_2170_);
v_snd_2172_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_snd_2172_);
lean_dec(v___x_2171_);
v___x_2173_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2172_, v_fid_2164_);
lean_dec(v_fid_2164_);
lean_dec(v_snd_2172_);
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2217_, v_x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2220_, v_x_2221_, v_x_2222_);
lean_dec(v_x_2222_);
lean_dec_ref(v_x_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2224_, lean_object* v_k_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2224_, v_k_2225_, v_x_2226_, v_x_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2230_, lean_object* v_k_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2230_, v_k_2231_, v_x_2232_, v_x_2233_, v_x_2234_);
lean_dec_ref(v_k_2231_);
lean_dec_ref(v_as_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2236_, lean_object* v_x_2237_, size_t v_x_2238_, lean_object* v_x_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2237_, v_x_2238_, v_x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_, lean_object* v_x_2244_){
_start:
{
size_t v_x_638__boxed_2245_; lean_object* v_res_2246_; 
v_x_638__boxed_2245_ = lean_unbox_usize(v_x_2243_);
lean_dec(v_x_2243_);
v_res_2246_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2241_, v_x_2242_, v_x_638__boxed_2245_, v_x_2244_);
lean_dec(v_x_2244_);
lean_dec_ref(v_x_2242_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2247_, lean_object* v_keys_2248_, lean_object* v_vals_2249_, lean_object* v_heq_2250_, lean_object* v_i_2251_, lean_object* v_k_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2248_, v_vals_2249_, v_i_2251_, v_k_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2254_, lean_object* v_keys_2255_, lean_object* v_vals_2256_, lean_object* v_heq_2257_, lean_object* v_i_2258_, lean_object* v_k_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2254_, v_keys_2255_, v_vals_2256_, v_heq_2257_, v_i_2258_, v_k_2259_);
lean_dec(v_k_2259_);
lean_dec_ref(v_vals_2256_);
lean_dec_ref(v_keys_2255_);
return v_res_2260_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0(void){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v_assignments_2267_; lean_object* v_currFnIdx_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2265_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0);
v___x_2266_ = lean_st_ref_get(v_a_2263_);
v_assignments_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc_ref(v_assignments_2267_);
lean_dec(v___x_2266_);
v_currFnIdx_2268_ = lean_ctor_get(v_a_2262_, 1);
v___x_2269_ = lean_array_get(v___x_2265_, v_assignments_2267_, v_currFnIdx_2268_);
lean_dec_ref(v_assignments_2267_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2275_, v_a_2276_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v_funVals_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_st_ref_get(v_a_2292_);
v_funVals_2296_ = lean_ctor_get(v___x_2295_, 1);
lean_inc_ref(v_funVals_2296_);
lean_dec(v___x_2295_);
v___x_2297_ = lean_array_get(v___x_2294_, v_funVals_2296_, v_funIdx_2291_);
lean_dec_ref(v_funVals_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec(v_funIdx_2299_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2303_, v_a_2305_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_funIdx_2312_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(lean_object* v_declName_2321_, lean_object* v_as_2322_, lean_object* v_j_2323_){
_start:
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_array_get_size(v_as_2322_);
v___x_2325_ = lean_nat_dec_lt(v_j_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
lean_dec(v_j_2323_);
v___x_2326_ = lean_box(0);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v_toSignature_2328_; lean_object* v_name_2329_; uint8_t v___x_2330_; 
v___x_2327_ = lean_array_fget_borrowed(v_as_2322_, v_j_2323_);
v_toSignature_2328_ = lean_ctor_get(v___x_2327_, 0);
v_name_2329_ = lean_ctor_get(v_toSignature_2328_, 0);
v___x_2330_ = lean_name_eq(v_name_2329_, v_declName_2321_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_nat_add(v_j_2323_, v___x_2331_);
lean_dec(v_j_2323_);
v_j_2323_ = v___x_2332_;
goto _start;
}
else
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_j_2323_);
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0___boxed(lean_object* v_declName_2335_, lean_object* v_as_2336_, lean_object* v_j_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2335_, v_as_2336_, v_j_2337_);
lean_dec_ref(v_as_2336_);
lean_dec(v_declName_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_decls_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_decls_2343_ = lean_ctor_get(v_a_2340_, 0);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f_spec__0(v_declName_2339_, v_decls_2343_, v___x_2344_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
else
{
lean_object* v_val_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2364_; 
v_val_2348_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2350_ = v___x_2345_;
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_val_2348_);
lean_dec(v___x_2345_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2363_; 
v___x_2352_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2348_, v_a_2341_);
lean_dec(v_val_2348_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_a_2353_);
v___x_2358_ = v___x_2350_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2358_);
v___x_2360_ = v___x_2355_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_declName_2365_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2370_, v_a_2371_, v_a_2372_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_declName_2379_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_currFnIdx_2392_; lean_object* v___x_2393_; lean_object* v_assignments_2394_; lean_object* v_funVals_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2413_; 
v_currFnIdx_2392_ = lean_ctor_get(v_a_2389_, 1);
v___x_2393_ = lean_st_ref_take(v_a_2390_);
v_assignments_2394_ = lean_ctor_get(v___x_2393_, 0);
v_funVals_2395_ = lean_ctor_get(v___x_2393_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2397_ = v___x_2393_;
v_isShared_2398_ = v_isSharedCheck_2413_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_funVals_2395_);
lean_inc(v_assignments_2394_);
lean_dec(v___x_2393_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2413_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___y_2401_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2399_ = lean_box(0);
v___x_2407_ = lean_array_get_size(v_assignments_2394_);
v___x_2408_ = lean_nat_dec_lt(v_currFnIdx_2392_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v_f_2388_);
v___y_2401_ = v_assignments_2394_;
goto v___jp_2400_;
}
else
{
lean_object* v_v_2409_; lean_object* v_xs_x27_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_v_2409_ = lean_array_fget(v_assignments_2394_, v_currFnIdx_2392_);
v_xs_x27_2410_ = lean_array_fset(v_assignments_2394_, v_currFnIdx_2392_, v___x_2399_);
v___x_2411_ = lean_apply_1(v_f_2388_, v_v_2409_);
v___x_2412_ = lean_array_fset(v_xs_x27_2410_, v_currFnIdx_2392_, v___x_2411_);
v___y_2401_ = v___x_2412_;
goto v___jp_2400_;
}
v___jp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___y_2401_);
v___x_2403_ = v___x_2397_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___y_2401_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_funVals_2395_);
v___x_2403_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_st_ref_put(v_a_2390_, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2399_);
return v___x_2405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2419_, v_a_2420_, v_a_2421_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2437_, lean_object* v_fallback_2438_, lean_object* v_x_2439_){
_start:
{
if (lean_obj_tag(v_x_2439_) == 0)
{
lean_inc(v_fallback_2438_);
return v_fallback_2438_;
}
else
{
lean_object* v_key_2440_; lean_object* v_value_2441_; lean_object* v_tail_2442_; uint8_t v___x_2443_; 
v_key_2440_ = lean_ctor_get(v_x_2439_, 0);
v_value_2441_ = lean_ctor_get(v_x_2439_, 1);
v_tail_2442_ = lean_ctor_get(v_x_2439_, 2);
v___x_2443_ = l_Lean_instBEqFVarId_beq(v_key_2440_, v_a_2437_);
if (v___x_2443_ == 0)
{
v_x_2439_ = v_tail_2442_;
goto _start;
}
else
{
lean_inc(v_value_2441_);
return v_value_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2445_, lean_object* v_fallback_2446_, lean_object* v_x_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2445_, v_fallback_2446_, v_x_2447_);
lean_dec(v_x_2447_);
lean_dec(v_fallback_2446_);
lean_dec(v_a_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2449_, lean_object* v_a_2450_, lean_object* v_fallback_2451_){
_start:
{
lean_object* v_buckets_2452_; lean_object* v___x_2453_; uint64_t v___x_2454_; uint64_t v___x_2455_; uint64_t v___x_2456_; uint64_t v_fold_2457_; uint64_t v___x_2458_; uint64_t v___x_2459_; uint64_t v___x_2460_; size_t v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; size_t v___x_2464_; size_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_buckets_2452_ = lean_ctor_get(v_m_2449_, 1);
v___x_2453_ = lean_array_get_size(v_buckets_2452_);
v___x_2454_ = l_Lean_instHashableFVarId_hash(v_a_2450_);
v___x_2455_ = 32ULL;
v___x_2456_ = lean_uint64_shift_right(v___x_2454_, v___x_2455_);
v_fold_2457_ = lean_uint64_xor(v___x_2454_, v___x_2456_);
v___x_2458_ = 16ULL;
v___x_2459_ = lean_uint64_shift_right(v_fold_2457_, v___x_2458_);
v___x_2460_ = lean_uint64_xor(v_fold_2457_, v___x_2459_);
v___x_2461_ = lean_uint64_to_usize(v___x_2460_);
v___x_2462_ = lean_usize_of_nat(v___x_2453_);
v___x_2463_ = ((size_t)1ULL);
v___x_2464_ = lean_usize_sub(v___x_2462_, v___x_2463_);
v___x_2465_ = lean_usize_land(v___x_2461_, v___x_2464_);
v___x_2466_ = lean_array_uget_borrowed(v_buckets_2452_, v___x_2465_);
v___x_2467_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2450_, v_fallback_2451_, v___x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2468_, lean_object* v_a_2469_, lean_object* v_fallback_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2468_, v_a_2469_, v_fallback_2470_);
lean_dec(v_fallback_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_m_2468_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v___x_2476_; lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2486_; 
v___x_2476_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2473_, v_a_2474_);
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2477_, v_var_2472_, v___x_2481_);
lean_dec(v_a_2477_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v___x_2482_);
v___x_2484_ = v___x_2479_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_var_2487_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2492_, v_a_2493_, v_a_2494_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_var_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2510_, lean_object* v_m_2511_, lean_object* v_a_2512_, lean_object* v_fallback_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2511_, v_a_2512_, v_fallback_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2515_, lean_object* v_m_2516_, lean_object* v_a_2517_, lean_object* v_fallback_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2515_, v_m_2516_, v_a_2517_, v_fallback_2518_);
lean_dec(v_fallback_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_m_2516_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2520_, lean_object* v_a_2521_, lean_object* v_fallback_2522_, lean_object* v_x_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2521_, v_fallback_2522_, v_x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2525_, lean_object* v_a_2526_, lean_object* v_fallback_2527_, lean_object* v_x_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2525_, v_a_2526_, v_fallback_2527_, v_x_2528_);
lean_dec(v_x_2528_);
lean_dec(v_fallback_2527_);
lean_dec(v_a_2526_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
if (lean_obj_tag(v_arg_2530_) == 1)
{
lean_object* v_fvarId_2534_; lean_object* v___x_2535_; 
v_fvarId_2534_ = lean_ctor_get(v_arg_2530_, 0);
v___x_2535_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2534_, v_a_2531_, v_a_2532_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_box(1);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_arg_2538_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2543_, v_a_2544_, v_a_2545_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_arg_2552_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2561_, lean_object* v_b_2562_, lean_object* v_x_2563_){
_start:
{
if (lean_obj_tag(v_x_2563_) == 0)
{
lean_dec(v_b_2562_);
lean_dec(v_a_2561_);
return v_x_2563_;
}
else
{
lean_object* v_key_2564_; lean_object* v_value_2565_; lean_object* v_tail_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2578_; 
v_key_2564_ = lean_ctor_get(v_x_2563_, 0);
v_value_2565_ = lean_ctor_get(v_x_2563_, 1);
v_tail_2566_ = lean_ctor_get(v_x_2563_, 2);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_x_2563_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2568_ = v_x_2563_;
v_isShared_2569_ = v_isSharedCheck_2578_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_tail_2566_);
lean_inc(v_value_2565_);
lean_inc(v_key_2564_);
lean_dec(v_x_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2578_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
uint8_t v___x_2570_; 
v___x_2570_ = l_Lean_instBEqFVarId_beq(v_key_2564_, v_a_2561_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2561_, v_b_2562_, v_tail_2566_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 2, v___x_2571_);
v___x_2573_ = v___x_2568_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_key_2564_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_value_2565_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
else
{
lean_object* v___x_2576_; 
lean_dec(v_value_2565_);
lean_dec(v_key_2564_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v_b_2562_);
lean_ctor_set(v___x_2568_, 0, v_a_2561_);
v___x_2576_ = v___x_2568_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2561_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_b_2562_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_tail_2566_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2579_, lean_object* v_x_2580_){
_start:
{
if (lean_obj_tag(v_x_2580_) == 0)
{
return v_x_2579_;
}
else
{
lean_object* v_key_2581_; lean_object* v_value_2582_; lean_object* v_tail_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2606_; 
v_key_2581_ = lean_ctor_get(v_x_2580_, 0);
v_value_2582_ = lean_ctor_get(v_x_2580_, 1);
v_tail_2583_ = lean_ctor_get(v_x_2580_, 2);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_x_2580_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2585_ = v_x_2580_;
v_isShared_2586_ = v_isSharedCheck_2606_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_tail_2583_);
lean_inc(v_value_2582_);
lean_inc(v_key_2581_);
lean_dec(v_x_2580_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2606_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; uint64_t v___x_2588_; uint64_t v___x_2589_; uint64_t v___x_2590_; uint64_t v_fold_2591_; uint64_t v___x_2592_; uint64_t v___x_2593_; uint64_t v___x_2594_; size_t v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2587_ = lean_array_get_size(v_x_2579_);
v___x_2588_ = l_Lean_instHashableFVarId_hash(v_key_2581_);
v___x_2589_ = 32ULL;
v___x_2590_ = lean_uint64_shift_right(v___x_2588_, v___x_2589_);
v_fold_2591_ = lean_uint64_xor(v___x_2588_, v___x_2590_);
v___x_2592_ = 16ULL;
v___x_2593_ = lean_uint64_shift_right(v_fold_2591_, v___x_2592_);
v___x_2594_ = lean_uint64_xor(v_fold_2591_, v___x_2593_);
v___x_2595_ = lean_uint64_to_usize(v___x_2594_);
v___x_2596_ = lean_usize_of_nat(v___x_2587_);
v___x_2597_ = ((size_t)1ULL);
v___x_2598_ = lean_usize_sub(v___x_2596_, v___x_2597_);
v___x_2599_ = lean_usize_land(v___x_2595_, v___x_2598_);
v___x_2600_ = lean_array_uget_borrowed(v_x_2579_, v___x_2599_);
lean_inc(v___x_2600_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 2, v___x_2600_);
v___x_2602_ = v___x_2585_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_key_2581_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_value_2582_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_array_uset(v_x_2579_, v___x_2599_, v___x_2602_);
v_x_2579_ = v___x_2603_;
v_x_2580_ = v_tail_2583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2607_, lean_object* v_source_2608_, lean_object* v_target_2609_){
_start:
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = lean_array_get_size(v_source_2608_);
v___x_2611_ = lean_nat_dec_lt(v_i_2607_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_dec_ref(v_source_2608_);
lean_dec(v_i_2607_);
return v_target_2609_;
}
else
{
lean_object* v_es_2612_; lean_object* v___x_2613_; lean_object* v_source_2614_; lean_object* v_target_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_es_2612_ = lean_array_fget(v_source_2608_, v_i_2607_);
v___x_2613_ = lean_box(0);
v_source_2614_ = lean_array_fset(v_source_2608_, v_i_2607_, v___x_2613_);
v_target_2615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2609_, v_es_2612_);
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_add(v_i_2607_, v___x_2616_);
lean_dec(v_i_2607_);
v_i_2607_ = v___x_2617_;
v_source_2608_ = v_source_2614_;
v_target_2609_ = v_target_2615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2619_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_nbuckets_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2620_ = lean_array_get_size(v_data_2619_);
v___x_2621_ = lean_unsigned_to_nat(2u);
v_nbuckets_2622_ = lean_nat_mul(v___x_2620_, v___x_2621_);
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_mk_array(v_nbuckets_2622_, v___x_2624_);
v___x_2626_ = lean_array_propagate_mark(v_data_2619_, v___x_2625_);
v___x_2627_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2623_, v_data_2619_, v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2628_, lean_object* v_x_2629_){
_start:
{
if (lean_obj_tag(v_x_2629_) == 0)
{
uint8_t v___x_2630_; 
v___x_2630_ = 0;
return v___x_2630_;
}
else
{
lean_object* v_key_2631_; lean_object* v_tail_2632_; uint8_t v___x_2633_; 
v_key_2631_ = lean_ctor_get(v_x_2629_, 0);
v_tail_2632_ = lean_ctor_get(v_x_2629_, 2);
v___x_2633_ = l_Lean_instBEqFVarId_beq(v_key_2631_, v_a_2628_);
if (v___x_2633_ == 0)
{
v_x_2629_ = v_tail_2632_;
goto _start;
}
else
{
return v___x_2633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2635_, lean_object* v_x_2636_){
_start:
{
uint8_t v_res_2637_; lean_object* v_r_2638_; 
v_res_2637_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2635_, v_x_2636_);
lean_dec(v_x_2636_);
lean_dec(v_a_2635_);
v_r_2638_ = lean_box(v_res_2637_);
return v_r_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2639_, lean_object* v_a_2640_, lean_object* v_b_2641_){
_start:
{
lean_object* v_size_2642_; lean_object* v_buckets_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2686_; 
v_size_2642_ = lean_ctor_get(v_m_2639_, 0);
v_buckets_2643_ = lean_ctor_get(v_m_2639_, 1);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_m_2639_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2645_ = v_m_2639_;
v_isShared_2646_ = v_isSharedCheck_2686_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_buckets_2643_);
lean_inc(v_size_2642_);
lean_dec(v_m_2639_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2686_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; uint64_t v___x_2648_; uint64_t v___x_2649_; uint64_t v___x_2650_; uint64_t v_fold_2651_; uint64_t v___x_2652_; uint64_t v___x_2653_; uint64_t v___x_2654_; size_t v___x_2655_; size_t v___x_2656_; size_t v___x_2657_; size_t v___x_2658_; size_t v___x_2659_; lean_object* v_bkt_2660_; uint8_t v___x_2661_; 
v___x_2647_ = lean_array_get_size(v_buckets_2643_);
v___x_2648_ = l_Lean_instHashableFVarId_hash(v_a_2640_);
v___x_2649_ = 32ULL;
v___x_2650_ = lean_uint64_shift_right(v___x_2648_, v___x_2649_);
v_fold_2651_ = lean_uint64_xor(v___x_2648_, v___x_2650_);
v___x_2652_ = 16ULL;
v___x_2653_ = lean_uint64_shift_right(v_fold_2651_, v___x_2652_);
v___x_2654_ = lean_uint64_xor(v_fold_2651_, v___x_2653_);
v___x_2655_ = lean_uint64_to_usize(v___x_2654_);
v___x_2656_ = lean_usize_of_nat(v___x_2647_);
v___x_2657_ = ((size_t)1ULL);
v___x_2658_ = lean_usize_sub(v___x_2656_, v___x_2657_);
v___x_2659_ = lean_usize_land(v___x_2655_, v___x_2658_);
v_bkt_2660_ = lean_array_uget_borrowed(v_buckets_2643_, v___x_2659_);
v___x_2661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2640_, v_bkt_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v_size_x27_2663_; lean_object* v___x_2664_; lean_object* v_buckets_x27_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v_size_x27_2663_ = lean_nat_add(v_size_2642_, v___x_2662_);
lean_dec(v_size_2642_);
lean_inc(v_bkt_2660_);
v___x_2664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2664_, 0, v_a_2640_);
lean_ctor_set(v___x_2664_, 1, v_b_2641_);
lean_ctor_set(v___x_2664_, 2, v_bkt_2660_);
v_buckets_x27_2665_ = lean_array_uset(v_buckets_2643_, v___x_2659_, v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(4u);
v___x_2667_ = lean_nat_mul(v_size_x27_2663_, v___x_2666_);
v___x_2668_ = lean_unsigned_to_nat(3u);
v___x_2669_ = lean_nat_div(v___x_2667_, v___x_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_array_get_size(v_buckets_x27_2665_);
v___x_2671_ = lean_nat_dec_le(v___x_2669_, v___x_2670_);
lean_dec(v___x_2669_);
if (v___x_2671_ == 0)
{
lean_object* v_val_2672_; lean_object* v___x_2674_; 
v_val_2672_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2665_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v_val_2672_);
lean_ctor_set(v___x_2645_, 0, v_size_x27_2663_);
v___x_2674_ = v___x_2645_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_size_x27_2663_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_val_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
else
{
lean_object* v___x_2677_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v_buckets_x27_2665_);
lean_ctor_set(v___x_2645_, 0, v_size_x27_2663_);
v___x_2677_ = v___x_2645_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_size_x27_2663_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_buckets_x27_2665_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v___x_2679_; lean_object* v_buckets_x27_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_inc(v_bkt_2660_);
v___x_2679_ = lean_box(0);
v_buckets_x27_2680_ = lean_array_uset(v_buckets_2643_, v___x_2659_, v___x_2679_);
v___x_2681_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2640_, v_b_2641_, v_bkt_2660_);
v___x_2682_ = lean_array_uset(v_buckets_x27_2680_, v___x_2659_, v___x_2681_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2682_);
v___x_2684_ = v___x_2645_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_size_2642_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2687_, lean_object* v___x_2688_, lean_object* v_x_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2689_, v_var_2687_, v___x_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2691_, lean_object* v_newVal_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v___x_2697_; lean_object* v_env_2698_; lean_object* v___x_2699_; 
v___x_2697_ = lean_st_ref_get(v_a_2695_);
v_env_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc_ref(v_env_2698_);
lean_dec(v___x_2697_);
v___x_2699_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2691_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2701_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2698_, v_a_2700_, v_newVal_2692_);
v___f_2702_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2702_, 0, v_var_2691_);
lean_closure_set(v___f_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2702_, v_a_2693_, v_a_2694_);
return v___x_2703_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_env_2698_);
lean_dec(v_newVal_2692_);
lean_dec(v_var_2691_);
v_a_2704_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2699_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2699_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2712_, lean_object* v_newVal_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2712_, v_newVal_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2719_, lean_object* v_newVal_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2719_, v_newVal_2720_, v_a_2721_, v_a_2722_, v_a_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2729_, lean_object* v_newVal_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2729_, v_newVal_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2739_, lean_object* v_m_2740_, lean_object* v_a_2741_, lean_object* v_b_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2740_, v_a_2741_, v_b_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2744_, lean_object* v_a_2745_, lean_object* v_x_2746_){
_start:
{
uint8_t v___x_2747_; 
v___x_2747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2745_, v_x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2748_, lean_object* v_a_2749_, lean_object* v_x_2750_){
_start:
{
uint8_t v_res_2751_; lean_object* v_r_2752_; 
v_res_2751_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2748_, v_a_2749_, v_x_2750_);
lean_dec(v_x_2750_);
lean_dec(v_a_2749_);
v_r_2752_ = lean_box(v_res_2751_);
return v_r_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2753_, lean_object* v_data_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2756_, lean_object* v_a_2757_, lean_object* v_b_2758_, lean_object* v_x_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2757_, v_b_2758_, v_x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2761_, lean_object* v_i_2762_, lean_object* v_source_2763_, lean_object* v_target_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2762_, v_source_2763_, v_target_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2766_, lean_object* v_x_2767_, lean_object* v_x_2768_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2767_, v_x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2771_, v_var_2770_, v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___f_2778_; lean_object* v___x_2779_; 
v___f_2778_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2778_, 0, v_var_2774_);
v___x_2779_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2778_, v_a_2775_, v_a_2776_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2780_, v_a_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2785_, v_a_2786_, v_a_2787_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2808_; lean_object* v_env_2809_; lean_object* v_currFnIdx_2810_; lean_object* v___x_2811_; lean_object* v_fst_2813_; lean_object* v_snd_2814_; lean_object* v_assignments_2817_; lean_object* v_funVals_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2808_ = lean_st_ref_get(v_a_2806_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v_currFnIdx_2810_ = lean_ctor_get(v_a_2804_, 1);
v___x_2811_ = lean_st_ref_take(v_a_2805_);
v_assignments_2817_ = lean_ctor_get(v___x_2811_, 0);
lean_inc_ref(v_assignments_2817_);
v_funVals_2818_ = lean_ctor_get(v___x_2811_, 1);
lean_inc_ref(v_funVals_2818_);
v___x_2819_ = lean_box(0);
v___x_2820_ = lean_array_get_size(v_funVals_2818_);
v___x_2821_ = lean_nat_dec_lt(v_currFnIdx_2810_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec_ref(v_funVals_2818_);
lean_dec_ref(v_assignments_2817_);
lean_dec_ref(v_env_2809_);
lean_dec(v_v_2803_);
v_fst_2813_ = v___x_2819_;
v_snd_2814_ = v___x_2811_;
goto v___jp_2812_;
}
else
{
lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2832_; 
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; lean_object* v_unused_2834_; 
v_unused_2833_ = lean_ctor_get(v___x_2811_, 1);
lean_dec(v_unused_2833_);
v_unused_2834_ = lean_ctor_get(v___x_2811_, 0);
lean_dec(v_unused_2834_);
v___x_2823_ = v___x_2811_;
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
else
{
lean_dec(v___x_2811_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_v_2825_; lean_object* v_xs_x27_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v_v_2825_ = lean_array_fget(v_funVals_2818_, v_currFnIdx_2810_);
v_xs_x27_2826_ = lean_array_fset(v_funVals_2818_, v_currFnIdx_2810_, v___x_2819_);
v___x_2827_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2809_, v_v_2803_, v_v_2825_);
v___x_2828_ = lean_array_fset(v_xs_x27_2826_, v_currFnIdx_2810_, v___x_2827_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2828_);
v___x_2830_ = v___x_2823_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_assignments_2817_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
v_fst_2813_ = v___x_2819_;
v_snd_2814_ = v___x_2830_;
goto v___jp_2812_;
}
}
}
v___jp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_st_ref_put(v_a_2805_, v_snd_2814_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_fst_2813_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2835_, v_a_2836_, v_a_2837_, v_a_2838_);
lean_dec(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2841_, v_a_2842_, v_a_2843_, v_a_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2859_, uint8_t v_b_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_array_2865_; lean_object* v_start_2866_; lean_object* v_stop_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2904_; 
v_array_2865_ = lean_ctor_get(v_a_2859_, 0);
v_start_2866_ = lean_ctor_get(v_a_2859_, 1);
v_stop_2867_ = lean_ctor_get(v_a_2859_, 2);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_a_2859_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2869_ = v_a_2859_;
v_isShared_2870_ = v_isSharedCheck_2904_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_stop_2867_);
lean_inc(v_start_2866_);
lean_inc(v_array_2865_);
lean_dec(v_a_2859_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2904_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_nat_dec_lt(v_start_2866_, v_stop_2867_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_del_object(v___x_2869_);
lean_dec(v_stop_2867_);
lean_dec(v_start_2866_);
lean_dec_ref(v_array_2865_);
v___x_2872_ = lean_box(v_b_2860_);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; lean_object* v_fvarId_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2874_ = lean_array_fget_borrowed(v_array_2865_, v_start_2866_);
v_fvarId_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_fvarId_2875_);
v___x_2876_ = lean_unsigned_to_nat(1u);
v___x_2877_ = lean_nat_add(v_start_2866_, v___x_2876_);
lean_dec(v_start_2866_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 1, v___x_2877_);
v___x_2879_ = v___x_2869_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_array_2865_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_stop_2867_);
v___x_2879_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2875_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = lean_box(0);
v___x_2883_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2881_, v___x_2882_);
lean_dec(v_a_2881_);
v___x_2884_ = lean_box(1);
v___x_2885_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2875_, v___x_2884_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_dec_ref_known(v___x_2885_, 1);
v_a_2859_ = v___x_2879_;
v_b_2860_ = v___x_2883_;
goto _start;
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v___x_2879_);
v_a_2887_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2885_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2885_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v___x_2879_);
lean_dec(v_fvarId_2875_);
v_a_2895_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2880_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2880_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2905_, lean_object* v_b_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v_b_boxed_2911_; lean_object* v_res_2912_; 
v_b_boxed_2911_ = lean_unbox(v_b_2906_);
v_res_2912_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2905_, v_b_boxed_2911_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2913_, lean_object* v___x_2914_, lean_object* v_x_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2915_, v_fvarId_2913_, v___x_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2917_, lean_object* v_as_2918_, size_t v_sz_2919_, size_t v_i_2920_, lean_object* v_b_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_a_2926_; uint8_t v___x_2930_; 
v___x_2930_ = lean_usize_dec_lt(v_i_2920_, v_sz_2919_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; 
lean_dec_ref(v___x_2917_);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_b_2921_);
return v___x_2931_;
}
else
{
lean_object* v_snd_2932_; lean_object* v_fst_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2999_; 
v_snd_2932_ = lean_ctor_get(v_b_2921_, 1);
v_fst_2933_ = lean_ctor_get(v_b_2921_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_b_2921_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2935_ = v_b_2921_;
v_isShared_2936_ = v_isSharedCheck_2999_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_snd_2932_);
lean_inc(v_fst_2933_);
lean_dec(v_b_2921_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2999_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v_array_2937_; lean_object* v_start_2938_; lean_object* v_stop_2939_; uint8_t v___x_2940_; 
v_array_2937_ = lean_ctor_get(v_snd_2932_, 0);
v_start_2938_ = lean_ctor_get(v_snd_2932_, 1);
v_stop_2939_ = lean_ctor_get(v_snd_2932_, 2);
v___x_2940_ = lean_nat_dec_lt(v_start_2938_, v_stop_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2942_; 
lean_dec_ref(v___x_2917_);
if (v_isShared_2936_ == 0)
{
v___x_2942_ = v___x_2935_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_fst_2933_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_snd_2932_);
v___x_2942_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
else
{
lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2995_; 
lean_inc(v_stop_2939_);
lean_inc(v_start_2938_);
lean_inc_ref(v_array_2937_);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_snd_2932_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; 
v_unused_2996_ = lean_ctor_get(v_snd_2932_, 2);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_snd_2932_, 1);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_snd_2932_, 0);
lean_dec(v_unused_2998_);
v___x_2946_ = v_snd_2932_;
v_isShared_2947_ = v_isSharedCheck_2995_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v_snd_2932_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2995_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v_a_2948_; lean_object* v_fvarId_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v_a_2948_ = lean_array_uget_borrowed(v_as_2918_, v_i_2920_);
v_fvarId_2949_ = lean_ctor_get(v_a_2948_, 0);
v___x_2950_ = lean_array_fget(v_array_2937_, v_start_2938_);
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_nat_add(v_start_2938_, v___x_2951_);
lean_dec(v_start_2938_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v___x_2952_);
v___x_2954_ = v___x_2946_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_array_2937_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_stop_2939_);
v___x_2954_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2949_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2950_, v___y_2922_, v___y_2923_);
lean_dec(v___x_2950_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
lean_inc(v_a_2956_);
lean_inc_ref(v___x_2917_);
v___x_2959_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2917_, v_a_2956_, v_a_2958_);
v___x_2960_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2959_, v_a_2956_);
lean_dec(v_a_2956_);
if (v___x_2960_ == 0)
{
lean_object* v___f_2961_; lean_object* v___x_2962_; 
lean_dec(v_fst_2933_);
lean_inc(v_fvarId_2949_);
v___f_2961_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2961_, 0, v_fvarId_2949_);
lean_closure_set(v___f_2961_, 1, v___x_2959_);
v___x_2962_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2961_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
lean_dec_ref_known(v___x_2962_, 1);
v___x_2963_ = lean_box(v___x_2940_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2954_);
lean_ctor_set(v___x_2935_, 0, v___x_2963_);
v___x_2965_ = v___x_2935_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2954_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
v_a_2926_ = v___x_2965_;
goto v___jp_2925_;
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v___x_2954_);
lean_del_object(v___x_2935_);
lean_dec_ref(v___x_2917_);
v_a_2967_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2962_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2962_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v___x_2976_; 
lean_dec(v___x_2959_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2954_);
v___x_2976_ = v___x_2935_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_fst_2933_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2954_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v_a_2926_ = v___x_2976_;
goto v___jp_2925_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v_a_2956_);
lean_dec_ref(v___x_2954_);
lean_del_object(v___x_2935_);
lean_dec(v_fst_2933_);
lean_dec_ref(v___x_2917_);
v_a_2978_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2957_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2957_);
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
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2950_);
lean_del_object(v___x_2935_);
lean_dec(v_fst_2933_);
lean_dec_ref(v___x_2917_);
v_a_2986_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2955_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2955_);
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
}
}
}
}
v___jp_2925_:
{
size_t v___x_2927_; size_t v___x_2928_; 
v___x_2927_ = ((size_t)1ULL);
v___x_2928_ = lean_usize_add(v_i_2920_, v___x_2927_);
v_i_2920_ = v___x_2928_;
v_b_2921_ = v_a_2926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_3000_, lean_object* v_as_3001_, lean_object* v_sz_3002_, lean_object* v_i_3003_, lean_object* v_b_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
size_t v_sz_boxed_3008_; size_t v_i_boxed_3009_; lean_object* v_res_3010_; 
v_sz_boxed_3008_ = lean_unbox_usize(v_sz_3002_);
lean_dec(v_sz_3002_);
v_i_boxed_3009_ = lean_unbox_usize(v_i_3003_);
lean_dec(v_i_3003_);
v_res_3010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3000_, v_as_3001_, v_sz_boxed_3008_, v_i_boxed_3009_, v_b_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec_ref(v_as_3001_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_3011_, lean_object* v_args_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
uint8_t v_ret_3020_; lean_object* v___x_3021_; lean_object* v_env_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; size_t v_sz_3028_; size_t v___x_3029_; lean_object* v___x_3030_; 
v_ret_3020_ = 0;
v___x_3021_ = lean_st_ref_get(v_a_3018_);
v_env_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc_ref(v_env_3022_);
lean_dec(v___x_3021_);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = lean_array_get_size(v_args_3012_);
v___x_3025_ = l_Array_toSubarray___redArg(v_args_3012_, v___x_3023_, v___x_3024_);
v___x_3026_ = lean_box(v_ret_3020_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v___x_3025_);
v_sz_3028_ = lean_array_size(v_params_3011_);
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_3022_, v_params_3011_, v_sz_3028_, v___x_3029_, v___x_3027_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3048_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3048_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3048_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v_fst_3035_; lean_object* v_lower_3037_; lean_object* v_upper_3038_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v_fst_3035_ = lean_ctor_get(v_a_3031_, 0);
lean_inc(v_fst_3035_);
lean_dec(v_a_3031_);
v___x_3042_ = lean_array_get_size(v_params_3011_);
v___x_3043_ = lean_nat_dec_eq(v___x_3042_, v___x_3024_);
if (v___x_3043_ == 0)
{
uint8_t v___x_3044_; 
lean_del_object(v___x_3033_);
v___x_3044_ = lean_nat_dec_le(v___x_3024_, v___x_3023_);
if (v___x_3044_ == 0)
{
v_lower_3037_ = v___x_3024_;
v_upper_3038_ = v___x_3042_;
goto v___jp_3036_;
}
else
{
v_lower_3037_ = v___x_3023_;
v_upper_3038_ = v___x_3042_;
goto v___jp_3036_;
}
}
else
{
lean_object* v___x_3046_; 
lean_dec_ref(v_params_3011_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v_fst_3035_);
v___x_3046_ = v___x_3033_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_fst_3035_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
v___jp_3036_:
{
lean_object* v___x_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = l_Array_toSubarray___redArg(v_params_3011_, v_lower_3037_, v_upper_3038_);
v___x_3040_ = lean_unbox(v_fst_3035_);
lean_dec(v_fst_3035_);
v___x_3041_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_3039_, v___x_3040_, v_a_3013_, v_a_3014_, v_a_3018_);
return v___x_3041_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v_params_3011_);
v_a_3049_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3030_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3030_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3057_, lean_object* v_args_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3057_, v_args_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3067_, lean_object* v_as_3068_, size_t v_sz_3069_, size_t v_i_3070_, lean_object* v_b_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3067_, v_as_3068_, v_sz_3069_, v_i_3070_, v_b_3071_, v___y_3072_, v___y_3073_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3080_, lean_object* v_as_3081_, lean_object* v_sz_3082_, lean_object* v_i_3083_, lean_object* v_b_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
size_t v_sz_boxed_3092_; size_t v_i_boxed_3093_; lean_object* v_res_3094_; 
v_sz_boxed_3092_ = lean_unbox_usize(v_sz_3082_);
lean_dec(v_sz_3082_);
v_i_boxed_3093_ = lean_unbox_usize(v_i_3083_);
lean_dec(v_i_3083_);
v_res_3094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3080_, v_as_3081_, v_sz_boxed_3092_, v_i_boxed_3093_, v_b_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec_ref(v_as_3081_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3095_, lean_object* v_R_3096_, lean_object* v_a_3097_, uint8_t v_b_3098_, lean_object* v_c_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3097_, v_b_3098_, v___y_3100_, v___y_3101_, v___y_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3108_, lean_object* v_R_3109_, lean_object* v_a_3110_, lean_object* v_b_3111_, lean_object* v_c_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v_b_boxed_3120_; lean_object* v_res_3121_; 
v_b_boxed_3120_ = lean_unbox(v_b_3111_);
v_res_3121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3108_, v_R_3109_, v_a_3110_, v_b_boxed_3120_, v_c_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3122_, size_t v_sz_3123_, size_t v_i_3124_, uint8_t v_b_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
uint8_t v_a_3130_; uint8_t v___x_3134_; 
v___x_3134_ = lean_usize_dec_lt(v_i_3124_, v_sz_3123_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_box(v_b_3125_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
else
{
lean_object* v_a_3137_; lean_object* v_fvarId_3138_; lean_object* v___x_3139_; 
v_a_3137_ = lean_array_uget_borrowed(v_as_3122_, v_i_3124_);
v_fvarId_3138_ = lean_ctor_get(v_a_3137_, 0);
v___x_3139_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3138_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = lean_box(1);
v___x_3142_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3141_, v_a_3140_);
lean_dec(v_a_3140_);
if (v___x_3142_ == 0)
{
lean_object* v___f_3143_; lean_object* v___x_3144_; 
lean_inc(v_fvarId_3138_);
v___f_3143_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3143_, 0, v_fvarId_3138_);
lean_closure_set(v___f_3143_, 1, v___x_3141_);
v___x_3144_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3143_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_dec_ref_known(v___x_3144_, 1);
v_a_3130_ = v___x_3134_;
goto v___jp_3129_;
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
v_a_3130_ = v_b_3125_;
goto v___jp_3129_;
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
v_a_3153_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3139_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3139_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
v___jp_3129_:
{
size_t v___x_3131_; size_t v___x_3132_; 
v___x_3131_ = ((size_t)1ULL);
v___x_3132_ = lean_usize_add(v_i_3124_, v___x_3131_);
v_i_3124_ = v___x_3132_;
v_b_3125_ = v_a_3130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3161_, lean_object* v_sz_3162_, lean_object* v_i_3163_, lean_object* v_b_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
size_t v_sz_boxed_3168_; size_t v_i_boxed_3169_; uint8_t v_b_boxed_3170_; lean_object* v_res_3171_; 
v_sz_boxed_3168_ = lean_unbox_usize(v_sz_3162_);
lean_dec(v_sz_3162_);
v_i_boxed_3169_ = lean_unbox_usize(v_i_3163_);
lean_dec(v_i_3163_);
v_b_boxed_3170_ = lean_unbox(v_b_3164_);
v_res_3171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3161_, v_sz_boxed_3168_, v_i_boxed_3169_, v_b_boxed_3170_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v_as_3161_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
uint8_t v_ret_3180_; size_t v_sz_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v_ret_3180_ = 0;
v_sz_3181_ = lean_array_size(v_params_3172_);
v___x_3182_ = ((size_t)0ULL);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3172_, v_sz_3181_, v___x_3182_, v_ret_3180_, v_a_3173_, v_a_3174_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec_ref(v_params_3184_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3193_, size_t v_sz_3194_, size_t v_i_3195_, uint8_t v_b_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3193_, v_sz_3194_, v_i_3195_, v_b_3196_, v___y_3197_, v___y_3198_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3205_, lean_object* v_sz_3206_, lean_object* v_i_3207_, lean_object* v_b_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
size_t v_sz_boxed_3216_; size_t v_i_boxed_3217_; uint8_t v_b_boxed_3218_; lean_object* v_res_3219_; 
v_sz_boxed_3216_ = lean_unbox_usize(v_sz_3206_);
lean_dec(v_sz_3206_);
v_i_boxed_3217_ = lean_unbox_usize(v_i_3207_);
lean_dec(v_i_3207_);
v_b_boxed_3218_ = lean_unbox(v_b_3208_);
v_res_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3205_, v_sz_boxed_3216_, v_i_boxed_3217_, v_b_boxed_3218_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v_as_3205_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3220_, size_t v_i_3221_, size_t v_stop_3222_, lean_object* v_b_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_usize_dec_eq(v_i_3221_, v_stop_3222_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; lean_object* v_fvarId_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_array_uget_borrowed(v_as_3220_, v_i_3221_);
v_fvarId_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_fvarId_3229_);
v___x_3230_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3229_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; size_t v___x_3232_; size_t v___x_3233_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = ((size_t)1ULL);
v___x_3233_ = lean_usize_add(v_i_3221_, v___x_3232_);
v_i_3221_ = v___x_3233_;
v_b_3223_ = v_a_3231_;
goto _start;
}
else
{
return v___x_3230_;
}
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3235_, 0, v_b_3223_);
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3236_, lean_object* v_i_3237_, lean_object* v_stop_3238_, lean_object* v_b_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
size_t v_i_boxed_3243_; size_t v_stop_boxed_3244_; lean_object* v_res_3245_; 
v_i_boxed_3243_ = lean_unbox_usize(v_i_3237_);
lean_dec(v_i_3237_);
v_stop_boxed_3244_ = lean_unbox_usize(v_stop_3238_);
lean_dec(v_stop_3238_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3236_, v_i_boxed_3243_, v_stop_boxed_3244_, v_b_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v_as_3236_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v_decl_3265_; lean_object* v_k_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; 
switch(lean_obj_tag(v_x_3246_))
{
case 0:
{
lean_object* v_k_3287_; 
v_k_3287_ = lean_ctor_get(v_x_3246_, 1);
lean_inc_ref(v_k_3287_);
lean_dec_ref_known(v_x_3246_, 2);
v_x_3246_ = v_k_3287_;
goto _start;
}
case 3:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec_ref_known(v_x_3246_, 2);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
case 4:
{
lean_object* v_cases_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3313_; 
v_cases_3291_ = lean_ctor_get(v_x_3246_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_x_3246_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3293_ = v_x_3246_;
v_isShared_3294_ = v_isSharedCheck_3313_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_cases_3291_);
lean_dec(v_x_3246_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3313_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v_alts_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v_alts_3295_ = lean_ctor_get(v_cases_3291_, 3);
lean_inc_ref(v_alts_3295_);
lean_dec_ref(v_cases_3291_);
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = lean_array_get_size(v_alts_3295_);
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_nat_dec_lt(v___x_3296_, v___x_3297_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3301_; 
lean_dec_ref(v_alts_3295_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3298_);
v___x_3301_ = v___x_3293_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3298_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
else
{
uint8_t v___x_3303_; 
v___x_3303_ = lean_nat_dec_le(v___x_3297_, v___x_3297_);
if (v___x_3303_ == 0)
{
if (v___x_3299_ == 0)
{
lean_object* v___x_3305_; 
lean_dec_ref(v_alts_3295_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3298_);
v___x_3305_ = v___x_3293_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3298_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
else
{
size_t v___x_3307_; size_t v___x_3308_; lean_object* v___x_3309_; 
lean_del_object(v___x_3293_);
v___x_3307_ = ((size_t)0ULL);
v___x_3308_ = lean_usize_of_nat(v___x_3297_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3295_, v___x_3307_, v___x_3308_, v___x_3298_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec_ref(v_alts_3295_);
return v___x_3309_;
}
}
else
{
size_t v___x_3310_; size_t v___x_3311_; lean_object* v___x_3312_; 
lean_del_object(v___x_3293_);
v___x_3310_ = ((size_t)0ULL);
v___x_3311_ = lean_usize_of_nat(v___x_3297_);
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3295_, v___x_3310_, v___x_3311_, v___x_3298_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec_ref(v_alts_3295_);
return v___x_3312_;
}
}
}
}
case 5:
{
lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3321_; 
v_isSharedCheck_3321_ = !lean_is_exclusive(v_x_3246_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v_x_3246_, 0);
lean_dec(v_unused_3322_);
v___x_3315_ = v_x_3246_;
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
else
{
lean_dec(v_x_3246_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3317_ = lean_box(0);
if (v_isShared_3316_ == 0)
{
lean_ctor_set_tag(v___x_3315_, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3317_);
v___x_3319_ = v___x_3315_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
case 6:
{
lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3330_; 
v_isSharedCheck_3330_ = !lean_is_exclusive(v_x_3246_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; 
v_unused_3331_ = lean_ctor_get(v_x_3246_, 0);
lean_dec(v_unused_3331_);
v___x_3324_ = v_x_3246_;
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
else
{
lean_dec(v_x_3246_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_box(0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3326_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
default: 
{
lean_object* v_decl_3332_; lean_object* v_k_3333_; 
v_decl_3332_ = lean_ctor_get(v_x_3246_, 0);
lean_inc_ref(v_decl_3332_);
v_k_3333_ = lean_ctor_get(v_x_3246_, 1);
lean_inc_ref(v_k_3333_);
lean_dec_ref(v_x_3246_);
v_decl_3265_ = v_decl_3332_;
v_k_3266_ = v_k_3333_;
v___y_3267_ = v_a_3247_;
v___y_3268_ = v_a_3248_;
v___y_3269_ = v_a_3249_;
v___y_3270_ = v_a_3250_;
v___y_3271_ = v_a_3251_;
v___y_3272_ = v_a_3252_;
goto v___jp_3264_;
}
}
v___jp_3254_:
{
if (lean_obj_tag(v___y_3262_) == 0)
{
lean_dec_ref_known(v___y_3262_, 1);
v_x_3246_ = v___y_3256_;
v_a_3247_ = v___y_3260_;
v_a_3248_ = v___y_3258_;
v_a_3249_ = v___y_3259_;
v_a_3250_ = v___y_3257_;
v_a_3251_ = v___y_3261_;
v_a_3252_ = v___y_3255_;
goto _start;
}
else
{
lean_dec_ref(v___y_3256_);
return v___y_3262_;
}
}
v___jp_3264_:
{
lean_object* v_params_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v_params_3273_ = lean_ctor_get(v_decl_3265_, 2);
lean_inc_ref(v_params_3273_);
lean_dec_ref(v_decl_3265_);
v___x_3274_ = lean_unsigned_to_nat(0u);
v___x_3275_ = lean_array_get_size(v_params_3273_);
v___x_3276_ = lean_nat_dec_lt(v___x_3274_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_dec_ref(v_params_3273_);
v_x_3246_ = v_k_3266_;
v_a_3247_ = v___y_3267_;
v_a_3248_ = v___y_3268_;
v_a_3249_ = v___y_3269_;
v_a_3250_ = v___y_3270_;
v_a_3251_ = v___y_3271_;
v_a_3252_ = v___y_3272_;
goto _start;
}
else
{
lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = lean_box(0);
v___x_3279_ = lean_nat_dec_le(v___x_3275_, v___x_3275_);
if (v___x_3279_ == 0)
{
if (v___x_3276_ == 0)
{
lean_dec_ref(v_params_3273_);
v_x_3246_ = v_k_3266_;
v_a_3247_ = v___y_3267_;
v_a_3248_ = v___y_3268_;
v_a_3249_ = v___y_3269_;
v_a_3250_ = v___y_3270_;
v_a_3251_ = v___y_3271_;
v_a_3252_ = v___y_3272_;
goto _start;
}
else
{
size_t v___x_3281_; size_t v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = ((size_t)0ULL);
v___x_3282_ = lean_usize_of_nat(v___x_3275_);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3273_, v___x_3281_, v___x_3282_, v___x_3278_, v___y_3267_, v___y_3268_);
lean_dec_ref(v_params_3273_);
v___y_3255_ = v___y_3272_;
v___y_3256_ = v_k_3266_;
v___y_3257_ = v___y_3270_;
v___y_3258_ = v___y_3268_;
v___y_3259_ = v___y_3269_;
v___y_3260_ = v___y_3267_;
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___x_3283_;
goto v___jp_3254_;
}
}
else
{
size_t v___x_3284_; size_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = ((size_t)0ULL);
v___x_3285_ = lean_usize_of_nat(v___x_3275_);
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3273_, v___x_3284_, v___x_3285_, v___x_3278_, v___y_3267_, v___y_3268_);
lean_dec_ref(v_params_3273_);
v___y_3255_ = v___y_3272_;
v___y_3256_ = v_k_3266_;
v___y_3257_ = v___y_3270_;
v___y_3258_ = v___y_3268_;
v___y_3259_ = v___y_3269_;
v___y_3260_ = v___y_3267_;
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___x_3286_;
goto v___jp_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3334_, size_t v_i_3335_, size_t v_stop_3336_, lean_object* v_b_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v___y_3346_; uint8_t v___x_3352_; 
v___x_3352_ = lean_usize_dec_eq(v_i_3335_, v_stop_3336_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; 
v___x_3353_ = lean_array_uget_borrowed(v_as_3334_, v_i_3335_);
switch(lean_obj_tag(v___x_3353_))
{
case 0:
{
lean_object* v_code_3354_; 
v_code_3354_ = lean_ctor_get(v___x_3353_, 2);
lean_inc_ref(v_code_3354_);
v___y_3346_ = v_code_3354_;
goto v___jp_3345_;
}
case 1:
{
lean_object* v_code_3355_; 
v_code_3355_ = lean_ctor_get(v___x_3353_, 1);
lean_inc_ref(v_code_3355_);
v___y_3346_ = v_code_3355_;
goto v___jp_3345_;
}
default: 
{
lean_object* v_code_3356_; 
v_code_3356_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_ref(v_code_3356_);
v___y_3346_ = v_code_3356_;
goto v___jp_3345_;
}
}
}
else
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_b_3337_);
return v___x_3357_;
}
v___jp_3345_:
{
lean_object* v___x_3347_; 
v___x_3347_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3346_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; size_t v___x_3349_; size_t v___x_3350_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___x_3349_ = ((size_t)1ULL);
v___x_3350_ = lean_usize_add(v_i_3335_, v___x_3349_);
v_i_3335_ = v___x_3350_;
v_b_3337_ = v_a_3348_;
goto _start;
}
else
{
return v___x_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3358_, lean_object* v_i_3359_, lean_object* v_stop_3360_, lean_object* v_b_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
size_t v_i_boxed_3369_; size_t v_stop_boxed_3370_; lean_object* v_res_3371_; 
v_i_boxed_3369_ = lean_unbox_usize(v_i_3359_);
lean_dec(v_i_3359_);
v_stop_boxed_3370_ = lean_unbox_usize(v_stop_3360_);
lean_dec(v_stop_3360_);
v_res_3371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3358_, v_i_boxed_3369_, v_stop_boxed_3370_, v_b_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec_ref(v_as_3358_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3381_, size_t v_i_3382_, size_t v_stop_3383_, lean_object* v_b_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3381_, v_i_3382_, v_stop_3383_, v_b_3384_, v___y_3385_, v___y_3386_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3393_, lean_object* v_i_3394_, lean_object* v_stop_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
size_t v_i_boxed_3404_; size_t v_stop_boxed_3405_; lean_object* v_res_3406_; 
v_i_boxed_3404_ = lean_unbox_usize(v_i_3394_);
lean_dec(v_i_3394_);
v_stop_boxed_3405_ = lean_unbox_usize(v_stop_3395_);
lean_dec(v_stop_3395_);
v_res_3406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3393_, v_i_boxed_3404_, v_stop_boxed_3405_, v_b_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v_as_3393_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3407_, lean_object* v_b_3408_){
_start:
{
lean_object* v_array_3409_; lean_object* v_start_3410_; lean_object* v_stop_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3424_; 
v_array_3409_ = lean_ctor_get(v_a_3407_, 0);
v_start_3410_ = lean_ctor_get(v_a_3407_, 1);
v_stop_3411_ = lean_ctor_get(v_a_3407_, 2);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3413_ = v_a_3407_;
v_isShared_3414_ = v_isSharedCheck_3424_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_stop_3411_);
lean_inc(v_start_3410_);
lean_inc(v_array_3409_);
lean_dec(v_a_3407_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3424_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
uint8_t v___x_3415_; 
v___x_3415_ = lean_nat_dec_lt(v_start_3410_, v_stop_3411_);
if (v___x_3415_ == 0)
{
lean_del_object(v___x_3413_);
lean_dec(v_stop_3411_);
lean_dec(v_start_3410_);
lean_dec_ref(v_array_3409_);
return v_b_3408_;
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3416_ = lean_unsigned_to_nat(1u);
v___x_3417_ = lean_nat_add(v_start_3410_, v___x_3416_);
lean_inc_ref(v_array_3409_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v___x_3417_);
v___x_3419_ = v___x_3413_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_array_3409_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_stop_3411_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_array_fget(v_array_3409_, v_start_3410_);
lean_dec(v_start_3410_);
lean_dec_ref(v_array_3409_);
v___x_3421_ = lean_array_push(v_b_3408_, v___x_3420_);
v_a_3407_ = v___x_3419_;
v_b_3408_ = v___x_3421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3425_, size_t v_i_3426_, lean_object* v_bs_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_usize_dec_lt(v_i_3426_, v_sz_3425_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3432_, 0, v_bs_3427_);
return v___x_3432_;
}
else
{
lean_object* v_v_3433_; lean_object* v___x_3434_; lean_object* v_bs_x27_3435_; lean_object* v___x_3436_; 
v_v_3433_ = lean_array_uget(v_bs_3427_, v_i_3426_);
v___x_3434_ = lean_unsigned_to_nat(0u);
v_bs_x27_3435_ = lean_array_uset(v_bs_3427_, v_i_3426_, v___x_3434_);
v___x_3436_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3433_, v___y_3428_, v___y_3429_);
lean_dec(v_v_3433_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
v___x_3438_ = ((size_t)1ULL);
v___x_3439_ = lean_usize_add(v_i_3426_, v___x_3438_);
v___x_3440_ = lean_array_uset(v_bs_x27_3435_, v_i_3426_, v_a_3437_);
v_i_3426_ = v___x_3439_;
v_bs_3427_ = v___x_3440_;
goto _start;
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec_ref(v_bs_x27_3435_);
v_a_3442_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3436_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3436_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3450_, lean_object* v_i_3451_, lean_object* v_bs_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
size_t v_sz_boxed_3456_; size_t v_i_boxed_3457_; lean_object* v_res_3458_; 
v_sz_boxed_3456_ = lean_unbox_usize(v_sz_3450_);
lean_dec(v_sz_3450_);
v_i_boxed_3457_ = lean_unbox_usize(v_i_3451_);
lean_dec(v_i_3451_);
v_res_3458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3456_, v_i_boxed_3457_, v_bs_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3459_, size_t v_i_3460_, size_t v_stop_3461_, lean_object* v_b_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_usize_dec_eq(v_i_3460_, v_stop_3461_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; lean_object* v_fvarId_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3468_ = lean_array_uget_borrowed(v_as_3459_, v_i_3460_);
v_fvarId_3469_ = lean_ctor_get(v___x_3468_, 0);
v___x_3470_ = lean_box(1);
lean_inc(v_fvarId_3469_);
v___x_3471_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3469_, v___x_3470_, v___y_3463_, v___y_3464_, v___y_3465_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; size_t v___x_3473_; size_t v___x_3474_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_add(v_i_3460_, v___x_3473_);
v_i_3460_ = v___x_3474_;
v_b_3462_ = v_a_3472_;
goto _start;
}
else
{
return v___x_3471_;
}
}
else
{
lean_object* v___x_3476_; 
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v_b_3462_);
return v___x_3476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3477_, lean_object* v_i_3478_, lean_object* v_stop_3479_, lean_object* v_b_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
size_t v_i_boxed_3485_; size_t v_stop_boxed_3486_; lean_object* v_res_3487_; 
v_i_boxed_3485_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_stop_boxed_3486_ = lean_unbox_usize(v_stop_3479_);
lean_dec(v_stop_3479_);
v_res_3487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3477_, v_i_boxed_3485_, v_stop_boxed_3486_, v_b_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v_as_3477_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3488_, size_t v_i_3489_, size_t v_stop_3490_, lean_object* v_b_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_usize_dec_eq(v_i_3489_, v_stop_3490_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; lean_object* v_fst_3498_; lean_object* v_snd_3499_; lean_object* v_fvarId_3500_; lean_object* v___x_3501_; 
v___x_3497_ = lean_array_uget_borrowed(v_as_3488_, v_i_3489_);
v_fst_3498_ = lean_ctor_get(v___x_3497_, 0);
v_snd_3499_ = lean_ctor_get(v___x_3497_, 1);
v_fvarId_3500_ = lean_ctor_get(v_fst_3498_, 0);
lean_inc(v_snd_3499_);
lean_inc(v_fvarId_3500_);
v___x_3501_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3500_, v_snd_3499_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; size_t v___x_3503_; size_t v___x_3504_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = ((size_t)1ULL);
v___x_3504_ = lean_usize_add(v_i_3489_, v___x_3503_);
v_i_3489_ = v___x_3504_;
v_b_3491_ = v_a_3502_;
goto _start;
}
else
{
return v___x_3501_;
}
}
else
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_b_3491_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3507_, lean_object* v_i_3508_, lean_object* v_stop_3509_, lean_object* v_b_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
size_t v_i_boxed_3515_; size_t v_stop_boxed_3516_; lean_object* v_res_3517_; 
v_i_boxed_3515_ = lean_unbox_usize(v_i_3508_);
lean_dec(v_i_3508_);
v_stop_boxed_3516_ = lean_unbox_usize(v_stop_3509_);
lean_dec(v_stop_3509_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3507_, v_i_boxed_3515_, v_stop_boxed_3516_, v_b_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v_as_3507_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3520_, size_t v_i_3521_, size_t v_stop_3522_, lean_object* v_b_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
uint8_t v___x_3531_; 
v___x_3531_ = lean_usize_dec_eq(v_i_3521_, v_stop_3522_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = lean_array_uget_borrowed(v_as_3520_, v_i_3521_);
v___x_3533_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3532_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; size_t v___x_3535_; size_t v___x_3536_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = ((size_t)1ULL);
v___x_3536_ = lean_usize_add(v_i_3521_, v___x_3535_);
v_i_3521_ = v___x_3536_;
v_b_3523_ = v_a_3534_;
goto _start;
}
else
{
return v___x_3533_;
}
}
else
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_b_3523_);
return v___x_3538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v___y_3554_; 
switch(lean_obj_tag(v_letVal_3539_))
{
case 0:
{
lean_object* v_value_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3571_; 
v_value_3563_ = lean_ctor_get(v_letVal_3539_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_letVal_3539_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3565_ = v_letVal_3539_;
v_isShared_3566_ = v_isSharedCheck_3571_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_value_3563_);
lean_dec(v_letVal_3539_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3571_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3567_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3563_);
lean_dec_ref(v_value_3563_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3567_);
v___x_3569_ = v___x_3565_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
case 1:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = lean_box(1);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
case 2:
{
lean_object* v_idx_3574_; lean_object* v_struct_3575_; lean_object* v___x_3576_; lean_object* v_env_3577_; lean_object* v___x_3578_; 
v_idx_3574_ = lean_ctor_get(v_letVal_3539_, 1);
lean_inc(v_idx_3574_);
v_struct_3575_ = lean_ctor_get(v_letVal_3539_, 2);
lean_inc(v_struct_3575_);
lean_dec_ref_known(v_letVal_3539_, 3);
v___x_3576_ = lean_st_ref_get(v_a_3545_);
v_env_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc_ref(v_env_3577_);
lean_dec(v___x_3576_);
v___x_3578_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3575_, v_a_3540_, v_a_3541_);
lean_dec(v_struct_3575_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3587_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3577_, v_a_3579_, v_idx_3574_);
lean_dec(v_idx_3574_);
lean_dec(v_a_3579_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3583_);
v___x_3585_ = v___x_3581_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
else
{
lean_dec_ref(v_env_3577_);
lean_dec(v_idx_3574_);
return v___x_3578_;
}
}
case 3:
{
lean_object* v_declName_3588_; lean_object* v_args_3589_; lean_object* v___x_3590_; lean_object* v_env_3591_; lean_object* v___x_3592_; lean_object* v_numFields_3594_; lean_object* v_lower_3595_; lean_object* v_upper_3596_; lean_object* v___x_3624_; lean_object* v___y_3693_; uint8_t v___x_3702_; 
v_declName_3588_ = lean_ctor_get(v_letVal_3539_, 0);
lean_inc(v_declName_3588_);
v_args_3589_ = lean_ctor_get(v_letVal_3539_, 2);
lean_inc_ref(v_args_3589_);
lean_dec_ref_known(v_letVal_3539_, 3);
v___x_3590_ = lean_st_ref_get(v_a_3545_);
v_env_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc_ref(v_env_3591_);
lean_dec(v___x_3590_);
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3624_ = lean_array_get_size(v_args_3589_);
v___x_3702_ = lean_nat_dec_lt(v___x_3592_, v___x_3624_);
if (v___x_3702_ == 0)
{
goto v___jp_3625_;
}
else
{
lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = lean_box(0);
v___x_3704_ = lean_nat_dec_le(v___x_3624_, v___x_3624_);
if (v___x_3704_ == 0)
{
if (v___x_3702_ == 0)
{
goto v___jp_3625_;
}
else
{
size_t v___x_3705_; size_t v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = ((size_t)0ULL);
v___x_3706_ = lean_usize_of_nat(v___x_3624_);
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3589_, v___x_3705_, v___x_3706_, v___x_3703_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
v___y_3693_ = v___x_3707_;
goto v___jp_3692_;
}
}
else
{
size_t v___x_3708_; size_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = ((size_t)0ULL);
v___x_3709_ = lean_usize_of_nat(v___x_3624_);
v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3589_, v___x_3708_, v___x_3709_, v___x_3703_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
v___y_3693_ = v___x_3710_;
goto v___jp_3692_;
}
}
v___jp_3593_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3597_ = l_Array_toSubarray___redArg(v_args_3589_, v_lower_3595_, v_upper_3596_);
v___x_3598_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3599_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3597_, v___x_3598_);
v___x_3600_ = lean_array_get_size(v___x_3599_);
v___x_3601_ = lean_nat_dec_eq(v_numFields_3594_, v___x_3600_);
lean_dec(v_numFields_3594_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec_ref(v___x_3599_);
lean_dec(v_declName_3588_);
v___x_3602_ = lean_box(1);
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
return v___x_3603_;
}
else
{
size_t v_sz_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v_sz_3604_ = lean_array_size(v___x_3599_);
v___x_3605_ = ((size_t)0ULL);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3604_, v___x_3605_, v___x_3599_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3615_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_declName_3588_);
lean_ctor_set(v___x_3611_, 1, v_a_3607_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3611_);
v___x_3613_ = v___x_3609_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_declName_3588_);
v_a_3616_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3606_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3606_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
v___jp_3625_:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3542_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3626_, 1);
v___x_3628_ = lean_unbox(v_a_3627_);
lean_dec(v_a_3627_);
lean_inc(v_declName_3588_);
v___x_3629_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3588_, v___x_3628_, v_a_3544_, v_a_3545_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3675_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3632_ = v___x_3629_;
v_isShared_3633_ = v_isSharedCheck_3675_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3629_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3675_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
if (lean_obj_tag(v_a_3630_) == 1)
{
lean_object* v_val_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
lean_dec_ref(v_args_3589_);
v_val_3634_ = lean_ctor_get(v_a_3630_, 0);
lean_inc(v_val_3634_);
lean_dec_ref_known(v_a_3630_, 1);
v___x_3635_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3634_);
lean_dec(v_val_3634_);
v___x_3636_ = lean_nat_dec_eq(v___x_3635_, v___x_3624_);
lean_dec(v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; lean_object* v___x_3639_; 
lean_dec_ref(v_env_3591_);
lean_dec(v_declName_3588_);
v___x_3637_ = lean_box(1);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3637_);
v___x_3639_ = v___x_3632_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
else
{
lean_object* v___x_3641_; 
lean_inc(v_declName_3588_);
v___x_3641_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3591_, v_declName_3588_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v___x_3642_; 
lean_del_object(v___x_3632_);
v___x_3642_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3588_, v_a_3540_, v_a_3541_);
lean_dec(v_declName_3588_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3655_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3655_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3655_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
if (lean_obj_tag(v_a_3643_) == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3647_ = lean_box(1);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3647_);
v___x_3649_ = v___x_3645_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
else
{
lean_object* v_val_3651_; lean_object* v___x_3653_; 
v_val_3651_ = lean_ctor_get(v_a_3643_, 0);
lean_inc(v_val_3651_);
lean_dec_ref_known(v_a_3643_, 1);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v_val_3651_);
v___x_3653_ = v___x_3645_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_val_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v_a_3656_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3642_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3642_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_val_3664_; lean_object* v___x_3666_; 
lean_dec(v_declName_3588_);
v_val_3664_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_val_3664_);
lean_dec_ref_known(v___x_3641_, 1);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v_val_3664_);
v___x_3666_ = v___x_3632_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_val_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
uint8_t v___x_3668_; lean_object* v___x_3669_; 
lean_del_object(v___x_3632_);
lean_dec(v_a_3630_);
v___x_3668_ = 0;
lean_inc(v_declName_3588_);
v___x_3669_ = l_Lean_Environment_find_x3f(v_env_3591_, v_declName_3588_, v___x_3668_);
if (lean_obj_tag(v___x_3669_) == 1)
{
lean_object* v_val_3670_; 
v_val_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_val_3670_);
lean_dec_ref_known(v___x_3669_, 1);
if (lean_obj_tag(v_val_3670_) == 6)
{
lean_object* v_val_3671_; lean_object* v_numParams_3672_; lean_object* v_numFields_3673_; uint8_t v___x_3674_; 
v_val_3671_ = lean_ctor_get(v_val_3670_, 0);
lean_inc_ref(v_val_3671_);
lean_dec_ref_known(v_val_3670_, 1);
v_numParams_3672_ = lean_ctor_get(v_val_3671_, 3);
lean_inc(v_numParams_3672_);
v_numFields_3673_ = lean_ctor_get(v_val_3671_, 4);
lean_inc(v_numFields_3673_);
lean_dec_ref(v_val_3671_);
v___x_3674_ = lean_nat_dec_le(v_numParams_3672_, v___x_3592_);
if (v___x_3674_ == 0)
{
v_numFields_3594_ = v_numFields_3673_;
v_lower_3595_ = v_numParams_3672_;
v_upper_3596_ = v___x_3624_;
goto v___jp_3593_;
}
else
{
lean_dec(v_numParams_3672_);
v_numFields_3594_ = v_numFields_3673_;
v_lower_3595_ = v___x_3592_;
v_upper_3596_ = v___x_3624_;
goto v___jp_3593_;
}
}
else
{
lean_dec(v_val_3670_);
lean_dec_ref(v_args_3589_);
lean_dec(v_declName_3588_);
goto v___jp_3547_;
}
}
else
{
lean_dec(v___x_3669_);
lean_dec_ref(v_args_3589_);
lean_dec(v_declName_3588_);
goto v___jp_3547_;
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec_ref(v_env_3591_);
lean_dec_ref(v_args_3589_);
lean_dec(v_declName_3588_);
v_a_3676_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3629_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3629_);
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
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec_ref(v_env_3591_);
lean_dec_ref(v_args_3589_);
lean_dec(v_declName_3588_);
v_a_3684_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3626_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3626_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
v___jp_3692_:
{
if (lean_obj_tag(v___y_3693_) == 0)
{
lean_dec_ref_known(v___y_3693_, 1);
goto v___jp_3625_;
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v_env_3591_);
lean_dec_ref(v_args_3589_);
lean_dec(v_declName_3588_);
v_a_3694_ = lean_ctor_get(v___y_3693_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___y_3693_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___y_3693_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___y_3693_);
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
default: 
{
lean_object* v_args_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_args_3711_ = lean_ctor_get(v_letVal_3539_, 1);
lean_inc_ref(v_args_3711_);
lean_dec_ref_known(v_letVal_3539_, 2);
v___x_3712_ = lean_unsigned_to_nat(0u);
v___x_3713_ = lean_array_get_size(v_args_3711_);
v___x_3714_ = lean_nat_dec_lt(v___x_3712_, v___x_3713_);
if (v___x_3714_ == 0)
{
lean_dec_ref(v_args_3711_);
goto v___jp_3550_;
}
else
{
lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3715_ = lean_box(0);
v___x_3716_ = lean_nat_dec_le(v___x_3713_, v___x_3713_);
if (v___x_3716_ == 0)
{
if (v___x_3714_ == 0)
{
lean_dec_ref(v_args_3711_);
goto v___jp_3550_;
}
else
{
size_t v___x_3717_; size_t v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = ((size_t)0ULL);
v___x_3718_ = lean_usize_of_nat(v___x_3713_);
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3711_, v___x_3717_, v___x_3718_, v___x_3715_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
lean_dec_ref(v_args_3711_);
v___y_3554_ = v___x_3719_;
goto v___jp_3553_;
}
}
else
{
size_t v___x_3720_; size_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = lean_usize_of_nat(v___x_3713_);
v___x_3722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3711_, v___x_3720_, v___x_3721_, v___x_3715_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
lean_dec_ref(v_args_3711_);
v___y_3554_ = v___x_3722_;
goto v___jp_3553_;
}
}
}
}
v___jp_3547_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_box(1);
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
return v___x_3549_;
}
v___jp_3550_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = lean_box(1);
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
v___jp_3553_:
{
if (lean_obj_tag(v___y_3554_) == 0)
{
lean_dec_ref_known(v___y_3554_, 1);
goto v___jp_3550_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_a_3555_ = lean_ctor_get(v___y_3554_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___y_3554_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___y_3554_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___y_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3723_, lean_object* v_args_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_params_3732_; lean_object* v_value_3733_; lean_object* v___x_3734_; 
v_params_3732_ = lean_ctor_get(v_funDecl_3723_, 2);
lean_inc_ref(v_params_3732_);
v_value_3733_ = lean_ctor_get(v_funDecl_3723_, 4);
lean_inc_ref(v_value_3733_);
lean_dec_ref(v_funDecl_3723_);
v___x_3734_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3732_, v_args_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3746_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3746_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3746_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
uint8_t v___x_3739_; 
v___x_3739_ = lean_unbox(v_a_3735_);
lean_dec(v_a_3735_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_dec_ref(v_value_3733_);
v___x_3740_ = lean_box(0);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3740_);
v___x_3742_ = v___x_3737_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
else
{
lean_object* v___x_3744_; 
lean_del_object(v___x_3737_);
lean_inc_ref(v_value_3733_);
v___x_3744_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3733_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v___x_3745_; 
lean_dec_ref_known(v___x_3744_, 1);
v___x_3745_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3733_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
return v___x_3745_;
}
else
{
lean_dec_ref(v_value_3733_);
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec_ref(v_value_3733_);
v_a_3747_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3734_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3734_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3755_, lean_object* v_as_3756_, size_t v_sz_3757_, size_t v_i_3758_, lean_object* v_b_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v_a_3768_; uint8_t v___x_3772_; 
v___x_3772_ = lean_usize_dec_lt(v_i_3758_, v_sz_3757_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v_b_3759_);
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; lean_object* v_a_3775_; 
v___x_3774_ = lean_box(0);
v_a_3775_ = lean_array_uget_borrowed(v_as_3756_, v_i_3758_);
if (lean_obj_tag(v_a_3775_) == 0)
{
lean_object* v_ctorName_3776_; lean_object* v_params_3777_; lean_object* v_code_3778_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3788_; lean_object* v___y_3790_; lean_object* v___x_3791_; 
v_ctorName_3776_ = lean_ctor_get(v_a_3775_, 0);
v_params_3777_ = lean_ctor_get(v_a_3775_, 1);
v_code_3778_ = lean_ctor_get(v_a_3775_, 2);
v___x_3791_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3755_, v_ctorName_3776_);
if (lean_obj_tag(v___x_3791_) == 1)
{
lean_object* v_val_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v_val_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_val_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l_Array_zip___redArg(v_params_3777_, v_val_3792_);
lean_dec(v_val_3792_);
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = lean_array_get_size(v___x_3793_);
v___x_3796_ = lean_nat_dec_lt(v___x_3794_, v___x_3795_);
if (v___x_3796_ == 0)
{
lean_dec_ref(v___x_3793_);
v___y_3780_ = v___y_3760_;
v___y_3781_ = v___y_3761_;
v___y_3782_ = v___y_3762_;
v___y_3783_ = v___y_3763_;
v___y_3784_ = v___y_3764_;
v___y_3785_ = v___y_3765_;
goto v___jp_3779_;
}
else
{
uint8_t v___x_3797_; 
v___x_3797_ = lean_nat_dec_le(v___x_3795_, v___x_3795_);
if (v___x_3797_ == 0)
{
if (v___x_3796_ == 0)
{
lean_dec_ref(v___x_3793_);
v___y_3780_ = v___y_3760_;
v___y_3781_ = v___y_3761_;
v___y_3782_ = v___y_3762_;
v___y_3783_ = v___y_3763_;
v___y_3784_ = v___y_3764_;
v___y_3785_ = v___y_3765_;
goto v___jp_3779_;
}
else
{
size_t v___x_3798_; size_t v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = ((size_t)0ULL);
v___x_3799_ = lean_usize_of_nat(v___x_3795_);
v___x_3800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3793_, v___x_3798_, v___x_3799_, v___x_3774_, v___y_3760_, v___y_3761_, v___y_3765_);
lean_dec_ref(v___x_3793_);
v___y_3788_ = v___x_3800_;
goto v___jp_3787_;
}
}
else
{
size_t v___x_3801_; size_t v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = ((size_t)0ULL);
v___x_3802_ = lean_usize_of_nat(v___x_3795_);
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3793_, v___x_3801_, v___x_3802_, v___x_3774_, v___y_3760_, v___y_3761_, v___y_3765_);
lean_dec_ref(v___x_3793_);
v___y_3788_ = v___x_3803_;
goto v___jp_3787_;
}
}
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
lean_dec(v___x_3791_);
v___x_3804_ = lean_unsigned_to_nat(0u);
v___x_3805_ = lean_array_get_size(v_params_3777_);
v___x_3806_ = lean_nat_dec_lt(v___x_3804_, v___x_3805_);
if (v___x_3806_ == 0)
{
v___y_3780_ = v___y_3760_;
v___y_3781_ = v___y_3761_;
v___y_3782_ = v___y_3762_;
v___y_3783_ = v___y_3763_;
v___y_3784_ = v___y_3764_;
v___y_3785_ = v___y_3765_;
goto v___jp_3779_;
}
else
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_nat_dec_le(v___x_3805_, v___x_3805_);
if (v___x_3807_ == 0)
{
if (v___x_3806_ == 0)
{
v___y_3780_ = v___y_3760_;
v___y_3781_ = v___y_3761_;
v___y_3782_ = v___y_3762_;
v___y_3783_ = v___y_3763_;
v___y_3784_ = v___y_3764_;
v___y_3785_ = v___y_3765_;
goto v___jp_3779_;
}
else
{
size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = ((size_t)0ULL);
v___x_3809_ = lean_usize_of_nat(v___x_3805_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3777_, v___x_3808_, v___x_3809_, v___x_3774_, v___y_3760_, v___y_3761_, v___y_3765_);
v___y_3790_ = v___x_3810_;
goto v___jp_3789_;
}
}
else
{
size_t v___x_3811_; size_t v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((size_t)0ULL);
v___x_3812_ = lean_usize_of_nat(v___x_3805_);
v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3777_, v___x_3811_, v___x_3812_, v___x_3774_, v___y_3760_, v___y_3761_, v___y_3765_);
v___y_3790_ = v___x_3813_;
goto v___jp_3789_;
}
}
}
v___jp_3779_:
{
lean_object* v___x_3786_; 
lean_inc_ref(v_code_3778_);
v___x_3786_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3778_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_dec_ref_known(v___x_3786_, 1);
v_a_3768_ = v___x_3774_;
goto v___jp_3767_;
}
else
{
return v___x_3786_;
}
}
v___jp_3787_:
{
if (lean_obj_tag(v___y_3788_) == 0)
{
lean_dec_ref_known(v___y_3788_, 1);
v___y_3780_ = v___y_3760_;
v___y_3781_ = v___y_3761_;
v___y_3782_ = v___y_3762_;
v___y_3783_ = v___y_3763_;
v___y_3784_ = v___y_3764_;
v___y_3785_ = v___y_3765_;
goto v___jp_3779_;
}
else
{
return v___y_3788_;
}
}
v___jp_3789_:
{
if (lean_obj_tag(v___y_3790_) == 0)
{
lean_dec_ref_known(v___y_3790_, 1);
v___y_3780_ = v___y_3760_;
v___y_3781_ = v___y_3761_;
v___y_3782_ = v___y_3762_;
v___y_3783_ = v___y_3763_;
v___y_3784_ = v___y_3764_;
v___y_3785_ = v___y_3765_;
goto v___jp_3779_;
}
else
{
return v___y_3790_;
}
}
}
else
{
lean_object* v_code_3814_; lean_object* v___x_3815_; 
v_code_3814_ = lean_ctor_get(v_a_3775_, 0);
lean_inc_ref(v_code_3814_);
v___x_3815_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3814_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_dec_ref_known(v___x_3815_, 1);
v_a_3768_ = v___x_3774_;
goto v___jp_3767_;
}
else
{
return v___x_3815_;
}
}
}
v___jp_3767_:
{
size_t v___x_3769_; size_t v___x_3770_; 
v___x_3769_ = ((size_t)1ULL);
v___x_3770_ = lean_usize_add(v_i_3758_, v___x_3769_);
v_i_3758_ = v___x_3770_;
v_b_3759_ = v_a_3768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v_decl_3825_; lean_object* v_k_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; 
switch(lean_obj_tag(v_x_3816_))
{
case 0:
{
lean_object* v_decl_3836_; lean_object* v_k_3837_; lean_object* v_fvarId_3838_; lean_object* v_value_3839_; lean_object* v___x_3840_; 
v_decl_3836_ = lean_ctor_get(v_x_3816_, 0);
lean_inc_ref(v_decl_3836_);
v_k_3837_ = lean_ctor_get(v_x_3816_, 1);
lean_inc_ref(v_k_3837_);
lean_dec_ref_known(v_x_3816_, 2);
v_fvarId_3838_ = lean_ctor_get(v_decl_3836_, 0);
lean_inc(v_fvarId_3838_);
v_value_3839_ = lean_ctor_get(v_decl_3836_, 3);
lean_inc_n(v_value_3839_, 2);
lean_dec_ref(v_decl_3836_);
v___x_3840_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3839_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v___x_3842_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3838_, v_a_3841_, v_a_3817_, v_a_3818_, v_a_3822_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_dec_ref_known(v___x_3842_, 1);
if (lean_obj_tag(v_value_3839_) == 4)
{
lean_object* v_fvarId_3843_; lean_object* v_args_3844_; uint8_t v___x_3845_; lean_object* v___x_3846_; 
v_fvarId_3843_ = lean_ctor_get(v_value_3839_, 0);
lean_inc(v_fvarId_3843_);
v_args_3844_ = lean_ctor_get(v_value_3839_, 1);
lean_inc_ref(v_args_3844_);
lean_dec_ref_known(v_value_3839_, 2);
v___x_3845_ = 0;
v___x_3846_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3845_, v_fvarId_3843_, v_a_3820_);
lean_dec(v_fvarId_3843_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
if (lean_obj_tag(v_a_3847_) == 1)
{
lean_object* v_val_3848_; lean_object* v___x_3849_; 
v_val_3848_ = lean_ctor_get(v_a_3847_, 0);
lean_inc(v_val_3848_);
lean_dec_ref_known(v_a_3847_, 1);
v___x_3849_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3848_, v_args_3844_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_dec_ref_known(v___x_3849_, 1);
v_x_3816_ = v_k_3837_;
goto _start;
}
else
{
lean_dec_ref(v_k_3837_);
return v___x_3849_;
}
}
else
{
lean_dec(v_a_3847_);
lean_dec_ref(v_args_3844_);
v_x_3816_ = v_k_3837_;
goto _start;
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec_ref(v_args_3844_);
lean_dec_ref(v_k_3837_);
v_a_3852_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3846_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3846_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_dec(v_value_3839_);
v_x_3816_ = v_k_3837_;
goto _start;
}
}
else
{
lean_dec(v_value_3839_);
lean_dec_ref(v_k_3837_);
return v___x_3842_;
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v_value_3839_);
lean_dec(v_fvarId_3838_);
lean_dec_ref(v_k_3837_);
v_a_3861_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3840_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3840_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3869_; lean_object* v_args_3870_; uint8_t v___x_3871_; lean_object* v___x_3872_; 
v_fvarId_3869_ = lean_ctor_get(v_x_3816_, 0);
lean_inc(v_fvarId_3869_);
v_args_3870_ = lean_ctor_get(v_x_3816_, 1);
lean_inc_ref(v_args_3870_);
lean_dec_ref_known(v_x_3816_, 2);
v___x_3871_ = 0;
v___x_3872_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3871_, v_fvarId_3869_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___y_3875_; lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = lean_array_get_size(v_args_3870_);
v___x_3879_ = lean_nat_dec_lt(v___x_3877_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; 
v___x_3880_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3873_, v_args_3870_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
return v___x_3880_;
}
else
{
lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3881_ = lean_box(0);
v___x_3882_ = lean_nat_dec_le(v___x_3878_, v___x_3878_);
if (v___x_3882_ == 0)
{
if (v___x_3879_ == 0)
{
lean_object* v___x_3883_; 
v___x_3883_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3873_, v_args_3870_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
return v___x_3883_;
}
else
{
size_t v___x_3884_; size_t v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = ((size_t)0ULL);
v___x_3885_ = lean_usize_of_nat(v___x_3878_);
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3870_, v___x_3884_, v___x_3885_, v___x_3881_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
v___y_3875_ = v___x_3886_;
goto v___jp_3874_;
}
}
else
{
size_t v___x_3887_; size_t v___x_3888_; lean_object* v___x_3889_; 
v___x_3887_ = ((size_t)0ULL);
v___x_3888_ = lean_usize_of_nat(v___x_3878_);
v___x_3889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3870_, v___x_3887_, v___x_3888_, v___x_3881_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
v___y_3875_ = v___x_3889_;
goto v___jp_3874_;
}
}
v___jp_3874_:
{
if (lean_obj_tag(v___y_3875_) == 0)
{
lean_object* v___x_3876_; 
lean_dec_ref_known(v___y_3875_, 1);
v___x_3876_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3873_, v_args_3870_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
return v___x_3876_;
}
else
{
lean_dec(v_a_3873_);
lean_dec_ref(v_args_3870_);
return v___y_3875_;
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec_ref(v_args_3870_);
v_a_3890_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3872_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3872_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
case 4:
{
lean_object* v_cases_3898_; lean_object* v_discr_3899_; lean_object* v_alts_3900_; lean_object* v___x_3901_; 
v_cases_3898_ = lean_ctor_get(v_x_3816_, 0);
lean_inc_ref(v_cases_3898_);
lean_dec_ref_known(v_x_3816_, 1);
v_discr_3899_ = lean_ctor_get(v_cases_3898_, 2);
lean_inc(v_discr_3899_);
v_alts_3900_ = lean_ctor_get(v_cases_3898_, 3);
lean_inc_ref(v_alts_3900_);
lean_dec_ref(v_cases_3898_);
v___x_3901_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3899_, v_a_3817_, v_a_3818_);
lean_dec(v_discr_3899_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3903_; size_t v_sz_3904_; size_t v___x_3905_; lean_object* v___x_3906_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3901_, 1);
v___x_3903_ = lean_box(0);
v_sz_3904_ = lean_array_size(v_alts_3900_);
v___x_3905_ = ((size_t)0ULL);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3902_, v_alts_3900_, v_sz_3904_, v___x_3905_, v___x_3903_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
lean_dec_ref(v_alts_3900_);
lean_dec(v_a_3902_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v___x_3906_, 0);
lean_dec(v_unused_3914_);
v___x_3908_ = v___x_3906_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_dec(v___x_3906_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3903_);
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3903_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
else
{
return v___x_3906_;
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v_alts_3900_);
v_a_3915_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3901_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3901_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3923_; lean_object* v___x_3924_; 
v_fvarId_3923_ = lean_ctor_get(v_x_3816_, 0);
lean_inc(v_fvarId_3923_);
lean_dec_ref_known(v_x_3816_, 1);
v___x_3924_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3923_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v___x_3925_; 
lean_dec_ref_known(v___x_3924_, 1);
v___x_3925_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3923_, v_a_3817_, v_a_3818_);
lean_dec(v_fvarId_3923_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3927_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3925_, 1);
v___x_3927_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3926_, v_a_3817_, v_a_3818_, v_a_3822_);
return v___x_3927_;
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_a_3928_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3925_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3925_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_dec(v_fvarId_3923_);
return v___x_3924_;
}
}
case 6:
{
lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3943_; 
v_isSharedCheck_3943_ = !lean_is_exclusive(v_x_3816_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; 
v_unused_3944_ = lean_ctor_get(v_x_3816_, 0);
lean_dec(v_unused_3944_);
v___x_3937_ = v_x_3816_;
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
else
{
lean_dec(v_x_3816_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = lean_box(0);
if (v_isShared_3938_ == 0)
{
lean_ctor_set_tag(v___x_3937_, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3941_ = v___x_3937_;
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
default: 
{
lean_object* v_decl_3945_; lean_object* v_k_3946_; 
v_decl_3945_ = lean_ctor_get(v_x_3816_, 0);
lean_inc_ref(v_decl_3945_);
v_k_3946_ = lean_ctor_get(v_x_3816_, 1);
lean_inc_ref(v_k_3946_);
lean_dec_ref(v_x_3816_);
v_decl_3825_ = v_decl_3945_;
v_k_3826_ = v_k_3946_;
v___y_3827_ = v_a_3817_;
v___y_3828_ = v_a_3818_;
v___y_3829_ = v_a_3819_;
v___y_3830_ = v_a_3820_;
v___y_3831_ = v_a_3821_;
v___y_3832_ = v_a_3822_;
goto v___jp_3824_;
}
}
v___jp_3824_:
{
lean_object* v_value_3833_; lean_object* v___x_3834_; 
v_value_3833_ = lean_ctor_get(v_decl_3825_, 4);
lean_inc_ref(v_value_3833_);
lean_dec_ref(v_decl_3825_);
v___x_3834_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3833_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_dec_ref_known(v___x_3834_, 1);
v_x_3816_ = v_k_3826_;
v_a_3817_ = v___y_3827_;
v_a_3818_ = v___y_3828_;
v_a_3819_ = v___y_3829_;
v_a_3820_ = v___y_3830_;
v_a_3821_ = v___y_3831_;
v_a_3822_ = v___y_3832_;
goto _start;
}
else
{
lean_dec_ref(v_k_3826_);
return v___x_3834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
uint8_t v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = 0;
v___x_3956_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3955_, v_var_3947_, v_a_3951_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3989_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3989_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3989_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
if (lean_obj_tag(v_a_3957_) == 1)
{
lean_object* v_val_3961_; lean_object* v_params_3962_; lean_object* v_value_3963_; lean_object* v___x_3964_; 
lean_del_object(v___x_3959_);
v_val_3961_ = lean_ctor_get(v_a_3957_, 0);
lean_inc(v_val_3961_);
lean_dec_ref_known(v_a_3957_, 1);
v_params_3962_ = lean_ctor_get(v_val_3961_, 2);
lean_inc_ref(v_params_3962_);
v_value_3963_ = lean_ctor_get(v_val_3961_, 4);
lean_inc_ref(v_value_3963_);
lean_dec(v_val_3961_);
v___x_3964_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3962_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
lean_dec_ref(v_params_3962_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3976_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3967_ = v___x_3964_;
v_isShared_3968_ = v_isSharedCheck_3976_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3976_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
uint8_t v___x_3969_; 
v___x_3969_ = lean_unbox(v_a_3965_);
lean_dec(v_a_3965_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3972_; 
lean_dec_ref(v_value_3963_);
v___x_3970_ = lean_box(0);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3970_);
v___x_3972_ = v___x_3967_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
else
{
lean_object* v___x_3974_; 
lean_del_object(v___x_3967_);
lean_inc_ref(v_value_3963_);
v___x_3974_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3963_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v___x_3975_; 
lean_dec_ref_known(v___x_3974_, 1);
v___x_3975_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3963_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
return v___x_3975_;
}
else
{
lean_dec_ref(v_value_3963_);
return v___x_3974_;
}
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v_value_3963_);
v_a_3977_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3964_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3964_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
else
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
lean_dec(v_a_3957_);
v___x_3985_ = lean_box(0);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3985_);
v___x_3987_ = v___x_3959_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
v_a_3990_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3956_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3956_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
if (lean_obj_tag(v_arg_3998_) == 1)
{
lean_object* v_fvarId_4006_; lean_object* v___x_4007_; 
v_fvarId_4006_ = lean_ctor_get(v_arg_3998_, 0);
v___x_4007_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_4006_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
return v___x_4007_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_box(0);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_arg_4010_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_4019_, lean_object* v_i_4020_, lean_object* v_stop_4021_, lean_object* v_b_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
size_t v_i_boxed_4030_; size_t v_stop_boxed_4031_; lean_object* v_res_4032_; 
v_i_boxed_4030_ = lean_unbox_usize(v_i_4020_);
lean_dec(v_i_4020_);
v_stop_boxed_4031_ = lean_unbox_usize(v_stop_4021_);
lean_dec(v_stop_4021_);
v_res_4032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_4019_, v_i_boxed_4030_, v_stop_boxed_4031_, v_b_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec_ref(v_as_4019_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_4033_, lean_object* v_args_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_4033_, v_args_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
lean_dec(v_a_4038_);
lean_dec_ref(v_a_4037_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_var_4043_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_4052_, lean_object* v_as_4053_, lean_object* v_sz_4054_, lean_object* v_i_4055_, lean_object* v_b_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
size_t v_sz_boxed_4064_; size_t v_i_boxed_4065_; lean_object* v_res_4066_; 
v_sz_boxed_4064_ = lean_unbox_usize(v_sz_4054_);
lean_dec(v_sz_4054_);
v_i_boxed_4065_ = lean_unbox_usize(v_i_4055_);
lean_dec(v_i_4055_);
v_res_4066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_4052_, v_as_4053_, v_sz_boxed_4064_, v_i_boxed_4065_, v_b_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec_ref(v_as_4053_);
lean_dec(v_a_4052_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4085_, lean_object* v_R_4086_, lean_object* v_a_4087_, lean_object* v_b_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4087_, v_b_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4090_, size_t v_i_4091_, lean_object* v_bs_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4090_, v_i_4091_, v_bs_4092_, v___y_4093_, v___y_4094_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4101_, lean_object* v_i_4102_, lean_object* v_bs_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
size_t v_sz_boxed_4111_; size_t v_i_boxed_4112_; lean_object* v_res_4113_; 
v_sz_boxed_4111_ = lean_unbox_usize(v_sz_4101_);
lean_dec(v_sz_4101_);
v_i_boxed_4112_ = lean_unbox_usize(v_i_4102_);
lean_dec(v_i_4102_);
v_res_4113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4111_, v_i_boxed_4112_, v_bs_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4114_, size_t v_i_4115_, size_t v_stop_4116_, lean_object* v_b_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4114_, v_i_4115_, v_stop_4116_, v_b_4117_, v___y_4118_, v___y_4119_, v___y_4123_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4126_, lean_object* v_i_4127_, lean_object* v_stop_4128_, lean_object* v_b_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
size_t v_i_boxed_4137_; size_t v_stop_boxed_4138_; lean_object* v_res_4139_; 
v_i_boxed_4137_ = lean_unbox_usize(v_i_4127_);
lean_dec(v_i_4127_);
v_stop_boxed_4138_ = lean_unbox_usize(v_stop_4128_);
lean_dec(v_stop_4128_);
v_res_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4126_, v_i_boxed_4137_, v_stop_boxed_4138_, v_b_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec_ref(v_as_4126_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4140_, size_t v_i_4141_, size_t v_stop_4142_, lean_object* v_b_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4140_, v_i_4141_, v_stop_4142_, v_b_4143_, v___y_4144_, v___y_4145_, v___y_4149_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4152_, lean_object* v_i_4153_, lean_object* v_stop_4154_, lean_object* v_b_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
size_t v_i_boxed_4163_; size_t v_stop_boxed_4164_; lean_object* v_res_4165_; 
v_i_boxed_4163_ = lean_unbox_usize(v_i_4153_);
lean_dec(v_i_4153_);
v_stop_boxed_4164_ = lean_unbox_usize(v_stop_4154_);
lean_dec(v_stop_4154_);
v_res_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4152_, v_i_boxed_4163_, v_stop_boxed_4164_, v_b_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec_ref(v_as_4152_);
return v_res_4165_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4166_ = lean_unsigned_to_nat(32u);
v___x_4167_ = lean_mk_empty_array_with_capacity(v___x_4166_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
return v___x_4168_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4169_ = ((size_t)5ULL);
v___x_4170_ = lean_unsigned_to_nat(0u);
v___x_4171_ = lean_unsigned_to_nat(32u);
v___x_4172_ = lean_mk_empty_array_with_capacity(v___x_4171_);
v___x_4173_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0);
v___x_4174_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
lean_ctor_set(v___x_4174_, 1, v___x_4172_);
lean_ctor_set(v___x_4174_, 2, v___x_4170_);
lean_ctor_set(v___x_4174_, 3, v___x_4170_);
lean_ctor_set_usize(v___x_4174_, 4, v___x_4169_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; lean_object* v_traceState_4178_; lean_object* v_traces_4179_; lean_object* v___x_4180_; lean_object* v_traceState_4181_; lean_object* v_env_4182_; lean_object* v_nextMacroScope_4183_; lean_object* v_ngen_4184_; lean_object* v_auxDeclNGen_4185_; lean_object* v_cache_4186_; lean_object* v_messages_4187_; lean_object* v_infoState_4188_; lean_object* v_snapshotTasks_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4208_; 
v___x_4177_ = lean_st_ref_get(v___y_4175_);
v_traceState_4178_ = lean_ctor_get(v___x_4177_, 4);
lean_inc_ref(v_traceState_4178_);
lean_dec(v___x_4177_);
v_traces_4179_ = lean_ctor_get(v_traceState_4178_, 0);
lean_inc_ref(v_traces_4179_);
lean_dec_ref(v_traceState_4178_);
v___x_4180_ = lean_st_ref_take(v___y_4175_);
v_traceState_4181_ = lean_ctor_get(v___x_4180_, 4);
v_env_4182_ = lean_ctor_get(v___x_4180_, 0);
v_nextMacroScope_4183_ = lean_ctor_get(v___x_4180_, 1);
v_ngen_4184_ = lean_ctor_get(v___x_4180_, 2);
v_auxDeclNGen_4185_ = lean_ctor_get(v___x_4180_, 3);
v_cache_4186_ = lean_ctor_get(v___x_4180_, 5);
v_messages_4187_ = lean_ctor_get(v___x_4180_, 6);
v_infoState_4188_ = lean_ctor_get(v___x_4180_, 7);
v_snapshotTasks_4189_ = lean_ctor_get(v___x_4180_, 8);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4191_ = v___x_4180_;
v_isShared_4192_ = v_isSharedCheck_4208_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_snapshotTasks_4189_);
lean_inc(v_infoState_4188_);
lean_inc(v_messages_4187_);
lean_inc(v_cache_4186_);
lean_inc(v_traceState_4181_);
lean_inc(v_auxDeclNGen_4185_);
lean_inc(v_ngen_4184_);
lean_inc(v_nextMacroScope_4183_);
lean_inc(v_env_4182_);
lean_dec(v___x_4180_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4208_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
uint64_t v_tid_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4206_; 
v_tid_4193_ = lean_ctor_get_uint64(v_traceState_4181_, sizeof(void*)*1);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_traceState_4181_);
if (v_isSharedCheck_4206_ == 0)
{
lean_object* v_unused_4207_; 
v_unused_4207_ = lean_ctor_get(v_traceState_4181_, 0);
lean_dec(v_unused_4207_);
v___x_4195_ = v_traceState_4181_;
v_isShared_4196_ = v_isSharedCheck_4206_;
goto v_resetjp_4194_;
}
else
{
lean_dec(v_traceState_4181_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4206_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4197_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v___x_4197_);
v___x_4199_ = v___x_4195_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4197_);
lean_ctor_set_uint64(v_reuseFailAlloc_4205_, sizeof(void*)*1, v_tid_4193_);
v___x_4199_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4201_; 
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 4, v___x_4199_);
v___x_4201_ = v___x_4191_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_env_4182_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v_nextMacroScope_4183_);
lean_ctor_set(v_reuseFailAlloc_4204_, 2, v_ngen_4184_);
lean_ctor_set(v_reuseFailAlloc_4204_, 3, v_auxDeclNGen_4185_);
lean_ctor_set(v_reuseFailAlloc_4204_, 4, v___x_4199_);
lean_ctor_set(v_reuseFailAlloc_4204_, 5, v_cache_4186_);
lean_ctor_set(v_reuseFailAlloc_4204_, 6, v_messages_4187_);
lean_ctor_set(v_reuseFailAlloc_4204_, 7, v_infoState_4188_);
lean_ctor_set(v_reuseFailAlloc_4204_, 8, v_snapshotTasks_4189_);
v___x_4201_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = lean_st_ref_put(v___y_4175_, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v_traces_4179_);
return v___x_4203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4209_);
lean_dec(v___y_4209_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4217_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
return v_res_4227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v_opts_4228_, lean_object* v_opt_4229_){
_start:
{
lean_object* v_name_4230_; lean_object* v_defValue_4231_; lean_object* v_map_4232_; lean_object* v___x_4233_; 
v_name_4230_ = lean_ctor_get(v_opt_4229_, 0);
v_defValue_4231_ = lean_ctor_get(v_opt_4229_, 1);
v_map_4232_ = lean_ctor_get(v_opts_4228_, 0);
v___x_4233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4232_, v_name_4230_);
if (lean_obj_tag(v___x_4233_) == 0)
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_unbox(v_defValue_4231_);
return v___x_4234_;
}
else
{
lean_object* v_val_4235_; 
v_val_4235_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_val_4235_);
lean_dec_ref_known(v___x_4233_, 1);
if (lean_obj_tag(v_val_4235_) == 1)
{
uint8_t v_v_4236_; 
v_v_4236_ = lean_ctor_get_uint8(v_val_4235_, 0);
lean_dec_ref_known(v_val_4235_, 0);
return v_v_4236_;
}
else
{
uint8_t v___x_4237_; 
lean_dec(v_val_4235_);
v___x_4237_ = lean_unbox(v_defValue_4231_);
return v___x_4237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v_opts_4238_, lean_object* v_opt_4239_){
_start:
{
uint8_t v_res_4240_; lean_object* v_r_4241_; 
v_res_4240_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4238_, v_opt_4239_);
lean_dec_ref(v_opt_4239_);
lean_dec_ref(v_opts_4238_);
v_r_4241_ = lean_box(v_res_4240_);
return v_r_4241_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__0));
v___x_4244_ = l_Lean_stringToMessageData(v___x_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* v_name_4245_, lean_object* v_x_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4254_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___closed__1);
v___x_4255_ = l_Lean_MessageData_ofName(v_name_4245_);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4254_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* v_name_4258_, lean_object* v_x_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0(v_name_4258_, v_x_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec_ref(v_x_4259_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(lean_object* v_opts_4268_, lean_object* v_opt_4269_){
_start:
{
lean_object* v_name_4270_; lean_object* v_defValue_4271_; lean_object* v_map_4272_; lean_object* v___x_4273_; 
v_name_4270_ = lean_ctor_get(v_opt_4269_, 0);
v_defValue_4271_ = lean_ctor_get(v_opt_4269_, 1);
v_map_4272_ = lean_ctor_get(v_opts_4268_, 0);
v___x_4273_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4272_, v_name_4270_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_inc(v_defValue_4271_);
return v_defValue_4271_;
}
else
{
lean_object* v_val_4274_; 
v_val_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_val_4274_);
lean_dec_ref_known(v___x_4273_, 1);
if (lean_obj_tag(v_val_4274_) == 3)
{
lean_object* v_v_4275_; 
v_v_4275_ = lean_ctor_get(v_val_4274_, 0);
lean_inc(v_v_4275_);
lean_dec_ref_known(v_val_4274_, 1);
return v_v_4275_;
}
else
{
lean_dec(v_val_4274_);
lean_inc(v_defValue_4271_);
return v_defValue_4271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5___boxed(lean_object* v_opts_4276_, lean_object* v_opt_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4276_, v_opt_4277_);
lean_dec_ref(v_opt_4277_);
lean_dec_ref(v_opts_4276_);
return v_res_4278_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(lean_object* v_e_4279_){
_start:
{
if (lean_obj_tag(v_e_4279_) == 0)
{
uint8_t v___x_4280_; 
v___x_4280_ = 2;
return v___x_4280_;
}
else
{
uint8_t v___x_4281_; 
v___x_4281_ = 0;
return v___x_4281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4___boxed(lean_object* v_e_4282_){
_start:
{
uint8_t v_res_4283_; lean_object* v_r_4284_; 
v_res_4283_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_e_4282_);
lean_dec_ref(v_e_4282_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(lean_object* v_x_4285_){
_start:
{
if (lean_obj_tag(v_x_4285_) == 0)
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
v_a_4287_ = lean_ctor_get(v_x_4285_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v_x_4285_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v_x_4285_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v_x_4285_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 1);
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_a_4295_ = lean_ctor_get(v_x_4285_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_x_4285_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v_x_4285_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v_x_4285_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
lean_ctor_set_tag(v___x_4297_, 0);
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg___boxed(lean_object* v_x_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4303_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(size_t v_sz_4306_, size_t v_i_4307_, lean_object* v_bs_4308_){
_start:
{
uint8_t v___x_4309_; 
v___x_4309_ = lean_usize_dec_lt(v_i_4307_, v_sz_4306_);
if (v___x_4309_ == 0)
{
return v_bs_4308_;
}
else
{
lean_object* v_v_4310_; lean_object* v_msg_4311_; lean_object* v___x_4312_; lean_object* v_bs_x27_4313_; size_t v___x_4314_; size_t v___x_4315_; lean_object* v___x_4316_; 
v_v_4310_ = lean_array_uget_borrowed(v_bs_4308_, v_i_4307_);
v_msg_4311_ = lean_ctor_get(v_v_4310_, 1);
lean_inc_ref(v_msg_4311_);
v___x_4312_ = lean_unsigned_to_nat(0u);
v_bs_x27_4313_ = lean_array_uset(v_bs_4308_, v_i_4307_, v___x_4312_);
v___x_4314_ = ((size_t)1ULL);
v___x_4315_ = lean_usize_add(v_i_4307_, v___x_4314_);
v___x_4316_ = lean_array_uset(v_bs_x27_4313_, v_i_4307_, v_msg_4311_);
v_i_4307_ = v___x_4315_;
v_bs_4308_ = v___x_4316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_4318_, lean_object* v_i_4319_, lean_object* v_bs_4320_){
_start:
{
size_t v_sz_boxed_4321_; size_t v_i_boxed_4322_; lean_object* v_res_4323_; 
v_sz_boxed_4321_ = lean_unbox_usize(v_sz_4318_);
lean_dec(v_sz_4318_);
v_i_boxed_4322_ = lean_unbox_usize(v_i_4319_);
lean_dec(v_i_4319_);
v_res_4323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_boxed_4321_, v_i_boxed_4322_, v_bs_4320_);
return v_res_4323_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4326_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__0);
v___x_4327_ = lean_unsigned_to_nat(0u);
v___x_4328_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4327_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
lean_ctor_set(v___x_4328_, 2, v___x_4327_);
lean_ctor_set(v___x_4328_, 3, v___x_4327_);
lean_ctor_set(v___x_4328_, 4, v___x_4326_);
lean_ctor_set(v___x_4328_, 5, v___x_4326_);
lean_ctor_set(v___x_4328_, 6, v___x_4326_);
lean_ctor_set(v___x_4328_, 7, v___x_4326_);
lean_ctor_set(v___x_4328_, 8, v___x_4326_);
lean_ctor_set(v___x_4328_, 9, v___x_4326_);
lean_ctor_set(v___x_4328_, 10, v___x_4326_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(lean_object* v_oldTraces_4329_, lean_object* v_data_4330_, lean_object* v_ref_4331_, lean_object* v_msg_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v_toCold_4338_; lean_object* v___x_4339_; lean_object* v_traceState_4340_; lean_object* v_traces_4341_; lean_object* v___x_4342_; size_t v_sz_4343_; size_t v___x_4344_; lean_object* v___x_4345_; lean_object* v_msg_4346_; lean_object* v___x_4347_; lean_object* v_env_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_toCold_4338_ = lean_ctor_get(v___y_4335_, 0);
v___x_4339_ = lean_st_ref_get(v___y_4336_);
v_traceState_4340_ = lean_ctor_get(v___x_4339_, 4);
lean_inc_ref(v_traceState_4340_);
lean_dec(v___x_4339_);
v_traces_4341_ = lean_ctor_get(v_traceState_4340_, 0);
lean_inc_ref(v_traces_4341_);
lean_dec_ref(v_traceState_4340_);
v___x_4342_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4341_);
lean_dec_ref(v_traces_4341_);
v_sz_4343_ = lean_array_size(v___x_4342_);
v___x_4344_ = ((size_t)0ULL);
v___x_4345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2_spec__3(v_sz_4343_, v___x_4344_, v___x_4342_);
v_msg_4346_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4346_, 0, v_data_4330_);
lean_ctor_set(v_msg_4346_, 1, v_msg_4332_);
lean_ctor_set(v_msg_4346_, 2, v___x_4345_);
v___x_4347_ = lean_st_ref_get(v___y_4336_);
v_env_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc_ref(v_env_4348_);
lean_dec(v___x_4347_);
v___x_4349_ = lean_st_ref_get(v___y_4334_);
v___x_4350_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4333_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4402_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4402_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4402_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v_lctx_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4400_; 
v_lctx_4355_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4400_ == 0)
{
lean_object* v_unused_4401_; 
v_unused_4401_ = lean_ctor_get(v___x_4349_, 1);
lean_dec(v_unused_4401_);
v___x_4357_ = v___x_4349_;
v_isShared_4358_ = v_isSharedCheck_4400_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_lctx_4355_);
lean_dec(v___x_4349_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4400_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v_options_4359_; uint8_t v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4365_; 
v_options_4359_ = lean_ctor_get(v_toCold_4338_, 2);
v___x_4360_ = lean_unbox(v_a_4351_);
lean_dec(v_a_4351_);
v___x_4361_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4355_, v___x_4360_);
lean_dec_ref(v_lctx_4355_);
v___x_4362_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
lean_inc_ref(v_options_4359_);
v___x_4363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4363_, 0, v_env_4348_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
lean_ctor_set(v___x_4363_, 2, v___x_4361_);
lean_ctor_set(v___x_4363_, 3, v_options_4359_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set_tag(v___x_4357_, 3);
lean_ctor_set(v___x_4357_, 1, v_msg_4346_);
lean_ctor_set(v___x_4357_, 0, v___x_4363_);
v___x_4365_ = v___x_4357_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_msg_4346_);
v___x_4365_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4366_; lean_object* v_traceState_4367_; lean_object* v_env_4368_; lean_object* v_nextMacroScope_4369_; lean_object* v_ngen_4370_; lean_object* v_auxDeclNGen_4371_; lean_object* v_cache_4372_; lean_object* v_messages_4373_; lean_object* v_infoState_4374_; lean_object* v_snapshotTasks_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4398_; 
v___x_4366_ = lean_st_ref_take(v___y_4336_);
v_traceState_4367_ = lean_ctor_get(v___x_4366_, 4);
v_env_4368_ = lean_ctor_get(v___x_4366_, 0);
v_nextMacroScope_4369_ = lean_ctor_get(v___x_4366_, 1);
v_ngen_4370_ = lean_ctor_get(v___x_4366_, 2);
v_auxDeclNGen_4371_ = lean_ctor_get(v___x_4366_, 3);
v_cache_4372_ = lean_ctor_get(v___x_4366_, 5);
v_messages_4373_ = lean_ctor_get(v___x_4366_, 6);
v_infoState_4374_ = lean_ctor_get(v___x_4366_, 7);
v_snapshotTasks_4375_ = lean_ctor_get(v___x_4366_, 8);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4377_ = v___x_4366_;
v_isShared_4378_ = v_isSharedCheck_4398_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_snapshotTasks_4375_);
lean_inc(v_infoState_4374_);
lean_inc(v_messages_4373_);
lean_inc(v_cache_4372_);
lean_inc(v_traceState_4367_);
lean_inc(v_auxDeclNGen_4371_);
lean_inc(v_ngen_4370_);
lean_inc(v_nextMacroScope_4369_);
lean_inc(v_env_4368_);
lean_dec(v___x_4366_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4398_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
uint64_t v_tid_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4396_; 
v_tid_4379_ = lean_ctor_get_uint64(v_traceState_4367_, sizeof(void*)*1);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_traceState_4367_);
if (v_isSharedCheck_4396_ == 0)
{
lean_object* v_unused_4397_; 
v_unused_4397_ = lean_ctor_get(v_traceState_4367_, 0);
lean_dec(v_unused_4397_);
v___x_4381_ = v_traceState_4367_;
v_isShared_4382_ = v_isSharedCheck_4396_;
goto v_resetjp_4380_;
}
else
{
lean_dec(v_traceState_4367_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4396_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
v___x_4383_ = lean_box(0);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v_ref_4331_);
lean_ctor_set(v___x_4384_, 1, v___x_4365_);
v___x_4385_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4329_, v___x_4384_);
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v___x_4385_);
v___x_4387_ = v___x_4381_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4385_);
lean_ctor_set_uint64(v_reuseFailAlloc_4395_, sizeof(void*)*1, v_tid_4379_);
v___x_4387_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4389_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 4, v___x_4387_);
v___x_4389_ = v___x_4377_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_env_4368_);
lean_ctor_set(v_reuseFailAlloc_4394_, 1, v_nextMacroScope_4369_);
lean_ctor_set(v_reuseFailAlloc_4394_, 2, v_ngen_4370_);
lean_ctor_set(v_reuseFailAlloc_4394_, 3, v_auxDeclNGen_4371_);
lean_ctor_set(v_reuseFailAlloc_4394_, 4, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4394_, 5, v_cache_4372_);
lean_ctor_set(v_reuseFailAlloc_4394_, 6, v_messages_4373_);
lean_ctor_set(v_reuseFailAlloc_4394_, 7, v_infoState_4374_);
lean_ctor_set(v_reuseFailAlloc_4394_, 8, v_snapshotTasks_4375_);
v___x_4389_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4392_; 
v___x_4390_ = lean_st_ref_put(v___y_4336_, v___x_4389_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4383_);
v___x_4392_ = v___x_4353_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4383_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
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
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v___x_4349_);
lean_dec_ref(v_env_4348_);
lean_dec_ref_known(v_msg_4346_, 3);
lean_dec(v_ref_4331_);
lean_dec_ref(v_oldTraces_4329_);
v_a_4403_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4350_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4350_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_4411_, lean_object* v_data_4412_, lean_object* v_ref_4413_, lean_object* v_msg_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4411_, v_data_4412_, v_ref_4413_, v_msg_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
return v_res_4420_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4421_; double v___x_4422_; 
v___x_4421_ = lean_unsigned_to_nat(0u);
v___x_4422_ = lean_float_of_nat(v___x_4421_);
return v___x_4422_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__1));
v___x_4425_ = l_Lean_stringToMessageData(v___x_4424_);
return v___x_4425_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4426_; double v___x_4427_; 
v___x_4426_ = lean_unsigned_to_nat(1000u);
v___x_4427_ = lean_float_of_nat(v___x_4426_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_cls_4428_, uint8_t v_collapsed_4429_, lean_object* v_tag_4430_, lean_object* v_opts_4431_, uint8_t v_clsEnabled_4432_, lean_object* v_oldTraces_4433_, lean_object* v_msg_4434_, lean_object* v_resStartStop_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v_fst_4443_; lean_object* v_snd_4444_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v_data_4448_; lean_object* v_fst_4451_; lean_object* v_snd_4452_; lean_object* v___x_4453_; uint8_t v___x_4454_; lean_object* v___y_4456_; lean_object* v_a_4457_; uint8_t v___y_4472_; double v___y_4503_; 
v_fst_4443_ = lean_ctor_get(v_resStartStop_4435_, 0);
lean_inc(v_fst_4443_);
v_snd_4444_ = lean_ctor_get(v_resStartStop_4435_, 1);
lean_inc(v_snd_4444_);
lean_dec_ref(v_resStartStop_4435_);
v_fst_4451_ = lean_ctor_get(v_snd_4444_, 0);
lean_inc(v_fst_4451_);
v_snd_4452_ = lean_ctor_get(v_snd_4444_, 1);
lean_inc(v_snd_4452_);
lean_dec(v_snd_4444_);
v___x_4453_ = l_Lean_trace_profiler;
v___x_4454_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4431_, v___x_4453_);
if (v___x_4454_ == 0)
{
v___y_4472_ = v___x_4454_;
goto v___jp_4471_;
}
else
{
lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4508_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4509_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_opts_4431_, v___x_4508_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4510_; lean_object* v___x_4511_; double v___x_4512_; double v___x_4513_; double v___x_4514_; 
v___x_4510_ = l_Lean_trace_profiler_threshold;
v___x_4511_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4431_, v___x_4510_);
v___x_4512_ = lean_float_of_nat(v___x_4511_);
v___x_4513_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__3);
v___x_4514_ = lean_float_div(v___x_4512_, v___x_4513_);
v___y_4503_ = v___x_4514_;
goto v___jp_4502_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; double v___x_4517_; 
v___x_4515_ = l_Lean_trace_profiler_threshold;
v___x_4516_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__5(v_opts_4431_, v___x_4515_);
v___x_4517_ = lean_float_of_nat(v___x_4516_);
v___y_4503_ = v___x_4517_;
goto v___jp_4502_;
}
}
v___jp_4445_:
{
lean_object* v___x_4449_; 
lean_inc(v___y_4447_);
v___x_4449_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4433_, v_data_4448_, v___y_4447_, v___y_4446_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v___x_4450_; 
lean_dec_ref_known(v___x_4449_, 1);
v___x_4450_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4443_);
return v___x_4450_;
}
else
{
lean_dec(v_fst_4443_);
return v___x_4449_;
}
}
v___jp_4455_:
{
uint8_t v_result_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; double v___x_4461_; lean_object* v_data_4462_; 
v_result_4458_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__4(v_fst_4443_);
v___x_4459_ = lean_box(v_result_4458_);
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
v___x_4461_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
lean_inc_ref(v_tag_4430_);
lean_inc_ref(v___x_4460_);
lean_inc(v_cls_4428_);
v_data_4462_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4462_, 0, v_cls_4428_);
lean_ctor_set(v_data_4462_, 1, v___x_4460_);
lean_ctor_set(v_data_4462_, 2, v_tag_4430_);
lean_ctor_set_float(v_data_4462_, sizeof(void*)*3, v___x_4461_);
lean_ctor_set_float(v_data_4462_, sizeof(void*)*3 + 8, v___x_4461_);
lean_ctor_set_uint8(v_data_4462_, sizeof(void*)*3 + 16, v_collapsed_4429_);
if (v___x_4454_ == 0)
{
lean_dec_ref_known(v___x_4460_, 1);
lean_dec(v_snd_4452_);
lean_dec(v_fst_4451_);
lean_dec_ref(v_tag_4430_);
lean_dec(v_cls_4428_);
v___y_4446_ = v_a_4457_;
v___y_4447_ = v___y_4456_;
v_data_4448_ = v_data_4462_;
goto v___jp_4445_;
}
else
{
lean_object* v_data_4463_; double v___x_4464_; double v___x_4465_; 
lean_dec_ref_known(v_data_4462_, 3);
v_data_4463_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4463_, 0, v_cls_4428_);
lean_ctor_set(v_data_4463_, 1, v___x_4460_);
lean_ctor_set(v_data_4463_, 2, v_tag_4430_);
v___x_4464_ = lean_unbox_float(v_fst_4451_);
lean_dec(v_fst_4451_);
lean_ctor_set_float(v_data_4463_, sizeof(void*)*3, v___x_4464_);
v___x_4465_ = lean_unbox_float(v_snd_4452_);
lean_dec(v_snd_4452_);
lean_ctor_set_float(v_data_4463_, sizeof(void*)*3 + 8, v___x_4465_);
lean_ctor_set_uint8(v_data_4463_, sizeof(void*)*3 + 16, v_collapsed_4429_);
v___y_4446_ = v_a_4457_;
v___y_4447_ = v___y_4456_;
v_data_4448_ = v_data_4463_;
goto v___jp_4445_;
}
}
v___jp_4466_:
{
lean_object* v_ref_4467_; lean_object* v___x_4468_; 
v_ref_4467_ = lean_ctor_get(v___y_4440_, 2);
lean_inc(v___y_4441_);
lean_inc_ref(v___y_4440_);
lean_inc(v___y_4439_);
lean_inc_ref(v___y_4438_);
lean_inc(v___y_4437_);
lean_inc_ref(v___y_4436_);
lean_inc(v_fst_4443_);
v___x_4468_ = lean_apply_8(v_msg_4434_, v_fst_4443_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, lean_box(0));
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref_known(v___x_4468_, 1);
v___y_4456_ = v_ref_4467_;
v_a_4457_ = v_a_4469_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4470_; 
lean_dec_ref_known(v___x_4468_, 1);
v___x_4470_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__2);
v___y_4456_ = v_ref_4467_;
v_a_4457_ = v___x_4470_;
goto v___jp_4455_;
}
}
v___jp_4471_:
{
if (v_clsEnabled_4432_ == 0)
{
if (v___y_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v_traceState_4474_; lean_object* v_env_4475_; lean_object* v_nextMacroScope_4476_; lean_object* v_ngen_4477_; lean_object* v_auxDeclNGen_4478_; lean_object* v_cache_4479_; lean_object* v_messages_4480_; lean_object* v_infoState_4481_; lean_object* v_snapshotTasks_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_snd_4452_);
lean_dec(v_fst_4451_);
lean_dec_ref(v_msg_4434_);
lean_dec_ref(v_tag_4430_);
lean_dec(v_cls_4428_);
v___x_4473_ = lean_st_ref_take(v___y_4441_);
v_traceState_4474_ = lean_ctor_get(v___x_4473_, 4);
v_env_4475_ = lean_ctor_get(v___x_4473_, 0);
v_nextMacroScope_4476_ = lean_ctor_get(v___x_4473_, 1);
v_ngen_4477_ = lean_ctor_get(v___x_4473_, 2);
v_auxDeclNGen_4478_ = lean_ctor_get(v___x_4473_, 3);
v_cache_4479_ = lean_ctor_get(v___x_4473_, 5);
v_messages_4480_ = lean_ctor_get(v___x_4473_, 6);
v_infoState_4481_ = lean_ctor_get(v___x_4473_, 7);
v_snapshotTasks_4482_ = lean_ctor_get(v___x_4473_, 8);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4484_ = v___x_4473_;
v_isShared_4485_ = v_isSharedCheck_4501_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_snapshotTasks_4482_);
lean_inc(v_infoState_4481_);
lean_inc(v_messages_4480_);
lean_inc(v_cache_4479_);
lean_inc(v_traceState_4474_);
lean_inc(v_auxDeclNGen_4478_);
lean_inc(v_ngen_4477_);
lean_inc(v_nextMacroScope_4476_);
lean_inc(v_env_4475_);
lean_dec(v___x_4473_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4501_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
uint64_t v_tid_4486_; lean_object* v_traces_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4500_; 
v_tid_4486_ = lean_ctor_get_uint64(v_traceState_4474_, sizeof(void*)*1);
v_traces_4487_ = lean_ctor_get(v_traceState_4474_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_traceState_4474_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4489_ = v_traceState_4474_;
v_isShared_4490_ = v_isSharedCheck_4500_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_traces_4487_);
lean_dec(v_traceState_4474_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4500_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4433_, v_traces_4487_);
lean_dec_ref(v_traces_4487_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___x_4491_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4491_);
lean_ctor_set_uint64(v_reuseFailAlloc_4499_, sizeof(void*)*1, v_tid_4486_);
v___x_4493_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4495_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 4, v___x_4493_);
v___x_4495_ = v___x_4484_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_env_4475_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_nextMacroScope_4476_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_ngen_4477_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v_auxDeclNGen_4478_);
lean_ctor_set(v_reuseFailAlloc_4498_, 4, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4498_, 5, v_cache_4479_);
lean_ctor_set(v_reuseFailAlloc_4498_, 6, v_messages_4480_);
lean_ctor_set(v_reuseFailAlloc_4498_, 7, v_infoState_4481_);
lean_ctor_set(v_reuseFailAlloc_4498_, 8, v_snapshotTasks_4482_);
v___x_4495_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4496_ = lean_st_ref_put(v___y_4441_, v___x_4495_);
v___x_4497_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_fst_4443_);
return v___x_4497_;
}
}
}
}
}
else
{
goto v___jp_4466_;
}
}
else
{
goto v___jp_4466_;
}
}
v___jp_4502_:
{
double v___x_4504_; double v___x_4505_; double v___x_4506_; uint8_t v___x_4507_; 
v___x_4504_ = lean_unbox_float(v_snd_4452_);
v___x_4505_ = lean_unbox_float(v_fst_4451_);
v___x_4506_ = lean_float_sub(v___x_4504_, v___x_4505_);
v___x_4507_ = lean_float_decLt(v___y_4503_, v___x_4506_);
v___y_4472_ = v___x_4507_;
goto v___jp_4471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_cls_4518_, lean_object* v_collapsed_4519_, lean_object* v_tag_4520_, lean_object* v_opts_4521_, lean_object* v_clsEnabled_4522_, lean_object* v_oldTraces_4523_, lean_object* v_msg_4524_, lean_object* v_resStartStop_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v_collapsed_boxed_4533_; uint8_t v_clsEnabled_boxed_4534_; lean_object* v_res_4535_; 
v_collapsed_boxed_4533_ = lean_unbox(v_collapsed_4519_);
v_clsEnabled_boxed_4534_ = lean_unbox(v_clsEnabled_4522_);
v_res_4535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_cls_4518_, v_collapsed_boxed_4533_, v_tag_4520_, v_opts_4521_, v_clsEnabled_boxed_4534_, v_oldTraces_4523_, v_msg_4524_, v_resStartStop_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec_ref(v_opts_4521_);
return v_res_4535_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4539_; double v___x_4540_; 
v___x_4539_ = lean_unsigned_to_nat(1000000000u);
v___x_4540_ = lean_float_of_nat(v___x_4539_);
return v___x_4540_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4549_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4550_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__6));
v___x_4551_ = l_Lean_Name_append(v___x_4550_, v___x_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(lean_object* v_upperBound_4552_, lean_object* v___x_4553_, lean_object* v_a_4554_, lean_object* v_b_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_a_4564_; uint8_t v___x_4568_; 
v___x_4568_ = lean_nat_dec_lt(v_a_4554_, v_upperBound_4552_);
if (v___x_4568_ == 0)
{
lean_object* v___x_4569_; 
lean_dec(v_a_4554_);
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v_b_4555_);
return v___x_4569_;
}
else
{
lean_object* v___x_4570_; lean_object* v_toSignature_4571_; lean_object* v_value_4572_; lean_object* v_name_4573_; lean_object* v_params_4574_; uint8_t v_safe_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
lean_dec_ref(v_b_4555_);
v___x_4570_ = lean_array_fget_borrowed(v___x_4553_, v_a_4554_);
v_toSignature_4571_ = lean_ctor_get(v___x_4570_, 0);
v_value_4572_ = lean_ctor_get(v___x_4570_, 1);
v_name_4573_ = lean_ctor_get(v_toSignature_4571_, 0);
v_params_4574_ = lean_ctor_get(v_toSignature_4571_, 3);
v_safe_4575_ = lean_ctor_get_uint8(v_toSignature_4571_, sizeof(void*)*4);
v___x_4576_ = lean_box(0);
v___x_4577_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
if (v_safe_4575_ == 0)
{
v_a_4564_ = v___x_4577_;
goto v___jp_4563_;
}
else
{
lean_object* v___f_4578_; lean_object* v___x_4579_; 
lean_inc(v_name_4573_);
v___f_4578_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4578_, 0, v_name_4573_);
v___x_4579_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4554_, v___y_4557_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___y_4582_; lean_object* v_decls_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___y_4617_; uint8_t v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v_a_4623_; uint8_t v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v_a_4642_; uint8_t v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4723_; uint8_t v___x_4732_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
v_decls_4612_ = lean_ctor_get(v___y_4556_, 0);
v___x_4613_ = lean_unsigned_to_nat(0u);
v___x_4614_ = lean_array_get_size(v_params_4574_);
lean_inc(v_a_4554_);
lean_inc_ref(v_decls_4612_);
v___x_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4615_, 0, v_decls_4612_);
lean_ctor_set(v___x_4615_, 1, v_a_4554_);
v___x_4732_ = lean_nat_dec_lt(v___x_4613_, v___x_4614_);
if (v___x_4732_ == 0)
{
goto v___jp_4705_;
}
else
{
uint8_t v___x_4733_; 
v___x_4733_ = lean_nat_dec_le(v___x_4614_, v___x_4614_);
if (v___x_4733_ == 0)
{
if (v___x_4732_ == 0)
{
goto v___jp_4705_;
}
else
{
size_t v___x_4734_; size_t v___x_4735_; lean_object* v___x_4736_; 
v___x_4734_ = ((size_t)0ULL);
v___x_4735_ = lean_usize_of_nat(v___x_4614_);
v___x_4736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4574_, v___x_4734_, v___x_4735_, v___x_4576_, v___x_4615_, v___y_4557_, v___y_4561_);
v___y_4723_ = v___x_4736_;
goto v___jp_4722_;
}
}
else
{
size_t v___x_4737_; size_t v___x_4738_; lean_object* v___x_4739_; 
v___x_4737_ = ((size_t)0ULL);
v___x_4738_ = lean_usize_of_nat(v___x_4614_);
v___x_4739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4574_, v___x_4737_, v___x_4738_, v___x_4576_, v___x_4615_, v___y_4557_, v___y_4561_);
v___y_4723_ = v___x_4739_;
goto v___jp_4722_;
}
}
v___jp_4581_:
{
if (lean_obj_tag(v___y_4582_) == 0)
{
lean_object* v___x_4583_; 
lean_dec_ref_known(v___y_4582_, 1);
v___x_4583_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4554_, v___y_4557_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4595_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4586_ = v___x_4583_;
v_isShared_4587_ = v_isSharedCheck_4595_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4595_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
uint8_t v___x_4588_; 
v___x_4588_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4580_, v_a_4584_);
lean_dec(v_a_4584_);
lean_dec(v_a_4580_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4593_; 
lean_dec(v_a_4554_);
v___x_4589_ = lean_box(v___x_4568_);
v___x_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
v___x_4591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
lean_ctor_set(v___x_4591_, 1, v___x_4576_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 0, v___x_4591_);
v___x_4593_ = v___x_4586_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4591_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
else
{
lean_del_object(v___x_4586_);
v_a_4564_ = v___x_4577_;
goto v___jp_4563_;
}
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_dec(v_a_4580_);
lean_dec(v_a_4554_);
v_a_4596_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4583_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4583_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
lean_dec(v_a_4580_);
lean_dec(v_a_4554_);
v_a_4604_ = lean_ctor_get(v___y_4582_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___y_4582_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___y_4582_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___y_4582_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
v___jp_4616_:
{
lean_object* v___x_4624_; double v___x_4625_; double v___x_4626_; double v___x_4627_; double v___x_4628_; double v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4624_ = lean_io_mono_nanos_now();
v___x_4625_ = lean_float_of_nat(v___y_4617_);
v___x_4626_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_4627_ = lean_float_div(v___x_4625_, v___x_4626_);
v___x_4628_ = lean_float_of_nat(v___x_4624_);
v___x_4629_ = lean_float_div(v___x_4628_, v___x_4626_);
v___x_4630_ = lean_box_float(v___x_4627_);
v___x_4631_ = lean_box_float(v___x_4629_);
v___x_4632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4630_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v_a_4623_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4619_);
v___x_4634_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4619_, v___x_4568_, v___y_4621_, v___y_4620_, v___y_4618_, v___y_4622_, v___f_4578_, v___x_4633_, v___x_4615_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec_ref_known(v___x_4615_, 2);
v___y_4582_ = v___x_4634_;
goto v___jp_4581_;
}
v___jp_4635_:
{
lean_object* v___x_4643_; double v___x_4644_; double v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4643_ = lean_io_get_num_heartbeats();
v___x_4644_ = lean_float_of_nat(v___y_4637_);
v___x_4645_ = lean_float_of_nat(v___x_4643_);
v___x_4646_ = lean_box_float(v___x_4644_);
v___x_4647_ = lean_box_float(v___x_4645_);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4646_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
v___x_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4649_, 0, v_a_4642_);
lean_ctor_set(v___x_4649_, 1, v___x_4648_);
lean_inc_ref(v___y_4640_);
lean_inc(v___y_4638_);
v___x_4650_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4638_, v___x_4568_, v___y_4640_, v___y_4639_, v___y_4636_, v___y_4641_, v___f_4578_, v___x_4649_, v___x_4615_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec_ref_known(v___x_4615_, 2);
v___y_4582_ = v___x_4650_;
goto v___jp_4581_;
}
v___jp_4651_:
{
lean_object* v___x_4657_; 
v___x_4657_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___y_4561_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc(v_a_4658_);
lean_dec_ref_known(v___x_4657_, 1);
v___x_4659_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4660_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4656_, v___x_4659_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = lean_io_mono_nanos_now();
v___x_4662_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4653_, v___x_4615_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4662_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4662_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
lean_ctor_set_tag(v___x_4665_, 1);
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
v___y_4617_ = v___x_4661_;
v___y_4618_ = v___y_4652_;
v___y_4619_ = v___y_4654_;
v___y_4620_ = v___y_4656_;
v___y_4621_ = v___y_4655_;
v___y_4622_ = v_a_4658_;
v_a_4623_ = v___x_4668_;
goto v___jp_4616_;
}
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
v_a_4671_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4662_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4662_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
lean_ctor_set_tag(v___x_4673_, 0);
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
v___y_4617_ = v___x_4661_;
v___y_4618_ = v___y_4652_;
v___y_4619_ = v___y_4654_;
v___y_4620_ = v___y_4656_;
v___y_4621_ = v___y_4655_;
v___y_4622_ = v_a_4658_;
v_a_4623_ = v___x_4676_;
goto v___jp_4616_;
}
}
}
}
else
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = lean_io_get_num_heartbeats();
v___x_4680_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4653_, v___x_4615_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4680_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4680_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
lean_ctor_set_tag(v___x_4683_, 1);
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
v___y_4636_ = v___y_4652_;
v___y_4637_ = v___x_4679_;
v___y_4638_ = v___y_4654_;
v___y_4639_ = v___y_4656_;
v___y_4640_ = v___y_4655_;
v___y_4641_ = v_a_4658_;
v_a_4642_ = v___x_4686_;
goto v___jp_4635_;
}
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
v_a_4689_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4680_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4680_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set_tag(v___x_4691_, 0);
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
v___y_4636_ = v___y_4652_;
v___y_4637_ = v___x_4679_;
v___y_4638_ = v___y_4654_;
v___y_4639_ = v___y_4656_;
v___y_4640_ = v___y_4655_;
v___y_4641_ = v_a_4658_;
v_a_4642_ = v___x_4694_;
goto v___jp_4635_;
}
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v___y_4653_);
lean_dec_ref_known(v___x_4615_, 2);
lean_dec(v_a_4580_);
lean_dec_ref(v___f_4578_);
lean_dec(v_a_4554_);
v_a_4697_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4657_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4657_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
v___jp_4705_:
{
if (lean_obj_tag(v_value_4572_) == 0)
{
lean_object* v_toCold_4706_; lean_object* v_options_4707_; uint8_t v_hasTrace_4708_; 
v_toCold_4706_ = lean_ctor_get(v___y_4560_, 0);
v_options_4707_ = lean_ctor_get(v_toCold_4706_, 2);
v_hasTrace_4708_ = lean_ctor_get_uint8(v_options_4707_, sizeof(void*)*1);
if (v_hasTrace_4708_ == 0)
{
lean_object* v_code_4709_; lean_object* v___x_4710_; 
lean_dec_ref(v___f_4578_);
v_code_4709_ = lean_ctor_get(v_value_4572_, 0);
lean_inc_ref(v_code_4709_);
v___x_4710_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4709_, v___x_4615_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec_ref_known(v___x_4615_, 2);
v___y_4582_ = v___x_4710_;
goto v___jp_4581_;
}
else
{
lean_object* v_code_4711_; lean_object* v_inheritedTraceOptions_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; uint8_t v___x_4716_; 
v_code_4711_ = lean_ctor_get(v_value_4572_, 0);
v_inheritedTraceOptions_4712_ = lean_ctor_get(v_toCold_4706_, 11);
v___x_4713_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_4714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4715_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4712_, v_options_4707_, v___x_4715_);
if (v___x_4716_ == 0)
{
lean_object* v___x_4717_; uint8_t v___x_4718_; 
v___x_4717_ = l_Lean_trace_profiler;
v___x_4718_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_4707_, v___x_4717_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4719_; 
lean_dec_ref(v___f_4578_);
lean_inc_ref(v_code_4711_);
v___x_4719_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4711_, v___x_4615_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec_ref_known(v___x_4615_, 2);
v___y_4582_ = v___x_4719_;
goto v___jp_4581_;
}
else
{
lean_inc_ref(v_code_4711_);
v___y_4652_ = v___x_4716_;
v___y_4653_ = v_code_4711_;
v___y_4654_ = v___x_4713_;
v___y_4655_ = v___x_4714_;
v___y_4656_ = v_options_4707_;
goto v___jp_4651_;
}
}
else
{
lean_inc_ref(v_code_4711_);
v___y_4652_ = v___x_4716_;
v___y_4653_ = v_code_4711_;
v___y_4654_ = v___x_4713_;
v___y_4655_ = v___x_4714_;
v___y_4656_ = v_options_4707_;
goto v___jp_4651_;
}
}
}
else
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
lean_dec_ref(v___f_4578_);
v___x_4720_ = lean_box(1);
v___x_4721_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4720_, v___x_4615_, v___y_4557_, v___y_4561_);
lean_dec_ref_known(v___x_4615_, 2);
v___y_4582_ = v___x_4721_;
goto v___jp_4581_;
}
}
v___jp_4722_:
{
if (lean_obj_tag(v___y_4723_) == 0)
{
lean_dec_ref_known(v___y_4723_, 1);
goto v___jp_4705_;
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
lean_dec_ref_known(v___x_4615_, 2);
lean_dec(v_a_4580_);
lean_dec_ref(v___f_4578_);
lean_dec(v_a_4554_);
v_a_4724_ = lean_ctor_get(v___y_4723_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___y_4723_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___y_4723_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___y_4723_);
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
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
lean_dec_ref(v___f_4578_);
lean_dec(v_a_4554_);
v_a_4740_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4742_ = v___x_4579_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4579_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
}
v___jp_4563_:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_unsigned_to_nat(1u);
v___x_4566_ = lean_nat_add(v_a_4554_, v___x_4565_);
lean_dec(v_a_4554_);
lean_inc_ref(v_a_4564_);
v_a_4554_ = v___x_4566_;
v_b_4555_ = v_a_4564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* v_upperBound_4748_, lean_object* v___x_4749_, lean_object* v_a_4750_, lean_object* v_b_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4748_, v___x_4749_, v_a_4750_, v_b_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec_ref(v___y_4752_);
lean_dec_ref(v___x_4749_);
lean_dec(v_upperBound_4748_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v_decls_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v_decls_4767_ = lean_ctor_get(v_a_4760_, 0);
v___x_4768_ = lean_array_get_size(v_decls_4767_);
v___x_4769_ = lean_unsigned_to_nat(0u);
v___x_4770_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__0));
v___x_4771_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v___x_4768_, v_decls_4767_, v___x_4769_, v___x_4770_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4786_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4774_ = v___x_4771_;
v_isShared_4775_ = v_isSharedCheck_4786_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4771_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4786_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v_fst_4776_; 
v_fst_4776_ = lean_ctor_get(v_a_4772_, 0);
lean_inc(v_fst_4776_);
lean_dec(v_a_4772_);
if (lean_obj_tag(v_fst_4776_) == 0)
{
uint8_t v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4780_; 
v___x_4777_ = 0;
v___x_4778_ = lean_box(v___x_4777_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4778_);
v___x_4780_ = v___x_4774_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
else
{
lean_object* v_val_4782_; lean_object* v___x_4784_; 
v_val_4782_ = lean_ctor_get(v_fst_4776_, 0);
lean_inc(v_val_4782_);
lean_dec_ref_known(v_fst_4776_, 1);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v_val_4782_);
v___x_4784_ = v___x_4774_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_val_4782_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
v_a_4787_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4771_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4771_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(lean_object* v_00_u03b1_4803_, lean_object* v_x_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___redArg(v_x_4804_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4813_, lean_object* v_x_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__3(v_00_u03b1_4813_, v_x_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
lean_dec(v___y_4816_);
lean_dec_ref(v___y_4815_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_upperBound_4823_, lean_object* v___x_4824_, lean_object* v_inst_4825_, lean_object* v_R_4826_, lean_object* v_a_4827_, lean_object* v_b_4828_, lean_object* v_c_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v___x_4837_; 
v___x_4837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg(v_upperBound_4823_, v___x_4824_, v_a_4827_, v_b_4828_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_upperBound_4838_, lean_object* v___x_4839_, lean_object* v_inst_4840_, lean_object* v_R_4841_, lean_object* v_a_4842_, lean_object* v_b_4843_, lean_object* v_c_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_upperBound_4838_, v___x_4839_, v_inst_4840_, v_R_4841_, v_a_4842_, v_b_4843_, v_c_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec_ref(v___x_4839_);
lean_dec(v_upperBound_4838_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(lean_object* v_oldTraces_4853_, lean_object* v_data_4854_, lean_object* v_ref_4855_, lean_object* v_msg_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg(v_oldTraces_4853_, v_data_4854_, v_ref_4855_, v_msg_4856_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___boxed(lean_object* v_oldTraces_4865_, lean_object* v_data_4866_, lean_object* v_ref_4867_, lean_object* v_msg_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2(v_oldTraces_4865_, v_data_4866_, v_ref_4867_, v_msg_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(lean_object* v_cls_4879_, lean_object* v_msg_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v_toCold_4886_; lean_object* v_ref_4887_; lean_object* v___x_4888_; lean_object* v_env_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
v_toCold_4886_ = lean_ctor_get(v___y_4883_, 0);
v_ref_4887_ = lean_ctor_get(v___y_4883_, 2);
v___x_4888_ = lean_st_ref_get(v___y_4884_);
v_env_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc_ref(v_env_4889_);
lean_dec(v___x_4888_);
v___x_4890_ = lean_st_ref_get(v___y_4882_);
v___x_4891_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4881_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4950_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4894_ = v___x_4891_;
v_isShared_4895_ = v_isSharedCheck_4950_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4950_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v_lctx_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4948_; 
v_lctx_4896_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4948_ == 0)
{
lean_object* v_unused_4949_; 
v_unused_4949_ = lean_ctor_get(v___x_4890_, 1);
lean_dec(v_unused_4949_);
v___x_4898_ = v___x_4890_;
v_isShared_4899_ = v_isSharedCheck_4948_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_lctx_4896_);
lean_dec(v___x_4890_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4948_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v_options_4900_; uint8_t v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4906_; 
v_options_4900_ = lean_ctor_get(v_toCold_4886_, 2);
v___x_4901_ = lean_unbox(v_a_4892_);
lean_dec(v_a_4892_);
v___x_4902_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4896_, v___x_4901_);
lean_dec_ref(v_lctx_4896_);
v___x_4903_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
lean_inc_ref(v_options_4900_);
v___x_4904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4904_, 0, v_env_4889_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
lean_ctor_set(v___x_4904_, 2, v___x_4902_);
lean_ctor_set(v___x_4904_, 3, v_options_4900_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set_tag(v___x_4898_, 3);
lean_ctor_set(v___x_4898_, 1, v_msg_4880_);
lean_ctor_set(v___x_4898_, 0, v___x_4904_);
v___x_4906_ = v___x_4898_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4947_, 1, v_msg_4880_);
v___x_4906_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; lean_object* v_traceState_4908_; lean_object* v_env_4909_; lean_object* v_nextMacroScope_4910_; lean_object* v_ngen_4911_; lean_object* v_auxDeclNGen_4912_; lean_object* v_cache_4913_; lean_object* v_messages_4914_; lean_object* v_infoState_4915_; lean_object* v_snapshotTasks_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4946_; 
v___x_4907_ = lean_st_ref_take(v___y_4884_);
v_traceState_4908_ = lean_ctor_get(v___x_4907_, 4);
v_env_4909_ = lean_ctor_get(v___x_4907_, 0);
v_nextMacroScope_4910_ = lean_ctor_get(v___x_4907_, 1);
v_ngen_4911_ = lean_ctor_get(v___x_4907_, 2);
v_auxDeclNGen_4912_ = lean_ctor_get(v___x_4907_, 3);
v_cache_4913_ = lean_ctor_get(v___x_4907_, 5);
v_messages_4914_ = lean_ctor_get(v___x_4907_, 6);
v_infoState_4915_ = lean_ctor_get(v___x_4907_, 7);
v_snapshotTasks_4916_ = lean_ctor_get(v___x_4907_, 8);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4918_ = v___x_4907_;
v_isShared_4919_ = v_isSharedCheck_4946_;
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
v_isShared_4919_ = v_isSharedCheck_4946_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
uint64_t v_tid_4920_; lean_object* v_traces_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4945_; 
v_tid_4920_ = lean_ctor_get_uint64(v_traceState_4908_, sizeof(void*)*1);
v_traces_4921_ = lean_ctor_get(v_traceState_4908_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_traceState_4908_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4923_ = v_traceState_4908_;
v_isShared_4924_ = v_isSharedCheck_4945_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_traces_4921_);
lean_dec(v_traceState_4908_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4945_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; double v___x_4927_; uint8_t v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4936_; 
v___x_4925_ = lean_box(0);
v___x_4926_ = lean_box(0);
v___x_4927_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_4928_ = 0;
v___x_4929_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_4930_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4930_, 0, v_cls_4879_);
lean_ctor_set(v___x_4930_, 1, v___x_4926_);
lean_ctor_set(v___x_4930_, 2, v___x_4929_);
lean_ctor_set_float(v___x_4930_, sizeof(void*)*3, v___x_4927_);
lean_ctor_set_float(v___x_4930_, sizeof(void*)*3 + 8, v___x_4927_);
lean_ctor_set_uint8(v___x_4930_, sizeof(void*)*3 + 16, v___x_4928_);
v___x_4931_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_4932_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4930_);
lean_ctor_set(v___x_4932_, 1, v___x_4906_);
lean_ctor_set(v___x_4932_, 2, v___x_4931_);
lean_inc(v_ref_4887_);
v___x_4933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4933_, 0, v_ref_4887_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
v___x_4934_ = l_Lean_PersistentArray_push___redArg(v_traces_4921_, v___x_4933_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v___x_4934_);
v___x_4936_ = v___x_4923_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4934_);
lean_ctor_set_uint64(v_reuseFailAlloc_4944_, sizeof(void*)*1, v_tid_4920_);
v___x_4936_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4938_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 4, v___x_4936_);
v___x_4938_ = v___x_4918_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_env_4909_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_nextMacroScope_4910_);
lean_ctor_set(v_reuseFailAlloc_4943_, 2, v_ngen_4911_);
lean_ctor_set(v_reuseFailAlloc_4943_, 3, v_auxDeclNGen_4912_);
lean_ctor_set(v_reuseFailAlloc_4943_, 4, v___x_4936_);
lean_ctor_set(v_reuseFailAlloc_4943_, 5, v_cache_4913_);
lean_ctor_set(v_reuseFailAlloc_4943_, 6, v_messages_4914_);
lean_ctor_set(v_reuseFailAlloc_4943_, 7, v_infoState_4915_);
lean_ctor_set(v_reuseFailAlloc_4943_, 8, v_snapshotTasks_4916_);
v___x_4938_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4939_ = lean_st_ref_put(v___y_4884_, v___x_4938_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4925_);
v___x_4941_ = v___x_4894_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4925_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
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
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4958_; 
lean_dec(v___x_4890_);
lean_dec_ref(v_env_4889_);
lean_dec_ref(v_msg_4880_);
lean_dec(v_cls_4879_);
v_a_4951_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4953_ = v___x_4891_;
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4891_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4956_; 
if (v_isShared_4954_ == 0)
{
v___x_4956_ = v___x_4953_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_a_4951_);
v___x_4956_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
return v___x_4956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___boxed(lean_object* v_cls_4959_, lean_object* v_msg_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4959_, v_msg_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(lean_object* v_cls_4967_, lean_object* v_msg_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v___x_4976_; 
v___x_4976_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v_cls_4967_, v_msg_4968_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___boxed(lean_object* v_cls_4977_, lean_object* v_msg_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1(v_cls_4977_, v_msg_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
return v_res_4986_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4987_ = lean_box(0);
v___x_4988_ = lean_unsigned_to_nat(16u);
v___x_4989_ = lean_mk_array(v___x_4988_, v___x_4987_);
return v___x_4989_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4990_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__0);
v___x_4991_ = lean_unsigned_to_nat(0u);
v___x_4992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4991_);
lean_ctor_set(v___x_4992_, 1, v___x_4990_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(size_t v_sz_4993_, size_t v_i_4994_, lean_object* v_bs_4995_){
_start:
{
uint8_t v___x_4996_; 
v___x_4996_ = lean_usize_dec_lt(v_i_4994_, v_sz_4993_);
if (v___x_4996_ == 0)
{
return v_bs_4995_;
}
else
{
lean_object* v___x_4997_; lean_object* v_bs_x27_4998_; lean_object* v___x_4999_; size_t v___x_5000_; size_t v___x_5001_; lean_object* v___x_5002_; 
v___x_4997_ = lean_unsigned_to_nat(0u);
v_bs_x27_4998_ = lean_array_uset(v_bs_4995_, v_i_4994_, v___x_4997_);
v___x_4999_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5000_ = ((size_t)1ULL);
v___x_5001_ = lean_usize_add(v_i_4994_, v___x_5000_);
v___x_5002_ = lean_array_uset(v_bs_x27_4998_, v_i_4994_, v___x_4999_);
v_i_4994_ = v___x_5001_;
v_bs_4995_ = v___x_5002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___boxed(lean_object* v_sz_5004_, lean_object* v_i_5005_, lean_object* v_bs_5006_){
_start:
{
size_t v_sz_boxed_5007_; size_t v_i_boxed_5008_; lean_object* v_res_5009_; 
v_sz_boxed_5007_ = lean_unbox_usize(v_sz_5004_);
lean_dec(v_sz_5004_);
v_i_boxed_5008_ = lean_unbox_usize(v_i_5005_);
lean_dec(v_i_5005_);
v_res_5009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_boxed_5007_, v_i_boxed_5008_, v_bs_5006_);
return v_res_5009_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__0));
v___x_5012_ = l_Lean_stringToMessageData(v___x_5011_);
return v___x_5012_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3(void){
_start:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5014_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__2));
v___x_5015_ = l_Lean_stringToMessageData(v___x_5014_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(lean_object* v_n_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_){
_start:
{
lean_object* v___x_5027_; lean_object* v_decls_5028_; lean_object* v_funVals_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5069_; 
v___x_5027_ = lean_st_ref_take(v_a_5018_);
v_decls_5028_ = lean_ctor_get(v_a_5017_, 0);
v_funVals_5029_ = lean_ctor_get(v___x_5027_, 1);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5069_ == 0)
{
lean_object* v_unused_5070_; 
v_unused_5070_ = lean_ctor_get(v___x_5027_, 0);
lean_dec(v_unused_5070_);
v___x_5031_ = v___x_5027_;
v_isShared_5032_ = v_isSharedCheck_5069_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_funVals_5029_);
lean_dec(v___x_5027_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5069_;
goto v_resetjp_5030_;
}
v___jp_5024_:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5025_ = lean_box(0);
v___x_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
return v___x_5026_;
}
v_resetjp_5030_:
{
size_t v_sz_5033_; size_t v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5037_; 
v_sz_5033_ = lean_array_size(v_decls_5028_);
v___x_5034_ = ((size_t)0ULL);
lean_inc_ref(v_decls_5028_);
v___x_5035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_5033_, v___x_5034_, v_decls_5028_);
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 0, v___x_5035_);
v___x_5037_ = v___x_5031_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_5035_);
lean_ctor_set(v_reuseFailAlloc_5068_, 1, v_funVals_5029_);
v___x_5037_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5038_ = lean_st_ref_put(v_a_5018_, v___x_5037_);
v___x_5039_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; uint8_t v___x_5041_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
lean_inc(v_a_5040_);
lean_dec_ref_known(v___x_5039_, 1);
v___x_5041_ = lean_unbox(v_a_5040_);
lean_dec(v_a_5040_);
if (v___x_5041_ == 0)
{
lean_object* v_toCold_5042_; lean_object* v_options_5043_; uint8_t v_hasTrace_5044_; 
v_toCold_5042_ = lean_ctor_get(v_a_5021_, 0);
v_options_5043_ = lean_ctor_get(v_toCold_5042_, 2);
v_hasTrace_5044_ = lean_ctor_get_uint8(v_options_5043_, sizeof(void*)*1);
if (v_hasTrace_5044_ == 0)
{
lean_dec(v_n_5016_);
goto v___jp_5024_;
}
else
{
lean_object* v_inheritedTraceOptions_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; 
v_inheritedTraceOptions_5045_ = lean_ctor_get(v_toCold_5042_, 11);
v___x_5046_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5047_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5048_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5045_, v_options_5043_, v___x_5047_);
if (v___x_5048_ == 0)
{
lean_dec(v_n_5016_);
goto v___jp_5024_;
}
else
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5049_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5050_ = l_Nat_reprFast(v_n_5016_);
v___x_5051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
v___x_5052_ = l_Lean_MessageData_ofFormat(v___x_5051_);
v___x_5053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5049_);
lean_ctor_set(v___x_5053_, 1, v___x_5052_);
v___x_5054_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5053_);
lean_ctor_set(v___x_5055_, 1, v___x_5054_);
v___x_5056_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5046_, v___x_5055_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_dec_ref_known(v___x_5056_, 1);
goto v___jp_5024_;
}
else
{
return v___x_5056_;
}
}
}
}
else
{
lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5057_ = lean_unsigned_to_nat(1u);
v___x_5058_ = lean_nat_add(v_n_5016_, v___x_5057_);
lean_dec(v_n_5016_);
v_n_5016_ = v___x_5058_;
goto _start;
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
lean_dec(v_n_5016_);
v_a_5060_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_5039_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5039_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
lean_dec(v_a_5077_);
lean_dec_ref(v_a_5076_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
return v_res_5079_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5081_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5083_ = lean_panic_fn_borrowed(v___x_5082_, v_msg_5081_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5084_, lean_object* v_msg_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_toCold_5091_; lean_object* v_ref_5092_; lean_object* v___x_5093_; lean_object* v_env_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v_toCold_5091_ = lean_ctor_get(v___y_5088_, 0);
v_ref_5092_ = lean_ctor_get(v___y_5088_, 2);
v___x_5093_ = lean_st_ref_get(v___y_5089_);
v_env_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc_ref(v_env_5094_);
lean_dec(v___x_5093_);
v___x_5095_ = lean_st_ref_get(v___y_5087_);
v___x_5096_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5086_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5155_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5155_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5155_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v_lctx_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5153_; 
v_lctx_5101_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5153_ == 0)
{
lean_object* v_unused_5154_; 
v_unused_5154_ = lean_ctor_get(v___x_5095_, 1);
lean_dec(v_unused_5154_);
v___x_5103_ = v___x_5095_;
v_isShared_5104_ = v_isSharedCheck_5153_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_lctx_5101_);
lean_dec(v___x_5095_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5153_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v_options_5105_; uint8_t v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5111_; 
v_options_5105_ = lean_ctor_get(v_toCold_5091_, 2);
v___x_5106_ = lean_unbox(v_a_5097_);
lean_dec(v_a_5097_);
v___x_5107_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5101_, v___x_5106_);
lean_dec_ref(v_lctx_5101_);
v___x_5108_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2_spec__2___redArg___closed__1);
lean_inc_ref(v_options_5105_);
v___x_5109_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5109_, 0, v_env_5094_);
lean_ctor_set(v___x_5109_, 1, v___x_5108_);
lean_ctor_set(v___x_5109_, 2, v___x_5107_);
lean_ctor_set(v___x_5109_, 3, v_options_5105_);
if (v_isShared_5104_ == 0)
{
lean_ctor_set_tag(v___x_5103_, 3);
lean_ctor_set(v___x_5103_, 1, v_msg_5085_);
lean_ctor_set(v___x_5103_, 0, v___x_5109_);
v___x_5111_ = v___x_5103_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5109_);
lean_ctor_set(v_reuseFailAlloc_5152_, 1, v_msg_5085_);
v___x_5111_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
lean_object* v___x_5112_; lean_object* v_traceState_5113_; lean_object* v_env_5114_; lean_object* v_nextMacroScope_5115_; lean_object* v_ngen_5116_; lean_object* v_auxDeclNGen_5117_; lean_object* v_cache_5118_; lean_object* v_messages_5119_; lean_object* v_infoState_5120_; lean_object* v_snapshotTasks_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5151_; 
v___x_5112_ = lean_st_ref_take(v___y_5089_);
v_traceState_5113_ = lean_ctor_get(v___x_5112_, 4);
v_env_5114_ = lean_ctor_get(v___x_5112_, 0);
v_nextMacroScope_5115_ = lean_ctor_get(v___x_5112_, 1);
v_ngen_5116_ = lean_ctor_get(v___x_5112_, 2);
v_auxDeclNGen_5117_ = lean_ctor_get(v___x_5112_, 3);
v_cache_5118_ = lean_ctor_get(v___x_5112_, 5);
v_messages_5119_ = lean_ctor_get(v___x_5112_, 6);
v_infoState_5120_ = lean_ctor_get(v___x_5112_, 7);
v_snapshotTasks_5121_ = lean_ctor_get(v___x_5112_, 8);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5123_ = v___x_5112_;
v_isShared_5124_ = v_isSharedCheck_5151_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_snapshotTasks_5121_);
lean_inc(v_infoState_5120_);
lean_inc(v_messages_5119_);
lean_inc(v_cache_5118_);
lean_inc(v_traceState_5113_);
lean_inc(v_auxDeclNGen_5117_);
lean_inc(v_ngen_5116_);
lean_inc(v_nextMacroScope_5115_);
lean_inc(v_env_5114_);
lean_dec(v___x_5112_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5151_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
uint64_t v_tid_5125_; lean_object* v_traces_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5150_; 
v_tid_5125_ = lean_ctor_get_uint64(v_traceState_5113_, sizeof(void*)*1);
v_traces_5126_ = lean_ctor_get(v_traceState_5113_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v_traceState_5113_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5128_ = v_traceState_5113_;
v_isShared_5129_ = v_isSharedCheck_5150_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_traces_5126_);
lean_dec(v_traceState_5113_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5150_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; double v___x_5132_; uint8_t v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5141_; 
v___x_5130_ = lean_box(0);
v___x_5131_ = lean_box(0);
v___x_5132_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___closed__0);
v___x_5133_ = 0;
v___x_5134_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_5135_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5135_, 0, v_cls_5084_);
lean_ctor_set(v___x_5135_, 1, v___x_5131_);
lean_ctor_set(v___x_5135_, 2, v___x_5134_);
lean_ctor_set_float(v___x_5135_, sizeof(void*)*3, v___x_5132_);
lean_ctor_set_float(v___x_5135_, sizeof(void*)*3 + 8, v___x_5132_);
lean_ctor_set_uint8(v___x_5135_, sizeof(void*)*3 + 16, v___x_5133_);
v___x_5136_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5137_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5135_);
lean_ctor_set(v___x_5137_, 1, v___x_5111_);
lean_ctor_set(v___x_5137_, 2, v___x_5136_);
lean_inc(v_ref_5092_);
v___x_5138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5138_, 0, v_ref_5092_);
lean_ctor_set(v___x_5138_, 1, v___x_5137_);
v___x_5139_ = l_Lean_PersistentArray_push___redArg(v_traces_5126_, v___x_5138_);
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v___x_5139_);
v___x_5141_ = v___x_5128_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v___x_5139_);
lean_ctor_set_uint64(v_reuseFailAlloc_5149_, sizeof(void*)*1, v_tid_5125_);
v___x_5141_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
lean_object* v___x_5143_; 
if (v_isShared_5124_ == 0)
{
lean_ctor_set(v___x_5123_, 4, v___x_5141_);
v___x_5143_ = v___x_5123_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_env_5114_);
lean_ctor_set(v_reuseFailAlloc_5148_, 1, v_nextMacroScope_5115_);
lean_ctor_set(v_reuseFailAlloc_5148_, 2, v_ngen_5116_);
lean_ctor_set(v_reuseFailAlloc_5148_, 3, v_auxDeclNGen_5117_);
lean_ctor_set(v_reuseFailAlloc_5148_, 4, v___x_5141_);
lean_ctor_set(v_reuseFailAlloc_5148_, 5, v_cache_5118_);
lean_ctor_set(v_reuseFailAlloc_5148_, 6, v_messages_5119_);
lean_ctor_set(v_reuseFailAlloc_5148_, 7, v_infoState_5120_);
lean_ctor_set(v_reuseFailAlloc_5148_, 8, v_snapshotTasks_5121_);
v___x_5143_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
lean_object* v___x_5144_; lean_object* v___x_5146_; 
v___x_5144_ = lean_st_ref_put(v___y_5089_, v___x_5143_);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v___x_5130_);
v___x_5146_ = v___x_5099_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v___x_5130_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
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
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec(v___x_5095_);
lean_dec_ref(v_env_5094_);
lean_dec_ref(v_msg_5085_);
lean_dec(v_cls_5084_);
v_a_5156_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5096_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5096_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5164_, lean_object* v_msg_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5164_, v_msg_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(lean_object* v_as_5172_, size_t v_i_5173_, size_t v_stop_5174_, lean_object* v_b_5175_){
_start:
{
uint8_t v___x_5177_; 
v___x_5177_ = lean_usize_dec_eq(v_i_5173_, v_stop_5174_);
if (v___x_5177_ == 0)
{
lean_object* v_fst_5178_; lean_object* v_snd_5179_; lean_object* v___x_5180_; lean_object* v_snd_5181_; lean_object* v_fst_5182_; lean_object* v_fst_5183_; lean_object* v_snd_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5198_; 
v_fst_5178_ = lean_ctor_get(v_b_5175_, 0);
lean_inc(v_fst_5178_);
v_snd_5179_ = lean_ctor_get(v_b_5175_, 1);
lean_inc(v_snd_5179_);
lean_dec_ref(v_b_5175_);
v___x_5180_ = lean_array_uget_borrowed(v_as_5172_, v_i_5173_);
v_snd_5181_ = lean_ctor_get(v___x_5180_, 1);
lean_inc(v_snd_5181_);
v_fst_5182_ = lean_ctor_get(v___x_5180_, 0);
v_fst_5183_ = lean_ctor_get(v_snd_5181_, 0);
v_snd_5184_ = lean_ctor_get(v_snd_5181_, 1);
v_isSharedCheck_5198_ = !lean_is_exclusive(v_snd_5181_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5186_ = v_snd_5181_;
v_isShared_5187_ = v_isSharedCheck_5198_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_snd_5184_);
lean_inc(v_fst_5183_);
lean_dec(v_snd_5181_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5198_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v_fvarId_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5193_; 
v_fvarId_5188_ = lean_ctor_get(v_fst_5182_, 0);
v___x_5189_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_5183_, v_fst_5178_);
lean_dec(v_fst_5183_);
v___x_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5190_, 0, v_snd_5184_);
lean_inc(v_fvarId_5188_);
v___x_5191_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5179_, v_fvarId_5188_, v___x_5190_);
if (v_isShared_5187_ == 0)
{
lean_ctor_set(v___x_5186_, 1, v___x_5191_);
lean_ctor_set(v___x_5186_, 0, v___x_5189_);
v___x_5193_ = v___x_5186_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v___x_5189_);
lean_ctor_set(v_reuseFailAlloc_5197_, 1, v___x_5191_);
v___x_5193_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
size_t v___x_5194_; size_t v___x_5195_; 
v___x_5194_ = ((size_t)1ULL);
v___x_5195_ = lean_usize_add(v_i_5173_, v___x_5194_);
v_i_5173_ = v___x_5195_;
v_b_5175_ = v___x_5193_;
goto _start;
}
}
}
else
{
lean_object* v___x_5199_; 
v___x_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5199_, 0, v_b_5175_);
return v___x_5199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg___boxed(lean_object* v_as_5200_, lean_object* v_i_5201_, lean_object* v_stop_5202_, lean_object* v_b_5203_, lean_object* v___y_5204_){
_start:
{
size_t v_i_boxed_5205_; size_t v_stop_boxed_5206_; lean_object* v_res_5207_; 
v_i_boxed_5205_ = lean_unbox_usize(v_i_5201_);
lean_dec(v_i_5201_);
v_stop_boxed_5206_ = lean_unbox_usize(v_stop_5202_);
lean_dec(v_stop_5202_);
v_res_5207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5200_, v_i_boxed_5205_, v_stop_boxed_5206_, v_b_5203_);
lean_dec_ref(v_as_5200_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5208_, lean_object* v_x_5209_){
_start:
{
if (lean_obj_tag(v_x_5209_) == 0)
{
lean_object* v___x_5210_; 
v___x_5210_ = lean_box(0);
return v___x_5210_;
}
else
{
lean_object* v_key_5211_; lean_object* v_value_5212_; lean_object* v_tail_5213_; uint8_t v___x_5214_; 
v_key_5211_ = lean_ctor_get(v_x_5209_, 0);
v_value_5212_ = lean_ctor_get(v_x_5209_, 1);
v_tail_5213_ = lean_ctor_get(v_x_5209_, 2);
v___x_5214_ = l_Lean_instBEqFVarId_beq(v_key_5211_, v_a_5208_);
if (v___x_5214_ == 0)
{
v_x_5209_ = v_tail_5213_;
goto _start;
}
else
{
lean_object* v___x_5216_; 
lean_inc(v_value_5212_);
v___x_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5216_, 0, v_value_5212_);
return v___x_5216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5217_, lean_object* v_x_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5217_, v_x_5218_);
lean_dec(v_x_5218_);
lean_dec(v_a_5217_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5220_, lean_object* v_a_5221_){
_start:
{
lean_object* v_buckets_5222_; lean_object* v___x_5223_; uint64_t v___x_5224_; uint64_t v___x_5225_; uint64_t v___x_5226_; uint64_t v_fold_5227_; uint64_t v___x_5228_; uint64_t v___x_5229_; uint64_t v___x_5230_; size_t v___x_5231_; size_t v___x_5232_; size_t v___x_5233_; size_t v___x_5234_; size_t v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v_buckets_5222_ = lean_ctor_get(v_m_5220_, 1);
v___x_5223_ = lean_array_get_size(v_buckets_5222_);
v___x_5224_ = l_Lean_instHashableFVarId_hash(v_a_5221_);
v___x_5225_ = 32ULL;
v___x_5226_ = lean_uint64_shift_right(v___x_5224_, v___x_5225_);
v_fold_5227_ = lean_uint64_xor(v___x_5224_, v___x_5226_);
v___x_5228_ = 16ULL;
v___x_5229_ = lean_uint64_shift_right(v_fold_5227_, v___x_5228_);
v___x_5230_ = lean_uint64_xor(v_fold_5227_, v___x_5229_);
v___x_5231_ = lean_uint64_to_usize(v___x_5230_);
v___x_5232_ = lean_usize_of_nat(v___x_5223_);
v___x_5233_ = ((size_t)1ULL);
v___x_5234_ = lean_usize_sub(v___x_5232_, v___x_5233_);
v___x_5235_ = lean_usize_land(v___x_5231_, v___x_5234_);
v___x_5236_ = lean_array_uget_borrowed(v_buckets_5222_, v___x_5235_);
v___x_5237_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5221_, v___x_5236_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5238_, v_a_5239_);
lean_dec(v_a_5239_);
lean_dec_ref(v_m_5238_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(lean_object* v_assignment_5241_, lean_object* v_as_5242_, size_t v_i_5243_, size_t v_stop_5244_, lean_object* v_b_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
lean_object* v_a_5252_; uint8_t v___x_5256_; 
v___x_5256_ = lean_usize_dec_eq(v_i_5243_, v_stop_5244_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; lean_object* v_fvarId_5258_; lean_object* v___x_5259_; 
v___x_5257_ = lean_array_uget_borrowed(v_as_5242_, v_i_5243_);
v_fvarId_5258_ = lean_ctor_get(v___x_5257_, 0);
v___x_5259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5241_, v_fvarId_5258_);
if (lean_obj_tag(v___x_5259_) == 1)
{
lean_object* v_val_5260_; lean_object* v___x_5261_; 
v_val_5260_ = lean_ctor_get(v___x_5259_, 0);
lean_inc(v_val_5260_);
lean_dec_ref_known(v___x_5259_, 1);
v___x_5261_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5260_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
if (lean_obj_tag(v___x_5261_) == 0)
{
lean_object* v_a_5262_; 
v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
lean_inc(v_a_5262_);
lean_dec_ref_known(v___x_5261_, 1);
if (lean_obj_tag(v_a_5262_) == 1)
{
lean_object* v_val_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v_val_5263_ = lean_ctor_get(v_a_5262_, 0);
lean_inc(v_val_5263_);
lean_dec_ref_known(v_a_5262_, 1);
lean_inc(v___x_5257_);
v___x_5264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5257_);
lean_ctor_set(v___x_5264_, 1, v_val_5263_);
v___x_5265_ = lean_array_push(v_b_5245_, v___x_5264_);
v_a_5252_ = v___x_5265_;
goto v___jp_5251_;
}
else
{
lean_dec(v_a_5262_);
v_a_5252_ = v_b_5245_;
goto v___jp_5251_;
}
}
else
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5273_; 
lean_dec_ref(v_b_5245_);
v_a_5266_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5268_ = v___x_5261_;
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5261_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
else
{
lean_dec(v___x_5259_);
v_a_5252_ = v_b_5245_;
goto v___jp_5251_;
}
}
else
{
lean_object* v___x_5274_; 
v___x_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5274_, 0, v_b_5245_);
return v___x_5274_;
}
v___jp_5251_:
{
size_t v___x_5253_; size_t v___x_5254_; 
v___x_5253_ = ((size_t)1ULL);
v___x_5254_ = lean_usize_add(v_i_5243_, v___x_5253_);
v_i_5243_ = v___x_5254_;
v_b_5245_ = v_a_5252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4___boxed(lean_object* v_assignment_5275_, lean_object* v_as_5276_, lean_object* v_i_5277_, lean_object* v_stop_5278_, lean_object* v_b_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
size_t v_i_boxed_5285_; size_t v_stop_boxed_5286_; lean_object* v_res_5287_; 
v_i_boxed_5285_ = lean_unbox_usize(v_i_5277_);
lean_dec(v_i_5277_);
v_stop_boxed_5286_ = lean_unbox_usize(v_stop_5278_);
lean_dec(v_stop_5278_);
v_res_5287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5275_, v_as_5276_, v_i_boxed_5285_, v_stop_boxed_5286_, v_b_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec_ref(v_as_5276_);
lean_dec_ref(v_assignment_5275_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_assignment_5290_, lean_object* v_as_5291_, lean_object* v_start_5292_, lean_object* v_stop_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v___x_5299_; uint8_t v___x_5300_; 
v___x_5299_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___closed__0));
v___x_5300_ = lean_nat_dec_lt(v_start_5292_, v_stop_5293_);
if (v___x_5300_ == 0)
{
lean_object* v___x_5301_; 
v___x_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5301_, 0, v___x_5299_);
return v___x_5301_;
}
else
{
lean_object* v___x_5302_; uint8_t v___x_5303_; 
v___x_5302_ = lean_array_get_size(v_as_5291_);
v___x_5303_ = lean_nat_dec_le(v_stop_5293_, v___x_5302_);
if (v___x_5303_ == 0)
{
uint8_t v___x_5304_; 
v___x_5304_ = lean_nat_dec_lt(v_start_5292_, v___x_5302_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; 
v___x_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5299_);
return v___x_5305_;
}
else
{
size_t v___x_5306_; size_t v___x_5307_; lean_object* v___x_5308_; 
v___x_5306_ = lean_usize_of_nat(v_start_5292_);
v___x_5307_ = lean_usize_of_nat(v___x_5302_);
v___x_5308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5290_, v_as_5291_, v___x_5306_, v___x_5307_, v___x_5299_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
return v___x_5308_;
}
}
else
{
size_t v___x_5309_; size_t v___x_5310_; lean_object* v___x_5311_; 
v___x_5309_ = lean_usize_of_nat(v_start_5292_);
v___x_5310_ = lean_usize_of_nat(v_stop_5293_);
v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3_spec__4(v_assignment_5290_, v_as_5291_, v___x_5309_, v___x_5310_, v___x_5299_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
return v___x_5311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_assignment_5312_, lean_object* v_as_5313_, lean_object* v_start_5314_, lean_object* v_stop_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5312_, v_as_5313_, v_start_5314_, v_stop_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v_stop_5315_);
lean_dec(v_start_5314_);
lean_dec_ref(v_as_5313_);
lean_dec_ref(v_assignment_5312_);
return v_res_5321_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; 
v___x_5324_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5325_ = lean_unsigned_to_nat(9u);
v___x_5326_ = lean_unsigned_to_nat(650u);
v___x_5327_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5328_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5329_ = l_mkPanicMessageWithDecl(v___x_5328_, v___x_5327_, v___x_5326_, v___x_5325_, v___x_5324_);
return v___x_5329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_resultType_5332_, lean_object* v_discrVal_5333_, lean_object* v_discr_5334_, lean_object* v_assignment_5335_, lean_object* v_i_5336_, lean_object* v_as_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v___x_5343_; uint8_t v___x_5344_; 
v___x_5343_ = lean_array_get_size(v_as_5337_);
v___x_5344_ = lean_nat_dec_lt(v_i_5336_, v___x_5343_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; 
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v___x_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5345_, 0, v_as_5337_);
return v___x_5345_;
}
else
{
lean_object* v_a_5346_; lean_object* v_a_5348_; 
v_a_5346_ = lean_array_fget_borrowed(v_as_5337_, v_i_5336_);
if (lean_obj_tag(v_a_5346_) == 0)
{
lean_object* v_ctorName_5359_; lean_object* v_params_5360_; lean_object* v_code_5361_; uint8_t v___x_5362_; lean_object* v___y_5364_; lean_object* v___y_5365_; lean_object* v___y_5378_; uint8_t v___x_5382_; 
v_ctorName_5359_ = lean_ctor_get(v_a_5346_, 0);
v_params_5360_ = lean_ctor_get(v_a_5346_, 1);
v_code_5361_ = lean_ctor_get(v_a_5346_, 2);
v___x_5362_ = 0;
v___x_5382_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5333_, v_ctorName_5359_);
if (v___x_5382_ == 0)
{
lean_object* v_toCold_5383_; lean_object* v_options_5384_; uint8_t v_hasTrace_5385_; 
v_toCold_5383_ = lean_ctor_get(v___y_5340_, 0);
v_options_5384_ = lean_ctor_get(v_toCold_5383_, 2);
v_hasTrace_5385_ = lean_ctor_get_uint8(v_options_5384_, sizeof(void*)*1);
if (v_hasTrace_5385_ == 0)
{
v___y_5378_ = v___y_5339_;
goto v___jp_5377_;
}
else
{
lean_object* v_inheritedTraceOptions_5386_; lean_object* v_cls_5387_; lean_object* v___x_5388_; uint8_t v___x_5389_; 
v_inheritedTraceOptions_5386_ = lean_ctor_get(v_toCold_5383_, 11);
v_cls_5387_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_5388_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_5389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5386_, v_options_5384_, v___x_5388_);
if (v___x_5389_ == 0)
{
v___y_5378_ = v___y_5339_;
goto v___jp_5377_;
}
else
{
lean_object* v___x_5390_; 
lean_inc(v_discr_5334_);
v___x_5390_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5334_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
lean_inc(v_a_5391_);
lean_dec_ref_known(v___x_5390_, 1);
v___x_5392_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__0));
v___x_5393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5391_, v___x_5389_);
v___x_5394_ = lean_string_append(v___x_5392_, v___x_5393_);
lean_dec_ref(v___x_5393_);
v___x_5395_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___closed__1));
v___x_5396_ = lean_string_append(v___x_5394_, v___x_5395_);
lean_inc(v_ctorName_5359_);
v___x_5397_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5359_, v___x_5389_);
v___x_5398_ = lean_string_append(v___x_5396_, v___x_5397_);
lean_dec_ref(v___x_5397_);
v___x_5399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5399_, 0, v___x_5398_);
v___x_5400_ = l_Lean_MessageData_ofFormat(v___x_5399_);
v___x_5401_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5387_, v___x_5400_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_dec_ref_known(v___x_5401_, 1);
v___y_5378_ = v___y_5339_;
goto v___jp_5377_;
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5401_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5401_);
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
else
{
lean_object* v_a_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5417_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5410_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5417_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5417_ == 0)
{
v___x_5412_ = v___x_5390_;
v_isShared_5413_ = v_isSharedCheck_5417_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_a_5410_);
lean_dec(v___x_5390_);
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
}
}
else
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5418_ = lean_unsigned_to_nat(0u);
v___x_5419_ = lean_array_get_size(v_params_5360_);
v___x_5420_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_assignment_5335_, v_params_5360_, v___x_5418_, v___x_5419_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; lean_object* v___x_5434_; uint8_t v___x_5435_; lean_object* v_fst_5437_; lean_object* v_snd_5438_; lean_object* v___y_5451_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref_known(v___x_5420_, 1);
v___x_5434_ = lean_array_get_size(v_a_5421_);
v___x_5435_ = lean_nat_dec_eq(v___x_5434_, v___x_5418_);
if (v___x_5435_ == 0)
{
if (v___x_5382_ == 0)
{
lean_dec(v_a_5421_);
goto v___jp_5422_;
}
else
{
lean_object* v___x_5463_; 
lean_inc_ref(v_code_5361_);
v___x_5463_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5335_, v_code_5361_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___x_5465_; uint8_t v___x_5466_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
lean_dec_ref_known(v___x_5463_, 1);
v___x_5465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5466_ = lean_nat_dec_lt(v___x_5418_, v___x_5434_);
if (v___x_5466_ == 0)
{
lean_dec(v_a_5421_);
v_fst_5437_ = v_a_5464_;
v_snd_5438_ = v___x_5465_;
goto v___jp_5436_;
}
else
{
lean_object* v___x_5467_; uint8_t v___x_5468_; 
lean_inc(v_a_5464_);
v___x_5467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5467_, 0, v_a_5464_);
lean_ctor_set(v___x_5467_, 1, v___x_5465_);
v___x_5468_ = lean_nat_dec_le(v___x_5434_, v___x_5434_);
if (v___x_5468_ == 0)
{
if (v___x_5466_ == 0)
{
lean_dec_ref_known(v___x_5467_, 2);
lean_dec(v_a_5421_);
v_fst_5437_ = v_a_5464_;
v_snd_5438_ = v___x_5465_;
goto v___jp_5436_;
}
else
{
size_t v___x_5469_; size_t v___x_5470_; lean_object* v___x_5471_; 
lean_dec(v_a_5464_);
v___x_5469_ = ((size_t)0ULL);
v___x_5470_ = lean_usize_of_nat(v___x_5434_);
v___x_5471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5421_, v___x_5469_, v___x_5470_, v___x_5467_);
lean_dec(v_a_5421_);
v___y_5451_ = v___x_5471_;
goto v___jp_5450_;
}
}
else
{
size_t v___x_5472_; size_t v___x_5473_; lean_object* v___x_5474_; 
lean_dec(v_a_5464_);
v___x_5472_ = ((size_t)0ULL);
v___x_5473_ = lean_usize_of_nat(v___x_5434_);
v___x_5474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_a_5421_, v___x_5472_, v___x_5473_, v___x_5467_);
lean_dec(v_a_5421_);
v___y_5451_ = v___x_5474_;
goto v___jp_5450_;
}
}
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_dec(v_a_5421_);
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5475_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5463_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5463_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
}
}
else
{
lean_dec(v_a_5421_);
goto v___jp_5422_;
}
v___jp_5422_:
{
lean_object* v___x_5423_; 
lean_inc_ref(v_code_5361_);
v___x_5423_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5335_, v_code_5361_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5425_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
lean_inc(v_a_5424_);
lean_dec_ref_known(v___x_5423_, 1);
lean_inc_ref(v_a_5346_);
v___x_5425_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5346_, v_a_5424_);
v_a_5348_ = v___x_5425_;
goto v___jp_5347_;
}
else
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5433_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5426_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5428_ = v___x_5423_;
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5423_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5431_; 
if (v_isShared_5429_ == 0)
{
v___x_5431_ = v___x_5428_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_a_5426_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
v___jp_5436_:
{
lean_object* v___x_5439_; 
v___x_5439_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5362_, v_fst_5437_, v_snd_5438_, v___x_5435_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
lean_dec_ref(v_snd_5438_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5441_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_a_5440_);
lean_dec_ref_known(v___x_5439_, 1);
lean_inc_ref(v_a_5346_);
v___x_5441_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5346_, v_a_5440_);
v_a_5348_ = v___x_5441_;
goto v___jp_5347_;
}
else
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5442_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5444_ = v___x_5439_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5439_);
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
v___jp_5450_:
{
if (lean_obj_tag(v___y_5451_) == 0)
{
lean_object* v_a_5452_; lean_object* v_fst_5453_; lean_object* v_snd_5454_; 
v_a_5452_ = lean_ctor_get(v___y_5451_, 0);
lean_inc(v_a_5452_);
lean_dec_ref_known(v___y_5451_, 1);
v_fst_5453_ = lean_ctor_get(v_a_5452_, 0);
lean_inc(v_fst_5453_);
v_snd_5454_ = lean_ctor_get(v_a_5452_, 1);
lean_inc(v_snd_5454_);
lean_dec(v_a_5452_);
v_fst_5437_ = v_fst_5453_;
v_snd_5438_ = v_snd_5454_;
goto v___jp_5436_;
}
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5455_ = lean_ctor_get(v___y_5451_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___y_5451_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___y_5451_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___y_5451_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
}
else
{
lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5483_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5420_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_dec(v___x_5420_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
v___jp_5363_:
{
lean_object* v___x_5366_; 
v___x_5366_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5362_, v___y_5365_, v___y_5364_);
lean_dec_ref(v___y_5365_);
if (lean_obj_tag(v___x_5366_) == 0)
{
lean_object* v___x_5367_; lean_object* v___x_5368_; 
lean_dec_ref_known(v___x_5366_, 1);
lean_inc_ref(v_resultType_5332_);
v___x_5367_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5367_, 0, v_resultType_5332_);
lean_inc_ref(v_a_5346_);
v___x_5368_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5346_, v___x_5367_);
v_a_5348_ = v___x_5368_;
goto v___jp_5347_;
}
else
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5369_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v___x_5366_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5366_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
v___jp_5377_:
{
switch(lean_obj_tag(v_a_5346_))
{
case 0:
{
lean_object* v_code_5379_; 
v_code_5379_ = lean_ctor_get(v_a_5346_, 2);
lean_inc_ref(v_code_5379_);
v___y_5364_ = v___y_5378_;
v___y_5365_ = v_code_5379_;
goto v___jp_5363_;
}
case 1:
{
lean_object* v_code_5380_; 
v_code_5380_ = lean_ctor_get(v_a_5346_, 1);
lean_inc_ref(v_code_5380_);
v___y_5364_ = v___y_5378_;
v___y_5365_ = v_code_5380_;
goto v___jp_5363_;
}
default: 
{
lean_object* v_code_5381_; 
v_code_5381_ = lean_ctor_get(v_a_5346_, 0);
lean_inc_ref(v_code_5381_);
v___y_5364_ = v___y_5378_;
v___y_5365_ = v_code_5381_;
goto v___jp_5363_;
}
}
}
}
else
{
lean_object* v_code_5491_; lean_object* v___x_5492_; 
v_code_5491_ = lean_ctor_get(v_a_5346_, 0);
lean_inc_ref(v_code_5491_);
v___x_5492_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5335_, v_code_5491_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5494_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref_known(v___x_5492_, 1);
lean_inc_ref(v_a_5346_);
v___x_5494_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5346_, v_a_5493_);
v_a_5348_ = v___x_5494_;
goto v___jp_5347_;
}
else
{
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5502_; 
lean_dec_ref(v_as_5337_);
lean_dec(v_i_5336_);
lean_dec(v_discr_5334_);
lean_dec_ref(v_resultType_5332_);
v_a_5495_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5502_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5502_ == 0)
{
v___x_5497_ = v___x_5492_;
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v___x_5492_);
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
v___jp_5347_:
{
size_t v___x_5349_; size_t v___x_5350_; uint8_t v___x_5351_; 
v___x_5349_ = lean_ptr_addr(v_a_5346_);
v___x_5350_ = lean_ptr_addr(v_a_5348_);
v___x_5351_ = lean_usize_dec_eq(v___x_5349_, v___x_5350_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; 
v___x_5352_ = lean_unsigned_to_nat(1u);
v___x_5353_ = lean_nat_add(v_i_5336_, v___x_5352_);
v___x_5354_ = lean_array_fset(v_as_5337_, v_i_5336_, v_a_5348_);
lean_dec(v_i_5336_);
v_i_5336_ = v___x_5353_;
v_as_5337_ = v___x_5354_;
goto _start;
}
else
{
lean_object* v___x_5356_; lean_object* v___x_5357_; 
lean_dec_ref(v_a_5348_);
v___x_5356_ = lean_unsigned_to_nat(1u);
v___x_5357_ = lean_nat_add(v_i_5336_, v___x_5356_);
lean_dec(v_i_5336_);
v_i_5336_ = v___x_5357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5503_, lean_object* v_code_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_){
_start:
{
lean_object* v_decl_5511_; lean_object* v_k_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; 
switch(lean_obj_tag(v_code_5504_))
{
case 0:
{
lean_object* v_decl_5624_; lean_object* v_k_5625_; lean_object* v___x_5626_; 
v_decl_5624_ = lean_ctor_get(v_code_5504_, 0);
v_k_5625_ = lean_ctor_get(v_code_5504_, 1);
lean_inc_ref(v_k_5625_);
v___x_5626_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5503_, v_k_5625_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
if (lean_obj_tag(v___x_5626_) == 0)
{
lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5663_; 
v_a_5627_ = lean_ctor_get(v___x_5626_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5629_ = v___x_5626_;
v_isShared_5630_ = v_isSharedCheck_5663_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_dec(v___x_5626_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5663_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
size_t v___x_5631_; size_t v___x_5632_; uint8_t v___x_5633_; 
v___x_5631_ = lean_ptr_addr(v_k_5625_);
v___x_5632_ = lean_ptr_addr(v_a_5627_);
v___x_5633_ = lean_usize_dec_eq(v___x_5631_, v___x_5632_);
if (v___x_5633_ == 0)
{
lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5643_; 
lean_inc_ref(v_decl_5624_);
v_isSharedCheck_5643_ = !lean_is_exclusive(v_code_5504_);
if (v_isSharedCheck_5643_ == 0)
{
lean_object* v_unused_5644_; lean_object* v_unused_5645_; 
v_unused_5644_ = lean_ctor_get(v_code_5504_, 1);
lean_dec(v_unused_5644_);
v_unused_5645_ = lean_ctor_get(v_code_5504_, 0);
lean_dec(v_unused_5645_);
v___x_5635_ = v_code_5504_;
v_isShared_5636_ = v_isSharedCheck_5643_;
goto v_resetjp_5634_;
}
else
{
lean_dec(v_code_5504_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5643_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v___x_5638_; 
if (v_isShared_5636_ == 0)
{
lean_ctor_set(v___x_5635_, 1, v_a_5627_);
v___x_5638_ = v___x_5635_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_decl_5624_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v_a_5627_);
v___x_5638_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
lean_object* v___x_5640_; 
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 0, v___x_5638_);
v___x_5640_ = v___x_5629_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v___x_5638_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
}
else
{
size_t v___x_5646_; uint8_t v___x_5647_; 
v___x_5646_ = lean_ptr_addr(v_decl_5624_);
v___x_5647_ = lean_usize_dec_eq(v___x_5646_, v___x_5646_);
if (v___x_5647_ == 0)
{
lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5657_; 
lean_inc_ref(v_decl_5624_);
v_isSharedCheck_5657_ = !lean_is_exclusive(v_code_5504_);
if (v_isSharedCheck_5657_ == 0)
{
lean_object* v_unused_5658_; lean_object* v_unused_5659_; 
v_unused_5658_ = lean_ctor_get(v_code_5504_, 1);
lean_dec(v_unused_5658_);
v_unused_5659_ = lean_ctor_get(v_code_5504_, 0);
lean_dec(v_unused_5659_);
v___x_5649_ = v_code_5504_;
v_isShared_5650_ = v_isSharedCheck_5657_;
goto v_resetjp_5648_;
}
else
{
lean_dec(v_code_5504_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5657_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5652_; 
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 1, v_a_5627_);
v___x_5652_ = v___x_5649_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_decl_5624_);
lean_ctor_set(v_reuseFailAlloc_5656_, 1, v_a_5627_);
v___x_5652_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
lean_object* v___x_5654_; 
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 0, v___x_5652_);
v___x_5654_ = v___x_5629_;
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
else
{
lean_object* v___x_5661_; 
lean_dec(v_a_5627_);
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 0, v_code_5504_);
v___x_5661_ = v___x_5629_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_code_5504_);
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
else
{
lean_dec_ref_known(v_code_5504_, 2);
return v___x_5626_;
}
}
case 1:
{
lean_object* v_decl_5664_; lean_object* v_k_5665_; 
v_decl_5664_ = lean_ctor_get(v_code_5504_, 0);
v_k_5665_ = lean_ctor_get(v_code_5504_, 1);
lean_inc_ref(v_k_5665_);
lean_inc_ref(v_decl_5664_);
v_decl_5511_ = v_decl_5664_;
v_k_5512_ = v_k_5665_;
v___y_5513_ = v_a_5505_;
v___y_5514_ = v_a_5506_;
v___y_5515_ = v_a_5507_;
v___y_5516_ = v_a_5508_;
goto v___jp_5510_;
}
case 2:
{
lean_object* v_decl_5666_; lean_object* v_k_5667_; 
v_decl_5666_ = lean_ctor_get(v_code_5504_, 0);
v_k_5667_ = lean_ctor_get(v_code_5504_, 1);
lean_inc_ref(v_k_5667_);
lean_inc_ref(v_decl_5666_);
v_decl_5511_ = v_decl_5666_;
v_k_5512_ = v_k_5667_;
v___y_5513_ = v_a_5505_;
v___y_5514_ = v_a_5506_;
v___y_5515_ = v_a_5507_;
v___y_5516_ = v_a_5508_;
goto v___jp_5510_;
}
case 4:
{
lean_object* v_cases_5668_; lean_object* v_typeName_5669_; lean_object* v_resultType_5670_; lean_object* v_discr_5671_; lean_object* v_alts_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5713_; 
v_cases_5668_ = lean_ctor_get(v_code_5504_, 0);
lean_inc_ref(v_cases_5668_);
v_typeName_5669_ = lean_ctor_get(v_cases_5668_, 0);
v_resultType_5670_ = lean_ctor_get(v_cases_5668_, 1);
v_discr_5671_ = lean_ctor_get(v_cases_5668_, 2);
v_alts_5672_ = lean_ctor_get(v_cases_5668_, 3);
v_isSharedCheck_5713_ = !lean_is_exclusive(v_cases_5668_);
if (v_isSharedCheck_5713_ == 0)
{
v___x_5674_ = v_cases_5668_;
v_isShared_5675_ = v_isSharedCheck_5713_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_alts_5672_);
lean_inc(v_discr_5671_);
lean_inc(v_resultType_5670_);
lean_inc(v_typeName_5669_);
lean_dec(v_cases_5668_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5713_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5676_; lean_object* v_discrVal_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5676_ = lean_box(0);
v_discrVal_5677_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5503_, v_discr_5671_, v___x_5676_);
v___x_5678_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5672_);
lean_inc(v_discr_5671_);
lean_inc_ref(v_resultType_5670_);
v___x_5679_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5670_, v_discrVal_5677_, v_discr_5671_, v_assignment_5503_, v___x_5678_, v_alts_5672_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
lean_dec(v_discrVal_5677_);
if (lean_obj_tag(v___x_5679_) == 0)
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5704_; 
v_a_5680_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5682_ = v___x_5679_;
v_isShared_5683_ = v_isSharedCheck_5704_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5679_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5704_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
size_t v___x_5684_; size_t v___x_5685_; uint8_t v___x_5686_; 
v___x_5684_ = lean_ptr_addr(v_alts_5672_);
lean_dec_ref(v_alts_5672_);
v___x_5685_ = lean_ptr_addr(v_a_5680_);
v___x_5686_ = lean_usize_dec_eq(v___x_5684_, v___x_5685_);
if (v___x_5686_ == 0)
{
lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5699_; 
v_isSharedCheck_5699_ = !lean_is_exclusive(v_code_5504_);
if (v_isSharedCheck_5699_ == 0)
{
lean_object* v_unused_5700_; 
v_unused_5700_ = lean_ctor_get(v_code_5504_, 0);
lean_dec(v_unused_5700_);
v___x_5688_ = v_code_5504_;
v_isShared_5689_ = v_isSharedCheck_5699_;
goto v_resetjp_5687_;
}
else
{
lean_dec(v_code_5504_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5699_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5691_; 
if (v_isShared_5675_ == 0)
{
lean_ctor_set(v___x_5674_, 3, v_a_5680_);
v___x_5691_ = v___x_5674_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_typeName_5669_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v_resultType_5670_);
lean_ctor_set(v_reuseFailAlloc_5698_, 2, v_discr_5671_);
lean_ctor_set(v_reuseFailAlloc_5698_, 3, v_a_5680_);
v___x_5691_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
lean_object* v___x_5693_; 
if (v_isShared_5689_ == 0)
{
lean_ctor_set(v___x_5688_, 0, v___x_5691_);
v___x_5693_ = v___x_5688_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v___x_5691_);
v___x_5693_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
lean_object* v___x_5695_; 
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 0, v___x_5693_);
v___x_5695_ = v___x_5682_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5693_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
}
else
{
lean_object* v___x_5702_; 
lean_dec(v_a_5680_);
lean_del_object(v___x_5674_);
lean_dec(v_discr_5671_);
lean_dec_ref(v_resultType_5670_);
lean_dec(v_typeName_5669_);
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 0, v_code_5504_);
v___x_5702_ = v___x_5682_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_code_5504_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
else
{
lean_object* v_a_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5712_; 
lean_del_object(v___x_5674_);
lean_dec_ref(v_alts_5672_);
lean_dec(v_discr_5671_);
lean_dec_ref(v_resultType_5670_);
lean_dec(v_typeName_5669_);
lean_dec_ref_known(v_code_5504_, 1);
v_a_5705_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5712_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5712_ == 0)
{
v___x_5707_ = v___x_5679_;
v_isShared_5708_ = v_isSharedCheck_5712_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_a_5705_);
lean_dec(v___x_5679_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5712_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
lean_object* v___x_5710_; 
if (v_isShared_5708_ == 0)
{
v___x_5710_ = v___x_5707_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v_a_5705_);
v___x_5710_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
return v___x_5710_;
}
}
}
}
}
default: 
{
lean_object* v___x_5714_; 
v___x_5714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5714_, 0, v_code_5504_);
return v___x_5714_;
}
}
v___jp_5510_:
{
lean_object* v_params_5517_; lean_object* v_type_5518_; lean_object* v_value_5519_; uint8_t v___x_5520_; lean_object* v___x_5521_; 
v_params_5517_ = lean_ctor_get(v_decl_5511_, 2);
lean_inc_ref(v_params_5517_);
v_type_5518_ = lean_ctor_get(v_decl_5511_, 3);
lean_inc_ref(v_type_5518_);
v_value_5519_ = lean_ctor_get(v_decl_5511_, 4);
v___x_5520_ = 0;
lean_inc_ref(v_value_5519_);
v___x_5521_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5503_, v_value_5519_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_object* v_a_5522_; lean_object* v___x_5523_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc(v_a_5522_);
lean_dec_ref_known(v___x_5521_, 1);
v___x_5523_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5520_, v_decl_5511_, v_type_5518_, v_params_5517_, v_a_5522_, v___y_5514_);
if (lean_obj_tag(v___x_5523_) == 0)
{
lean_object* v_a_5524_; lean_object* v___x_5525_; 
v_a_5524_ = lean_ctor_get(v___x_5523_, 0);
lean_inc(v_a_5524_);
lean_dec_ref_known(v___x_5523_, 1);
v___x_5525_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5503_, v_k_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
if (lean_obj_tag(v___x_5525_) == 0)
{
switch(lean_obj_tag(v_code_5504_))
{
case 1:
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5565_; 
v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5565_ == 0)
{
v___x_5528_ = v___x_5525_;
v_isShared_5529_ = v_isSharedCheck_5565_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5525_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5565_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v_decl_5530_; lean_object* v_k_5531_; size_t v___x_5532_; size_t v___x_5533_; uint8_t v___x_5534_; 
v_decl_5530_ = lean_ctor_get(v_code_5504_, 0);
v_k_5531_ = lean_ctor_get(v_code_5504_, 1);
v___x_5532_ = lean_ptr_addr(v_k_5531_);
v___x_5533_ = lean_ptr_addr(v_a_5526_);
v___x_5534_ = lean_usize_dec_eq(v___x_5532_, v___x_5533_);
if (v___x_5534_ == 0)
{
lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5544_; 
v_isSharedCheck_5544_ = !lean_is_exclusive(v_code_5504_);
if (v_isSharedCheck_5544_ == 0)
{
lean_object* v_unused_5545_; lean_object* v_unused_5546_; 
v_unused_5545_ = lean_ctor_get(v_code_5504_, 1);
lean_dec(v_unused_5545_);
v_unused_5546_ = lean_ctor_get(v_code_5504_, 0);
lean_dec(v_unused_5546_);
v___x_5536_ = v_code_5504_;
v_isShared_5537_ = v_isSharedCheck_5544_;
goto v_resetjp_5535_;
}
else
{
lean_dec(v_code_5504_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5544_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5539_; 
if (v_isShared_5537_ == 0)
{
lean_ctor_set(v___x_5536_, 1, v_a_5526_);
lean_ctor_set(v___x_5536_, 0, v_a_5524_);
v___x_5539_ = v___x_5536_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_a_5524_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v_a_5526_);
v___x_5539_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5541_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 0, v___x_5539_);
v___x_5541_ = v___x_5528_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v___x_5539_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
else
{
size_t v___x_5547_; size_t v___x_5548_; uint8_t v___x_5549_; 
v___x_5547_ = lean_ptr_addr(v_decl_5530_);
v___x_5548_ = lean_ptr_addr(v_a_5524_);
v___x_5549_ = lean_usize_dec_eq(v___x_5547_, v___x_5548_);
if (v___x_5549_ == 0)
{
lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5559_; 
v_isSharedCheck_5559_ = !lean_is_exclusive(v_code_5504_);
if (v_isSharedCheck_5559_ == 0)
{
lean_object* v_unused_5560_; lean_object* v_unused_5561_; 
v_unused_5560_ = lean_ctor_get(v_code_5504_, 1);
lean_dec(v_unused_5560_);
v_unused_5561_ = lean_ctor_get(v_code_5504_, 0);
lean_dec(v_unused_5561_);
v___x_5551_ = v_code_5504_;
v_isShared_5552_ = v_isSharedCheck_5559_;
goto v_resetjp_5550_;
}
else
{
lean_dec(v_code_5504_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5559_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 1, v_a_5526_);
lean_ctor_set(v___x_5551_, 0, v_a_5524_);
v___x_5554_ = v___x_5551_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5524_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v_a_5526_);
v___x_5554_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5556_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 0, v___x_5554_);
v___x_5556_ = v___x_5528_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
else
{
lean_object* v___x_5563_; 
lean_dec(v_a_5526_);
lean_dec(v_a_5524_);
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 0, v_code_5504_);
v___x_5563_ = v___x_5528_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_code_5504_);
v___x_5563_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
return v___x_5563_;
}
}
}
}
}
case 2:
{
lean_object* v_a_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5605_; 
v_a_5566_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5568_ = v___x_5525_;
v_isShared_5569_ = v_isSharedCheck_5605_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_a_5566_);
lean_dec(v___x_5525_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5605_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v_decl_5570_; lean_object* v_k_5571_; size_t v___x_5572_; size_t v___x_5573_; uint8_t v___x_5574_; 
v_decl_5570_ = lean_ctor_get(v_code_5504_, 0);
v_k_5571_ = lean_ctor_get(v_code_5504_, 1);
v___x_5572_ = lean_ptr_addr(v_k_5571_);
v___x_5573_ = lean_ptr_addr(v_a_5566_);
v___x_5574_ = lean_usize_dec_eq(v___x_5572_, v___x_5573_);
if (v___x_5574_ == 0)
{
lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5584_; 
v_isSharedCheck_5584_ = !lean_is_exclusive(v_code_5504_);
if (v_isSharedCheck_5584_ == 0)
{
lean_object* v_unused_5585_; lean_object* v_unused_5586_; 
v_unused_5585_ = lean_ctor_get(v_code_5504_, 1);
lean_dec(v_unused_5585_);
v_unused_5586_ = lean_ctor_get(v_code_5504_, 0);
lean_dec(v_unused_5586_);
v___x_5576_ = v_code_5504_;
v_isShared_5577_ = v_isSharedCheck_5584_;
goto v_resetjp_5575_;
}
else
{
lean_dec(v_code_5504_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5584_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
lean_ctor_set(v___x_5576_, 1, v_a_5566_);
lean_ctor_set(v___x_5576_, 0, v_a_5524_);
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5524_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v_a_5566_);
v___x_5579_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5581_; 
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 0, v___x_5579_);
v___x_5581_ = v___x_5568_;
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
else
{
size_t v___x_5587_; size_t v___x_5588_; uint8_t v___x_5589_; 
v___x_5587_ = lean_ptr_addr(v_decl_5570_);
v___x_5588_ = lean_ptr_addr(v_a_5524_);
v___x_5589_ = lean_usize_dec_eq(v___x_5587_, v___x_5588_);
if (v___x_5589_ == 0)
{
lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5599_; 
v_isSharedCheck_5599_ = !lean_is_exclusive(v_code_5504_);
if (v_isSharedCheck_5599_ == 0)
{
lean_object* v_unused_5600_; lean_object* v_unused_5601_; 
v_unused_5600_ = lean_ctor_get(v_code_5504_, 1);
lean_dec(v_unused_5600_);
v_unused_5601_ = lean_ctor_get(v_code_5504_, 0);
lean_dec(v_unused_5601_);
v___x_5591_ = v_code_5504_;
v_isShared_5592_ = v_isSharedCheck_5599_;
goto v_resetjp_5590_;
}
else
{
lean_dec(v_code_5504_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5599_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5594_; 
if (v_isShared_5592_ == 0)
{
lean_ctor_set(v___x_5591_, 1, v_a_5566_);
lean_ctor_set(v___x_5591_, 0, v_a_5524_);
v___x_5594_ = v___x_5591_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5524_);
lean_ctor_set(v_reuseFailAlloc_5598_, 1, v_a_5566_);
v___x_5594_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
lean_object* v___x_5596_; 
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 0, v___x_5594_);
v___x_5596_ = v___x_5568_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v___x_5594_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
return v___x_5596_;
}
}
}
}
else
{
lean_object* v___x_5603_; 
lean_dec(v_a_5566_);
lean_dec(v_a_5524_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 0, v_code_5504_);
v___x_5603_ = v___x_5568_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_code_5504_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
}
}
}
default: 
{
lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5614_; 
lean_dec(v_a_5524_);
lean_dec_ref(v_code_5504_);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v___x_5525_, 0);
lean_dec(v_unused_5615_);
v___x_5607_ = v___x_5525_;
v_isShared_5608_ = v_isSharedCheck_5614_;
goto v_resetjp_5606_;
}
else
{
lean_dec(v___x_5525_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5614_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5612_; 
v___x_5609_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5610_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5609_);
if (v_isShared_5608_ == 0)
{
lean_ctor_set(v___x_5607_, 0, v___x_5610_);
v___x_5612_ = v___x_5607_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5610_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
}
else
{
lean_dec(v_a_5524_);
lean_dec_ref(v_code_5504_);
return v___x_5525_;
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec_ref(v_k_5512_);
lean_dec_ref(v_code_5504_);
v_a_5616_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5523_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5523_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
else
{
lean_dec_ref(v_type_5518_);
lean_dec_ref(v_params_5517_);
lean_dec_ref(v_k_5512_);
lean_dec_ref(v_decl_5511_);
lean_dec_ref(v_code_5504_);
return v___x_5521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5715_, lean_object* v_code_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_){
_start:
{
lean_object* v_res_5722_; 
v_res_5722_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5715_, v_code_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_);
lean_dec(v_a_5720_);
lean_dec_ref(v_a_5719_);
lean_dec(v_a_5718_);
lean_dec_ref(v_a_5717_);
lean_dec_ref(v_assignment_5715_);
return v_res_5722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_resultType_5723_, lean_object* v_discrVal_5724_, lean_object* v_discr_5725_, lean_object* v_assignment_5726_, lean_object* v_i_5727_, lean_object* v_as_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_resultType_5723_, v_discrVal_5724_, v_discr_5725_, v_assignment_5726_, v_i_5727_, v_as_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_);
lean_dec(v___y_5732_);
lean_dec_ref(v___y_5731_);
lean_dec(v___y_5730_);
lean_dec_ref(v___y_5729_);
lean_dec_ref(v_assignment_5726_);
lean_dec(v_discrVal_5724_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5735_, lean_object* v_m_5736_, lean_object* v_a_5737_){
_start:
{
lean_object* v___x_5738_; 
v___x_5738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5736_, v_a_5737_);
return v___x_5738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5739_, lean_object* v_m_5740_, lean_object* v_a_5741_){
_start:
{
lean_object* v_res_5742_; 
v_res_5742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5739_, v_m_5740_, v_a_5741_);
lean_dec(v_a_5741_);
lean_dec_ref(v_m_5740_);
return v_res_5742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_as_5743_, size_t v_i_5744_, size_t v_stop_5745_, lean_object* v_b_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_){
_start:
{
lean_object* v___x_5752_; 
v___x_5752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___redArg(v_as_5743_, v_i_5744_, v_stop_5745_, v_b_5746_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_as_5753_, lean_object* v_i_5754_, lean_object* v_stop_5755_, lean_object* v_b_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_){
_start:
{
size_t v_i_boxed_5762_; size_t v_stop_boxed_5763_; lean_object* v_res_5764_; 
v_i_boxed_5762_ = lean_unbox_usize(v_i_5754_);
lean_dec(v_i_5754_);
v_stop_boxed_5763_ = lean_unbox_usize(v_stop_5755_);
lean_dec(v_stop_5755_);
v_res_5764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_as_5753_, v_i_boxed_5762_, v_stop_boxed_5763_, v_b_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec_ref(v_as_5753_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5765_, lean_object* v_a_5766_, lean_object* v_x_5767_){
_start:
{
lean_object* v___x_5768_; 
v___x_5768_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5766_, v_x_5767_);
return v___x_5768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5769_, lean_object* v_a_5770_, lean_object* v_x_5771_){
_start:
{
lean_object* v_res_5772_; 
v_res_5772_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5769_, v_a_5770_, v_x_5771_);
lean_dec(v_x_5771_);
lean_dec(v_a_5770_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5773_, lean_object* v_v_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_){
_start:
{
if (lean_obj_tag(v_v_5774_) == 0)
{
lean_object* v_code_5780_; lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5804_; 
v_code_5780_ = lean_ctor_get(v_v_5774_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v_v_5774_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5782_ = v_v_5774_;
v_isShared_5783_ = v_isSharedCheck_5804_;
goto v_resetjp_5781_;
}
else
{
lean_inc(v_code_5780_);
lean_dec(v_v_5774_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5804_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
lean_object* v___x_5784_; 
lean_inc(v___y_5778_);
lean_inc_ref(v___y_5777_);
lean_inc(v___y_5776_);
lean_inc_ref(v___y_5775_);
v___x_5784_ = lean_apply_6(v_f_5773_, v_code_5780_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, lean_box(0));
if (lean_obj_tag(v___x_5784_) == 0)
{
lean_object* v_a_5785_; lean_object* v___x_5787_; uint8_t v_isShared_5788_; uint8_t v_isSharedCheck_5795_; 
v_a_5785_ = lean_ctor_get(v___x_5784_, 0);
v_isSharedCheck_5795_ = !lean_is_exclusive(v___x_5784_);
if (v_isSharedCheck_5795_ == 0)
{
v___x_5787_ = v___x_5784_;
v_isShared_5788_ = v_isSharedCheck_5795_;
goto v_resetjp_5786_;
}
else
{
lean_inc(v_a_5785_);
lean_dec(v___x_5784_);
v___x_5787_ = lean_box(0);
v_isShared_5788_ = v_isSharedCheck_5795_;
goto v_resetjp_5786_;
}
v_resetjp_5786_:
{
lean_object* v___x_5790_; 
if (v_isShared_5783_ == 0)
{
lean_ctor_set(v___x_5782_, 0, v_a_5785_);
v___x_5790_ = v___x_5782_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_a_5785_);
v___x_5790_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
lean_object* v___x_5792_; 
if (v_isShared_5788_ == 0)
{
lean_ctor_set(v___x_5787_, 0, v___x_5790_);
v___x_5792_ = v___x_5787_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v___x_5790_);
v___x_5792_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
return v___x_5792_;
}
}
}
}
else
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5803_; 
lean_del_object(v___x_5782_);
v_a_5796_ = lean_ctor_get(v___x_5784_, 0);
v_isSharedCheck_5803_ = !lean_is_exclusive(v___x_5784_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5798_ = v___x_5784_;
v_isShared_5799_ = v_isSharedCheck_5803_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5784_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5803_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v___x_5801_; 
if (v_isShared_5799_ == 0)
{
v___x_5801_ = v___x_5798_;
goto v_reusejp_5800_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_a_5796_);
v___x_5801_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5800_;
}
v_reusejp_5800_:
{
return v___x_5801_;
}
}
}
}
}
else
{
lean_object* v___x_5805_; 
lean_dec_ref(v_f_5773_);
v___x_5805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5805_, 0, v_v_5774_);
return v___x_5805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5806_, lean_object* v_v_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_){
_start:
{
lean_object* v_res_5813_; 
v_res_5813_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5806_, v_v_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5808_);
return v_res_5813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5814_, lean_object* v_f_5815_, lean_object* v_v_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_){
_start:
{
lean_object* v___x_5822_; 
v___x_5822_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5815_, v_v_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5823_, lean_object* v_f_5824_, lean_object* v_v_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_){
_start:
{
uint8_t v_pu_boxed_5831_; lean_object* v_res_5832_; 
v_pu_boxed_5831_ = lean_unbox(v_pu_5823_);
v_res_5832_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5831_, v_f_5824_, v_v_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_);
lean_dec(v___y_5829_);
lean_dec_ref(v___y_5828_);
lean_dec(v___y_5827_);
lean_dec_ref(v___y_5826_);
return v_res_5832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5833_, lean_object* v_x_5834_){
_start:
{
if (lean_obj_tag(v_x_5834_) == 0)
{
return v_x_5833_;
}
else
{
lean_object* v_key_5835_; lean_object* v_value_5836_; lean_object* v_tail_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
v_key_5835_ = lean_ctor_get(v_x_5834_, 0);
v_value_5836_ = lean_ctor_get(v_x_5834_, 1);
v_tail_5837_ = lean_ctor_get(v_x_5834_, 2);
lean_inc(v_value_5836_);
lean_inc(v_key_5835_);
v___x_5838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5838_, 0, v_key_5835_);
lean_ctor_set(v___x_5838_, 1, v_value_5836_);
v___x_5839_ = lean_array_push(v_x_5833_, v___x_5838_);
v_x_5833_ = v___x_5839_;
v_x_5834_ = v_tail_5837_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5841_, lean_object* v_x_5842_){
_start:
{
lean_object* v_res_5843_; 
v_res_5843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5841_, v_x_5842_);
lean_dec(v_x_5842_);
return v_res_5843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5844_, size_t v_i_5845_, size_t v_stop_5846_, lean_object* v_b_5847_){
_start:
{
uint8_t v___x_5848_; 
v___x_5848_ = lean_usize_dec_eq(v_i_5845_, v_stop_5846_);
if (v___x_5848_ == 0)
{
lean_object* v___x_5849_; lean_object* v___x_5850_; size_t v___x_5851_; size_t v___x_5852_; 
v___x_5849_ = lean_array_uget_borrowed(v_as_5844_, v_i_5845_);
v___x_5850_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5847_, v___x_5849_);
v___x_5851_ = ((size_t)1ULL);
v___x_5852_ = lean_usize_add(v_i_5845_, v___x_5851_);
v_i_5845_ = v___x_5852_;
v_b_5847_ = v___x_5850_;
goto _start;
}
else
{
return v_b_5847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5854_, lean_object* v_i_5855_, lean_object* v_stop_5856_, lean_object* v_b_5857_){
_start:
{
size_t v_i_boxed_5858_; size_t v_stop_boxed_5859_; lean_object* v_res_5860_; 
v_i_boxed_5858_ = lean_unbox_usize(v_i_5855_);
lean_dec(v_i_5855_);
v_stop_boxed_5859_ = lean_unbox_usize(v_stop_5856_);
lean_dec(v_stop_5856_);
v_res_5860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5854_, v_i_boxed_5858_, v_stop_boxed_5859_, v_b_5857_);
lean_dec_ref(v_as_5854_);
return v_res_5860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5861_, size_t v_sz_5862_, size_t v_i_5863_, lean_object* v_bs_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_){
_start:
{
uint8_t v___x_5870_; 
v___x_5870_ = lean_usize_dec_lt(v_i_5863_, v_sz_5862_);
if (v___x_5870_ == 0)
{
lean_object* v___x_5871_; 
v___x_5871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5871_, 0, v_bs_5864_);
return v___x_5871_;
}
else
{
lean_object* v_v_5872_; lean_object* v_fst_5873_; lean_object* v_snd_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5898_; 
v_v_5872_ = lean_array_uget(v_bs_5864_, v_i_5863_);
v_fst_5873_ = lean_ctor_get(v_v_5872_, 0);
v_snd_5874_ = lean_ctor_get(v_v_5872_, 1);
v_isSharedCheck_5898_ = !lean_is_exclusive(v_v_5872_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5876_ = v_v_5872_;
v_isShared_5877_ = v_isSharedCheck_5898_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_snd_5874_);
lean_inc(v_fst_5873_);
lean_dec(v_v_5872_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5898_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5878_; lean_object* v_bs_x27_5879_; lean_object* v___x_5880_; 
v___x_5878_ = lean_unsigned_to_nat(0u);
v_bs_x27_5879_ = lean_array_uset(v_bs_5864_, v_i_5863_, v___x_5878_);
v___x_5880_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5873_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_);
if (lean_obj_tag(v___x_5880_) == 0)
{
lean_object* v_a_5881_; lean_object* v___x_5882_; lean_object* v___x_5884_; 
v_a_5881_ = lean_ctor_get(v___x_5880_, 0);
lean_inc(v_a_5881_);
lean_dec_ref_known(v___x_5880_, 1);
v___x_5882_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5881_, v_a_5861_);
if (v_isShared_5877_ == 0)
{
lean_ctor_set(v___x_5876_, 0, v___x_5882_);
v___x_5884_ = v___x_5876_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v___x_5882_);
lean_ctor_set(v_reuseFailAlloc_5889_, 1, v_snd_5874_);
v___x_5884_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
size_t v___x_5885_; size_t v___x_5886_; lean_object* v___x_5887_; 
v___x_5885_ = ((size_t)1ULL);
v___x_5886_ = lean_usize_add(v_i_5863_, v___x_5885_);
v___x_5887_ = lean_array_uset(v_bs_x27_5879_, v_i_5863_, v___x_5884_);
v_i_5863_ = v___x_5886_;
v_bs_5864_ = v___x_5887_;
goto _start;
}
}
else
{
lean_object* v_a_5890_; lean_object* v___x_5892_; uint8_t v_isShared_5893_; uint8_t v_isSharedCheck_5897_; 
lean_dec_ref(v_bs_x27_5879_);
lean_del_object(v___x_5876_);
lean_dec(v_snd_5874_);
v_a_5890_ = lean_ctor_get(v___x_5880_, 0);
v_isSharedCheck_5897_ = !lean_is_exclusive(v___x_5880_);
if (v_isSharedCheck_5897_ == 0)
{
v___x_5892_ = v___x_5880_;
v_isShared_5893_ = v_isSharedCheck_5897_;
goto v_resetjp_5891_;
}
else
{
lean_inc(v_a_5890_);
lean_dec(v___x_5880_);
v___x_5892_ = lean_box(0);
v_isShared_5893_ = v_isSharedCheck_5897_;
goto v_resetjp_5891_;
}
v_resetjp_5891_:
{
lean_object* v___x_5895_; 
if (v_isShared_5893_ == 0)
{
v___x_5895_ = v___x_5892_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_a_5890_);
v___x_5895_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
return v___x_5895_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5899_, lean_object* v_sz_5900_, lean_object* v_i_5901_, lean_object* v_bs_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_){
_start:
{
uint8_t v_a_2401__boxed_5908_; size_t v_sz_boxed_5909_; size_t v_i_boxed_5910_; lean_object* v_res_5911_; 
v_a_2401__boxed_5908_ = lean_unbox(v_a_5899_);
v_sz_boxed_5909_ = lean_unbox_usize(v_sz_5900_);
lean_dec(v_sz_5900_);
v_i_boxed_5910_ = lean_unbox_usize(v_i_5901_);
lean_dec(v_i_5901_);
v_res_5911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2401__boxed_5908_, v_sz_boxed_5909_, v_i_boxed_5910_, v_bs_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
lean_dec(v___y_5906_);
lean_dec_ref(v___y_5905_);
lean_dec(v___y_5904_);
lean_dec_ref(v___y_5903_);
return v_res_5911_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5912_){
_start:
{
lean_object* v_fst_5913_; lean_object* v_snd_5914_; lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5937_; 
v_fst_5913_ = lean_ctor_get(v_x_5912_, 0);
v_snd_5914_ = lean_ctor_get(v_x_5912_, 1);
v_isSharedCheck_5937_ = !lean_is_exclusive(v_x_5912_);
if (v_isSharedCheck_5937_ == 0)
{
v___x_5916_ = v_x_5912_;
v_isShared_5917_ = v_isSharedCheck_5937_;
goto v_resetjp_5915_;
}
else
{
lean_inc(v_snd_5914_);
lean_inc(v_fst_5913_);
lean_dec(v_x_5912_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5937_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5922_; 
v___x_5918_ = l_String_quote(v_fst_5913_);
v___x_5919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
v___x_5920_ = lean_box(0);
if (v_isShared_5917_ == 0)
{
lean_ctor_set_tag(v___x_5916_, 1);
lean_ctor_set(v___x_5916_, 1, v___x_5920_);
lean_ctor_set(v___x_5916_, 0, v___x_5919_);
v___x_5922_ = v___x_5916_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v___x_5919_);
lean_ctor_set(v_reuseFailAlloc_5936_, 1, v___x_5920_);
v___x_5922_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; uint8_t v___x_5934_; lean_object* v___x_5935_; 
v___x_5923_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5914_);
v___x_5924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5923_);
lean_ctor_set(v___x_5924_, 1, v___x_5922_);
v___x_5925_ = l_List_reverse___redArg(v___x_5924_);
v___x_5926_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5927_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5925_, v___x_5926_);
v___x_5928_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5929_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
lean_ctor_set(v___x_5930_, 1, v___x_5927_);
v___x_5931_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5930_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
v___x_5933_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5928_);
lean_ctor_set(v___x_5933_, 1, v___x_5932_);
v___x_5934_ = 0;
v___x_5935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5935_, 0, v___x_5933_);
lean_ctor_set_uint8(v___x_5935_, sizeof(void*)*1, v___x_5934_);
return v___x_5935_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5938_, lean_object* v_x_5939_, lean_object* v_x_5940_){
_start:
{
if (lean_obj_tag(v_x_5940_) == 0)
{
lean_dec(v_x_5938_);
return v_x_5939_;
}
else
{
lean_object* v_head_5941_; lean_object* v_tail_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5952_; 
v_head_5941_ = lean_ctor_get(v_x_5940_, 0);
v_tail_5942_ = lean_ctor_get(v_x_5940_, 1);
v_isSharedCheck_5952_ = !lean_is_exclusive(v_x_5940_);
if (v_isSharedCheck_5952_ == 0)
{
v___x_5944_ = v_x_5940_;
v_isShared_5945_ = v_isSharedCheck_5952_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_tail_5942_);
lean_inc(v_head_5941_);
lean_dec(v_x_5940_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5952_;
goto v_resetjp_5943_;
}
v_resetjp_5943_:
{
lean_object* v___x_5947_; 
lean_inc(v_x_5938_);
if (v_isShared_5945_ == 0)
{
lean_ctor_set_tag(v___x_5944_, 5);
lean_ctor_set(v___x_5944_, 1, v_x_5938_);
lean_ctor_set(v___x_5944_, 0, v_x_5939_);
v___x_5947_ = v___x_5944_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5951_; 
v_reuseFailAlloc_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5951_, 0, v_x_5939_);
lean_ctor_set(v_reuseFailAlloc_5951_, 1, v_x_5938_);
v___x_5947_ = v_reuseFailAlloc_5951_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
lean_object* v___x_5948_; lean_object* v___x_5949_; 
v___x_5948_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5941_);
v___x_5949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5947_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v_x_5939_ = v___x_5949_;
v_x_5940_ = v_tail_5942_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5953_, lean_object* v_x_5954_, lean_object* v_x_5955_){
_start:
{
if (lean_obj_tag(v_x_5955_) == 0)
{
lean_dec(v_x_5953_);
return v_x_5954_;
}
else
{
lean_object* v_head_5956_; lean_object* v_tail_5957_; lean_object* v___x_5959_; uint8_t v_isShared_5960_; uint8_t v_isSharedCheck_5967_; 
v_head_5956_ = lean_ctor_get(v_x_5955_, 0);
v_tail_5957_ = lean_ctor_get(v_x_5955_, 1);
v_isSharedCheck_5967_ = !lean_is_exclusive(v_x_5955_);
if (v_isSharedCheck_5967_ == 0)
{
v___x_5959_ = v_x_5955_;
v_isShared_5960_ = v_isSharedCheck_5967_;
goto v_resetjp_5958_;
}
else
{
lean_inc(v_tail_5957_);
lean_inc(v_head_5956_);
lean_dec(v_x_5955_);
v___x_5959_ = lean_box(0);
v_isShared_5960_ = v_isSharedCheck_5967_;
goto v_resetjp_5958_;
}
v_resetjp_5958_:
{
lean_object* v___x_5962_; 
lean_inc(v_x_5953_);
if (v_isShared_5960_ == 0)
{
lean_ctor_set_tag(v___x_5959_, 5);
lean_ctor_set(v___x_5959_, 1, v_x_5953_);
lean_ctor_set(v___x_5959_, 0, v_x_5954_);
v___x_5962_ = v___x_5959_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v_x_5954_);
lean_ctor_set(v_reuseFailAlloc_5966_, 1, v_x_5953_);
v___x_5962_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5963_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5956_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5962_);
lean_ctor_set(v___x_5964_, 1, v___x_5963_);
v___x_5965_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5953_, v___x_5964_, v_tail_5957_);
return v___x_5965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5968_, lean_object* v_x_5969_){
_start:
{
if (lean_obj_tag(v_x_5968_) == 0)
{
lean_object* v___x_5970_; 
lean_dec(v_x_5969_);
v___x_5970_ = lean_box(0);
return v___x_5970_;
}
else
{
lean_object* v_tail_5971_; 
v_tail_5971_ = lean_ctor_get(v_x_5968_, 1);
if (lean_obj_tag(v_tail_5971_) == 0)
{
lean_object* v_head_5972_; lean_object* v___x_5973_; 
lean_dec(v_x_5969_);
v_head_5972_ = lean_ctor_get(v_x_5968_, 0);
lean_inc(v_head_5972_);
lean_dec_ref_known(v_x_5968_, 2);
v___x_5973_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5972_);
return v___x_5973_;
}
else
{
lean_object* v_head_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; 
lean_inc(v_tail_5971_);
v_head_5974_ = lean_ctor_get(v_x_5968_, 0);
lean_inc(v_head_5974_);
lean_dec_ref_known(v_x_5968_, 2);
v___x_5975_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5974_);
v___x_5976_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5969_, v___x_5975_, v_tail_5971_);
return v___x_5976_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5978_; lean_object* v___x_5979_; 
v___x_5978_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5979_ = lean_string_length(v___x_5978_);
return v___x_5979_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5980_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5981_ = lean_nat_to_int(v___x_5980_);
return v___x_5981_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5987_){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; uint8_t v___x_5990_; 
v___x_5988_ = lean_array_get_size(v_xs_5987_);
v___x_5989_ = lean_unsigned_to_nat(0u);
v___x_5990_ = lean_nat_dec_eq(v___x_5988_, v___x_5989_);
if (v___x_5990_ == 0)
{
lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5991_ = lean_array_to_list(v_xs_5987_);
v___x_5992_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5993_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5991_, v___x_5992_);
v___x_5994_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5995_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set(v___x_5996_, 1, v___x_5993_);
v___x_5997_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5996_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5994_);
lean_ctor_set(v___x_5999_, 1, v___x_5998_);
v___x_6000_ = l_Std_Format_fill(v___x_5999_);
return v___x_6000_;
}
else
{
lean_object* v___x_6001_; 
lean_dec_ref(v_xs_5987_);
v___x_6001_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_6001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_6004_, lean_object* v_decl_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_){
_start:
{
lean_object* v___y_6012_; lean_object* v___y_6013_; lean_object* v___y_6014_; lean_object* v___y_6015_; lean_object* v_toCold_6045_; lean_object* v_options_6046_; uint8_t v_hasTrace_6047_; 
v_toCold_6045_ = lean_ctor_get(v_a_6008_, 0);
v_options_6046_ = lean_ctor_get(v_toCold_6045_, 2);
v_hasTrace_6047_ = lean_ctor_get_uint8(v_options_6046_, sizeof(void*)*1);
if (v_hasTrace_6047_ == 0)
{
v___y_6012_ = v_a_6006_;
v___y_6013_ = v_a_6007_;
v___y_6014_ = v_a_6008_;
v___y_6015_ = v_a_6009_;
goto v___jp_6011_;
}
else
{
lean_object* v_inheritedTraceOptions_6048_; lean_object* v_cls_6049_; uint8_t v___y_6051_; lean_object* v___y_6052_; lean_object* v___x_6088_; uint8_t v___x_6089_; 
v_inheritedTraceOptions_6048_ = lean_ctor_get(v_toCold_6045_, 11);
v_cls_6049_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6088_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6048_, v_options_6046_, v___x_6088_);
if (v___x_6089_ == 0)
{
v___y_6012_ = v_a_6006_;
v___y_6013_ = v_a_6007_;
v___y_6014_ = v_a_6008_;
v___y_6015_ = v_a_6009_;
goto v___jp_6011_;
}
else
{
lean_object* v_size_6090_; lean_object* v_buckets_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; uint8_t v___x_6095_; 
v_size_6090_ = lean_ctor_get(v_assignment_6004_, 0);
v_buckets_6091_ = lean_ctor_get(v_assignment_6004_, 1);
v___x_6092_ = lean_mk_empty_array_with_capacity(v_size_6090_);
v___x_6093_ = lean_unsigned_to_nat(0u);
v___x_6094_ = lean_array_get_size(v_buckets_6091_);
v___x_6095_ = lean_nat_dec_lt(v___x_6093_, v___x_6094_);
if (v___x_6095_ == 0)
{
v___y_6051_ = v___x_6089_;
v___y_6052_ = v___x_6092_;
goto v___jp_6050_;
}
else
{
size_t v___x_6096_; size_t v___x_6097_; lean_object* v___x_6098_; 
v___x_6096_ = ((size_t)0ULL);
v___x_6097_ = lean_usize_of_nat(v___x_6094_);
v___x_6098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6091_, v___x_6096_, v___x_6097_, v___x_6092_);
v___y_6051_ = v___x_6089_;
v___y_6052_ = v___x_6098_;
goto v___jp_6050_;
}
}
v___jp_6050_:
{
size_t v_sz_6053_; size_t v___x_6054_; lean_object* v___x_6055_; 
v_sz_6053_ = lean_array_size(v___y_6052_);
v___x_6054_ = ((size_t)0ULL);
v___x_6055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___y_6051_, v_sz_6053_, v___x_6054_, v___y_6052_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
if (lean_obj_tag(v___x_6055_) == 0)
{
lean_object* v_toSignature_6056_; lean_object* v_a_6057_; lean_object* v_name_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; 
v_toSignature_6056_ = lean_ctor_get(v_decl_6005_, 0);
v_a_6057_ = lean_ctor_get(v___x_6055_, 0);
lean_inc(v_a_6057_);
lean_dec_ref_known(v___x_6055_, 1);
v_name_6058_ = lean_ctor_get(v_toSignature_6056_, 0);
v___x_6059_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
lean_inc(v_name_6058_);
v___x_6060_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6058_, v___y_6051_);
v___x_6061_ = lean_string_append(v___x_6059_, v___x_6060_);
lean_dec_ref(v___x_6060_);
v___x_6062_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6063_ = lean_string_append(v___x_6061_, v___x_6062_);
v___x_6064_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6057_);
v___x_6065_ = l_Std_Format_defWidth;
v___x_6066_ = lean_unsigned_to_nat(0u);
v___x_6067_ = l_Std_Format_pretty(v___x_6064_, v___x_6065_, v___x_6066_, v___x_6066_);
v___x_6068_ = lean_string_append(v___x_6063_, v___x_6067_);
lean_dec_ref(v___x_6067_);
v___x_6069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
v___x_6070_ = l_Lean_MessageData_ofFormat(v___x_6069_);
v___x_6071_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_6049_, v___x_6070_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
if (lean_obj_tag(v___x_6071_) == 0)
{
lean_dec_ref_known(v___x_6071_, 1);
v___y_6012_ = v_a_6006_;
v___y_6013_ = v_a_6007_;
v___y_6014_ = v_a_6008_;
v___y_6015_ = v_a_6009_;
goto v___jp_6011_;
}
else
{
lean_object* v_a_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6079_; 
lean_dec_ref(v_decl_6005_);
lean_dec_ref(v_assignment_6004_);
v_a_6072_ = lean_ctor_get(v___x_6071_, 0);
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6071_);
if (v_isSharedCheck_6079_ == 0)
{
v___x_6074_ = v___x_6071_;
v_isShared_6075_ = v_isSharedCheck_6079_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_a_6072_);
lean_dec(v___x_6071_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6079_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6077_; 
if (v_isShared_6075_ == 0)
{
v___x_6077_ = v___x_6074_;
goto v_reusejp_6076_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_a_6072_);
v___x_6077_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6076_;
}
v_reusejp_6076_:
{
return v___x_6077_;
}
}
}
}
else
{
lean_object* v_a_6080_; lean_object* v___x_6082_; uint8_t v_isShared_6083_; uint8_t v_isSharedCheck_6087_; 
lean_dec_ref(v_decl_6005_);
lean_dec_ref(v_assignment_6004_);
v_a_6080_ = lean_ctor_get(v___x_6055_, 0);
v_isSharedCheck_6087_ = !lean_is_exclusive(v___x_6055_);
if (v_isSharedCheck_6087_ == 0)
{
v___x_6082_ = v___x_6055_;
v_isShared_6083_ = v_isSharedCheck_6087_;
goto v_resetjp_6081_;
}
else
{
lean_inc(v_a_6080_);
lean_dec(v___x_6055_);
v___x_6082_ = lean_box(0);
v_isShared_6083_ = v_isSharedCheck_6087_;
goto v_resetjp_6081_;
}
v_resetjp_6081_:
{
lean_object* v___x_6085_; 
if (v_isShared_6083_ == 0)
{
v___x_6085_ = v___x_6082_;
goto v_reusejp_6084_;
}
else
{
lean_object* v_reuseFailAlloc_6086_; 
v_reuseFailAlloc_6086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6086_, 0, v_a_6080_);
v___x_6085_ = v_reuseFailAlloc_6086_;
goto v_reusejp_6084_;
}
v_reusejp_6084_:
{
return v___x_6085_;
}
}
}
}
}
v___jp_6011_:
{
lean_object* v_toSignature_6016_; lean_object* v_value_6017_; uint8_t v_recursive_6018_; lean_object* v_inlineAttr_x3f_6019_; lean_object* v___x_6021_; uint8_t v_isShared_6022_; uint8_t v_isSharedCheck_6044_; 
v_toSignature_6016_ = lean_ctor_get(v_decl_6005_, 0);
v_value_6017_ = lean_ctor_get(v_decl_6005_, 1);
v_recursive_6018_ = lean_ctor_get_uint8(v_decl_6005_, sizeof(void*)*3);
v_inlineAttr_x3f_6019_ = lean_ctor_get(v_decl_6005_, 2);
v_isSharedCheck_6044_ = !lean_is_exclusive(v_decl_6005_);
if (v_isSharedCheck_6044_ == 0)
{
v___x_6021_ = v_decl_6005_;
v_isShared_6022_ = v_isSharedCheck_6044_;
goto v_resetjp_6020_;
}
else
{
lean_inc(v_inlineAttr_x3f_6019_);
lean_inc(v_value_6017_);
lean_inc(v_toSignature_6016_);
lean_dec(v_decl_6005_);
v___x_6021_ = lean_box(0);
v_isShared_6022_ = v_isSharedCheck_6044_;
goto v_resetjp_6020_;
}
v_resetjp_6020_:
{
lean_object* v___x_6023_; lean_object* v___x_6024_; 
v___x_6023_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_6023_, 0, v_assignment_6004_);
v___x_6024_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_6023_, v_value_6017_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_);
if (lean_obj_tag(v___x_6024_) == 0)
{
lean_object* v_a_6025_; lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6035_; 
v_a_6025_ = lean_ctor_get(v___x_6024_, 0);
v_isSharedCheck_6035_ = !lean_is_exclusive(v___x_6024_);
if (v_isSharedCheck_6035_ == 0)
{
v___x_6027_ = v___x_6024_;
v_isShared_6028_ = v_isSharedCheck_6035_;
goto v_resetjp_6026_;
}
else
{
lean_inc(v_a_6025_);
lean_dec(v___x_6024_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6035_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v___x_6030_; 
if (v_isShared_6022_ == 0)
{
lean_ctor_set(v___x_6021_, 1, v_a_6025_);
v___x_6030_ = v___x_6021_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6034_; 
v_reuseFailAlloc_6034_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_toSignature_6016_);
lean_ctor_set(v_reuseFailAlloc_6034_, 1, v_a_6025_);
lean_ctor_set(v_reuseFailAlloc_6034_, 2, v_inlineAttr_x3f_6019_);
lean_ctor_set_uint8(v_reuseFailAlloc_6034_, sizeof(void*)*3, v_recursive_6018_);
v___x_6030_ = v_reuseFailAlloc_6034_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
lean_object* v___x_6032_; 
if (v_isShared_6028_ == 0)
{
lean_ctor_set(v___x_6027_, 0, v___x_6030_);
v___x_6032_ = v___x_6027_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v___x_6030_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
}
}
else
{
lean_object* v_a_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6043_; 
lean_del_object(v___x_6021_);
lean_dec(v_inlineAttr_x3f_6019_);
lean_dec_ref(v_toSignature_6016_);
v_a_6036_ = lean_ctor_get(v___x_6024_, 0);
v_isSharedCheck_6043_ = !lean_is_exclusive(v___x_6024_);
if (v_isSharedCheck_6043_ == 0)
{
v___x_6038_ = v___x_6024_;
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_a_6036_);
lean_dec(v___x_6024_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v___x_6041_; 
if (v_isShared_6039_ == 0)
{
v___x_6041_ = v___x_6038_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v_a_6036_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6099_, lean_object* v_decl_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_, lean_object* v_a_6103_, lean_object* v_a_6104_, lean_object* v_a_6105_){
_start:
{
lean_object* v_res_6106_; 
v_res_6106_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6099_, v_decl_6100_, v_a_6101_, v_a_6102_, v_a_6103_, v_a_6104_);
lean_dec(v_a_6104_);
lean_dec_ref(v_a_6103_);
lean_dec(v_a_6102_);
lean_dec_ref(v_a_6101_);
return v_res_6106_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6107_, lean_object* v_x_6108_){
_start:
{
lean_object* v___x_6109_; 
v___x_6109_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6107_);
return v___x_6109_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6110_, lean_object* v_x_6111_){
_start:
{
lean_object* v_res_6112_; 
v_res_6112_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6110_, v_x_6111_);
lean_dec(v_x_6111_);
return v_res_6112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6113_, size_t v_i_6114_, lean_object* v_bs_6115_){
_start:
{
uint8_t v___x_6116_; 
v___x_6116_ = lean_usize_dec_lt(v_i_6114_, v_sz_6113_);
if (v___x_6116_ == 0)
{
return v_bs_6115_;
}
else
{
lean_object* v_v_6117_; lean_object* v_toSignature_6118_; lean_object* v_name_6119_; lean_object* v___x_6120_; lean_object* v_bs_x27_6121_; size_t v___x_6122_; size_t v___x_6123_; lean_object* v___x_6124_; 
v_v_6117_ = lean_array_uget_borrowed(v_bs_6115_, v_i_6114_);
v_toSignature_6118_ = lean_ctor_get(v_v_6117_, 0);
v_name_6119_ = lean_ctor_get(v_toSignature_6118_, 0);
lean_inc(v_name_6119_);
v___x_6120_ = lean_unsigned_to_nat(0u);
v_bs_x27_6121_ = lean_array_uset(v_bs_6115_, v_i_6114_, v___x_6120_);
v___x_6122_ = ((size_t)1ULL);
v___x_6123_ = lean_usize_add(v_i_6114_, v___x_6122_);
v___x_6124_ = lean_array_uset(v_bs_x27_6121_, v_i_6114_, v_name_6119_);
v_i_6114_ = v___x_6123_;
v_bs_6115_ = v___x_6124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6126_, lean_object* v_i_6127_, lean_object* v_bs_6128_){
_start:
{
size_t v_sz_boxed_6129_; size_t v_i_boxed_6130_; lean_object* v_res_6131_; 
v_sz_boxed_6129_ = lean_unbox_usize(v_sz_6126_);
lean_dec(v_sz_6126_);
v_i_boxed_6130_ = lean_unbox_usize(v_i_6127_);
lean_dec(v_i_6127_);
v_res_6131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6129_, v_i_boxed_6130_, v_bs_6128_);
return v_res_6131_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6132_, lean_object* v_a_6133_){
_start:
{
if (lean_obj_tag(v_a_6132_) == 0)
{
lean_object* v___x_6134_; 
v___x_6134_ = l_List_reverse___redArg(v_a_6133_);
return v___x_6134_;
}
else
{
lean_object* v_head_6135_; lean_object* v_tail_6136_; lean_object* v___x_6138_; uint8_t v_isShared_6139_; uint8_t v_isSharedCheck_6145_; 
v_head_6135_ = lean_ctor_get(v_a_6132_, 0);
v_tail_6136_ = lean_ctor_get(v_a_6132_, 1);
v_isSharedCheck_6145_ = !lean_is_exclusive(v_a_6132_);
if (v_isSharedCheck_6145_ == 0)
{
v___x_6138_ = v_a_6132_;
v_isShared_6139_ = v_isSharedCheck_6145_;
goto v_resetjp_6137_;
}
else
{
lean_inc(v_tail_6136_);
lean_inc(v_head_6135_);
lean_dec(v_a_6132_);
v___x_6138_ = lean_box(0);
v_isShared_6139_ = v_isSharedCheck_6145_;
goto v_resetjp_6137_;
}
v_resetjp_6137_:
{
lean_object* v___x_6140_; lean_object* v___x_6142_; 
v___x_6140_ = l_Lean_MessageData_ofName(v_head_6135_);
if (v_isShared_6139_ == 0)
{
lean_ctor_set(v___x_6138_, 1, v_a_6133_);
lean_ctor_set(v___x_6138_, 0, v___x_6140_);
v___x_6142_ = v___x_6138_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6144_; 
v_reuseFailAlloc_6144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6144_, 0, v___x_6140_);
lean_ctor_set(v_reuseFailAlloc_6144_, 1, v_a_6133_);
v___x_6142_ = v_reuseFailAlloc_6144_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
v_a_6132_ = v_tail_6136_;
v_a_6133_ = v___x_6142_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6147_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6148_ = l_Lean_stringToMessageData(v___x_6147_);
return v___x_6148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6149_, lean_object* v_x_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_){
_start:
{
lean_object* v___x_6158_; size_t v_sz_6159_; size_t v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; 
v___x_6158_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6159_ = lean_array_size(v___y_6149_);
v___x_6160_ = ((size_t)0ULL);
v___x_6161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6159_, v___x_6160_, v___y_6149_);
v___x_6162_ = lean_array_to_list(v___x_6161_);
v___x_6163_ = lean_box(0);
v___x_6164_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6162_, v___x_6163_);
v___x_6165_ = l_Lean_MessageData_ofList(v___x_6164_);
v___x_6166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6158_);
lean_ctor_set(v___x_6166_, 1, v___x_6165_);
v___x_6167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6167_, 0, v___x_6166_);
return v___x_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6168_, lean_object* v_x_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_){
_start:
{
lean_object* v_res_6177_; 
v_res_6177_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6168_, v_x_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec_ref(v_x_6169_);
return v_res_6177_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_6178_; 
v___x_6178_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default___redArg();
return v___x_6178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(lean_object* v___y_6179_, lean_object* v_n_6180_, lean_object* v_j_6181_, lean_object* v_a_6182_){
_start:
{
lean_object* v_zero_6183_; uint8_t v_isZero_6184_; 
v_zero_6183_ = lean_unsigned_to_nat(0u);
v_isZero_6184_ = lean_nat_dec_eq(v_j_6181_, v_zero_6183_);
if (v_isZero_6184_ == 1)
{
lean_dec(v_j_6181_);
return v_a_6182_;
}
else
{
lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v_toSignature_6188_; uint8_t v_safe_6189_; lean_object* v_one_6190_; lean_object* v_n_6191_; 
v___x_6185_ = lean_nat_sub(v_n_6180_, v_j_6181_);
v___x_6186_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0, &l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0);
v___x_6187_ = lean_array_get_borrowed(v___x_6186_, v___y_6179_, v___x_6185_);
lean_dec(v___x_6185_);
v_toSignature_6188_ = lean_ctor_get(v___x_6187_, 0);
v_safe_6189_ = lean_ctor_get_uint8(v_toSignature_6188_, sizeof(void*)*4);
v_one_6190_ = lean_unsigned_to_nat(1u);
v_n_6191_ = lean_nat_sub(v_j_6181_, v_one_6190_);
lean_dec(v_j_6181_);
if (v_safe_6189_ == 0)
{
lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6192_ = lean_box(1);
v___x_6193_ = lean_array_push(v_a_6182_, v___x_6192_);
v_j_6181_ = v_n_6191_;
v_a_6182_ = v___x_6193_;
goto _start;
}
else
{
lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6195_ = lean_box(0);
v___x_6196_ = lean_array_push(v_a_6182_, v___x_6195_);
v_j_6181_ = v_n_6191_;
v_a_6182_ = v___x_6196_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___boxed(lean_object* v___y_6198_, lean_object* v_n_6199_, lean_object* v_j_6200_, lean_object* v_a_6201_){
_start:
{
lean_object* v_res_6202_; 
v_res_6202_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6198_, v_n_6199_, v_j_6200_, v_a_6201_);
lean_dec(v_n_6199_);
lean_dec_ref(v___y_6198_);
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6203_, size_t v_sz_6204_, size_t v_i_6205_, lean_object* v_bs_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_){
_start:
{
uint8_t v___x_6212_; 
v___x_6212_ = lean_usize_dec_lt(v_i_6205_, v_sz_6204_);
if (v___x_6212_ == 0)
{
lean_object* v___x_6213_; 
v___x_6213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6213_, 0, v_bs_6206_);
return v___x_6213_;
}
else
{
lean_object* v_v_6214_; lean_object* v_toSignature_6215_; uint8_t v_safe_6216_; lean_object* v___x_6217_; lean_object* v_bs_x27_6218_; lean_object* v_a_6220_; 
v_v_6214_ = lean_array_uget(v_bs_6206_, v_i_6205_);
v_toSignature_6215_ = lean_ctor_get(v_v_6214_, 0);
v_safe_6216_ = lean_ctor_get_uint8(v_toSignature_6215_, sizeof(void*)*4);
v___x_6217_ = lean_unsigned_to_nat(0u);
v_bs_x27_6218_ = lean_array_uset(v_bs_6206_, v_i_6205_, v___x_6217_);
if (v_safe_6216_ == 0)
{
v_a_6220_ = v_v_6214_;
goto v___jp_6219_;
}
else
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6225_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0);
v___x_6226_ = lean_usize_to_nat(v_i_6205_);
v___x_6227_ = lean_array_get_borrowed(v___x_6225_, v___x_6203_, v___x_6226_);
lean_dec(v___x_6226_);
lean_inc(v___x_6227_);
v___x_6228_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6227_, v_v_6214_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_);
if (lean_obj_tag(v___x_6228_) == 0)
{
lean_object* v_a_6229_; 
v_a_6229_ = lean_ctor_get(v___x_6228_, 0);
lean_inc(v_a_6229_);
lean_dec_ref_known(v___x_6228_, 1);
v_a_6220_ = v_a_6229_;
goto v___jp_6219_;
}
else
{
lean_object* v_a_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6237_; 
lean_dec_ref(v_bs_x27_6218_);
v_a_6230_ = lean_ctor_get(v___x_6228_, 0);
v_isSharedCheck_6237_ = !lean_is_exclusive(v___x_6228_);
if (v_isSharedCheck_6237_ == 0)
{
v___x_6232_ = v___x_6228_;
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
else
{
lean_inc(v_a_6230_);
lean_dec(v___x_6228_);
v___x_6232_ = lean_box(0);
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
v_resetjp_6231_:
{
lean_object* v___x_6235_; 
if (v_isShared_6233_ == 0)
{
v___x_6235_ = v___x_6232_;
goto v_reusejp_6234_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_a_6230_);
v___x_6235_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6234_;
}
v_reusejp_6234_:
{
return v___x_6235_;
}
}
}
}
v___jp_6219_:
{
size_t v___x_6221_; size_t v___x_6222_; lean_object* v___x_6223_; 
v___x_6221_ = ((size_t)1ULL);
v___x_6222_ = lean_usize_add(v_i_6205_, v___x_6221_);
v___x_6223_ = lean_array_uset(v_bs_x27_6218_, v_i_6205_, v_a_6220_);
v_i_6205_ = v___x_6222_;
v_bs_6206_ = v___x_6223_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6238_, lean_object* v_sz_6239_, lean_object* v_i_6240_, lean_object* v_bs_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
size_t v_sz_boxed_6247_; size_t v_i_boxed_6248_; lean_object* v_res_6249_; 
v_sz_boxed_6247_ = lean_unbox_usize(v_sz_6239_);
lean_dec(v_sz_6239_);
v_i_boxed_6248_ = lean_unbox_usize(v_i_6240_);
lean_dec(v_i_6240_);
v_res_6249_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6238_, v_sz_boxed_6247_, v_i_boxed_6248_, v_bs_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_);
lean_dec(v___y_6245_);
lean_dec_ref(v___y_6244_);
lean_dec(v___y_6243_);
lean_dec_ref(v___y_6242_);
lean_dec_ref(v___x_6238_);
return v_res_6249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(lean_object* v_hi_6252_, lean_object* v_pivot_6253_, lean_object* v_as_6254_, lean_object* v_i_6255_, lean_object* v_k_6256_){
_start:
{
uint8_t v___x_6257_; 
v___x_6257_ = lean_nat_dec_lt(v_k_6256_, v_hi_6252_);
if (v___x_6257_ == 0)
{
lean_object* v___x_6258_; lean_object* v___x_6259_; 
lean_dec(v_k_6256_);
lean_dec_ref(v_pivot_6253_);
v___x_6258_ = lean_array_fswap(v_as_6254_, v_i_6255_, v_hi_6252_);
v___x_6259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6259_, 0, v_i_6255_);
lean_ctor_set(v___x_6259_, 1, v___x_6258_);
return v___x_6259_;
}
else
{
lean_object* v___x_6260_; lean_object* v_toSignature_6261_; lean_object* v_toSignature_6262_; lean_object* v_name_6263_; lean_object* v_name_6264_; uint8_t v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; uint8_t v___x_6275_; 
v___x_6260_ = lean_array_fget_borrowed(v_as_6254_, v_k_6256_);
v_toSignature_6261_ = lean_ctor_get(v___x_6260_, 0);
v_toSignature_6262_ = lean_ctor_get(v_pivot_6253_, 0);
v_name_6263_ = lean_ctor_get(v_toSignature_6261_, 0);
v_name_6264_ = lean_ctor_get(v_toSignature_6262_, 0);
v___x_6265_ = 0;
v___x_6266_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6265_, v___x_6260_);
v___x_6267_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6268_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6269_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
lean_inc(v_name_6263_);
v___x_6270_ = l_Lean_Name_toString(v_name_6263_, v___x_6257_);
v___x_6271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6271_, 0, v___x_6266_);
lean_ctor_set(v___x_6271_, 1, v___x_6270_);
v___x_6272_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6265_, v_pivot_6253_);
lean_inc(v_name_6264_);
v___x_6273_ = l_Lean_Name_toString(v_name_6264_, v___x_6257_);
v___x_6274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6274_, 0, v___x_6272_);
lean_ctor_set(v___x_6274_, 1, v___x_6273_);
v___x_6275_ = l_Prod_lexLtDec___redArg(v___x_6267_, v___x_6268_, v___x_6269_, v___x_6271_, v___x_6274_);
if (v___x_6275_ == 0)
{
lean_object* v___x_6276_; lean_object* v___x_6277_; 
v___x_6276_ = lean_unsigned_to_nat(1u);
v___x_6277_ = lean_nat_add(v_k_6256_, v___x_6276_);
lean_dec(v_k_6256_);
v_k_6256_ = v___x_6277_;
goto _start;
}
else
{
lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; 
v___x_6279_ = lean_array_fswap(v_as_6254_, v_i_6255_, v_k_6256_);
v___x_6280_ = lean_unsigned_to_nat(1u);
v___x_6281_ = lean_nat_add(v_i_6255_, v___x_6280_);
lean_dec(v_i_6255_);
v___x_6282_ = lean_nat_add(v_k_6256_, v___x_6280_);
lean_dec(v_k_6256_);
v_as_6254_ = v___x_6279_;
v_i_6255_ = v___x_6281_;
v_k_6256_ = v___x_6282_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___boxed(lean_object* v_hi_6284_, lean_object* v_pivot_6285_, lean_object* v_as_6286_, lean_object* v_i_6287_, lean_object* v_k_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6284_, v_pivot_6285_, v_as_6286_, v_i_6287_, v_k_6288_);
lean_dec(v_hi_6284_);
return v_res_6289_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6290_, lean_object* v_l_6291_, lean_object* v_r_6292_){
_start:
{
lean_object* v_toSignature_6293_; lean_object* v_toSignature_6294_; lean_object* v_name_6295_; lean_object* v_name_6296_; uint8_t v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; uint8_t v___x_6307_; 
v_toSignature_6293_ = lean_ctor_get(v_l_6291_, 0);
v_toSignature_6294_ = lean_ctor_get(v_r_6292_, 0);
v_name_6295_ = lean_ctor_get(v_toSignature_6293_, 0);
lean_inc(v_name_6295_);
v_name_6296_ = lean_ctor_get(v_toSignature_6294_, 0);
lean_inc(v_name_6296_);
v___x_6297_ = 0;
v___x_6298_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6297_, v_l_6291_);
lean_dec_ref(v_l_6291_);
v___x_6299_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6300_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__0));
v___x_6301_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg___closed__1));
v___x_6302_ = l_Lean_Name_toString(v_name_6295_, v___x_6290_);
v___x_6303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6303_, 0, v___x_6298_);
lean_ctor_set(v___x_6303_, 1, v___x_6302_);
v___x_6304_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6297_, v_r_6292_);
lean_dec_ref(v_r_6292_);
v___x_6305_ = l_Lean_Name_toString(v_name_6296_, v___x_6290_);
v___x_6306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6306_, 0, v___x_6304_);
lean_ctor_set(v___x_6306_, 1, v___x_6305_);
v___x_6307_ = l_Prod_lexLtDec___redArg(v___x_6299_, v___x_6300_, v___x_6301_, v___x_6303_, v___x_6306_);
return v___x_6307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6308_, lean_object* v_l_6309_, lean_object* v_r_6310_){
_start:
{
uint8_t v___x_13173__boxed_6311_; uint8_t v_res_6312_; lean_object* v_r_6313_; 
v___x_13173__boxed_6311_ = lean_unbox(v___x_6308_);
v_res_6312_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_13173__boxed_6311_, v_l_6309_, v_r_6310_);
v_r_6313_ = lean_box(v_res_6312_);
return v_r_6313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_n_6314_, lean_object* v_as_6315_, lean_object* v_lo_6316_, lean_object* v_hi_6317_){
_start:
{
lean_object* v___y_6319_; uint8_t v___x_6329_; 
v___x_6329_ = lean_nat_dec_lt(v_lo_6316_, v_hi_6317_);
if (v___x_6329_ == 0)
{
lean_dec(v_lo_6316_);
return v_as_6315_;
}
else
{
lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v_mid_6332_; lean_object* v___y_6334_; lean_object* v___y_6340_; lean_object* v___x_6345_; lean_object* v___x_6346_; uint8_t v___x_6347_; 
v___x_6330_ = lean_nat_add(v_lo_6316_, v_hi_6317_);
v___x_6331_ = lean_unsigned_to_nat(1u);
v_mid_6332_ = lean_nat_shiftr(v___x_6330_, v___x_6331_);
lean_dec(v___x_6330_);
v___x_6345_ = lean_array_fget_borrowed(v_as_6315_, v_mid_6332_);
v___x_6346_ = lean_array_fget_borrowed(v_as_6315_, v_lo_6316_);
lean_inc(v___x_6346_);
lean_inc(v___x_6345_);
v___x_6347_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6329_, v___x_6345_, v___x_6346_);
if (v___x_6347_ == 0)
{
v___y_6340_ = v_as_6315_;
goto v___jp_6339_;
}
else
{
lean_object* v___x_6348_; 
v___x_6348_ = lean_array_fswap(v_as_6315_, v_lo_6316_, v_mid_6332_);
v___y_6340_ = v___x_6348_;
goto v___jp_6339_;
}
v___jp_6333_:
{
lean_object* v___x_6335_; lean_object* v___x_6336_; uint8_t v___x_6337_; 
v___x_6335_ = lean_array_fget_borrowed(v___y_6334_, v_mid_6332_);
v___x_6336_ = lean_array_fget_borrowed(v___y_6334_, v_hi_6317_);
lean_inc(v___x_6336_);
lean_inc(v___x_6335_);
v___x_6337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6329_, v___x_6335_, v___x_6336_);
if (v___x_6337_ == 0)
{
lean_dec(v_mid_6332_);
v___y_6319_ = v___y_6334_;
goto v___jp_6318_;
}
else
{
lean_object* v___x_6338_; 
v___x_6338_ = lean_array_fswap(v___y_6334_, v_mid_6332_, v_hi_6317_);
lean_dec(v_mid_6332_);
v___y_6319_ = v___x_6338_;
goto v___jp_6318_;
}
}
v___jp_6339_:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; uint8_t v___x_6343_; 
v___x_6341_ = lean_array_fget_borrowed(v___y_6340_, v_hi_6317_);
v___x_6342_ = lean_array_fget_borrowed(v___y_6340_, v_lo_6316_);
lean_inc(v___x_6342_);
lean_inc(v___x_6341_);
v___x_6343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_6329_, v___x_6341_, v___x_6342_);
if (v___x_6343_ == 0)
{
v___y_6334_ = v___y_6340_;
goto v___jp_6333_;
}
else
{
lean_object* v___x_6344_; 
v___x_6344_ = lean_array_fswap(v___y_6340_, v_lo_6316_, v_hi_6317_);
v___y_6334_ = v___x_6344_;
goto v___jp_6333_;
}
}
}
v___jp_6318_:
{
lean_object* v_pivot_6320_; lean_object* v___x_6321_; lean_object* v_fst_6322_; lean_object* v_snd_6323_; uint8_t v___x_6324_; 
v_pivot_6320_ = lean_array_fget(v___y_6319_, v_hi_6317_);
lean_inc_n(v_lo_6316_, 2);
v___x_6321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6317_, v_pivot_6320_, v___y_6319_, v_lo_6316_, v_lo_6316_);
v_fst_6322_ = lean_ctor_get(v___x_6321_, 0);
lean_inc(v_fst_6322_);
v_snd_6323_ = lean_ctor_get(v___x_6321_, 1);
lean_inc(v_snd_6323_);
lean_dec_ref(v___x_6321_);
v___x_6324_ = lean_nat_dec_le(v_hi_6317_, v_fst_6322_);
if (v___x_6324_ == 0)
{
lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___x_6327_; 
v___x_6325_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6314_, v_snd_6323_, v_lo_6316_, v_fst_6322_);
v___x_6326_ = lean_unsigned_to_nat(1u);
v___x_6327_ = lean_nat_add(v_fst_6322_, v___x_6326_);
lean_dec(v_fst_6322_);
v_as_6315_ = v___x_6325_;
v_lo_6316_ = v___x_6327_;
goto _start;
}
else
{
lean_dec(v_fst_6322_);
lean_dec(v_lo_6316_);
return v_snd_6323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_n_6349_, lean_object* v_as_6350_, lean_object* v_lo_6351_, lean_object* v_hi_6352_){
_start:
{
lean_object* v_res_6353_; 
v_res_6353_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6349_, v_as_6350_, v_lo_6351_, v_hi_6352_);
lean_dec(v_hi_6352_);
lean_dec(v_n_6349_);
return v_res_6353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6354_, lean_object* v___x_6355_, lean_object* v_n_6356_, lean_object* v_j_6357_, lean_object* v_a_6358_){
_start:
{
lean_object* v_zero_6359_; uint8_t v_isZero_6360_; 
v_zero_6359_ = lean_unsigned_to_nat(0u);
v_isZero_6360_ = lean_nat_dec_eq(v_j_6357_, v_zero_6359_);
if (v_isZero_6360_ == 1)
{
lean_dec(v_j_6357_);
return v_a_6358_;
}
else
{
lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v_toSignature_6363_; lean_object* v_name_6364_; lean_object* v___x_6365_; lean_object* v_one_6366_; lean_object* v_n_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; 
v___x_6361_ = lean_nat_sub(v_n_6356_, v_j_6357_);
v___x_6362_ = lean_array_fget_borrowed(v___y_6354_, v___x_6361_);
v_toSignature_6363_ = lean_ctor_get(v___x_6362_, 0);
v_name_6364_ = lean_ctor_get(v_toSignature_6363_, 0);
v___x_6365_ = lean_box(0);
v_one_6366_ = lean_unsigned_to_nat(1u);
v_n_6367_ = lean_nat_sub(v_j_6357_, v_one_6366_);
lean_dec(v_j_6357_);
v___x_6368_ = lean_array_get_borrowed(v___x_6365_, v___x_6355_, v___x_6361_);
lean_dec(v___x_6361_);
lean_inc(v___x_6368_);
lean_inc(v_name_6364_);
v___x_6369_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6358_, v_name_6364_, v___x_6368_);
v_j_6357_ = v_n_6367_;
v_a_6358_ = v___x_6369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6371_, lean_object* v___x_6372_, lean_object* v_n_6373_, lean_object* v_j_6374_, lean_object* v_a_6375_){
_start:
{
lean_object* v_res_6376_; 
v_res_6376_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6371_, v___x_6372_, v_n_6373_, v_j_6374_, v_a_6375_);
lean_dec(v_n_6373_);
lean_dec_ref(v___x_6372_);
lean_dec_ref(v___y_6371_);
return v_res_6376_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6377_; lean_object* v___x_6378_; 
v___x_6377_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_368603888____hygCtx___hyg_2_);
v___x_6378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6378_, 0, v___x_6377_);
return v___x_6378_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6379_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6380_, 0, v___x_6379_);
lean_ctor_set(v___x_6380_, 1, v___x_6379_);
return v___x_6380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_){
_start:
{
lean_object* v___y_6390_; size_t v___y_6391_; lean_object* v___y_6392_; size_t v___y_6393_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v___y_6429_; lean_object* v___y_6430_; lean_object* v___y_6431_; lean_object* v___y_6432_; lean_object* v___y_6433_; lean_object* v___y_6434_; uint8_t v___y_6435_; uint8_t v___y_6436_; lean_object* v___y_6437_; size_t v___y_6438_; size_t v___y_6439_; lean_object* v___y_6440_; lean_object* v___y_6441_; lean_object* v___y_6442_; lean_object* v_a_6443_; lean_object* v___y_6453_; lean_object* v___y_6454_; lean_object* v___y_6455_; lean_object* v___y_6456_; lean_object* v___y_6457_; uint8_t v___y_6458_; uint8_t v___y_6459_; lean_object* v___y_6460_; size_t v___y_6461_; lean_object* v___y_6462_; size_t v___y_6463_; lean_object* v___y_6464_; lean_object* v___y_6465_; lean_object* v___y_6466_; lean_object* v_a_6467_; lean_object* v___x_6479_; lean_object* v___y_6481_; lean_object* v___y_6482_; lean_object* v___y_6483_; lean_object* v___y_6484_; lean_object* v___y_6485_; uint8_t v___y_6486_; uint8_t v___y_6487_; lean_object* v___y_6488_; size_t v___y_6489_; size_t v___y_6490_; lean_object* v___y_6491_; lean_object* v___y_6492_; lean_object* v___y_6534_; lean_object* v___x_6558_; lean_object* v___y_6560_; lean_object* v___y_6561_; uint8_t v___x_6563_; 
v___x_6479_ = lean_unsigned_to_nat(0u);
v___x_6558_ = lean_array_get_size(v_decls_6383_);
v___x_6563_ = lean_nat_dec_eq(v___x_6558_, v___x_6479_);
if (v___x_6563_ == 0)
{
lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___y_6567_; uint8_t v___x_6569_; 
v___x_6564_ = lean_unsigned_to_nat(1u);
v___x_6565_ = lean_nat_sub(v___x_6558_, v___x_6564_);
v___x_6569_ = lean_nat_dec_le(v___x_6479_, v___x_6565_);
if (v___x_6569_ == 0)
{
lean_inc(v___x_6565_);
v___y_6567_ = v___x_6565_;
goto v___jp_6566_;
}
else
{
v___y_6567_ = v___x_6479_;
goto v___jp_6566_;
}
v___jp_6566_:
{
uint8_t v___x_6568_; 
v___x_6568_ = lean_nat_dec_le(v___y_6567_, v___x_6565_);
if (v___x_6568_ == 0)
{
lean_dec(v___x_6565_);
lean_inc(v___y_6567_);
v___y_6560_ = v___y_6567_;
v___y_6561_ = v___y_6567_;
goto v___jp_6559_;
}
else
{
v___y_6560_ = v___y_6567_;
v___y_6561_ = v___x_6565_;
goto v___jp_6559_;
}
}
}
else
{
v___y_6534_ = v_decls_6383_;
goto v___jp_6533_;
}
v___jp_6389_:
{
if (lean_obj_tag(v___y_6395_) == 0)
{
lean_object* v___x_6396_; lean_object* v_assignments_6397_; lean_object* v_funVals_6398_; lean_object* v___x_6399_; lean_object* v_env_6400_; lean_object* v_nextMacroScope_6401_; lean_object* v_ngen_6402_; lean_object* v_auxDeclNGen_6403_; lean_object* v_traceState_6404_; lean_object* v_messages_6405_; lean_object* v_infoState_6406_; lean_object* v_snapshotTasks_6407_; lean_object* v___x_6409_; uint8_t v_isShared_6410_; uint8_t v_isSharedCheck_6418_; 
lean_dec_ref_known(v___y_6395_, 1);
v___x_6396_ = lean_st_ref_get(v___y_6394_);
lean_dec(v___y_6394_);
v_assignments_6397_ = lean_ctor_get(v___x_6396_, 0);
lean_inc_ref(v_assignments_6397_);
v_funVals_6398_ = lean_ctor_get(v___x_6396_, 1);
lean_inc_ref(v_funVals_6398_);
lean_dec(v___x_6396_);
v___x_6399_ = lean_st_ref_take(v_a_6387_);
v_env_6400_ = lean_ctor_get(v___x_6399_, 0);
v_nextMacroScope_6401_ = lean_ctor_get(v___x_6399_, 1);
v_ngen_6402_ = lean_ctor_get(v___x_6399_, 2);
v_auxDeclNGen_6403_ = lean_ctor_get(v___x_6399_, 3);
v_traceState_6404_ = lean_ctor_get(v___x_6399_, 4);
v_messages_6405_ = lean_ctor_get(v___x_6399_, 6);
v_infoState_6406_ = lean_ctor_get(v___x_6399_, 7);
v_snapshotTasks_6407_ = lean_ctor_get(v___x_6399_, 8);
v_isSharedCheck_6418_ = !lean_is_exclusive(v___x_6399_);
if (v_isSharedCheck_6418_ == 0)
{
lean_object* v_unused_6419_; 
v_unused_6419_ = lean_ctor_get(v___x_6399_, 5);
lean_dec(v_unused_6419_);
v___x_6409_ = v___x_6399_;
v_isShared_6410_ = v_isSharedCheck_6418_;
goto v_resetjp_6408_;
}
else
{
lean_inc(v_snapshotTasks_6407_);
lean_inc(v_infoState_6406_);
lean_inc(v_messages_6405_);
lean_inc(v_traceState_6404_);
lean_inc(v_auxDeclNGen_6403_);
lean_inc(v_ngen_6402_);
lean_inc(v_nextMacroScope_6401_);
lean_inc(v_env_6400_);
lean_dec(v___x_6399_);
v___x_6409_ = lean_box(0);
v_isShared_6410_ = v_isSharedCheck_6418_;
goto v_resetjp_6408_;
}
v_resetjp_6408_:
{
lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6414_; 
lean_inc(v___y_6392_);
v___x_6411_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6390_, v_funVals_6398_, v___y_6392_, v___y_6392_, v_env_6400_);
lean_dec(v___y_6392_);
lean_dec_ref(v_funVals_6398_);
v___x_6412_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
if (v_isShared_6410_ == 0)
{
lean_ctor_set(v___x_6409_, 5, v___x_6412_);
lean_ctor_set(v___x_6409_, 0, v___x_6411_);
v___x_6414_ = v___x_6409_;
goto v_reusejp_6413_;
}
else
{
lean_object* v_reuseFailAlloc_6417_; 
v_reuseFailAlloc_6417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6417_, 0, v___x_6411_);
lean_ctor_set(v_reuseFailAlloc_6417_, 1, v_nextMacroScope_6401_);
lean_ctor_set(v_reuseFailAlloc_6417_, 2, v_ngen_6402_);
lean_ctor_set(v_reuseFailAlloc_6417_, 3, v_auxDeclNGen_6403_);
lean_ctor_set(v_reuseFailAlloc_6417_, 4, v_traceState_6404_);
lean_ctor_set(v_reuseFailAlloc_6417_, 5, v___x_6412_);
lean_ctor_set(v_reuseFailAlloc_6417_, 6, v_messages_6405_);
lean_ctor_set(v_reuseFailAlloc_6417_, 7, v_infoState_6406_);
lean_ctor_set(v_reuseFailAlloc_6417_, 8, v_snapshotTasks_6407_);
v___x_6414_ = v_reuseFailAlloc_6417_;
goto v_reusejp_6413_;
}
v_reusejp_6413_:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; 
v___x_6415_ = lean_st_ref_put(v_a_6387_, v___x_6414_);
v___x_6416_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6397_, v___y_6393_, v___y_6391_, v___y_6390_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec_ref(v_assignments_6397_);
return v___x_6416_;
}
}
}
else
{
lean_object* v_a_6420_; lean_object* v___x_6422_; uint8_t v_isShared_6423_; uint8_t v_isSharedCheck_6427_; 
lean_dec(v___y_6394_);
lean_dec(v___y_6392_);
lean_dec_ref(v___y_6390_);
v_a_6420_ = lean_ctor_get(v___y_6395_, 0);
v_isSharedCheck_6427_ = !lean_is_exclusive(v___y_6395_);
if (v_isSharedCheck_6427_ == 0)
{
v___x_6422_ = v___y_6395_;
v_isShared_6423_ = v_isSharedCheck_6427_;
goto v_resetjp_6421_;
}
else
{
lean_inc(v_a_6420_);
lean_dec(v___y_6395_);
v___x_6422_ = lean_box(0);
v_isShared_6423_ = v_isSharedCheck_6427_;
goto v_resetjp_6421_;
}
v_resetjp_6421_:
{
lean_object* v___x_6425_; 
if (v_isShared_6423_ == 0)
{
v___x_6425_ = v___x_6422_;
goto v_reusejp_6424_;
}
else
{
lean_object* v_reuseFailAlloc_6426_; 
v_reuseFailAlloc_6426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6426_, 0, v_a_6420_);
v___x_6425_ = v_reuseFailAlloc_6426_;
goto v_reusejp_6424_;
}
v_reusejp_6424_:
{
return v___x_6425_;
}
}
}
}
v___jp_6428_:
{
lean_object* v___x_6444_; double v___x_6445_; double v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6444_ = lean_io_get_num_heartbeats();
v___x_6445_ = lean_float_of_nat(v___y_6434_);
v___x_6446_ = lean_float_of_nat(v___x_6444_);
v___x_6447_ = lean_box_float(v___x_6445_);
v___x_6448_ = lean_box_float(v___x_6446_);
v___x_6449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6449_, 0, v___x_6447_);
lean_ctor_set(v___x_6449_, 1, v___x_6448_);
v___x_6450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6450_, 0, v_a_6443_);
lean_ctor_set(v___x_6450_, 1, v___x_6449_);
lean_inc_ref(v___y_6437_);
lean_inc(v___y_6430_);
v___x_6451_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6430_, v___y_6436_, v___y_6437_, v___y_6432_, v___y_6435_, v___y_6440_, v___y_6442_, v___x_6450_, v___y_6441_, v___y_6433_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec_ref(v___y_6441_);
v___y_6390_ = v___y_6429_;
v___y_6391_ = v___y_6438_;
v___y_6392_ = v___y_6431_;
v___y_6393_ = v___y_6439_;
v___y_6394_ = v___y_6433_;
v___y_6395_ = v___x_6451_;
goto v___jp_6389_;
}
v___jp_6452_:
{
lean_object* v___x_6468_; double v___x_6469_; double v___x_6470_; double v___x_6471_; double v___x_6472_; double v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6468_ = lean_io_mono_nanos_now();
v___x_6469_ = lean_float_of_nat(v___y_6462_);
v___x_6470_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__1);
v___x_6471_ = lean_float_div(v___x_6469_, v___x_6470_);
v___x_6472_ = lean_float_of_nat(v___x_6468_);
v___x_6473_ = lean_float_div(v___x_6472_, v___x_6470_);
v___x_6474_ = lean_box_float(v___x_6471_);
v___x_6475_ = lean_box_float(v___x_6473_);
v___x_6476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6476_, 0, v___x_6474_);
lean_ctor_set(v___x_6476_, 1, v___x_6475_);
v___x_6477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6477_, 0, v_a_6467_);
lean_ctor_set(v___x_6477_, 1, v___x_6476_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6454_);
v___x_6478_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6454_, v___y_6459_, v___y_6460_, v___y_6456_, v___y_6458_, v___y_6464_, v___y_6466_, v___x_6477_, v___y_6465_, v___y_6457_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec_ref(v___y_6465_);
v___y_6390_ = v___y_6453_;
v___y_6391_ = v___y_6461_;
v___y_6392_ = v___y_6455_;
v___y_6393_ = v___y_6463_;
v___y_6394_ = v___y_6457_;
v___y_6395_ = v___x_6478_;
goto v___jp_6389_;
}
v___jp_6480_:
{
lean_object* v___x_6493_; lean_object* v_a_6494_; lean_object* v___x_6495_; uint8_t v___x_6496_; 
v___x_6493_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_a_6387_);
v_a_6494_ = lean_ctor_get(v___x_6493_, 0);
lean_inc(v_a_6494_);
lean_dec_ref(v___x_6493_);
v___x_6495_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6496_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_6484_, v___x_6495_);
if (v___x_6496_ == 0)
{
lean_object* v___x_6497_; lean_object* v___x_6498_; 
v___x_6497_ = lean_io_mono_nanos_now();
v___x_6498_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6479_, v___y_6491_, v___y_6485_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
if (lean_obj_tag(v___x_6498_) == 0)
{
lean_object* v_a_6499_; lean_object* v___x_6501_; uint8_t v_isShared_6502_; uint8_t v_isSharedCheck_6506_; 
v_a_6499_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6506_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6506_ == 0)
{
v___x_6501_ = v___x_6498_;
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
else
{
lean_inc(v_a_6499_);
lean_dec(v___x_6498_);
v___x_6501_ = lean_box(0);
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
v_resetjp_6500_:
{
lean_object* v___x_6504_; 
if (v_isShared_6502_ == 0)
{
lean_ctor_set_tag(v___x_6501_, 1);
v___x_6504_ = v___x_6501_;
goto v_reusejp_6503_;
}
else
{
lean_object* v_reuseFailAlloc_6505_; 
v_reuseFailAlloc_6505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6505_, 0, v_a_6499_);
v___x_6504_ = v_reuseFailAlloc_6505_;
goto v_reusejp_6503_;
}
v_reusejp_6503_:
{
v___y_6453_ = v___y_6481_;
v___y_6454_ = v___y_6482_;
v___y_6455_ = v___y_6483_;
v___y_6456_ = v___y_6484_;
v___y_6457_ = v___y_6485_;
v___y_6458_ = v___y_6486_;
v___y_6459_ = v___y_6487_;
v___y_6460_ = v___y_6488_;
v___y_6461_ = v___y_6489_;
v___y_6462_ = v___x_6497_;
v___y_6463_ = v___y_6490_;
v___y_6464_ = v_a_6494_;
v___y_6465_ = v___y_6491_;
v___y_6466_ = v___y_6492_;
v_a_6467_ = v___x_6504_;
goto v___jp_6452_;
}
}
}
else
{
lean_object* v_a_6507_; lean_object* v___x_6509_; uint8_t v_isShared_6510_; uint8_t v_isSharedCheck_6514_; 
v_a_6507_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6514_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6514_ == 0)
{
v___x_6509_ = v___x_6498_;
v_isShared_6510_ = v_isSharedCheck_6514_;
goto v_resetjp_6508_;
}
else
{
lean_inc(v_a_6507_);
lean_dec(v___x_6498_);
v___x_6509_ = lean_box(0);
v_isShared_6510_ = v_isSharedCheck_6514_;
goto v_resetjp_6508_;
}
v_resetjp_6508_:
{
lean_object* v___x_6512_; 
if (v_isShared_6510_ == 0)
{
lean_ctor_set_tag(v___x_6509_, 0);
v___x_6512_ = v___x_6509_;
goto v_reusejp_6511_;
}
else
{
lean_object* v_reuseFailAlloc_6513_; 
v_reuseFailAlloc_6513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6513_, 0, v_a_6507_);
v___x_6512_ = v_reuseFailAlloc_6513_;
goto v_reusejp_6511_;
}
v_reusejp_6511_:
{
v___y_6453_ = v___y_6481_;
v___y_6454_ = v___y_6482_;
v___y_6455_ = v___y_6483_;
v___y_6456_ = v___y_6484_;
v___y_6457_ = v___y_6485_;
v___y_6458_ = v___y_6486_;
v___y_6459_ = v___y_6487_;
v___y_6460_ = v___y_6488_;
v___y_6461_ = v___y_6489_;
v___y_6462_ = v___x_6497_;
v___y_6463_ = v___y_6490_;
v___y_6464_ = v_a_6494_;
v___y_6465_ = v___y_6491_;
v___y_6466_ = v___y_6492_;
v_a_6467_ = v___x_6512_;
goto v___jp_6452_;
}
}
}
}
else
{
lean_object* v___x_6515_; lean_object* v___x_6516_; 
v___x_6515_ = lean_io_get_num_heartbeats();
v___x_6516_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6479_, v___y_6491_, v___y_6485_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
if (lean_obj_tag(v___x_6516_) == 0)
{
lean_object* v_a_6517_; lean_object* v___x_6519_; uint8_t v_isShared_6520_; uint8_t v_isSharedCheck_6524_; 
v_a_6517_ = lean_ctor_get(v___x_6516_, 0);
v_isSharedCheck_6524_ = !lean_is_exclusive(v___x_6516_);
if (v_isSharedCheck_6524_ == 0)
{
v___x_6519_ = v___x_6516_;
v_isShared_6520_ = v_isSharedCheck_6524_;
goto v_resetjp_6518_;
}
else
{
lean_inc(v_a_6517_);
lean_dec(v___x_6516_);
v___x_6519_ = lean_box(0);
v_isShared_6520_ = v_isSharedCheck_6524_;
goto v_resetjp_6518_;
}
v_resetjp_6518_:
{
lean_object* v___x_6522_; 
if (v_isShared_6520_ == 0)
{
lean_ctor_set_tag(v___x_6519_, 1);
v___x_6522_ = v___x_6519_;
goto v_reusejp_6521_;
}
else
{
lean_object* v_reuseFailAlloc_6523_; 
v_reuseFailAlloc_6523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6523_, 0, v_a_6517_);
v___x_6522_ = v_reuseFailAlloc_6523_;
goto v_reusejp_6521_;
}
v_reusejp_6521_:
{
v___y_6429_ = v___y_6481_;
v___y_6430_ = v___y_6482_;
v___y_6431_ = v___y_6483_;
v___y_6432_ = v___y_6484_;
v___y_6433_ = v___y_6485_;
v___y_6434_ = v___x_6515_;
v___y_6435_ = v___y_6486_;
v___y_6436_ = v___y_6487_;
v___y_6437_ = v___y_6488_;
v___y_6438_ = v___y_6489_;
v___y_6439_ = v___y_6490_;
v___y_6440_ = v_a_6494_;
v___y_6441_ = v___y_6491_;
v___y_6442_ = v___y_6492_;
v_a_6443_ = v___x_6522_;
goto v___jp_6428_;
}
}
}
else
{
lean_object* v_a_6525_; lean_object* v___x_6527_; uint8_t v_isShared_6528_; uint8_t v_isSharedCheck_6532_; 
v_a_6525_ = lean_ctor_get(v___x_6516_, 0);
v_isSharedCheck_6532_ = !lean_is_exclusive(v___x_6516_);
if (v_isSharedCheck_6532_ == 0)
{
v___x_6527_ = v___x_6516_;
v_isShared_6528_ = v_isSharedCheck_6532_;
goto v_resetjp_6526_;
}
else
{
lean_inc(v_a_6525_);
lean_dec(v___x_6516_);
v___x_6527_ = lean_box(0);
v_isShared_6528_ = v_isSharedCheck_6532_;
goto v_resetjp_6526_;
}
v_resetjp_6526_:
{
lean_object* v___x_6530_; 
if (v_isShared_6528_ == 0)
{
lean_ctor_set_tag(v___x_6527_, 0);
v___x_6530_ = v___x_6527_;
goto v_reusejp_6529_;
}
else
{
lean_object* v_reuseFailAlloc_6531_; 
v_reuseFailAlloc_6531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6531_, 0, v_a_6525_);
v___x_6530_ = v_reuseFailAlloc_6531_;
goto v_reusejp_6529_;
}
v_reusejp_6529_:
{
v___y_6429_ = v___y_6481_;
v___y_6430_ = v___y_6482_;
v___y_6431_ = v___y_6483_;
v___y_6432_ = v___y_6484_;
v___y_6433_ = v___y_6485_;
v___y_6434_ = v___x_6515_;
v___y_6435_ = v___y_6486_;
v___y_6436_ = v___y_6487_;
v___y_6437_ = v___y_6488_;
v___y_6438_ = v___y_6489_;
v___y_6439_ = v___y_6490_;
v___y_6440_ = v_a_6494_;
v___y_6441_ = v___y_6491_;
v___y_6442_ = v___y_6492_;
v_a_6443_ = v___x_6530_;
goto v___jp_6428_;
}
}
}
}
}
v___jp_6533_:
{
lean_object* v___f_6535_; size_t v_sz_6536_; size_t v___x_6537_; lean_object* v_assignments_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v_funVals_6541_; lean_object* v_ctx_6542_; lean_object* v_state_6543_; lean_object* v___x_6544_; uint8_t v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v_toCold_6548_; lean_object* v_options_6549_; uint8_t v_hasTrace_6550_; 
lean_inc_ref_n(v___y_6534_, 3);
v___f_6535_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6535_, 0, v___y_6534_);
v_sz_6536_ = lean_array_size(v___y_6534_);
v___x_6537_ = ((size_t)0ULL);
v_assignments_6538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6536_, v___x_6537_, v___y_6534_);
v___x_6539_ = lean_array_get_size(v___y_6534_);
v___x_6540_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2));
v_funVals_6541_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6534_, v___x_6539_, v___x_6539_, v___x_6540_);
v_ctx_6542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6542_, 0, v___y_6534_);
lean_ctor_set(v_ctx_6542_, 1, v___x_6479_);
v_state_6543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6543_, 0, v_assignments_6538_);
lean_ctor_set(v_state_6543_, 1, v_funVals_6541_);
v___x_6544_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6545_ = 1;
v___x_6546_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__4));
v___x_6547_ = lean_st_mk_ref(v_state_6543_);
v_toCold_6548_ = lean_ctor_get(v_a_6386_, 0);
v_options_6549_ = lean_ctor_get(v_toCold_6548_, 2);
v_hasTrace_6550_ = lean_ctor_get_uint8(v_options_6549_, sizeof(void*)*1);
if (v_hasTrace_6550_ == 0)
{
lean_object* v___x_6551_; 
lean_dec_ref(v___f_6535_);
v___x_6551_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6479_, v_ctx_6542_, v___x_6547_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec_ref_known(v_ctx_6542_, 2);
v___y_6390_ = v___y_6534_;
v___y_6391_ = v___x_6537_;
v___y_6392_ = v___x_6539_;
v___y_6393_ = v_sz_6536_;
v___y_6394_ = v___x_6547_;
v___y_6395_ = v___x_6551_;
goto v___jp_6389_;
}
else
{
lean_object* v_inheritedTraceOptions_6552_; lean_object* v___x_6553_; uint8_t v___x_6554_; 
v_inheritedTraceOptions_6552_ = lean_ctor_get(v_toCold_6548_, 11);
v___x_6553_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__7);
v___x_6554_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6552_, v_options_6549_, v___x_6553_);
if (v___x_6554_ == 0)
{
lean_object* v___x_6555_; uint8_t v___x_6556_; 
v___x_6555_ = l_Lean_trace_profiler;
v___x_6556_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v_options_6549_, v___x_6555_);
if (v___x_6556_ == 0)
{
lean_object* v___x_6557_; 
lean_dec_ref(v___f_6535_);
v___x_6557_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6479_, v_ctx_6542_, v___x_6547_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec_ref_known(v_ctx_6542_, 2);
v___y_6390_ = v___y_6534_;
v___y_6391_ = v___x_6537_;
v___y_6392_ = v___x_6539_;
v___y_6393_ = v_sz_6536_;
v___y_6394_ = v___x_6547_;
v___y_6395_ = v___x_6557_;
goto v___jp_6389_;
}
else
{
v___y_6481_ = v___y_6534_;
v___y_6482_ = v___x_6544_;
v___y_6483_ = v___x_6539_;
v___y_6484_ = v_options_6549_;
v___y_6485_ = v___x_6547_;
v___y_6486_ = v___x_6554_;
v___y_6487_ = v___x_6545_;
v___y_6488_ = v___x_6546_;
v___y_6489_ = v___x_6537_;
v___y_6490_ = v_sz_6536_;
v___y_6491_ = v_ctx_6542_;
v___y_6492_ = v___f_6535_;
goto v___jp_6480_;
}
}
else
{
v___y_6481_ = v___y_6534_;
v___y_6482_ = v___x_6544_;
v___y_6483_ = v___x_6539_;
v___y_6484_ = v_options_6549_;
v___y_6485_ = v___x_6547_;
v___y_6486_ = v___x_6554_;
v___y_6487_ = v___x_6545_;
v___y_6488_ = v___x_6546_;
v___y_6489_ = v___x_6537_;
v___y_6490_ = v_sz_6536_;
v___y_6491_ = v_ctx_6542_;
v___y_6492_ = v___f_6535_;
goto v___jp_6480_;
}
}
}
v___jp_6559_:
{
lean_object* v___x_6562_; 
v___x_6562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v___x_6558_, v_decls_6383_, v___y_6560_, v___y_6561_);
lean_dec(v___y_6561_);
v___y_6534_ = v___x_6562_;
goto v___jp_6533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_, lean_object* v_a_6575_){
_start:
{
lean_object* v_res_6576_; 
v_res_6576_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6570_, v_a_6571_, v_a_6572_, v_a_6573_, v_a_6574_);
lean_dec(v_a_6574_);
lean_dec_ref(v_a_6573_);
lean_dec(v_a_6572_);
lean_dec_ref(v_a_6571_);
return v_res_6576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6577_, lean_object* v_n_6578_, lean_object* v_j_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_){
_start:
{
lean_object* v___x_6582_; 
v___x_6582_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6577_, v_n_6578_, v_j_6579_, v_a_6581_);
return v___x_6582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6583_, lean_object* v_n_6584_, lean_object* v_j_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_){
_start:
{
lean_object* v_res_6588_; 
v_res_6588_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6583_, v_n_6584_, v_j_6585_, v_a_6586_, v_a_6587_);
lean_dec(v_n_6584_);
lean_dec_ref(v___y_6583_);
return v_res_6588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6589_, lean_object* v___x_6590_, lean_object* v_n_6591_, lean_object* v_j_6592_, lean_object* v_a_6593_, lean_object* v_a_6594_){
_start:
{
lean_object* v___x_6595_; 
v___x_6595_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6589_, v___x_6590_, v_n_6591_, v_j_6592_, v_a_6594_);
return v___x_6595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6596_, lean_object* v___x_6597_, lean_object* v_n_6598_, lean_object* v_j_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_){
_start:
{
lean_object* v_res_6602_; 
v_res_6602_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6596_, v___x_6597_, v_n_6598_, v_j_6599_, v_a_6600_, v_a_6601_);
lean_dec(v_n_6598_);
lean_dec_ref(v___x_6597_);
lean_dec_ref(v___y_6596_);
return v_res_6602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6603_, lean_object* v_as_6604_, size_t v_sz_6605_, size_t v_i_6606_, lean_object* v_bs_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_, lean_object* v___y_6611_){
_start:
{
lean_object* v___x_6613_; 
v___x_6613_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6603_, v_sz_6605_, v_i_6606_, v_bs_6607_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_);
return v___x_6613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6614_, lean_object* v_as_6615_, lean_object* v_sz_6616_, lean_object* v_i_6617_, lean_object* v_bs_6618_, lean_object* v___y_6619_, lean_object* v___y_6620_, lean_object* v___y_6621_, lean_object* v___y_6622_, lean_object* v___y_6623_){
_start:
{
size_t v_sz_boxed_6624_; size_t v_i_boxed_6625_; lean_object* v_res_6626_; 
v_sz_boxed_6624_ = lean_unbox_usize(v_sz_6616_);
lean_dec(v_sz_6616_);
v_i_boxed_6625_ = lean_unbox_usize(v_i_6617_);
lean_dec(v_i_6617_);
v_res_6626_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6614_, v_as_6615_, v_sz_boxed_6624_, v_i_boxed_6625_, v_bs_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec(v___y_6620_);
lean_dec_ref(v___y_6619_);
lean_dec_ref(v_as_6615_);
lean_dec_ref(v___x_6614_);
return v_res_6626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6627_, lean_object* v_as_6628_, lean_object* v_lo_6629_, lean_object* v_hi_6630_, lean_object* v_w_6631_, lean_object* v_hlo_6632_, lean_object* v_hhi_6633_){
_start:
{
lean_object* v___x_6634_; 
v___x_6634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_n_6627_, v_as_6628_, v_lo_6629_, v_hi_6630_);
return v___x_6634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6635_, lean_object* v_as_6636_, lean_object* v_lo_6637_, lean_object* v_hi_6638_, lean_object* v_w_6639_, lean_object* v_hlo_6640_, lean_object* v_hhi_6641_){
_start:
{
lean_object* v_res_6642_; 
v_res_6642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6635_, v_as_6636_, v_lo_6637_, v_hi_6638_, v_w_6639_, v_hlo_6640_, v_hhi_6641_);
lean_dec(v_hi_6638_);
lean_dec(v_n_6635_);
return v_res_6642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(lean_object* v_n_6643_, lean_object* v_lo_6644_, lean_object* v_hi_6645_, lean_object* v_hhi_6646_, lean_object* v_pivot_6647_, lean_object* v_as_6648_, lean_object* v_i_6649_, lean_object* v_k_6650_, lean_object* v_ilo_6651_, lean_object* v_ik_6652_, lean_object* v_w_6653_){
_start:
{
lean_object* v___x_6654_; 
v___x_6654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___redArg(v_hi_6645_, v_pivot_6647_, v_as_6648_, v_i_6649_, v_k_6650_);
return v___x_6654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5___boxed(lean_object* v_n_6655_, lean_object* v_lo_6656_, lean_object* v_hi_6657_, lean_object* v_hhi_6658_, lean_object* v_pivot_6659_, lean_object* v_as_6660_, lean_object* v_i_6661_, lean_object* v_k_6662_, lean_object* v_ilo_6663_, lean_object* v_ik_6664_, lean_object* v_w_6665_){
_start:
{
lean_object* v_res_6666_; 
v_res_6666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5_spec__5(v_n_6655_, v_lo_6656_, v_hi_6657_, v_hhi_6658_, v_pivot_6659_, v_as_6660_, v_i_6661_, v_k_6662_, v_ilo_6663_, v_ik_6664_, v_w_6665_);
lean_dec(v_hi_6657_);
lean_dec(v_lo_6656_);
lean_dec(v_n_6655_);
return v_res_6666_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; 
v___x_6726_ = lean_unsigned_to_nat(3955956072u);
v___x_6727_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6728_ = l_Lean_Name_num___override(v___x_6727_, v___x_6726_);
return v___x_6728_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; 
v___x_6730_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6731_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6732_ = l_Lean_Name_str___override(v___x_6731_, v___x_6730_);
return v___x_6732_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; 
v___x_6734_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6735_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6736_ = l_Lean_Name_str___override(v___x_6735_, v___x_6734_);
return v___x_6736_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
v___x_6737_ = lean_unsigned_to_nat(2u);
v___x_6738_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6739_ = l_Lean_Name_num___override(v___x_6738_, v___x_6737_);
return v___x_6739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6741_; uint8_t v___x_6742_; lean_object* v___x_6743_; lean_object* v___x_6744_; 
v___x_6741_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___redArg___closed__3));
v___x_6742_ = 1;
v___x_6743_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6744_ = l_Lean_registerTraceClass(v___x_6741_, v___x_6742_, v___x_6743_);
return v___x_6744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6745_){
_start:
{
lean_object* v_res_6746_; 
v_res_6746_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6746_;
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
