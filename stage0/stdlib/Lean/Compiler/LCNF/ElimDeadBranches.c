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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Format_join(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(uint8_t, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
uint8_t l_Prod_lexLtDec___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceFVars(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "UnreachableBranches"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "functionSummariesExt"};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 130, 135, 69, 155, 14, 96, 131)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 217, 249, 17, 195, 152, 212, 89)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Analyzing "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elimDeadBranches"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 80, 110, 205, 32, 43, 118, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Threw away cases "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " branch "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Compiler_LCNF_elimDeadBranches___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 204, 232, 255, 130, 130, 66, 205)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ElimDeadBranches"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 48, 204, 64, 9, 167, 133, 249)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(200, 150, 161, 93, 149, 239, 245, 119)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 115, 55, 70, 37, 185, 29, 189)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 112, 73, 71, 157, 233, 191, 127)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 232, 253, 11, 187, 111, 207, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 23, 231, 170, 231, 155, 87, 99)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 213, 22, 254, 230, 125, 90, 112)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 11, 80, 195, 104, 227, 74, 88)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 249, 148, 177, 5, 97, 125, 57)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 90, 29, 229, 248, 57, 61, 64)}};
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
lean_inc(v_vs_105_);
lean_dec_ref(v_x_89_);
v_vs_106_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_vs_106_);
lean_dec_ref(v_x_90_);
lean_inc(v_vs_106_);
lean_inc(v_vs_105_);
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
v___x_289_ = lean_panic_fn(v___x_288_, v_msg_276_);
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
v___x_389_ = lean_panic_fn(v___x_388_, v_msg_376_);
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
v___x_447_ = lean_panic_fn(v___x_446_, v_msg_445_);
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
lean_inc_ref(v_env_895_);
v___x_901_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_895_, v_head_899_, v_x_896_);
lean_inc_ref(v_env_895_);
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
v___x_947_ = lean_panic_fn(v___x_946_, v_msg_945_);
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
v___x_1978__overap_1025_ = lean_panic_fn(v___f_1024_, v_msg_988_);
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
lean_inc(v_pre_1192_);
lean_inc_ref(v_str_1193_);
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
v___y_1099_ = v___y_1156_;
v___y_1100_ = v___y_1157_;
v___y_1101_ = v___y_1154_;
v___y_1102_ = v___y_1155_;
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
v___y_1099_ = v___y_1156_;
v___y_1100_ = v___y_1157_;
v___y_1101_ = v___y_1154_;
v___y_1102_ = v___y_1155_;
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
v___y_1132_ = v___y_1156_;
v___y_1133_ = v___y_1157_;
v___y_1134_ = v___y_1154_;
v___y_1135_ = v___y_1155_;
v___y_1136_ = v_ctorName_1153_;
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
v___y_1132_ = v___y_1156_;
v___y_1133_ = v___y_1157_;
v___y_1134_ = v___y_1154_;
v___y_1135_ = v___y_1155_;
v___y_1136_ = v_ctorName_1153_;
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
v___x_1110_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1106_, v___x_1108_, v___x_1109_, v___y_1101_, v___y_1102_, v___y_1099_, v___y_1100_);
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
v___y_1102_ = v___y_1135_;
v___y_1103_ = v___y_1136_;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_es_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_array_mk(v_es_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1392_, lean_object* v_i_1393_, lean_object* v_k_1394_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1402_, lean_object* v_i_1403_, lean_object* v_k_1404_){
_start:
{
uint8_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1402_, v_i_1403_, v_k_1404_);
lean_dec(v_k_1404_);
lean_dec_ref(v_keys_1402_);
v_r_1406_ = lean_box(v_res_1405_);
return v_r_1406_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; 
v___x_1407_ = ((size_t)5ULL);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_shift_left(v___x_1408_, v___x_1407_);
return v___x_1409_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; 
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_1412_ = lean_usize_sub(v___x_1411_, v___x_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1413_, size_t v_x_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v_es_1416_; lean_object* v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; size_t v___x_1420_; lean_object* v_j_1421_; lean_object* v___x_1422_; 
v_es_1416_ = lean_ctor_get(v_x_1413_, 0);
lean_inc_ref(v_es_1416_);
lean_dec_ref(v_x_1413_);
v___x_1417_ = lean_box(2);
v___x_1418_ = ((size_t)5ULL);
v___x_1419_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1420_ = lean_usize_land(v_x_1414_, v___x_1419_);
v_j_1421_ = lean_usize_to_nat(v___x_1420_);
v___x_1422_ = lean_array_get(v___x_1417_, v_es_1416_, v_j_1421_);
lean_dec(v_j_1421_);
lean_dec_ref(v_es_1416_);
switch(lean_obj_tag(v___x_1422_))
{
case 0:
{
lean_object* v_key_1423_; uint8_t v___x_1424_; 
v_key_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_key_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_name_eq(v_x_1415_, v_key_1423_);
lean_dec(v_key_1423_);
return v___x_1424_;
}
case 1:
{
lean_object* v_node_1425_; size_t v___x_1426_; 
v_node_1425_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_node_1425_);
lean_dec_ref(v___x_1422_);
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
lean_inc_ref(v_ks_1429_);
lean_dec_ref(v_x_1413_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ks_1429_, v___x_1430_, v_x_1415_);
lean_dec_ref(v_ks_1429_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
size_t v_x_1122__boxed_1435_; uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_x_1122__boxed_1435_ = lean_unbox_usize(v_x_1433_);
lean_dec(v_x_1433_);
v_res_1436_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1432_, v_x_1122__boxed_1435_, v_x_1434_);
lean_dec(v_x_1434_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1438_; uint64_t v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1723u);
v___x_1439_ = lean_uint64_of_nat(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
uint64_t v___y_1443_; 
if (lean_obj_tag(v_x_1441_) == 0)
{
uint64_t v___x_1446_; 
v___x_1446_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
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
v___x_1445_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1440_, v___x_1444_, v_x_1441_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(v_x_1448_, v_x_1449_);
lean_dec(v_x_1449_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_x1_1452_, lean_object* v_x2_1453_){
_start:
{
lean_object* v_fst_1454_; uint8_t v___x_1455_; 
v_fst_1454_ = lean_ctor_get(v_x2_1453_, 0);
v___x_1455_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(v_x1_1452_, v_fst_1454_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_x1_1458_, lean_object* v_x2_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(v_x1_1458_, v_x2_1459_);
lean_dec_ref(v_x2_1459_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_fst_1464_; lean_object* v_fst_1465_; uint8_t v___x_1466_; 
v_fst_1464_ = lean_ctor_get(v___y_1462_, 0);
v_fst_1465_ = lean_ctor_get(v___y_1463_, 0);
v___x_1466_ = l_Lean_Name_quickLt(v_fst_1464_, v_fst_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_1467_, v___y_1468_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v___y_1467_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_1472_, lean_object* v_lo_1473_, lean_object* v_hi_1474_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_nat_dec_lt(v_lo_1473_, v_hi_1474_);
if (v___x_1475_ == 0)
{
lean_dec(v_lo_1473_);
return v_as_1472_;
}
else
{
lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; uint8_t v___x_1480_; 
v___f_1476_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_1473_);
v___x_1477_ = l_Array_qpartition___redArg(v_as_1472_, v___f_1476_, v_lo_1473_, v_hi_1474_);
v_fst_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_fst_1478_);
v_snd_1479_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_snd_1479_);
lean_dec_ref(v___x_1477_);
v___x_1480_ = lean_nat_dec_le(v_hi_1474_, v_fst_1478_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v_snd_1479_, v_lo_1473_, v_fst_1478_);
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_nat_add(v_fst_1478_, v___x_1482_);
lean_dec(v_fst_1478_);
v_as_1472_ = v___x_1481_;
v_lo_1473_ = v___x_1483_;
goto _start;
}
else
{
lean_dec(v_fst_1478_);
lean_dec(v_lo_1473_);
return v_snd_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_1485_, lean_object* v_lo_1486_, lean_object* v_hi_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v_as_1485_, v_lo_1486_, v_hi_1487_);
lean_dec(v_hi_1487_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1489_, lean_object* v_keys_1490_, lean_object* v_vals_1491_, lean_object* v_i_1492_, lean_object* v_acc_1493_){
_start:
{
lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = lean_array_get_size(v_keys_1490_);
v___x_1495_ = lean_nat_dec_lt(v_i_1492_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_dec(v_i_1492_);
lean_dec(v_f_1489_);
return v_acc_1493_;
}
else
{
lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_k_1496_ = lean_array_fget_borrowed(v_keys_1490_, v_i_1492_);
v_v_1497_ = lean_array_fget_borrowed(v_vals_1491_, v_i_1492_);
lean_inc(v_f_1489_);
lean_inc(v_v_1497_);
lean_inc(v_k_1496_);
v___x_1498_ = lean_apply_3(v_f_1489_, v_acc_1493_, v_k_1496_, v_v_1497_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_i_1492_, v___x_1499_);
lean_dec(v_i_1492_);
v_i_1492_ = v___x_1500_;
v_acc_1493_ = v___x_1498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1502_, lean_object* v_keys_1503_, lean_object* v_vals_1504_, lean_object* v_i_1505_, lean_object* v_acc_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1502_, v_keys_1503_, v_vals_1504_, v_i_1505_, v_acc_1506_);
lean_dec_ref(v_vals_1504_);
lean_dec_ref(v_keys_1503_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v_es_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_es_1511_ = lean_ctor_get(v_x_1509_, 0);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_array_get_size(v_es_1511_);
v___x_1514_ = lean_nat_dec_lt(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_dec(v_f_1508_);
return v_x_1510_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_nat_dec_le(v___x_1513_, v___x_1513_);
if (v___x_1515_ == 0)
{
if (v___x_1514_ == 0)
{
lean_dec(v_f_1508_);
return v_x_1510_;
}
else
{
size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_of_nat(v___x_1513_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1508_, v_es_1511_, v___x_1516_, v___x_1517_, v_x_1510_);
return v___x_1518_;
}
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1513_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1508_, v_es_1511_, v___x_1519_, v___x_1520_, v_x_1510_);
return v___x_1521_;
}
}
}
else
{
lean_object* v_ks_1522_; lean_object* v_vs_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_ks_1522_ = lean_ctor_get(v_x_1509_, 0);
v_vs_1523_ = lean_ctor_get(v_x_1509_, 1);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1508_, v_ks_1522_, v_vs_1523_, v___x_1524_, v_x_1510_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(lean_object* v_f_1526_, lean_object* v_as_1527_, size_t v_i_1528_, size_t v_stop_1529_, lean_object* v_b_1530_){
_start:
{
lean_object* v___y_1532_; uint8_t v___x_1536_; 
v___x_1536_ = lean_usize_dec_eq(v_i_1528_, v_stop_1529_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_array_uget_borrowed(v_as_1527_, v_i_1528_);
switch(lean_obj_tag(v___x_1537_))
{
case 0:
{
lean_object* v_key_1538_; lean_object* v_val_1539_; lean_object* v___x_1540_; 
v_key_1538_ = lean_ctor_get(v___x_1537_, 0);
v_val_1539_ = lean_ctor_get(v___x_1537_, 1);
lean_inc(v_f_1526_);
lean_inc(v_val_1539_);
lean_inc(v_key_1538_);
v___x_1540_ = lean_apply_3(v_f_1526_, v_b_1530_, v_key_1538_, v_val_1539_);
v___y_1532_ = v___x_1540_;
goto v___jp_1531_;
}
case 1:
{
lean_object* v_node_1541_; lean_object* v___x_1542_; 
v_node_1541_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_f_1526_);
v___x_1542_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1526_, v_node_1541_, v_b_1530_);
v___y_1532_ = v___x_1542_;
goto v___jp_1531_;
}
default: 
{
v___y_1532_ = v_b_1530_;
goto v___jp_1531_;
}
}
}
else
{
lean_dec(v_f_1526_);
return v_b_1530_;
}
v___jp_1531_:
{
size_t v___x_1533_; size_t v___x_1534_; 
v___x_1533_ = ((size_t)1ULL);
v___x_1534_ = lean_usize_add(v_i_1528_, v___x_1533_);
v_i_1528_ = v___x_1534_;
v_b_1530_ = v___y_1532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_f_1543_, lean_object* v_as_1544_, lean_object* v_i_1545_, lean_object* v_stop_1546_, lean_object* v_b_1547_){
_start:
{
size_t v_i_boxed_1548_; size_t v_stop_boxed_1549_; lean_object* v_res_1550_; 
v_i_boxed_1548_ = lean_unbox_usize(v_i_1545_);
lean_dec(v_i_1545_);
v_stop_boxed_1549_ = lean_unbox_usize(v_stop_1546_);
lean_dec(v_stop_1546_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1543_, v_as_1544_, v_i_boxed_1548_, v_stop_boxed_1549_, v_b_1547_);
lean_dec_ref(v_as_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1551_, v_x_1552_, v_x_1553_);
lean_dec_ref(v_x_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0(lean_object* v_f_1555_, lean_object* v_x1_1556_, lean_object* v_x2_1557_, lean_object* v_x3_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_apply_3(v_f_1555_, v_x1_1556_, v_x2_1557_, v_x3_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1560_, lean_object* v_f_1561_, lean_object* v_init_1562_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; 
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1563_, 0, v_f_1561_);
v___x_1564_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v___f_1563_, v_map_1560_, v_init_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1565_, lean_object* v_f_1566_, lean_object* v_init_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1565_, v_f_1566_, v_init_1567_);
lean_dec_ref(v_map_1565_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_ps_1569_, lean_object* v_k_1570_, lean_object* v_v_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_k_1570_);
lean_ctor_set(v___x_1572_, 1, v_v_1571_);
v___x_1573_ = lean_array_push(v_ps_1569_, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_1577_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___f_1578_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1579_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___closed__1));
v___x_1580_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_1577_, v___f_1578_, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(v_m_1581_);
lean_dec_ref(v_m_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_x_1585_, lean_object* v_s_1586_, lean_object* v_x_1587_, uint8_t v_x_1588_){
_start:
{
if (v_x_1588_ == 2)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1589_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(v_s_1586_);
v___x_1590_ = lean_array_get_size(v___x_1589_);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_nat_dec_eq(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___y_1596_; uint8_t v___x_1600_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_sub(v___x_1590_, v___x_1593_);
v___x_1600_ = lean_nat_dec_le(v___x_1591_, v___x_1594_);
if (v___x_1600_ == 0)
{
lean_inc(v___x_1594_);
v___y_1596_ = v___x_1594_;
goto v___jp_1595_;
}
else
{
v___y_1596_ = v___x_1591_;
goto v___jp_1595_;
}
v___jp_1595_:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_nat_dec_le(v___y_1596_, v___x_1594_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec(v___x_1594_);
lean_inc(v___y_1596_);
v___x_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v___x_1589_, v___y_1596_, v___y_1596_);
lean_dec(v___y_1596_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v___x_1589_, v___y_1596_, v___x_1594_);
lean_dec(v___x_1594_);
return v___x_1599_;
}
}
}
else
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_));
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_x_1602_, lean_object* v_s_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
uint8_t v_x_1342__boxed_1606_; lean_object* v_res_1607_; 
v_x_1342__boxed_1606_ = lean_unbox(v_x_1605_);
v_res_1607_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__2_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(v_x_1602_, v_s_1603_, v_x_1604_, v_x_1342__boxed_1606_);
lean_dec(v_x_1604_);
lean_dec_ref(v_s_1603_);
lean_dec_ref(v_x_1602_);
return v_res_1607_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__0_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_, &l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3___closed__1_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_x_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__3_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(v_x_1613_);
lean_dec_ref(v_x_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v_ks_1619_; lean_object* v_vs_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1644_; 
v_ks_1619_ = lean_ctor_get(v_x_1615_, 0);
v_vs_1620_ = lean_ctor_get(v_x_1615_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1622_ = v_x_1615_;
v_isShared_1623_ = v_isSharedCheck_1644_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_vs_1620_);
lean_inc(v_ks_1619_);
lean_dec(v_x_1615_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1644_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = lean_array_get_size(v_ks_1619_);
v___x_1625_ = lean_nat_dec_lt(v_x_1616_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_x_1616_);
v___x_1626_ = lean_array_push(v_ks_1619_, v_x_1617_);
v___x_1627_ = lean_array_push(v_vs_1620_, v_x_1618_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1627_);
lean_ctor_set(v___x_1622_, 0, v___x_1626_);
v___x_1629_ = v___x_1622_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v_k_x27_1631_; uint8_t v___x_1632_; 
v_k_x27_1631_ = lean_array_fget_borrowed(v_ks_1619_, v_x_1616_);
v___x_1632_ = lean_name_eq(v_x_1617_, v_k_x27_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1634_; 
if (v_isShared_1623_ == 0)
{
v___x_1634_ = v___x_1622_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_ks_1619_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_vs_1620_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_x_1616_, v___x_1635_);
lean_dec(v_x_1616_);
v_x_1615_ = v___x_1634_;
v_x_1616_ = v___x_1636_;
goto _start;
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1639_ = lean_array_fset(v_ks_1619_, v_x_1616_, v_x_1617_);
v___x_1640_ = lean_array_fset(v_vs_1620_, v_x_1616_, v_x_1618_);
lean_dec(v_x_1616_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1640_);
lean_ctor_set(v___x_1622_, 0, v___x_1639_);
v___x_1642_ = v___x_1622_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object* v_n_1645_, lean_object* v_k_1646_, lean_object* v_v_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(v_n_1645_, v___x_1648_, v_k_1646_, v_v_1647_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_1651_, size_t v_x_1652_, size_t v_x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 0)
{
lean_object* v_es_1656_; size_t v___x_1657_; size_t v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; lean_object* v_j_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_es_1656_ = lean_ctor_get(v_x_1651_, 0);
v___x_1657_ = ((size_t)5ULL);
v___x_1658_ = ((size_t)1ULL);
v___x_1659_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1660_ = lean_usize_land(v_x_1652_, v___x_1659_);
v_j_1661_ = lean_usize_to_nat(v___x_1660_);
v___x_1662_ = lean_array_get_size(v_es_1656_);
v___x_1663_ = lean_nat_dec_lt(v_j_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_dec(v_j_1661_);
lean_dec(v_x_1655_);
lean_dec(v_x_1654_);
return v_x_1651_;
}
else
{
lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1700_; 
lean_inc_ref(v_es_1656_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_x_1651_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v_x_1651_, 0);
lean_dec(v_unused_1701_);
v___x_1665_ = v_x_1651_;
v_isShared_1666_ = v_isSharedCheck_1700_;
goto v_resetjp_1664_;
}
else
{
lean_dec(v_x_1651_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1700_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_v_1667_; lean_object* v___x_1668_; lean_object* v_xs_x27_1669_; lean_object* v___y_1671_; 
v_v_1667_ = lean_array_fget(v_es_1656_, v_j_1661_);
v___x_1668_ = lean_box(0);
v_xs_x27_1669_ = lean_array_fset(v_es_1656_, v_j_1661_, v___x_1668_);
switch(lean_obj_tag(v_v_1667_))
{
case 0:
{
lean_object* v_key_1676_; lean_object* v_val_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1687_; 
v_key_1676_ = lean_ctor_get(v_v_1667_, 0);
v_val_1677_ = lean_ctor_get(v_v_1667_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_v_1667_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1679_ = v_v_1667_;
v_isShared_1680_ = v_isSharedCheck_1687_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_val_1677_);
lean_inc(v_key_1676_);
lean_dec(v_v_1667_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1687_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
uint8_t v___x_1681_; 
v___x_1681_ = lean_name_eq(v_x_1654_, v_key_1676_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_del_object(v___x_1679_);
v___x_1682_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1676_, v_val_1677_, v_x_1654_, v_x_1655_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
v___y_1671_ = v___x_1683_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1685_; 
lean_dec(v_val_1677_);
lean_dec(v_key_1676_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v_x_1655_);
lean_ctor_set(v___x_1679_, 0, v_x_1654_);
v___x_1685_ = v___x_1679_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_x_1654_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_x_1655_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v___y_1671_ = v___x_1685_;
goto v___jp_1670_;
}
}
}
}
case 1:
{
lean_object* v_node_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1698_; 
v_node_1688_ = lean_ctor_get(v_v_1667_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_v_1667_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1690_ = v_v_1667_;
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_node_1688_);
lean_dec(v_v_1667_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1692_ = lean_usize_shift_right(v_x_1652_, v___x_1657_);
v___x_1693_ = lean_usize_add(v_x_1653_, v___x_1658_);
v___x_1694_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_1688_, v___x_1692_, v___x_1693_, v_x_1654_, v_x_1655_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1694_);
v___x_1696_ = v___x_1690_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
v___y_1671_ = v___x_1696_;
goto v___jp_1670_;
}
}
}
default: 
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_x_1654_);
lean_ctor_set(v___x_1699_, 1, v_x_1655_);
v___y_1671_ = v___x_1699_;
goto v___jp_1670_;
}
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = lean_array_fset(v_xs_x27_1669_, v_j_1661_, v___y_1671_);
lean_dec(v_j_1661_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1672_);
v___x_1674_ = v___x_1665_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_object* v_ks_1702_; lean_object* v_vs_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1723_; 
v_ks_1702_ = lean_ctor_get(v_x_1651_, 0);
v_vs_1703_ = lean_ctor_get(v_x_1651_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_x_1651_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1705_ = v_x_1651_;
v_isShared_1706_ = v_isSharedCheck_1723_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_vs_1703_);
lean_inc(v_ks_1702_);
lean_dec(v_x_1651_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1723_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_ks_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_vs_1703_);
v___x_1708_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v_newNode_1709_; uint8_t v___y_1711_; size_t v___x_1717_; uint8_t v___x_1718_; 
v_newNode_1709_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v___x_1708_, v_x_1654_, v_x_1655_);
v___x_1717_ = ((size_t)7ULL);
v___x_1718_ = lean_usize_dec_le(v___x_1717_, v_x_1653_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1719_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1709_);
v___x_1720_ = lean_unsigned_to_nat(4u);
v___x_1721_ = lean_nat_dec_lt(v___x_1719_, v___x_1720_);
lean_dec(v___x_1719_);
v___y_1711_ = v___x_1721_;
goto v___jp_1710_;
}
else
{
v___y_1711_ = v___x_1718_;
goto v___jp_1710_;
}
v___jp_1710_:
{
if (v___y_1711_ == 0)
{
lean_object* v_ks_1712_; lean_object* v_vs_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_ks_1712_ = lean_ctor_get(v_newNode_1709_, 0);
lean_inc_ref(v_ks_1712_);
v_vs_1713_ = lean_ctor_get(v_newNode_1709_, 1);
lean_inc_ref(v_vs_1713_);
lean_dec_ref(v_newNode_1709_);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_1716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_x_1653_, v_ks_1712_, v_vs_1713_, v___x_1714_, v___x_1715_);
lean_dec_ref(v_vs_1713_);
lean_dec_ref(v_ks_1712_);
return v___x_1716_;
}
else
{
return v_newNode_1709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(size_t v_depth_1724_, lean_object* v_keys_1725_, lean_object* v_vals_1726_, lean_object* v_i_1727_, lean_object* v_entries_1728_){
_start:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = lean_array_get_size(v_keys_1725_);
v___x_1730_ = lean_nat_dec_lt(v_i_1727_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_dec(v_i_1727_);
return v_entries_1728_;
}
else
{
lean_object* v_k_1731_; lean_object* v_v_1732_; uint64_t v___y_1734_; 
v_k_1731_ = lean_array_fget_borrowed(v_keys_1725_, v_i_1727_);
v_v_1732_ = lean_array_fget_borrowed(v_vals_1726_, v_i_1727_);
if (lean_obj_tag(v_k_1731_) == 0)
{
uint64_t v___x_1745_; 
v___x_1745_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1734_ = v___x_1745_;
goto v___jp_1733_;
}
else
{
uint64_t v_hash_1746_; 
v_hash_1746_ = lean_ctor_get_uint64(v_k_1731_, sizeof(void*)*2);
v___y_1734_ = v_hash_1746_;
goto v___jp_1733_;
}
v___jp_1733_:
{
size_t v_h_1735_; size_t v___x_1736_; lean_object* v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v_h_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_h_1735_ = lean_uint64_to_usize(v___y_1734_);
v___x_1736_ = ((size_t)5ULL);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_sub(v_depth_1724_, v___x_1738_);
v___x_1740_ = lean_usize_mul(v___x_1736_, v___x_1739_);
v_h_1741_ = lean_usize_shift_right(v_h_1735_, v___x_1740_);
v___x_1742_ = lean_nat_add(v_i_1727_, v___x_1737_);
lean_dec(v_i_1727_);
lean_inc(v_v_1732_);
lean_inc(v_k_1731_);
v___x_1743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_1728_, v_h_1741_, v_depth_1724_, v_k_1731_, v_v_1732_);
v_i_1727_ = v___x_1742_;
v_entries_1728_ = v___x_1743_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_1747_, lean_object* v_keys_1748_, lean_object* v_vals_1749_, lean_object* v_i_1750_, lean_object* v_entries_1751_){
_start:
{
size_t v_depth_boxed_1752_; lean_object* v_res_1753_; 
v_depth_boxed_1752_ = lean_unbox_usize(v_depth_1747_);
lean_dec(v_depth_1747_);
v_res_1753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_depth_boxed_1752_, v_keys_1748_, v_vals_1749_, v_i_1750_, v_entries_1751_);
lean_dec_ref(v_vals_1749_);
lean_dec_ref(v_keys_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
size_t v_x_1479__boxed_1759_; size_t v_x_1480__boxed_1760_; lean_object* v_res_1761_; 
v_x_1479__boxed_1759_ = lean_unbox_usize(v_x_1755_);
lean_dec(v_x_1755_);
v_x_1480__boxed_1760_ = lean_unbox_usize(v_x_1756_);
lean_dec(v_x_1756_);
v_res_1761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1754_, v_x_1479__boxed_1759_, v_x_1480__boxed_1760_, v_x_1757_, v_x_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint64_t v___y_1766_; 
if (lean_obj_tag(v_x_1763_) == 0)
{
uint64_t v___x_1770_; 
v___x_1770_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_1766_ = v___x_1770_;
goto v___jp_1765_;
}
else
{
uint64_t v_hash_1771_; 
v_hash_1771_ = lean_ctor_get_uint64(v_x_1763_, sizeof(void*)*2);
v___y_1766_ = v_hash_1771_;
goto v___jp_1765_;
}
v___jp_1765_:
{
size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_uint64_to_usize(v___y_1766_);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1762_, v___x_1767_, v___x_1768_, v_x_1763_, v_x_1764_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn___lam__4_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(lean_object* v_s_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v_fst_1774_; lean_object* v_snd_1775_; lean_object* v___x_1776_; 
v_fst_1774_ = lean_ctor_get(v_x_1773_, 0);
lean_inc(v_fst_1774_);
v_snd_1775_ = lean_ctor_get(v_x_1773_, 1);
lean_inc(v_snd_1775_);
lean_dec_ref(v_x_1773_);
v___x_1776_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(v_s_1772_, v_fst_1774_, v_snd_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_));
v___x_1810_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2____boxed(lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_();
return v_res_1812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg(v_x_1814_, v_x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_res_1820_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0(v_00_u03b2_1817_, v_x_1818_, v_x_1819_);
lean_dec(v_x_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1822_, lean_object* v_m_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___redArg(v_m_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1825_, lean_object* v_m_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1(v_00_u03b2_1825_, v_m_1826_);
lean_dec_ref(v_m_1826_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2(lean_object* v_n_1828_, lean_object* v_as_1829_, lean_object* v_lo_1830_, lean_object* v_hi_1831_, lean_object* v_w_1832_, lean_object* v_hlo_1833_, lean_object* v_hhi_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg(v_as_1829_, v_lo_1830_, v_hi_1831_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_1836_, lean_object* v_as_1837_, lean_object* v_lo_1838_, lean_object* v_hi_1839_, lean_object* v_w_1840_, lean_object* v_hlo_1841_, lean_object* v_hhi_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2(v_n_1836_, v_as_1837_, v_lo_1838_, v_hi_1839_, v_w_1840_, v_hlo_1841_, v_hhi_1842_);
lean_dec(v_hi_1839_);
lean_dec(v_n_1836_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3___redArg(v_x_1845_, v_x_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1849_, lean_object* v_x_1850_, size_t v_x_1851_, lean_object* v_x_1852_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1850_, v_x_1851_, v_x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
size_t v_x_1786__boxed_1858_; uint8_t v_res_1859_; lean_object* v_r_1860_; 
v_x_1786__boxed_1858_ = lean_unbox_usize(v_x_1856_);
lean_dec(v_x_1856_);
v_res_1859_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_1854_, v_x_1855_, v_x_1786__boxed_1858_, v_x_1857_);
lean_dec(v_x_1857_);
v_r_1860_ = lean_box(v_res_1859_);
return v_r_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_map_1863_, lean_object* v_f_1864_, lean_object* v_init_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1863_, v_f_1864_, v_init_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_map_1869_, lean_object* v_f_1870_, lean_object* v_init_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1867_, v_00_u03b2_1868_, v_map_1869_, v_f_1870_, v_init_1871_);
lean_dec_ref(v_map_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_1873_, lean_object* v_x_1874_, size_t v_x_1875_, size_t v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_1874_, v_x_1875_, v_x_1876_, v_x_1877_, v_x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
size_t v_x_1799__boxed_1886_; size_t v_x_1800__boxed_1887_; lean_object* v_res_1888_; 
v_x_1799__boxed_1886_ = lean_unbox_usize(v_x_1882_);
lean_dec(v_x_1882_);
v_x_1800__boxed_1887_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_res_1888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_1880_, v_x_1881_, v_x_1799__boxed_1886_, v_x_1800__boxed_1887_, v_x_1884_, v_x_1885_);
return v_res_1888_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1889_, lean_object* v_keys_1890_, lean_object* v_vals_1891_, lean_object* v_heq_1892_, lean_object* v_i_1893_, lean_object* v_k_1894_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_keys_1890_, v_i_1893_, v_k_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1896_, lean_object* v_keys_1897_, lean_object* v_vals_1898_, lean_object* v_heq_1899_, lean_object* v_i_1900_, lean_object* v_k_1901_){
_start:
{
uint8_t v_res_1902_; lean_object* v_r_1903_; 
v_res_1902_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1896_, v_keys_1897_, v_vals_1898_, v_heq_1899_, v_i_1900_, v_k_1901_);
lean_dec(v_k_1901_);
lean_dec_ref(v_vals_1898_);
lean_dec_ref(v_keys_1897_);
v_r_1903_ = lean_box(v_res_1902_);
return v_r_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_map_1904_, lean_object* v_f_1905_, lean_object* v_init_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1905_, v_map_1904_, v_init_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_map_1908_, lean_object* v_f_1909_, lean_object* v_init_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_map_1908_, v_f_1909_, v_init_1910_);
lean_dec_ref(v_map_1908_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1912_, lean_object* v_00_u03b2_1913_, lean_object* v_map_1914_, lean_object* v_f_1915_, lean_object* v_init_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1915_, v_map_1914_, v_init_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_map_1920_, lean_object* v_f_1921_, lean_object* v_init_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03c3_1918_, v_00_u03b2_1919_, v_map_1920_, v_f_1921_, v_init_1922_);
lean_dec_ref(v_map_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1924_, lean_object* v_n_1925_, lean_object* v_k_1926_, lean_object* v_v_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_n_1925_, v_k_1926_, v_v_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1929_, size_t v_depth_1930_, lean_object* v_keys_1931_, lean_object* v_vals_1932_, lean_object* v_heq_1933_, lean_object* v_i_1934_, lean_object* v_entries_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___redArg(v_depth_1930_, v_keys_1931_, v_vals_1932_, v_i_1934_, v_entries_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1937_, lean_object* v_depth_1938_, lean_object* v_keys_1939_, lean_object* v_vals_1940_, lean_object* v_heq_1941_, lean_object* v_i_1942_, lean_object* v_entries_1943_){
_start:
{
size_t v_depth_boxed_1944_; lean_object* v_res_1945_; 
v_depth_boxed_1944_ = lean_unbox_usize(v_depth_1938_);
lean_dec(v_depth_1938_);
v_res_1945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__9(v_00_u03b2_1937_, v_depth_boxed_1944_, v_keys_1939_, v_vals_1940_, v_heq_1941_, v_i_1942_, v_entries_1943_);
lean_dec_ref(v_vals_1940_);
lean_dec_ref(v_keys_1939_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_1946_, lean_object* v_00_u03b1_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_f_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___redArg(v_f_1949_, v_x_1950_, v_x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_1953_, lean_object* v_00_u03b1_1954_, lean_object* v_00_u03b2_1955_, lean_object* v_f_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7(v_00_u03c3_1953_, v_00_u03b1_1954_, v_00_u03b2_1955_, v_f_1956_, v_x_1957_, v_x_1958_);
lean_dec_ref(v_x_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__10___redArg(v_x_1961_, v_x_1962_, v_x_1963_, v_x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_00_u03c3_1968_, lean_object* v_f_1969_, lean_object* v_as_1970_, size_t v_i_1971_, size_t v_stop_1972_, lean_object* v_b_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___redArg(v_f_1969_, v_as_1970_, v_i_1971_, v_stop_1972_, v_b_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_00_u03c3_1977_, lean_object* v_f_1978_, lean_object* v_as_1979_, lean_object* v_i_1980_, lean_object* v_stop_1981_, lean_object* v_b_1982_){
_start:
{
size_t v_i_boxed_1983_; size_t v_stop_boxed_1984_; lean_object* v_res_1985_; 
v_i_boxed_1983_ = lean_unbox_usize(v_i_1980_);
lean_dec(v_i_1980_);
v_stop_boxed_1984_ = lean_unbox_usize(v_stop_1981_);
lean_dec(v_stop_1981_);
v_res_1985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__9(v_00_u03b1_1975_, v_00_u03b2_1976_, v_00_u03c3_1977_, v_f_1978_, v_as_1979_, v_i_boxed_1983_, v_stop_boxed_1984_, v_b_1982_);
lean_dec_ref(v_as_1979_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(lean_object* v_00_u03c3_1986_, lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_f_1989_, lean_object* v_keys_1990_, lean_object* v_vals_1991_, lean_object* v_heq_1992_, lean_object* v_i_1993_, lean_object* v_acc_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___redArg(v_f_1989_, v_keys_1990_, v_vals_1991_, v_i_1993_, v_acc_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03c3_1996_, lean_object* v_00_u03b1_1997_, lean_object* v_00_u03b2_1998_, lean_object* v_f_1999_, lean_object* v_keys_2000_, lean_object* v_vals_2001_, lean_object* v_heq_2002_, lean_object* v_i_2003_, lean_object* v_acc_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__7_spec__10(v_00_u03c3_1996_, v_00_u03b1_1997_, v_00_u03b2_1998_, v_f_1999_, v_keys_2000_, v_vals_2001_, v_heq_2002_, v_i_2003_, v_acc_2004_);
lean_dec_ref(v_vals_2001_);
lean_dec_ref(v_keys_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(lean_object* v_env_2006_, lean_object* v_fid_2007_, lean_object* v_v_2008_){
_start:
{
lean_object* v___x_2009_; lean_object* v_toEnvExtension_2010_; lean_object* v_asyncMode_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2009_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v_toEnvExtension_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc_ref(v_toEnvExtension_2010_);
v_asyncMode_2011_ = lean_ctor_get(v_toEnvExtension_2010_, 2);
lean_inc(v_asyncMode_2011_);
lean_dec_ref(v_toEnvExtension_2010_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_fid_2007_);
lean_ctor_set(v___x_2012_, 1, v_v_2008_);
v___x_2013_ = lean_box(0);
v___x_2014_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2009_, v_env_2006_, v___x_2012_, v_asyncMode_2011_, v___x_2013_);
lean_dec(v_asyncMode_2011_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2015_, lean_object* v_vals_2016_, lean_object* v_i_2017_, lean_object* v_k_2018_){
_start:
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = lean_array_get_size(v_keys_2015_);
v___x_2020_ = lean_nat_dec_lt(v_i_2017_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v_i_2017_);
v___x_2021_ = lean_box(0);
return v___x_2021_;
}
else
{
lean_object* v_k_x27_2022_; uint8_t v___x_2023_; 
v_k_x27_2022_ = lean_array_fget_borrowed(v_keys_2015_, v_i_2017_);
v___x_2023_ = lean_name_eq(v_k_2018_, v_k_x27_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_add(v_i_2017_, v___x_2024_);
lean_dec(v_i_2017_);
v_i_2017_ = v___x_2025_;
goto _start;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_array_fget_borrowed(v_vals_2016_, v_i_2017_);
lean_dec(v_i_2017_);
lean_inc(v___x_2027_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2029_, lean_object* v_vals_2030_, lean_object* v_i_2031_, lean_object* v_k_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2029_, v_vals_2030_, v_i_2031_, v_k_2032_);
lean_dec(v_k_2032_);
lean_dec_ref(v_vals_2030_);
lean_dec_ref(v_keys_2029_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(lean_object* v_x_2034_, size_t v_x_2035_, lean_object* v_x_2036_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v_es_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2058_; 
v_es_2037_ = lean_ctor_get(v_x_2034_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_2034_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2039_ = v_x_2034_;
v_isShared_2040_ = v_isSharedCheck_2058_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_es_2037_);
lean_dec(v_x_2034_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2058_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; size_t v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; lean_object* v_j_2045_; lean_object* v___x_2046_; 
v___x_2041_ = lean_box(2);
v___x_2042_ = ((size_t)5ULL);
v___x_2043_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_2044_ = lean_usize_land(v_x_2035_, v___x_2043_);
v_j_2045_ = lean_usize_to_nat(v___x_2044_);
v___x_2046_ = lean_array_get(v___x_2041_, v_es_2037_, v_j_2045_);
lean_dec(v_j_2045_);
lean_dec_ref(v_es_2037_);
switch(lean_obj_tag(v___x_2046_))
{
case 0:
{
lean_object* v_key_2047_; lean_object* v_val_2048_; uint8_t v___x_2049_; 
v_key_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_key_2047_);
v_val_2048_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_val_2048_);
lean_dec_ref(v___x_2046_);
v___x_2049_ = lean_name_eq(v_x_2036_, v_key_2047_);
lean_dec(v_key_2047_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec(v_val_2048_);
lean_del_object(v___x_2039_);
v___x_2050_ = lean_box(0);
return v___x_2050_;
}
else
{
lean_object* v___x_2052_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set_tag(v___x_2039_, 1);
lean_ctor_set(v___x_2039_, 0, v_val_2048_);
v___x_2052_ = v___x_2039_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_val_2048_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
case 1:
{
lean_object* v_node_2054_; size_t v___x_2055_; 
lean_del_object(v___x_2039_);
v_node_2054_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_node_2054_);
lean_dec_ref(v___x_2046_);
v___x_2055_ = lean_usize_shift_right(v_x_2035_, v___x_2042_);
v_x_2034_ = v_node_2054_;
v_x_2035_ = v___x_2055_;
goto _start;
}
default: 
{
lean_object* v___x_2057_; 
lean_del_object(v___x_2039_);
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_ks_2059_; lean_object* v_vs_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_ks_2059_ = lean_ctor_get(v_x_2034_, 0);
lean_inc_ref(v_ks_2059_);
v_vs_2060_ = lean_ctor_get(v_x_2034_, 1);
lean_inc_ref(v_vs_2060_);
lean_dec_ref(v_x_2034_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2059_, v_vs_2060_, v___x_2061_, v_x_2036_);
lean_dec_ref(v_vs_2060_);
lean_dec_ref(v_ks_2059_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
size_t v_x_396__boxed_2066_; lean_object* v_res_2067_; 
v_x_396__boxed_2066_ = lean_unbox_usize(v_x_2064_);
lean_dec(v_x_2064_);
v_res_2067_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2063_, v_x_396__boxed_2066_, v_x_2065_);
lean_dec(v_x_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
uint64_t v___y_2071_; 
if (lean_obj_tag(v_x_2069_) == 0)
{
uint64_t v___x_2074_; 
v___x_2074_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___y_2071_ = v___x_2074_;
goto v___jp_2070_;
}
else
{
uint64_t v_hash_2075_; 
v_hash_2075_ = lean_ctor_get_uint64(v_x_2069_, sizeof(void*)*2);
v___y_2071_ = v_hash_2075_;
goto v___jp_2070_;
}
v___jp_2070_:
{
size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_uint64_to_usize(v___y_2071_);
v___x_2073_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2068_, v___x_2072_, v_x_2069_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* v_x_2076_, lean_object* v_x_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2076_, v_x_2077_);
lean_dec(v_x_2077_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(lean_object* v_as_2079_, lean_object* v_k_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_m_2085_; lean_object* v_a_2086_; uint8_t v___x_2087_; 
v___x_2083_ = lean_nat_add(v_x_2081_, v_x_2082_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v_m_2085_ = lean_nat_shiftr(v___x_2083_, v___x_2084_);
lean_dec(v___x_2083_);
v_a_2086_ = lean_array_fget_borrowed(v_as_2079_, v_m_2085_);
v___x_2087_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_2086_, v_k_2080_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; 
lean_dec(v_x_2082_);
v___x_2088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_2080_, v_a_2086_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v_m_2085_);
lean_dec(v_x_2081_);
lean_inc(v_a_2086_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_a_2086_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_nat_dec_eq(v_m_2085_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = lean_nat_sub(v_m_2085_, v___x_2084_);
lean_dec(v_m_2085_);
v___x_2093_ = lean_nat_dec_lt(v___x_2092_, v_x_2081_);
if (v___x_2093_ == 0)
{
v_x_2082_ = v___x_2092_;
goto _start;
}
else
{
lean_object* v___x_2095_; 
lean_dec(v___x_2092_);
lean_dec(v_x_2081_);
v___x_2095_ = lean_box(0);
return v___x_2095_;
}
}
else
{
lean_object* v___x_2096_; 
lean_dec(v_m_2085_);
lean_dec(v_x_2081_);
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
}
}
else
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
lean_dec(v_x_2081_);
v___x_2097_ = lean_nat_add(v_m_2085_, v___x_2084_);
lean_dec(v_m_2085_);
v___x_2098_ = lean_nat_dec_le(v___x_2097_, v_x_2082_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
lean_dec(v___x_2097_);
lean_dec(v_x_2082_);
v___x_2099_ = lean_box(0);
return v___x_2099_;
}
else
{
v_x_2081_ = v___x_2097_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg___boxed(lean_object* v_as_2101_, lean_object* v_k_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2101_, v_k_2102_, v_x_2103_, v_x_2104_);
lean_dec_ref(v_k_2102_);
lean_dec_ref(v_as_2101_);
return v_res_2105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__1));
v___x_2109_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__0));
v___x_2110_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2109_, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__2);
v___x_2112_ = lean_box(0);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___x_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(lean_object* v_env_2114_, lean_object* v_fid_2115_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2125_; 
v___x_2116_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f___closed__3);
v___x_2117_ = l_Lean_Compiler_LCNF_UnreachableBranches_functionSummariesExt;
v___x_2125_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2114_, v_fid_2115_);
if (lean_obj_tag(v___x_2125_) == 0)
{
goto v___jp_2118_;
}
else
{
lean_object* v_val_2126_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_val_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2126_);
lean_dec_ref(v___x_2125_);
v___x_2148_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_2116_, v___x_2117_, v_env_2114_, v_val_2126_);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = lean_array_get_size(v___x_2148_);
v___x_2151_ = lean_nat_dec_lt(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec_ref(v___x_2148_);
goto v___jp_2127_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2152_ = lean_unsigned_to_nat(1u);
v___x_2153_ = lean_nat_sub(v___x_2150_, v___x_2152_);
v___x_2154_ = lean_nat_dec_le(v___x_2149_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_dec(v___x_2153_);
lean_dec_ref(v___x_2148_);
goto v___jp_2127_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(0);
lean_inc(v_fid_2115_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v_fid_2115_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2148_, v___x_2156_, v___x_2149_, v___x_2153_);
lean_dec_ref(v___x_2156_);
lean_dec_ref(v___x_2148_);
if (lean_obj_tag(v___x_2157_) == 0)
{
goto v___jp_2127_;
}
else
{
lean_object* v_val_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_val_2126_);
lean_dec(v_fid_2115_);
lean_dec_ref(v_env_2114_);
v_val_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_val_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_snd_2162_; lean_object* v___x_2164_; 
v_snd_2162_ = lean_ctor_get(v_val_2158_, 1);
lean_inc(v_snd_2162_);
lean_dec(v_val_2158_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v_snd_2162_);
v___x_2164_ = v___x_2160_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_snd_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
v___jp_2127_:
{
uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2128_ = 0;
v___x_2129_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2116_, v___x_2117_, v_env_2114_, v_val_2126_, v___x_2128_);
lean_dec(v_val_2126_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_array_get_size(v___x_2129_);
v___x_2132_ = lean_nat_dec_lt(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_dec_ref(v___x_2129_);
goto v___jp_2118_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_sub(v___x_2131_, v___x_2133_);
v___x_2135_ = lean_nat_dec_le(v___x_2130_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_dec(v___x_2134_);
lean_dec_ref(v___x_2129_);
goto v___jp_2118_;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = lean_box(0);
lean_inc(v_fid_2115_);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v_fid_2115_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v___x_2129_, v___x_2137_, v___x_2130_, v___x_2134_);
lean_dec_ref(v___x_2137_);
lean_dec_ref(v___x_2129_);
if (lean_obj_tag(v___x_2138_) == 0)
{
goto v___jp_2118_;
}
else
{
lean_object* v_val_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_fid_2115_);
lean_dec_ref(v_env_2114_);
v_val_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_val_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2147_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_snd_2143_; lean_object* v___x_2145_; 
v_snd_2143_ = lean_ctor_get(v_val_2139_, 1);
lean_inc(v_snd_2143_);
lean_dec(v_val_2139_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v_snd_2143_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_snd_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
}
}
v___jp_2118_:
{
lean_object* v_toEnvExtension_2119_; lean_object* v_asyncMode_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_snd_2123_; lean_object* v___x_2124_; 
v_toEnvExtension_2119_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_ref(v_toEnvExtension_2119_);
v_asyncMode_2120_ = lean_ctor_get(v_toEnvExtension_2119_, 2);
lean_inc(v_asyncMode_2120_);
lean_dec_ref(v_toEnvExtension_2119_);
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2116_, v___x_2117_, v_env_2114_, v_asyncMode_2120_, v___x_2121_);
lean_dec(v_asyncMode_2120_);
v_snd_2123_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_snd_2123_);
lean_dec(v___x_2122_);
v___x_2124_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_snd_2123_, v_fid_2115_);
lean_dec(v_fid_2115_);
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* v_00_u03b2_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(v_x_2168_, v_x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* v_00_u03b2_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0(v_00_u03b2_2171_, v_x_2172_, v_x_2173_);
lean_dec(v_x_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(lean_object* v_as_2175_, lean_object* v_k_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___redArg(v_as_2175_, v_k_2176_, v_x_2177_, v_x_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1___boxed(lean_object* v_as_2181_, lean_object* v_k_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__1(v_as_2181_, v_k_2182_, v_x_2183_, v_x_2184_, v_x_2185_);
lean_dec_ref(v_k_2182_);
lean_dec_ref(v_as_2181_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2187_, lean_object* v_x_2188_, size_t v_x_2189_, lean_object* v_x_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___redArg(v_x_2188_, v_x_2189_, v_x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
size_t v_x_649__boxed_2196_; lean_object* v_res_2197_; 
v_x_649__boxed_2196_ = lean_unbox_usize(v_x_2194_);
lean_dec(v_x_2194_);
v_res_2197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0(v_00_u03b2_2192_, v_x_2193_, v_x_649__boxed_2196_, v_x_2195_);
lean_dec(v_x_2195_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2198_, lean_object* v_keys_2199_, lean_object* v_vals_2200_, lean_object* v_heq_2201_, lean_object* v_i_2202_, lean_object* v_k_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2199_, v_vals_2200_, v_i_2202_, v_k_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_keys_2206_, lean_object* v_vals_2207_, lean_object* v_heq_2208_, lean_object* v_i_2209_, lean_object* v_k_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2205_, v_keys_2206_, v_vals_2207_, v_heq_2208_, v_i_2209_, v_k_2210_);
lean_dec(v_k_2210_);
lean_dec_ref(v_vals_2207_);
lean_dec_ref(v_keys_2206_);
return v_res_2211_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__1));
v___x_2215_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__0));
v___x_2216_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2220_; lean_object* v_assignments_2221_; lean_object* v_currFnIdx_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2220_ = lean_st_ref_get(v_a_2218_);
v_assignments_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc_ref(v_assignments_2221_);
lean_dec(v___x_2220_);
v_currFnIdx_2222_ = lean_ctor_get(v_a_2217_, 1);
v___x_2223_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_2224_ = lean_array_get(v___x_2223_, v_assignments_2221_, v_currFnIdx_2222_);
lean_dec_ref(v_assignments_2221_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___boxed(lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2226_, v_a_2227_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2230_, v_a_2231_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___boxed(lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment(v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(lean_object* v_funIdx_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v_funVals_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2249_ = lean_st_ref_get(v_a_2247_);
v_funVals_2250_ = lean_ctor_get(v___x_2249_, 1);
lean_inc_ref(v_funVals_2250_);
lean_dec(v___x_2249_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_array_get(v___x_2251_, v_funVals_2250_, v_funIdx_2246_);
lean_dec_ref(v_funVals_2250_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg___boxed(lean_object* v_funIdx_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2254_, v_a_2255_);
lean_dec(v_a_2255_);
lean_dec(v_funIdx_2254_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(lean_object* v_funIdx_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_funIdx_2258_, v_a_2260_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___boxed(lean_object* v_funIdx_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal(v_funIdx_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_funIdx_2267_);
return v_res_2275_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0(lean_object* v_declName_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v_toSignature_2278_; lean_object* v_name_2279_; uint8_t v___x_2280_; 
v_toSignature_2278_ = lean_ctor_get(v_x_2277_, 0);
v_name_2279_ = lean_ctor_get(v_toSignature_2278_, 0);
v___x_2280_ = lean_name_eq(v_name_2279_, v_declName_2276_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0___boxed(lean_object* v_declName_2281_, lean_object* v_x_2282_){
_start:
{
uint8_t v_res_2283_; lean_object* v_r_2284_; 
v_res_2283_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0(v_declName_2281_, v_x_2282_);
lean_dec_ref(v_x_2282_);
lean_dec(v_declName_2281_);
v_r_2284_ = lean_box(v_res_2283_);
return v_r_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(lean_object* v_declName_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_decls_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_decls_2289_ = lean_ctor_get(v_a_2286_, 0);
v___f_2290_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2290_, 0, v_declName_2285_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = l_Array_findIdx_x3f_loop___redArg(v___f_2290_, v_decls_2289_, v___x_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
else
{
lean_object* v_val_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2311_; 
v_val_2295_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2297_ = v___x_2292_;
v_isShared_2298_ = v_isSharedCheck_2311_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_val_2295_);
lean_dec(v___x_2292_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2311_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2310_; 
v___x_2299_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_val_2295_, v_a_2287_);
lean_dec(v_val_2295_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_a_2300_);
v___x_2305_ = v___x_2297_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2305_);
v___x_2307_ = v___x_2302_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg___boxed(lean_object* v_declName_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(lean_object* v_declName_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_2317_, v_a_2318_, v_a_2319_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___boxed(lean_object* v_declName_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f(v_declName_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(lean_object* v_f_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2339_; lean_object* v_currFnIdx_2340_; lean_object* v_assignments_2341_; lean_object* v_funVals_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2360_; 
v___x_2339_ = lean_st_ref_take(v_a_2337_);
v_currFnIdx_2340_ = lean_ctor_get(v_a_2336_, 1);
v_assignments_2341_ = lean_ctor_get(v___x_2339_, 0);
v_funVals_2342_ = lean_ctor_get(v___x_2339_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2344_ = v___x_2339_;
v_isShared_2345_ = v_isSharedCheck_2360_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_funVals_2342_);
lean_inc(v_assignments_2341_);
lean_dec(v___x_2339_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2360_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___y_2348_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2346_ = lean_box(0);
v___x_2354_ = lean_array_get_size(v_assignments_2341_);
v___x_2355_ = lean_nat_dec_lt(v_currFnIdx_2340_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v_f_2335_);
v___y_2348_ = v_assignments_2341_;
goto v___jp_2347_;
}
else
{
lean_object* v_v_2356_; lean_object* v_xs_x27_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_v_2356_ = lean_array_fget(v_assignments_2341_, v_currFnIdx_2340_);
v_xs_x27_2357_ = lean_array_fset(v_assignments_2341_, v_currFnIdx_2340_, v___x_2346_);
v___x_2358_ = lean_apply_1(v_f_2335_, v_v_2356_);
v___x_2359_ = lean_array_fset(v_xs_x27_2357_, v_currFnIdx_2340_, v___x_2358_);
v___y_2348_ = v___x_2359_;
goto v___jp_2347_;
}
v___jp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___y_2348_);
v___x_2350_ = v___x_2344_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___y_2348_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_funVals_2342_);
v___x_2350_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_st_ref_set(v_a_2337_, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2346_);
return v___x_2352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg___boxed(lean_object* v_f_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(lean_object* v_f_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v_f_2366_, v_a_2367_, v_a_2368_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___boxed(lean_object* v_f_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment(v_f_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(lean_object* v_a_2384_, lean_object* v_fallback_2385_, lean_object* v_x_2386_){
_start:
{
if (lean_obj_tag(v_x_2386_) == 0)
{
lean_inc(v_fallback_2385_);
return v_fallback_2385_;
}
else
{
lean_object* v_key_2387_; lean_object* v_value_2388_; lean_object* v_tail_2389_; uint8_t v___x_2390_; 
v_key_2387_ = lean_ctor_get(v_x_2386_, 0);
v_value_2388_ = lean_ctor_get(v_x_2386_, 1);
v_tail_2389_ = lean_ctor_get(v_x_2386_, 2);
v___x_2390_ = l_Lean_instBEqFVarId_beq(v_key_2387_, v_a_2384_);
if (v___x_2390_ == 0)
{
v_x_2386_ = v_tail_2389_;
goto _start;
}
else
{
lean_inc(v_value_2388_);
return v_value_2388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_a_2392_, lean_object* v_fallback_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2392_, v_fallback_2393_, v_x_2394_);
lean_dec(v_x_2394_);
lean_dec(v_fallback_2393_);
lean_dec(v_a_2392_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* v_m_2396_, lean_object* v_a_2397_, lean_object* v_fallback_2398_){
_start:
{
lean_object* v_buckets_2399_; lean_object* v___x_2400_; uint64_t v___x_2401_; uint64_t v___x_2402_; uint64_t v___x_2403_; uint64_t v_fold_2404_; uint64_t v___x_2405_; uint64_t v___x_2406_; uint64_t v___x_2407_; size_t v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_buckets_2399_ = lean_ctor_get(v_m_2396_, 1);
v___x_2400_ = lean_array_get_size(v_buckets_2399_);
v___x_2401_ = l_Lean_instHashableFVarId_hash(v_a_2397_);
v___x_2402_ = 32ULL;
v___x_2403_ = lean_uint64_shift_right(v___x_2401_, v___x_2402_);
v_fold_2404_ = lean_uint64_xor(v___x_2401_, v___x_2403_);
v___x_2405_ = 16ULL;
v___x_2406_ = lean_uint64_shift_right(v_fold_2404_, v___x_2405_);
v___x_2407_ = lean_uint64_xor(v_fold_2404_, v___x_2406_);
v___x_2408_ = lean_uint64_to_usize(v___x_2407_);
v___x_2409_ = lean_usize_of_nat(v___x_2400_);
v___x_2410_ = ((size_t)1ULL);
v___x_2411_ = lean_usize_sub(v___x_2409_, v___x_2410_);
v___x_2412_ = lean_usize_land(v___x_2408_, v___x_2411_);
v___x_2413_ = lean_array_uget_borrowed(v_buckets_2399_, v___x_2412_);
v___x_2414_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2397_, v_fallback_2398_, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* v_m_2415_, lean_object* v_a_2416_, lean_object* v_fallback_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2415_, v_a_2416_, v_fallback_2417_);
lean_dec(v_fallback_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_m_2415_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(lean_object* v_var_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2423_; lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2433_; 
v___x_2423_ = l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg(v_a_2420_, v_a_2421_);
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2433_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2433_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2428_ = lean_box(0);
v___x_2429_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_a_2424_, v_var_2419_, v___x_2428_);
lean_dec(v_a_2424_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2429_);
v___x_2431_ = v___x_2426_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg___boxed(lean_object* v_var_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_var_2434_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(lean_object* v_var_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2439_, v_a_2440_, v_a_2441_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___boxed(lean_object* v_var_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue(v_var_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_var_2448_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(lean_object* v_00_u03b2_2457_, lean_object* v_m_2458_, lean_object* v_a_2459_, lean_object* v_fallback_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_m_2458_, v_a_2459_, v_fallback_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* v_00_u03b2_2462_, lean_object* v_m_2463_, lean_object* v_a_2464_, lean_object* v_fallback_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0(v_00_u03b2_2462_, v_m_2463_, v_a_2464_, v_fallback_2465_);
lean_dec(v_fallback_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_m_2463_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(lean_object* v_00_u03b2_2467_, lean_object* v_a_2468_, lean_object* v_fallback_2469_, lean_object* v_x_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___redArg(v_a_2468_, v_fallback_2469_, v_x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2472_, lean_object* v_a_2473_, lean_object* v_fallback_2474_, lean_object* v_x_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0_spec__0(v_00_u03b2_2472_, v_a_2473_, v_fallback_2474_, v_x_2475_);
lean_dec(v_x_2475_);
lean_dec(v_fallback_2474_);
lean_dec(v_a_2473_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(lean_object* v_arg_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
if (lean_obj_tag(v_arg_2477_) == 1)
{
lean_object* v_fvarId_2481_; lean_object* v___x_2482_; 
v_fvarId_2481_ = lean_ctor_get(v_arg_2477_, 0);
v___x_2482_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2481_, v_a_2478_, v_a_2479_);
return v___x_2482_;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_box(1);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg___boxed(lean_object* v_arg_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_arg_2485_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(lean_object* v_arg_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_arg_2490_, v_a_2491_, v_a_2492_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___boxed(lean_object* v_arg_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue(v_arg_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_arg_2499_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(lean_object* v_a_2508_, lean_object* v_b_2509_, lean_object* v_x_2510_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
lean_dec(v_b_2509_);
lean_dec(v_a_2508_);
return v_x_2510_;
}
else
{
lean_object* v_key_2511_; lean_object* v_value_2512_; lean_object* v_tail_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2525_; 
v_key_2511_ = lean_ctor_get(v_x_2510_, 0);
v_value_2512_ = lean_ctor_get(v_x_2510_, 1);
v_tail_2513_ = lean_ctor_get(v_x_2510_, 2);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_x_2510_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2515_ = v_x_2510_;
v_isShared_2516_ = v_isSharedCheck_2525_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_tail_2513_);
lean_inc(v_value_2512_);
lean_inc(v_key_2511_);
lean_dec(v_x_2510_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2525_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
uint8_t v___x_2517_; 
v___x_2517_ = l_Lean_instBEqFVarId_beq(v_key_2511_, v_a_2508_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2508_, v_b_2509_, v_tail_2513_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 2, v___x_2518_);
v___x_2520_ = v___x_2515_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_key_2511_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_value_2512_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
else
{
lean_object* v___x_2523_; 
lean_dec(v_value_2512_);
lean_dec(v_key_2511_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 1, v_b_2509_);
lean_ctor_set(v___x_2515_, 0, v_a_2508_);
v___x_2523_ = v___x_2515_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2508_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_b_2509_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_tail_2513_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
return v_x_2526_;
}
else
{
lean_object* v_key_2528_; lean_object* v_value_2529_; lean_object* v_tail_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2553_; 
v_key_2528_ = lean_ctor_get(v_x_2527_, 0);
v_value_2529_ = lean_ctor_get(v_x_2527_, 1);
v_tail_2530_ = lean_ctor_get(v_x_2527_, 2);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_x_2527_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2532_ = v_x_2527_;
v_isShared_2533_ = v_isSharedCheck_2553_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_tail_2530_);
lean_inc(v_value_2529_);
lean_inc(v_key_2528_);
lean_dec(v_x_2527_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2553_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; uint64_t v___x_2535_; uint64_t v___x_2536_; uint64_t v___x_2537_; uint64_t v_fold_2538_; uint64_t v___x_2539_; uint64_t v___x_2540_; uint64_t v___x_2541_; size_t v___x_2542_; size_t v___x_2543_; size_t v___x_2544_; size_t v___x_2545_; size_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2534_ = lean_array_get_size(v_x_2526_);
v___x_2535_ = l_Lean_instHashableFVarId_hash(v_key_2528_);
v___x_2536_ = 32ULL;
v___x_2537_ = lean_uint64_shift_right(v___x_2535_, v___x_2536_);
v_fold_2538_ = lean_uint64_xor(v___x_2535_, v___x_2537_);
v___x_2539_ = 16ULL;
v___x_2540_ = lean_uint64_shift_right(v_fold_2538_, v___x_2539_);
v___x_2541_ = lean_uint64_xor(v_fold_2538_, v___x_2540_);
v___x_2542_ = lean_uint64_to_usize(v___x_2541_);
v___x_2543_ = lean_usize_of_nat(v___x_2534_);
v___x_2544_ = ((size_t)1ULL);
v___x_2545_ = lean_usize_sub(v___x_2543_, v___x_2544_);
v___x_2546_ = lean_usize_land(v___x_2542_, v___x_2545_);
v___x_2547_ = lean_array_uget_borrowed(v_x_2526_, v___x_2546_);
lean_inc(v___x_2547_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 2, v___x_2547_);
v___x_2549_ = v___x_2532_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_key_2528_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_value_2529_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_array_uset(v_x_2526_, v___x_2546_, v___x_2549_);
v_x_2526_ = v___x_2550_;
v_x_2527_ = v_tail_2530_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2554_, lean_object* v_source_2555_, lean_object* v_target_2556_){
_start:
{
lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = lean_array_get_size(v_source_2555_);
v___x_2558_ = lean_nat_dec_lt(v_i_2554_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_dec_ref(v_source_2555_);
lean_dec(v_i_2554_);
return v_target_2556_;
}
else
{
lean_object* v_es_2559_; lean_object* v___x_2560_; lean_object* v_source_2561_; lean_object* v_target_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_es_2559_ = lean_array_fget(v_source_2555_, v_i_2554_);
v___x_2560_ = lean_box(0);
v_source_2561_ = lean_array_fset(v_source_2555_, v_i_2554_, v___x_2560_);
v_target_2562_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2556_, v_es_2559_);
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = lean_nat_add(v_i_2554_, v___x_2563_);
lean_dec(v_i_2554_);
v_i_2554_ = v___x_2564_;
v_source_2555_ = v_source_2561_;
v_target_2556_ = v_target_2562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(lean_object* v_data_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_nbuckets_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2567_ = lean_array_get_size(v_data_2566_);
v___x_2568_ = lean_unsigned_to_nat(2u);
v_nbuckets_2569_ = lean_nat_mul(v___x_2567_, v___x_2568_);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_mk_array(v_nbuckets_2569_, v___x_2571_);
v___x_2573_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v___x_2570_, v_data_2566_, v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(lean_object* v_a_2574_, lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2575_) == 0)
{
uint8_t v___x_2576_; 
v___x_2576_ = 0;
return v___x_2576_;
}
else
{
lean_object* v_key_2577_; lean_object* v_tail_2578_; uint8_t v___x_2579_; 
v_key_2577_ = lean_ctor_get(v_x_2575_, 0);
v_tail_2578_ = lean_ctor_get(v_x_2575_, 2);
v___x_2579_ = l_Lean_instBEqFVarId_beq(v_key_2577_, v_a_2574_);
if (v___x_2579_ == 0)
{
v_x_2575_ = v_tail_2578_;
goto _start;
}
else
{
return v___x_2579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_a_2581_, lean_object* v_x_2582_){
_start:
{
uint8_t v_res_2583_; lean_object* v_r_2584_; 
v_res_2583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2581_, v_x_2582_);
lean_dec(v_x_2582_);
lean_dec(v_a_2581_);
v_r_2584_ = lean_box(v_res_2583_);
return v_r_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* v_m_2585_, lean_object* v_a_2586_, lean_object* v_b_2587_){
_start:
{
lean_object* v_size_2588_; lean_object* v_buckets_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2632_; 
v_size_2588_ = lean_ctor_get(v_m_2585_, 0);
v_buckets_2589_ = lean_ctor_get(v_m_2585_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_m_2585_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2591_ = v_m_2585_;
v_isShared_2592_ = v_isSharedCheck_2632_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_buckets_2589_);
lean_inc(v_size_2588_);
lean_dec(v_m_2585_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2632_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; uint64_t v___x_2594_; uint64_t v___x_2595_; uint64_t v___x_2596_; uint64_t v_fold_2597_; uint64_t v___x_2598_; uint64_t v___x_2599_; uint64_t v___x_2600_; size_t v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; lean_object* v_bkt_2606_; uint8_t v___x_2607_; 
v___x_2593_ = lean_array_get_size(v_buckets_2589_);
v___x_2594_ = l_Lean_instHashableFVarId_hash(v_a_2586_);
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
v_bkt_2606_ = lean_array_uget_borrowed(v_buckets_2589_, v___x_2605_);
v___x_2607_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2586_, v_bkt_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v_size_x27_2609_; lean_object* v___x_2610_; lean_object* v_buckets_x27_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2608_ = lean_unsigned_to_nat(1u);
v_size_x27_2609_ = lean_nat_add(v_size_2588_, v___x_2608_);
lean_dec(v_size_2588_);
lean_inc(v_bkt_2606_);
v___x_2610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2610_, 0, v_a_2586_);
lean_ctor_set(v___x_2610_, 1, v_b_2587_);
lean_ctor_set(v___x_2610_, 2, v_bkt_2606_);
v_buckets_x27_2611_ = lean_array_uset(v_buckets_2589_, v___x_2605_, v___x_2610_);
v___x_2612_ = lean_unsigned_to_nat(4u);
v___x_2613_ = lean_nat_mul(v_size_x27_2609_, v___x_2612_);
v___x_2614_ = lean_unsigned_to_nat(3u);
v___x_2615_ = lean_nat_div(v___x_2613_, v___x_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_array_get_size(v_buckets_x27_2611_);
v___x_2617_ = lean_nat_dec_le(v___x_2615_, v___x_2616_);
lean_dec(v___x_2615_);
if (v___x_2617_ == 0)
{
lean_object* v_val_2618_; lean_object* v___x_2620_; 
v_val_2618_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_buckets_x27_2611_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v_val_2618_);
lean_ctor_set(v___x_2591_, 0, v_size_x27_2609_);
v___x_2620_ = v___x_2591_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_size_x27_2609_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_val_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2623_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v_buckets_x27_2611_);
lean_ctor_set(v___x_2591_, 0, v_size_x27_2609_);
v___x_2623_ = v___x_2591_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_size_x27_2609_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_buckets_x27_2611_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v_buckets_x27_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_inc(v_bkt_2606_);
v___x_2625_ = lean_box(0);
v_buckets_x27_2626_ = lean_array_uset(v_buckets_2589_, v___x_2605_, v___x_2625_);
v___x_2627_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2586_, v_b_2587_, v_bkt_2606_);
v___x_2628_ = lean_array_uset(v_buckets_x27_2626_, v___x_2605_, v___x_2627_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2628_);
v___x_2630_ = v___x_2591_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_size_2588_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0(lean_object* v_var_2633_, lean_object* v___x_2634_, lean_object* v_x_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2635_, v_var_2633_, v___x_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(lean_object* v_var_2637_, lean_object* v_newVal_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_st_ref_get(v_a_2641_);
v___x_2644_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_var_2637_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v_env_2646_; lean_object* v___x_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2644_);
v_env_2646_ = lean_ctor_get(v___x_2643_, 0);
lean_inc_ref(v_env_2646_);
lean_dec(v___x_2643_);
v___x_2647_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2646_, v_a_2645_, v_newVal_2638_);
v___f_2648_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2648_, 0, v_var_2637_);
lean_closure_set(v___f_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2648_, v_a_2639_, v_a_2640_);
return v___x_2649_;
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v___x_2643_);
lean_dec(v_newVal_2638_);
lean_dec(v_var_2637_);
v_a_2650_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2644_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2644_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg___boxed(lean_object* v_var_2658_, lean_object* v_newVal_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2658_, v_newVal_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(lean_object* v_var_2665_, lean_object* v_newVal_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_var_2665_, v_newVal_2666_, v_a_2667_, v_a_2668_, v_a_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___boxed(lean_object* v_var_2675_, lean_object* v_newVal_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment(v_var_2675_, v_newVal_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0(lean_object* v_00_u03b2_2685_, lean_object* v_m_2686_, lean_object* v_a_2687_, lean_object* v_b_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_m_2686_, v_a_2687_, v_b_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(lean_object* v_00_u03b2_2690_, lean_object* v_a_2691_, lean_object* v_x_2692_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___redArg(v_a_2691_, v_x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2694_, lean_object* v_a_2695_, lean_object* v_x_2696_){
_start:
{
uint8_t v_res_2697_; lean_object* v_r_2698_; 
v_res_2697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__0(v_00_u03b2_2694_, v_a_2695_, v_x_2696_);
lean_dec(v_x_2696_);
lean_dec(v_a_2695_);
v_r_2698_ = lean_box(v_res_2697_);
return v_r_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1(lean_object* v_00_u03b2_2699_, lean_object* v_data_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1___redArg(v_data_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2(lean_object* v_00_u03b2_2702_, lean_object* v_a_2703_, lean_object* v_b_2704_, lean_object* v_x_2705_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__2___redArg(v_a_2703_, v_b_2704_, v_x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2707_, lean_object* v_i_2708_, lean_object* v_source_2709_, lean_object* v_target_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2___redArg(v_i_2708_, v_source_2709_, v_target_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2713_, v_x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0(lean_object* v_var_2716_, lean_object* v_x_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_box(0);
v___x_2719_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2717_, v_var_2716_, v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(lean_object* v_var_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v___f_2724_; lean_object* v___x_2725_; 
v___f_2724_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2724_, 0, v_var_2720_);
v___x_2725_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2724_, v_a_2721_, v_a_2722_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg___boxed(lean_object* v_var_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(lean_object* v_var_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_var_2731_, v_a_2732_, v_a_2733_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___boxed(lean_object* v_var_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment(v_var_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(lean_object* v_v_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v_fst_2757_; lean_object* v_snd_2758_; lean_object* v_currFnIdx_2761_; lean_object* v_assignments_2762_; lean_object* v_funVals_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2754_ = lean_st_ref_get(v_a_2752_);
v___x_2755_ = lean_st_ref_take(v_a_2751_);
v_currFnIdx_2761_ = lean_ctor_get(v_a_2750_, 1);
v_assignments_2762_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_ref(v_assignments_2762_);
v_funVals_2763_ = lean_ctor_get(v___x_2755_, 1);
lean_inc_ref(v_funVals_2763_);
v___x_2764_ = lean_box(0);
v___x_2765_ = lean_array_get_size(v_funVals_2763_);
v___x_2766_ = lean_nat_dec_lt(v_currFnIdx_2761_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_dec_ref(v_funVals_2763_);
lean_dec_ref(v_assignments_2762_);
lean_dec(v___x_2754_);
lean_dec(v_v_2749_);
v_fst_2757_ = v___x_2764_;
v_snd_2758_ = v___x_2755_;
goto v___jp_2756_;
}
else
{
lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2778_; 
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; lean_object* v_unused_2780_; 
v_unused_2779_ = lean_ctor_get(v___x_2755_, 1);
lean_dec(v_unused_2779_);
v_unused_2780_ = lean_ctor_get(v___x_2755_, 0);
lean_dec(v_unused_2780_);
v___x_2768_ = v___x_2755_;
v_isShared_2769_ = v_isSharedCheck_2778_;
goto v_resetjp_2767_;
}
else
{
lean_dec(v___x_2755_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2778_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_env_2770_; lean_object* v_v_2771_; lean_object* v_xs_x27_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v_env_2770_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_ref(v_env_2770_);
lean_dec(v___x_2754_);
v_v_2771_ = lean_array_fget(v_funVals_2763_, v_currFnIdx_2761_);
v_xs_x27_2772_ = lean_array_fset(v_funVals_2763_, v_currFnIdx_2761_, v___x_2764_);
v___x_2773_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v_env_2770_, v_v_2749_, v_v_2771_);
v___x_2774_ = lean_array_fset(v_xs_x27_2772_, v_currFnIdx_2761_, v___x_2773_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v___x_2774_);
v___x_2776_ = v___x_2768_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_assignments_2762_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
v_fst_2757_ = v___x_2764_;
v_snd_2758_ = v___x_2776_;
goto v___jp_2756_;
}
}
}
v___jp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_st_ref_set(v_a_2751_, v_snd_2758_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_fst_2757_);
return v___x_2760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg___boxed(lean_object* v_v_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(lean_object* v_v_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_v_2787_, v_a_2788_, v_a_2789_, v_a_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___boxed(lean_object* v_v_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary(v_v_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(lean_object* v_a_2805_, uint8_t v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_array_2811_; lean_object* v_start_2812_; lean_object* v_stop_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2850_; 
v_array_2811_ = lean_ctor_get(v_a_2805_, 0);
v_start_2812_ = lean_ctor_get(v_a_2805_, 1);
v_stop_2813_ = lean_ctor_get(v_a_2805_, 2);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_a_2805_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2815_ = v_a_2805_;
v_isShared_2816_ = v_isSharedCheck_2850_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_stop_2813_);
lean_inc(v_start_2812_);
lean_inc(v_array_2811_);
lean_dec(v_a_2805_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2850_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
uint8_t v___x_2817_; 
v___x_2817_ = lean_nat_dec_lt(v_start_2812_, v_stop_2813_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2815_);
lean_dec(v_stop_2813_);
lean_dec(v_start_2812_);
lean_dec_ref(v_array_2811_);
v___x_2818_ = lean_box(v_b_2806_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; lean_object* v_fvarId_2821_; lean_object* v___x_2822_; 
v___x_2820_ = lean_array_fget_borrowed(v_array_2811_, v_start_2812_);
v_fvarId_2821_ = lean_ctor_get(v___x_2820_, 0);
v___x_2822_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2821_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2822_);
v___x_2824_ = lean_box(1);
lean_inc(v_fvarId_2821_);
v___x_2825_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_2821_, v___x_2824_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
lean_dec_ref(v___x_2825_);
v___x_2826_ = lean_unsigned_to_nat(1u);
v___x_2827_ = lean_nat_add(v_start_2812_, v___x_2826_);
lean_dec(v_start_2812_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v___x_2827_);
v___x_2829_ = v___x_2815_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_array_2811_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_stop_2813_);
v___x_2829_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = lean_box(0);
v___x_2831_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_2823_, v___x_2830_);
v_a_2805_ = v___x_2829_;
v_b_2806_ = v___x_2831_;
goto _start;
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2823_);
lean_del_object(v___x_2815_);
lean_dec(v_stop_2813_);
lean_dec(v_start_2812_);
lean_dec_ref(v_array_2811_);
v_a_2834_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2825_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2825_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_del_object(v___x_2815_);
lean_dec(v_stop_2813_);
lean_dec(v_start_2812_);
lean_dec_ref(v_array_2811_);
v_a_2842_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2822_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2822_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg___boxed(lean_object* v_a_2851_, lean_object* v_b_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
uint8_t v_b_boxed_2857_; lean_object* v_res_2858_; 
v_b_boxed_2857_ = lean_unbox(v_b_2852_);
v_res_2858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_2851_, v_b_boxed_2857_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0(lean_object* v_fvarId_2859_, lean_object* v___x_2860_, lean_object* v_x_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_x_2861_, v_fvarId_2859_, v___x_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(lean_object* v___x_2863_, lean_object* v_as_2864_, size_t v_sz_2865_, size_t v_i_2866_, lean_object* v_b_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_a_2872_; uint8_t v___x_2876_; 
v___x_2876_ = lean_usize_dec_lt(v_i_2866_, v_sz_2865_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
lean_dec_ref(v___x_2863_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v_b_2867_);
return v___x_2877_;
}
else
{
lean_object* v_snd_2878_; lean_object* v_fst_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2945_; 
v_snd_2878_ = lean_ctor_get(v_b_2867_, 1);
v_fst_2879_ = lean_ctor_get(v_b_2867_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_b_2867_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2881_ = v_b_2867_;
v_isShared_2882_ = v_isSharedCheck_2945_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_snd_2878_);
lean_inc(v_fst_2879_);
lean_dec(v_b_2867_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2945_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_array_2883_; lean_object* v_start_2884_; lean_object* v_stop_2885_; uint8_t v___x_2886_; 
v_array_2883_ = lean_ctor_get(v_snd_2878_, 0);
v_start_2884_ = lean_ctor_get(v_snd_2878_, 1);
v_stop_2885_ = lean_ctor_get(v_snd_2878_, 2);
v___x_2886_ = lean_nat_dec_lt(v_start_2884_, v_stop_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2888_; 
lean_dec_ref(v___x_2863_);
if (v_isShared_2882_ == 0)
{
v___x_2888_ = v___x_2881_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_fst_2879_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_snd_2878_);
v___x_2888_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
}
else
{
lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2941_; 
lean_inc(v_stop_2885_);
lean_inc(v_start_2884_);
lean_inc_ref(v_array_2883_);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_snd_2878_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; lean_object* v_unused_2943_; lean_object* v_unused_2944_; 
v_unused_2942_ = lean_ctor_get(v_snd_2878_, 2);
lean_dec(v_unused_2942_);
v_unused_2943_ = lean_ctor_get(v_snd_2878_, 1);
lean_dec(v_unused_2943_);
v_unused_2944_ = lean_ctor_get(v_snd_2878_, 0);
lean_dec(v_unused_2944_);
v___x_2892_ = v_snd_2878_;
v_isShared_2893_ = v_isSharedCheck_2941_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v_snd_2878_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2941_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v_a_2894_; lean_object* v_fvarId_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_array_uget_borrowed(v_as_2864_, v_i_2866_);
v_fvarId_2895_ = lean_ctor_get(v_a_2894_, 0);
v___x_2896_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_2895_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = lean_array_fget_borrowed(v_array_2883_, v_start_2884_);
v___x_2899_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v___x_2898_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = lean_unsigned_to_nat(1u);
v___x_2902_ = lean_nat_add(v_start_2884_, v___x_2901_);
lean_dec(v_start_2884_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v___x_2902_);
v___x_2904_ = v___x_2892_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_array_2883_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_stop_2885_);
v___x_2904_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
lean_inc(v_a_2897_);
lean_inc_ref(v___x_2863_);
v___x_2905_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_widening(v___x_2863_, v_a_2897_, v_a_2900_);
lean_inc(v___x_2905_);
v___x_2906_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_2905_, v_a_2897_);
if (v___x_2906_ == 0)
{
lean_object* v___f_2907_; lean_object* v___x_2908_; 
lean_dec(v_fst_2879_);
lean_inc(v_fvarId_2895_);
v___f_2907_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2907_, 0, v_fvarId_2895_);
lean_closure_set(v___f_2907_, 1, v___x_2905_);
v___x_2908_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_2907_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
lean_dec_ref(v___x_2908_);
v___x_2909_ = lean_box(v___x_2886_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2904_);
lean_ctor_set(v___x_2881_, 0, v___x_2909_);
v___x_2911_ = v___x_2881_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2904_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v_a_2872_ = v___x_2911_;
goto v___jp_2871_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___x_2904_);
lean_del_object(v___x_2881_);
lean_dec_ref(v___x_2863_);
v_a_2913_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2908_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2908_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v___x_2922_; 
lean_dec(v___x_2905_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2904_);
v___x_2922_ = v___x_2881_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_fst_2879_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v___x_2904_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
v_a_2872_ = v___x_2922_;
goto v___jp_2871_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_a_2897_);
lean_del_object(v___x_2892_);
lean_dec(v_stop_2885_);
lean_dec(v_start_2884_);
lean_dec_ref(v_array_2883_);
lean_del_object(v___x_2881_);
lean_dec(v_fst_2879_);
lean_dec_ref(v___x_2863_);
v_a_2925_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2899_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2899_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_del_object(v___x_2892_);
lean_dec(v_stop_2885_);
lean_dec(v_start_2884_);
lean_dec_ref(v_array_2883_);
lean_del_object(v___x_2881_);
lean_dec(v_fst_2879_);
lean_dec_ref(v___x_2863_);
v_a_2933_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2896_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2896_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
}
}
v___jp_2871_:
{
size_t v___x_2873_; size_t v___x_2874_; 
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_add(v_i_2866_, v___x_2873_);
v_i_2866_ = v___x_2874_;
v_b_2867_ = v_a_2872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___boxed(lean_object* v___x_2946_, lean_object* v_as_2947_, lean_object* v_sz_2948_, lean_object* v_i_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
size_t v_sz_boxed_2954_; size_t v_i_boxed_2955_; lean_object* v_res_2956_; 
v_sz_boxed_2954_ = lean_unbox_usize(v_sz_2948_);
lean_dec(v_sz_2948_);
v_i_boxed_2955_ = lean_unbox_usize(v_i_2949_);
lean_dec(v_i_2949_);
v_res_2956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_2946_, v_as_2947_, v_sz_boxed_2954_, v_i_boxed_2955_, v_b_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_as_2947_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(lean_object* v_params_2957_, lean_object* v_args_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v___x_2966_; lean_object* v_env_2967_; uint8_t v_ret_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; size_t v_sz_2974_; size_t v___x_2975_; lean_object* v___x_2976_; 
v___x_2966_ = lean_st_ref_get(v_a_2964_);
v_env_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc_ref(v_env_2967_);
lean_dec(v___x_2966_);
v_ret_2968_ = 0;
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = lean_array_get_size(v_args_2958_);
v___x_2971_ = l_Array_toSubarray___redArg(v_args_2958_, v___x_2969_, v___x_2970_);
v___x_2972_ = lean_box(v_ret_2968_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2971_);
v_sz_2974_ = lean_array_size(v_params_2957_);
v___x_2975_ = ((size_t)0ULL);
v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v_env_2967_, v_params_2957_, v_sz_2974_, v___x_2975_, v___x_2973_, v_a_2959_, v_a_2960_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2994_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2979_ = v___x_2976_;
v_isShared_2980_ = v_isSharedCheck_2994_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2976_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2994_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v_fst_2981_; lean_object* v_lower_2983_; lean_object* v_upper_2984_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v_fst_2981_ = lean_ctor_get(v_a_2977_, 0);
lean_inc(v_fst_2981_);
lean_dec(v_a_2977_);
v___x_2988_ = lean_array_get_size(v_params_2957_);
v___x_2989_ = lean_nat_dec_eq(v___x_2988_, v___x_2970_);
if (v___x_2989_ == 0)
{
uint8_t v___x_2990_; 
lean_del_object(v___x_2979_);
v___x_2990_ = lean_nat_dec_le(v___x_2970_, v___x_2969_);
if (v___x_2990_ == 0)
{
v_lower_2983_ = v___x_2970_;
v_upper_2984_ = v___x_2988_;
goto v___jp_2982_;
}
else
{
v_lower_2983_ = v___x_2969_;
v_upper_2984_ = v___x_2988_;
goto v___jp_2982_;
}
}
else
{
lean_object* v___x_2992_; 
lean_dec_ref(v_params_2957_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v_fst_2981_);
v___x_2992_ = v___x_2979_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_fst_2981_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
v___jp_2982_:
{
lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = l_Array_toSubarray___redArg(v_params_2957_, v_lower_2983_, v_upper_2984_);
v___x_2986_ = lean_unbox(v_fst_2981_);
lean_dec(v_fst_2981_);
v___x_2987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v___x_2985_, v___x_2986_, v_a_2959_, v_a_2960_, v_a_2964_);
return v___x_2987_;
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v_params_2957_);
v_a_2995_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2976_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2976_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment___boxed(lean_object* v_params_3003_, lean_object* v_args_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3003_, v_args_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(lean_object* v___x_3013_, lean_object* v_as_3014_, size_t v_sz_3015_, size_t v_i_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg(v___x_3013_, v_as_3014_, v_sz_3015_, v_i_3016_, v_b_3017_, v___y_3018_, v___y_3019_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___boxed(lean_object* v___x_3026_, lean_object* v_as_3027_, lean_object* v_sz_3028_, lean_object* v_i_3029_, lean_object* v_b_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
size_t v_sz_boxed_3038_; size_t v_i_boxed_3039_; lean_object* v_res_3040_; 
v_sz_boxed_3038_ = lean_unbox_usize(v_sz_3028_);
lean_dec(v_sz_3028_);
v_i_boxed_3039_ = lean_unbox_usize(v_i_3029_);
lean_dec(v_i_3029_);
v_res_3040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0(v___x_3026_, v_as_3027_, v_sz_boxed_3038_, v_i_boxed_3039_, v_b_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v_as_3027_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(lean_object* v_inst_3041_, lean_object* v_R_3042_, lean_object* v_a_3043_, uint8_t v_b_3044_, lean_object* v_c_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___redArg(v_a_3043_, v_b_3044_, v___y_3046_, v___y_3047_, v___y_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1___boxed(lean_object* v_inst_3054_, lean_object* v_R_3055_, lean_object* v_a_3056_, lean_object* v_b_3057_, lean_object* v_c_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
uint8_t v_b_boxed_3066_; lean_object* v_res_3067_; 
v_b_boxed_3066_ = lean_unbox(v_b_3057_);
v_res_3067_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__1(v_inst_3054_, v_R_3055_, v_a_3056_, v_b_boxed_3066_, v_c_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(lean_object* v_as_3068_, size_t v_sz_3069_, size_t v_i_3070_, uint8_t v_b_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
uint8_t v_a_3076_; uint8_t v___x_3080_; 
v___x_3080_ = lean_usize_dec_lt(v_i_3070_, v_sz_3069_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_box(v_b_3071_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
else
{
lean_object* v_a_3083_; lean_object* v_fvarId_3084_; lean_object* v___x_3085_; 
v_a_3083_ = lean_array_uget_borrowed(v_as_3068_, v_i_3070_);
v_fvarId_3084_ = lean_ctor_get(v_a_3083_, 0);
v___x_3085_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3084_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___x_3085_);
v___x_3087_ = lean_box(1);
v___x_3088_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v___x_3087_, v_a_3086_);
if (v___x_3088_ == 0)
{
lean_object* v___f_3089_; lean_object* v___x_3090_; 
lean_inc(v_fvarId_3084_);
v___f_3089_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3089_, 0, v_fvarId_3084_);
lean_closure_set(v___f_3089_, 1, v___x_3087_);
v___x_3090_ = l_Lean_Compiler_LCNF_UnreachableBranches_modifyAssignment___redArg(v___f_3089_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_dec_ref(v___x_3090_);
v_a_3076_ = v___x_3080_;
goto v___jp_3075_;
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
v_a_3076_ = v_b_3071_;
goto v___jp_3075_;
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_a_3099_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3085_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3085_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
v___jp_3075_:
{
size_t v___x_3077_; size_t v___x_3078_; 
v___x_3077_ = ((size_t)1ULL);
v___x_3078_ = lean_usize_add(v_i_3070_, v___x_3077_);
v_i_3070_ = v___x_3078_;
v_b_3071_ = v_a_3076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg___boxed(lean_object* v_as_3107_, lean_object* v_sz_3108_, lean_object* v_i_3109_, lean_object* v_b_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
size_t v_sz_boxed_3114_; size_t v_i_boxed_3115_; uint8_t v_b_boxed_3116_; lean_object* v_res_3117_; 
v_sz_boxed_3114_ = lean_unbox_usize(v_sz_3108_);
lean_dec(v_sz_3108_);
v_i_boxed_3115_ = lean_unbox_usize(v_i_3109_);
lean_dec(v_i_3109_);
v_b_boxed_3116_ = lean_unbox(v_b_3110_);
v_res_3117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3107_, v_sz_boxed_3114_, v_i_boxed_3115_, v_b_boxed_3116_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v_as_3107_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(lean_object* v_params_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_){
_start:
{
uint8_t v_ret_3126_; size_t v_sz_3127_; size_t v___x_3128_; lean_object* v___x_3129_; 
v_ret_3126_ = 0;
v_sz_3127_ = lean_array_size(v_params_3118_);
v___x_3128_ = ((size_t)0ULL);
v___x_3129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_params_3118_, v_sz_3127_, v___x_3128_, v_ret_3126_, v_a_3119_, v_a_3120_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop___boxed(lean_object* v_params_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec_ref(v_params_3130_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(lean_object* v_as_3139_, size_t v_sz_3140_, size_t v_i_3141_, uint8_t v_b_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___redArg(v_as_3139_, v_sz_3140_, v_i_3141_, v_b_3142_, v___y_3143_, v___y_3144_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0___boxed(lean_object* v_as_3151_, lean_object* v_sz_3152_, lean_object* v_i_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
size_t v_sz_boxed_3162_; size_t v_i_boxed_3163_; uint8_t v_b_boxed_3164_; lean_object* v_res_3165_; 
v_sz_boxed_3162_ = lean_unbox_usize(v_sz_3152_);
lean_dec(v_sz_3152_);
v_i_boxed_3163_ = lean_unbox_usize(v_i_3153_);
lean_dec(v_i_3153_);
v_b_boxed_3164_ = lean_unbox(v_b_3154_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop_spec__0(v_as_3151_, v_sz_boxed_3162_, v_i_boxed_3163_, v_b_boxed_3164_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v_as_3151_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(lean_object* v_as_3166_, size_t v_i_3167_, size_t v_stop_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
uint8_t v___x_3173_; 
v___x_3173_ = lean_usize_dec_eq(v_i_3167_, v_stop_3168_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; lean_object* v_fvarId_3175_; lean_object* v___x_3176_; 
v___x_3174_ = lean_array_uget_borrowed(v_as_3166_, v_i_3167_);
v_fvarId_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_fvarId_3175_);
v___x_3176_ = l_Lean_Compiler_LCNF_UnreachableBranches_resetVarAssignment___redArg(v_fvarId_3175_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; size_t v___x_3178_; size_t v___x_3179_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = ((size_t)1ULL);
v___x_3179_ = lean_usize_add(v_i_3167_, v___x_3178_);
v_i_3167_ = v___x_3179_;
v_b_3169_ = v_a_3177_;
goto _start;
}
else
{
return v___x_3176_;
}
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_b_3169_);
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg___boxed(lean_object* v_as_3182_, lean_object* v_i_3183_, lean_object* v_stop_3184_, lean_object* v_b_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
size_t v_i_boxed_3189_; size_t v_stop_boxed_3190_; lean_object* v_res_3191_; 
v_i_boxed_3189_ = lean_unbox_usize(v_i_3183_);
lean_dec(v_i_3183_);
v_stop_boxed_3190_ = lean_unbox_usize(v_stop_3184_);
lean_dec(v_stop_3184_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3182_, v_i_boxed_3189_, v_stop_boxed_3190_, v_b_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec_ref(v_as_3182_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(lean_object* v_x_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v_decl_3211_; lean_object* v_k_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; 
switch(lean_obj_tag(v_x_3192_))
{
case 0:
{
lean_object* v_k_3233_; 
v_k_3233_ = lean_ctor_get(v_x_3192_, 1);
lean_inc_ref(v_k_3233_);
lean_dec_ref(v_x_3192_);
v_x_3192_ = v_k_3233_;
goto _start;
}
case 3:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec_ref(v_x_3192_);
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
case 4:
{
lean_object* v_cases_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3259_; 
v_cases_3237_ = lean_ctor_get(v_x_3192_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_x_3192_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3239_ = v_x_3192_;
v_isShared_3240_ = v_isSharedCheck_3259_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_cases_3237_);
lean_dec(v_x_3192_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3259_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_alts_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v_alts_3241_ = lean_ctor_get(v_cases_3237_, 3);
lean_inc_ref(v_alts_3241_);
lean_dec_ref(v_cases_3237_);
v___x_3242_ = lean_unsigned_to_nat(0u);
v___x_3243_ = lean_array_get_size(v_alts_3241_);
v___x_3244_ = lean_box(0);
v___x_3245_ = lean_nat_dec_lt(v___x_3242_, v___x_3243_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3247_; 
lean_dec_ref(v_alts_3241_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3244_);
v___x_3247_ = v___x_3239_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3244_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
else
{
uint8_t v___x_3249_; 
v___x_3249_ = lean_nat_dec_le(v___x_3243_, v___x_3243_);
if (v___x_3249_ == 0)
{
if (v___x_3245_ == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v_alts_3241_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3244_);
v___x_3251_ = v___x_3239_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3244_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
else
{
size_t v___x_3253_; size_t v___x_3254_; lean_object* v___x_3255_; 
lean_del_object(v___x_3239_);
v___x_3253_ = ((size_t)0ULL);
v___x_3254_ = lean_usize_of_nat(v___x_3243_);
v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3241_, v___x_3253_, v___x_3254_, v___x_3244_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec_ref(v_alts_3241_);
return v___x_3255_;
}
}
else
{
size_t v___x_3256_; size_t v___x_3257_; lean_object* v___x_3258_; 
lean_del_object(v___x_3239_);
v___x_3256_ = ((size_t)0ULL);
v___x_3257_ = lean_usize_of_nat(v___x_3243_);
v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_alts_3241_, v___x_3256_, v___x_3257_, v___x_3244_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec_ref(v_alts_3241_);
return v___x_3258_;
}
}
}
}
case 5:
{
lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3267_; 
v_isSharedCheck_3267_ = !lean_is_exclusive(v_x_3192_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v_x_3192_, 0);
lean_dec(v_unused_3268_);
v___x_3261_ = v_x_3192_;
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
else
{
lean_dec(v_x_3192_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3263_ = lean_box(0);
if (v_isShared_3262_ == 0)
{
lean_ctor_set_tag(v___x_3261_, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3263_);
v___x_3265_ = v___x_3261_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
case 6:
{
lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3276_; 
v_isSharedCheck_3276_ = !lean_is_exclusive(v_x_3192_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v_x_3192_, 0);
lean_dec(v_unused_3277_);
v___x_3270_ = v_x_3192_;
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
else
{
lean_dec(v_x_3192_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = lean_box(0);
if (v_isShared_3271_ == 0)
{
lean_ctor_set_tag(v___x_3270_, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3272_);
v___x_3274_ = v___x_3270_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
default: 
{
lean_object* v_decl_3278_; lean_object* v_k_3279_; 
v_decl_3278_ = lean_ctor_get(v_x_3192_, 0);
lean_inc_ref(v_decl_3278_);
v_k_3279_ = lean_ctor_get(v_x_3192_, 1);
lean_inc_ref(v_k_3279_);
lean_dec_ref(v_x_3192_);
v_decl_3211_ = v_decl_3278_;
v_k_3212_ = v_k_3279_;
v___y_3213_ = v_a_3193_;
v___y_3214_ = v_a_3194_;
v___y_3215_ = v_a_3195_;
v___y_3216_ = v_a_3196_;
v___y_3217_ = v_a_3197_;
v___y_3218_ = v_a_3198_;
goto v___jp_3210_;
}
}
v___jp_3200_:
{
if (lean_obj_tag(v___y_3208_) == 0)
{
lean_dec_ref(v___y_3208_);
v_x_3192_ = v___y_3202_;
v_a_3193_ = v___y_3207_;
v_a_3194_ = v___y_3206_;
v_a_3195_ = v___y_3205_;
v_a_3196_ = v___y_3201_;
v_a_3197_ = v___y_3204_;
v_a_3198_ = v___y_3203_;
goto _start;
}
else
{
lean_dec_ref(v___y_3202_);
return v___y_3208_;
}
}
v___jp_3210_:
{
lean_object* v_params_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_params_3219_ = lean_ctor_get(v_decl_3211_, 2);
lean_inc_ref(v_params_3219_);
lean_dec_ref(v_decl_3211_);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_array_get_size(v_params_3219_);
v___x_3222_ = lean_nat_dec_lt(v___x_3220_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_dec_ref(v_params_3219_);
v_x_3192_ = v_k_3212_;
v_a_3193_ = v___y_3213_;
v_a_3194_ = v___y_3214_;
v_a_3195_ = v___y_3215_;
v_a_3196_ = v___y_3216_;
v_a_3197_ = v___y_3217_;
v_a_3198_ = v___y_3218_;
goto _start;
}
else
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = lean_box(0);
v___x_3225_ = lean_nat_dec_le(v___x_3221_, v___x_3221_);
if (v___x_3225_ == 0)
{
if (v___x_3222_ == 0)
{
lean_dec_ref(v_params_3219_);
v_x_3192_ = v_k_3212_;
v_a_3193_ = v___y_3213_;
v_a_3194_ = v___y_3214_;
v_a_3195_ = v___y_3215_;
v_a_3196_ = v___y_3216_;
v_a_3197_ = v___y_3217_;
v_a_3198_ = v___y_3218_;
goto _start;
}
else
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((size_t)0ULL);
v___x_3228_ = lean_usize_of_nat(v___x_3221_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3219_, v___x_3227_, v___x_3228_, v___x_3224_, v___y_3213_, v___y_3214_);
lean_dec_ref(v_params_3219_);
v___y_3201_ = v___y_3216_;
v___y_3202_ = v_k_3212_;
v___y_3203_ = v___y_3218_;
v___y_3204_ = v___y_3217_;
v___y_3205_ = v___y_3215_;
v___y_3206_ = v___y_3214_;
v___y_3207_ = v___y_3213_;
v___y_3208_ = v___x_3229_;
goto v___jp_3200_;
}
}
else
{
size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = lean_usize_of_nat(v___x_3221_);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_params_3219_, v___x_3230_, v___x_3231_, v___x_3224_, v___y_3213_, v___y_3214_);
lean_dec_ref(v_params_3219_);
v___y_3201_ = v___y_3216_;
v___y_3202_ = v_k_3212_;
v___y_3203_ = v___y_3218_;
v___y_3204_ = v___y_3217_;
v___y_3205_ = v___y_3215_;
v___y_3206_ = v___y_3214_;
v___y_3207_ = v___y_3213_;
v___y_3208_ = v___x_3232_;
goto v___jp_3200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(lean_object* v_as_3280_, size_t v_i_3281_, size_t v_stop_3282_, lean_object* v_b_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___y_3292_; uint8_t v___x_3298_; 
v___x_3298_ = lean_usize_dec_eq(v_i_3281_, v_stop_3282_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_array_uget_borrowed(v_as_3280_, v_i_3281_);
switch(lean_obj_tag(v___x_3299_))
{
case 0:
{
lean_object* v_code_3300_; 
v_code_3300_ = lean_ctor_get(v___x_3299_, 2);
lean_inc_ref(v_code_3300_);
v___y_3292_ = v_code_3300_;
goto v___jp_3291_;
}
case 1:
{
lean_object* v_code_3301_; 
v_code_3301_ = lean_ctor_get(v___x_3299_, 1);
lean_inc_ref(v_code_3301_);
v___y_3292_ = v_code_3301_;
goto v___jp_3291_;
}
default: 
{
lean_object* v_code_3302_; 
v_code_3302_ = lean_ctor_get(v___x_3299_, 0);
lean_inc_ref(v_code_3302_);
v___y_3292_ = v_code_3302_;
goto v___jp_3291_;
}
}
}
else
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_b_3283_);
return v___x_3303_;
}
v___jp_3291_:
{
lean_object* v___x_3293_; 
v___x_3293_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v___y_3292_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; size_t v___x_3295_; size_t v___x_3296_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref(v___x_3293_);
v___x_3295_ = ((size_t)1ULL);
v___x_3296_ = lean_usize_add(v_i_3281_, v___x_3295_);
v_i_3281_ = v___x_3296_;
v_b_3283_ = v_a_3294_;
goto _start;
}
else
{
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1___boxed(lean_object* v_as_3304_, lean_object* v_i_3305_, lean_object* v_stop_3306_, lean_object* v_b_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
size_t v_i_boxed_3315_; size_t v_stop_boxed_3316_; lean_object* v_res_3317_; 
v_i_boxed_3315_ = lean_unbox_usize(v_i_3305_);
lean_dec(v_i_3305_);
v_stop_boxed_3316_ = lean_unbox_usize(v_stop_3306_);
lean_dec(v_stop_3306_);
v_res_3317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__1(v_as_3304_, v_i_boxed_3315_, v_stop_boxed_3316_, v_b_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec_ref(v_as_3304_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams___boxed(lean_object* v_x_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_x_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(lean_object* v_as_3327_, size_t v_i_3328_, size_t v_stop_3329_, lean_object* v_b_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___redArg(v_as_3327_, v_i_3328_, v_stop_3329_, v_b_3330_, v___y_3331_, v___y_3332_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0___boxed(lean_object* v_as_3339_, lean_object* v_i_3340_, lean_object* v_stop_3341_, lean_object* v_b_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
size_t v_i_boxed_3350_; size_t v_stop_boxed_3351_; lean_object* v_res_3352_; 
v_i_boxed_3350_ = lean_unbox_usize(v_i_3340_);
lean_dec(v_i_3340_);
v_stop_boxed_3351_ = lean_unbox_usize(v_stop_3341_);
lean_dec(v_stop_3341_);
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams_spec__0(v_as_3339_, v_i_boxed_3350_, v_stop_boxed_3351_, v_b_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec_ref(v_as_3339_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(lean_object* v_a_3353_, lean_object* v_b_3354_){
_start:
{
lean_object* v_array_3355_; lean_object* v_start_3356_; lean_object* v_stop_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3370_; 
v_array_3355_ = lean_ctor_get(v_a_3353_, 0);
v_start_3356_ = lean_ctor_get(v_a_3353_, 1);
v_stop_3357_ = lean_ctor_get(v_a_3353_, 2);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_a_3353_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3359_ = v_a_3353_;
v_isShared_3360_ = v_isSharedCheck_3370_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_stop_3357_);
lean_inc(v_start_3356_);
lean_inc(v_array_3355_);
lean_dec(v_a_3353_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3370_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_nat_dec_lt(v_start_3356_, v_stop_3357_);
if (v___x_3361_ == 0)
{
lean_del_object(v___x_3359_);
lean_dec(v_stop_3357_);
lean_dec(v_start_3356_);
lean_dec_ref(v_array_3355_);
return v_b_3354_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3362_ = lean_unsigned_to_nat(1u);
v___x_3363_ = lean_nat_add(v_start_3356_, v___x_3362_);
lean_inc_ref(v_array_3355_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3363_);
v___x_3365_ = v___x_3359_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_array_3355_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_stop_3357_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_array_fget(v_array_3355_, v_start_3356_);
lean_dec(v_start_3356_);
lean_dec_ref(v_array_3355_);
v___x_3367_ = lean_array_push(v_b_3354_, v___x_3366_);
v_a_3353_ = v___x_3365_;
v_b_3354_ = v___x_3367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(size_t v_sz_3371_, size_t v_i_3372_, lean_object* v_bs_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
uint8_t v___x_3377_; 
v___x_3377_ = lean_usize_dec_lt(v_i_3372_, v_sz_3371_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v_bs_3373_);
return v___x_3378_;
}
else
{
lean_object* v_v_3379_; lean_object* v___x_3380_; 
v_v_3379_ = lean_array_uget_borrowed(v_bs_3373_, v_i_3372_);
v___x_3380_ = l_Lean_Compiler_LCNF_UnreachableBranches_findArgValue___redArg(v_v_3379_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; lean_object* v_bs_x27_3383_; size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = lean_unsigned_to_nat(0u);
v_bs_x27_3383_ = lean_array_uset(v_bs_3373_, v_i_3372_, v___x_3382_);
v___x_3384_ = ((size_t)1ULL);
v___x_3385_ = lean_usize_add(v_i_3372_, v___x_3384_);
v___x_3386_ = lean_array_uset(v_bs_x27_3383_, v_i_3372_, v_a_3381_);
v_i_3372_ = v___x_3385_;
v_bs_3373_ = v___x_3386_;
goto _start;
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v_bs_3373_);
v_a_3388_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3380_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3380_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg___boxed(lean_object* v_sz_3396_, lean_object* v_i_3397_, lean_object* v_bs_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
size_t v_sz_boxed_3402_; size_t v_i_boxed_3403_; lean_object* v_res_3404_; 
v_sz_boxed_3402_ = lean_unbox_usize(v_sz_3396_);
lean_dec(v_sz_3396_);
v_i_boxed_3403_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_boxed_3402_, v_i_boxed_3403_, v_bs_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(lean_object* v_as_3405_, size_t v_i_3406_, size_t v_stop_3407_, lean_object* v_b_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_usize_dec_eq(v_i_3406_, v_stop_3407_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v_fvarId_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3414_ = lean_array_uget_borrowed(v_as_3405_, v_i_3406_);
v_fvarId_3415_ = lean_ctor_get(v___x_3414_, 0);
v___x_3416_ = lean_box(1);
lean_inc(v_fvarId_3415_);
v___x_3417_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3415_, v___x_3416_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; size_t v___x_3419_; size_t v___x_3420_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = ((size_t)1ULL);
v___x_3420_ = lean_usize_add(v_i_3406_, v___x_3419_);
v_i_3406_ = v___x_3420_;
v_b_3408_ = v_a_3418_;
goto _start;
}
else
{
return v___x_3417_;
}
}
else
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v_b_3408_);
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg___boxed(lean_object* v_as_3423_, lean_object* v_i_3424_, lean_object* v_stop_3425_, lean_object* v_b_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
size_t v_i_boxed_3431_; size_t v_stop_boxed_3432_; lean_object* v_res_3433_; 
v_i_boxed_3431_ = lean_unbox_usize(v_i_3424_);
lean_dec(v_i_3424_);
v_stop_boxed_3432_ = lean_unbox_usize(v_stop_3425_);
lean_dec(v_stop_3425_);
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_3423_, v_i_boxed_3431_, v_stop_boxed_3432_, v_b_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v_as_3423_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(lean_object* v_as_3434_, size_t v_i_3435_, size_t v_stop_3436_, lean_object* v_b_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
uint8_t v___x_3442_; 
v___x_3442_ = lean_usize_dec_eq(v_i_3435_, v_stop_3436_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v_fst_3444_; lean_object* v_snd_3445_; lean_object* v_fvarId_3446_; lean_object* v___x_3447_; 
v___x_3443_ = lean_array_uget_borrowed(v_as_3434_, v_i_3435_);
v_fst_3444_ = lean_ctor_get(v___x_3443_, 0);
v_snd_3445_ = lean_ctor_get(v___x_3443_, 1);
v_fvarId_3446_ = lean_ctor_get(v_fst_3444_, 0);
lean_inc(v_snd_3445_);
lean_inc(v_fvarId_3446_);
v___x_3447_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3446_, v_snd_3445_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; size_t v___x_3449_; size_t v___x_3450_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref(v___x_3447_);
v___x_3449_ = ((size_t)1ULL);
v___x_3450_ = lean_usize_add(v_i_3435_, v___x_3449_);
v_i_3435_ = v___x_3450_;
v_b_3437_ = v_a_3448_;
goto _start;
}
else
{
return v___x_3447_;
}
}
else
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_b_3437_);
return v___x_3452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg___boxed(lean_object* v_as_3453_, lean_object* v_i_3454_, lean_object* v_stop_3455_, lean_object* v_b_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
size_t v_i_boxed_3461_; size_t v_stop_boxed_3462_; lean_object* v_res_3463_; 
v_i_boxed_3461_ = lean_unbox_usize(v_i_3454_);
lean_dec(v_i_3454_);
v_stop_boxed_3462_ = lean_unbox_usize(v_stop_3455_);
lean_dec(v_stop_3455_);
v_res_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_3453_, v_i_boxed_3461_, v_stop_boxed_3462_, v_b_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec_ref(v_as_3453_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(lean_object* v_as_3466_, size_t v_i_3467_, size_t v_stop_3468_, lean_object* v_b_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_usize_dec_eq(v_i_3467_, v_stop_3468_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_array_uget_borrowed(v_as_3466_, v_i_3467_);
v___x_3479_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v___x_3478_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; size_t v___x_3481_; size_t v___x_3482_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3479_);
v___x_3481_ = ((size_t)1ULL);
v___x_3482_ = lean_usize_add(v_i_3467_, v___x_3481_);
v_i_3467_ = v___x_3482_;
v_b_3469_ = v_a_3480_;
goto _start;
}
else
{
return v___x_3479_;
}
}
else
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_b_3469_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(lean_object* v_letVal_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___y_3500_; 
switch(lean_obj_tag(v_letVal_3485_))
{
case 0:
{
lean_object* v_value_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3517_; 
v_value_3509_ = lean_ctor_get(v_letVal_3485_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_letVal_3485_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3511_ = v_letVal_3485_;
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_value_3509_);
lean_dec(v_letVal_3485_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3513_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_ofLCNFLit(v_value_3509_);
lean_dec_ref(v_value_3509_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3513_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
case 1:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_box(1);
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
return v___x_3519_;
}
case 2:
{
lean_object* v_idx_3520_; lean_object* v_struct_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_idx_3520_ = lean_ctor_get(v_letVal_3485_, 1);
lean_inc(v_idx_3520_);
v_struct_3521_ = lean_ctor_get(v_letVal_3485_, 2);
lean_inc(v_struct_3521_);
lean_dec_ref(v_letVal_3485_);
v___x_3522_ = lean_st_ref_get(v_a_3491_);
v___x_3523_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_struct_3521_, v_a_3486_, v_a_3487_);
lean_dec(v_struct_3521_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3533_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3533_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3533_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_env_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v_env_3528_ = lean_ctor_get(v___x_3522_, 0);
lean_inc_ref(v_env_3528_);
lean_dec(v___x_3522_);
v___x_3529_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_proj(v_env_3528_, v_a_3524_, v_idx_3520_);
lean_dec(v_idx_3520_);
lean_dec(v_a_3524_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3529_);
v___x_3531_ = v___x_3526_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
else
{
lean_dec(v___x_3522_);
lean_dec(v_idx_3520_);
return v___x_3523_;
}
}
case 3:
{
lean_object* v_declName_3534_; lean_object* v_args_3535_; lean_object* v___x_3536_; lean_object* v_env_3537_; lean_object* v___x_3538_; lean_object* v_numFields_3540_; lean_object* v_lower_3541_; lean_object* v_upper_3542_; lean_object* v___x_3570_; lean_object* v___y_3639_; uint8_t v___x_3648_; 
v_declName_3534_ = lean_ctor_get(v_letVal_3485_, 0);
lean_inc(v_declName_3534_);
v_args_3535_ = lean_ctor_get(v_letVal_3485_, 2);
lean_inc_ref(v_args_3535_);
lean_dec_ref(v_letVal_3485_);
v___x_3536_ = lean_st_ref_get(v_a_3491_);
v_env_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc_ref(v_env_3537_);
lean_dec(v___x_3536_);
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3570_ = lean_array_get_size(v_args_3535_);
v___x_3648_ = lean_nat_dec_lt(v___x_3538_, v___x_3570_);
if (v___x_3648_ == 0)
{
goto v___jp_3571_;
}
else
{
lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3649_ = lean_box(0);
v___x_3650_ = lean_nat_dec_le(v___x_3570_, v___x_3570_);
if (v___x_3650_ == 0)
{
if (v___x_3648_ == 0)
{
goto v___jp_3571_;
}
else
{
size_t v___x_3651_; size_t v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = ((size_t)0ULL);
v___x_3652_ = lean_usize_of_nat(v___x_3570_);
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3535_, v___x_3651_, v___x_3652_, v___x_3649_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3639_ = v___x_3653_;
goto v___jp_3638_;
}
}
else
{
size_t v___x_3654_; size_t v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = ((size_t)0ULL);
v___x_3655_ = lean_usize_of_nat(v___x_3570_);
v___x_3656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3535_, v___x_3654_, v___x_3655_, v___x_3649_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
v___y_3639_ = v___x_3656_;
goto v___jp_3638_;
}
}
v___jp_3539_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v___x_3543_ = l_Array_toSubarray___redArg(v_args_3535_, v_lower_3541_, v_upper_3542_);
v___x_3544_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___closed__0));
v___x_3545_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v___x_3543_, v___x_3544_);
v___x_3546_ = lean_array_get_size(v___x_3545_);
v___x_3547_ = lean_nat_dec_eq(v_numFields_3540_, v___x_3546_);
lean_dec(v_numFields_3540_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_dec_ref(v___x_3545_);
lean_dec(v_declName_3534_);
v___x_3548_ = lean_box(1);
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
return v___x_3549_;
}
else
{
size_t v_sz_3550_; size_t v___x_3551_; lean_object* v___x_3552_; 
v_sz_3550_ = lean_array_size(v___x_3545_);
v___x_3551_ = ((size_t)0ULL);
v___x_3552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_3550_, v___x_3551_, v___x_3545_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3561_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_declName_3534_);
lean_ctor_set(v___x_3557_, 1, v_a_3553_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3557_);
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_declName_3534_);
v_a_3562_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3552_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3552_);
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
v___jp_3571_:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3488_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = lean_unbox(v_a_3573_);
lean_dec(v_a_3573_);
lean_inc(v_declName_3534_);
v___x_3575_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_3534_, v___x_3574_, v_a_3490_, v_a_3491_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3621_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3621_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3621_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
if (lean_obj_tag(v_a_3576_) == 1)
{
lean_object* v_val_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
lean_dec_ref(v_args_3535_);
v_val_3580_ = lean_ctor_get(v_a_3576_, 0);
lean_inc(v_val_3580_);
lean_dec_ref(v_a_3576_);
v___x_3581_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_3580_);
lean_dec(v_val_3580_);
v___x_3582_ = lean_nat_dec_eq(v___x_3581_, v___x_3570_);
lean_dec(v___x_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
lean_dec_ref(v_env_3537_);
lean_dec(v_declName_3534_);
v___x_3583_ = lean_box(1);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3583_);
v___x_3585_ = v___x_3578_;
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
else
{
lean_object* v___x_3587_; 
lean_inc(v_declName_3534_);
v___x_3587_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunctionSummary_x3f(v_env_3537_, v_declName_3534_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v___x_3588_; 
lean_del_object(v___x_3578_);
v___x_3588_ = l_Lean_Compiler_LCNF_UnreachableBranches_findFunVal_x3f___redArg(v_declName_3534_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3601_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3601_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3601_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
if (lean_obj_tag(v_a_3589_) == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = lean_box(1);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3593_);
v___x_3595_ = v___x_3591_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
else
{
lean_object* v_val_3597_; lean_object* v___x_3599_; 
v_val_3597_ = lean_ctor_get(v_a_3589_, 0);
lean_inc(v_val_3597_);
lean_dec_ref(v_a_3589_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v_val_3597_);
v___x_3599_ = v___x_3591_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_val_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
v_a_3602_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3588_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3588_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3612_; 
lean_dec(v_declName_3534_);
v_val_3610_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_val_3610_);
lean_dec_ref(v___x_3587_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v_val_3610_);
v___x_3612_ = v___x_3578_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_val_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
uint8_t v___x_3614_; lean_object* v___x_3615_; 
lean_del_object(v___x_3578_);
lean_dec(v_a_3576_);
v___x_3614_ = 0;
lean_inc(v_declName_3534_);
v___x_3615_ = l_Lean_Environment_find_x3f(v_env_3537_, v_declName_3534_, v___x_3614_);
if (lean_obj_tag(v___x_3615_) == 1)
{
lean_object* v_val_3616_; 
v_val_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_val_3616_);
lean_dec_ref(v___x_3615_);
if (lean_obj_tag(v_val_3616_) == 6)
{
lean_object* v_val_3617_; lean_object* v_numParams_3618_; lean_object* v_numFields_3619_; uint8_t v___x_3620_; 
v_val_3617_ = lean_ctor_get(v_val_3616_, 0);
lean_inc_ref(v_val_3617_);
lean_dec_ref(v_val_3616_);
v_numParams_3618_ = lean_ctor_get(v_val_3617_, 3);
lean_inc(v_numParams_3618_);
v_numFields_3619_ = lean_ctor_get(v_val_3617_, 4);
lean_inc(v_numFields_3619_);
lean_dec_ref(v_val_3617_);
v___x_3620_ = lean_nat_dec_le(v_numParams_3618_, v___x_3538_);
if (v___x_3620_ == 0)
{
v_numFields_3540_ = v_numFields_3619_;
v_lower_3541_ = v_numParams_3618_;
v_upper_3542_ = v___x_3570_;
goto v___jp_3539_;
}
else
{
lean_dec(v_numParams_3618_);
v_numFields_3540_ = v_numFields_3619_;
v_lower_3541_ = v___x_3538_;
v_upper_3542_ = v___x_3570_;
goto v___jp_3539_;
}
}
else
{
lean_dec(v_val_3616_);
lean_dec_ref(v_args_3535_);
lean_dec(v_declName_3534_);
goto v___jp_3493_;
}
}
else
{
lean_dec(v___x_3615_);
lean_dec_ref(v_args_3535_);
lean_dec(v_declName_3534_);
goto v___jp_3493_;
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref(v_env_3537_);
lean_dec_ref(v_args_3535_);
lean_dec(v_declName_3534_);
v_a_3622_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3575_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3575_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref(v_env_3537_);
lean_dec_ref(v_args_3535_);
lean_dec(v_declName_3534_);
v_a_3630_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3572_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3572_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
v___jp_3638_:
{
if (lean_obj_tag(v___y_3639_) == 0)
{
lean_dec_ref(v___y_3639_);
goto v___jp_3571_;
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v_env_3537_);
lean_dec_ref(v_args_3535_);
lean_dec(v_declName_3534_);
v_a_3640_ = lean_ctor_get(v___y_3639_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___y_3639_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___y_3639_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___y_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
default: 
{
lean_object* v_args_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v_args_3657_ = lean_ctor_get(v_letVal_3485_, 1);
lean_inc_ref(v_args_3657_);
lean_dec_ref(v_letVal_3485_);
v___x_3658_ = lean_unsigned_to_nat(0u);
v___x_3659_ = lean_array_get_size(v_args_3657_);
v___x_3660_ = lean_nat_dec_lt(v___x_3658_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_dec_ref(v_args_3657_);
goto v___jp_3496_;
}
else
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = lean_box(0);
v___x_3662_ = lean_nat_dec_le(v___x_3659_, v___x_3659_);
if (v___x_3662_ == 0)
{
if (v___x_3660_ == 0)
{
lean_dec_ref(v_args_3657_);
goto v___jp_3496_;
}
else
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = ((size_t)0ULL);
v___x_3664_ = lean_usize_of_nat(v___x_3659_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3657_, v___x_3663_, v___x_3664_, v___x_3661_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec_ref(v_args_3657_);
v___y_3500_ = v___x_3665_;
goto v___jp_3499_;
}
}
else
{
size_t v___x_3666_; size_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = ((size_t)0ULL);
v___x_3667_ = lean_usize_of_nat(v___x_3659_);
v___x_3668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3657_, v___x_3666_, v___x_3667_, v___x_3661_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec_ref(v_args_3657_);
v___y_3500_ = v___x_3668_;
goto v___jp_3499_;
}
}
}
}
v___jp_3493_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = lean_box(1);
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
return v___x_3495_;
}
v___jp_3496_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = lean_box(1);
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
return v___x_3498_;
}
v___jp_3499_:
{
if (lean_obj_tag(v___y_3500_) == 0)
{
lean_dec_ref(v___y_3500_);
goto v___jp_3496_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
v_a_3501_ = lean_ctor_get(v___y_3500_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___y_3500_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___y_3500_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___y_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(lean_object* v_funDecl_3669_, lean_object* v_args_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v_params_3678_; lean_object* v_value_3679_; lean_object* v___x_3680_; 
v_params_3678_ = lean_ctor_get(v_funDecl_3669_, 2);
lean_inc_ref(v_params_3678_);
v_value_3679_ = lean_ctor_get(v_funDecl_3669_, 4);
lean_inc_ref(v_value_3679_);
lean_dec_ref(v_funDecl_3669_);
v___x_3680_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsAssignment(v_params_3678_, v_args_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3692_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3692_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3692_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
uint8_t v___x_3685_; 
v___x_3685_ = lean_unbox(v_a_3681_);
lean_dec(v_a_3681_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
lean_dec_ref(v_value_3679_);
v___x_3686_ = lean_box(0);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3686_);
v___x_3688_ = v___x_3683_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
else
{
lean_object* v___x_3690_; 
lean_del_object(v___x_3683_);
lean_inc_ref(v_value_3679_);
v___x_3690_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3679_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v___x_3691_; 
lean_dec_ref(v___x_3690_);
v___x_3691_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3679_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
return v___x_3691_;
}
else
{
lean_dec_ref(v_value_3679_);
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec_ref(v_value_3679_);
v_a_3693_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3680_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3680_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(lean_object* v_a_3701_, lean_object* v_as_3702_, size_t v_sz_3703_, size_t v_i_3704_, lean_object* v_b_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_a_3714_; uint8_t v___x_3718_; 
v___x_3718_ = lean_usize_dec_lt(v_i_3704_, v_sz_3703_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; 
lean_dec(v_a_3701_);
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v_b_3705_);
return v___x_3719_;
}
else
{
lean_object* v___x_3720_; lean_object* v_a_3721_; 
v___x_3720_ = lean_box(0);
v_a_3721_ = lean_array_uget_borrowed(v_as_3702_, v_i_3704_);
if (lean_obj_tag(v_a_3721_) == 0)
{
lean_object* v_ctorName_3722_; lean_object* v_params_3723_; lean_object* v_code_3724_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3734_; lean_object* v___y_3736_; lean_object* v___x_3737_; 
v_ctorName_3722_ = lean_ctor_get(v_a_3721_, 0);
v_params_3723_ = lean_ctor_get(v_a_3721_, 1);
v_code_3724_ = lean_ctor_get(v_a_3721_, 2);
lean_inc(v_a_3701_);
v___x_3737_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getCtorArgs(v_a_3701_, v_ctorName_3722_);
if (lean_obj_tag(v___x_3737_) == 1)
{
lean_object* v_val_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; uint8_t v___x_3742_; 
v_val_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_val_3738_);
lean_dec_ref(v___x_3737_);
v___x_3739_ = l_Array_zip___redArg(v_params_3723_, v_val_3738_);
lean_dec(v_val_3738_);
v___x_3740_ = lean_unsigned_to_nat(0u);
v___x_3741_ = lean_array_get_size(v___x_3739_);
v___x_3742_ = lean_nat_dec_lt(v___x_3740_, v___x_3741_);
if (v___x_3742_ == 0)
{
lean_dec_ref(v___x_3739_);
v___y_3726_ = v___y_3706_;
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
goto v___jp_3725_;
}
else
{
uint8_t v___x_3743_; 
v___x_3743_ = lean_nat_dec_le(v___x_3741_, v___x_3741_);
if (v___x_3743_ == 0)
{
if (v___x_3742_ == 0)
{
lean_dec_ref(v___x_3739_);
v___y_3726_ = v___y_3706_;
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
goto v___jp_3725_;
}
else
{
size_t v___x_3744_; size_t v___x_3745_; lean_object* v___x_3746_; 
v___x_3744_ = ((size_t)0ULL);
v___x_3745_ = lean_usize_of_nat(v___x_3741_);
v___x_3746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3739_, v___x_3744_, v___x_3745_, v___x_3720_, v___y_3706_, v___y_3707_, v___y_3711_);
lean_dec_ref(v___x_3739_);
v___y_3734_ = v___x_3746_;
goto v___jp_3733_;
}
}
else
{
size_t v___x_3747_; size_t v___x_3748_; lean_object* v___x_3749_; 
v___x_3747_ = ((size_t)0ULL);
v___x_3748_ = lean_usize_of_nat(v___x_3741_);
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v___x_3739_, v___x_3747_, v___x_3748_, v___x_3720_, v___y_3706_, v___y_3707_, v___y_3711_);
lean_dec_ref(v___x_3739_);
v___y_3734_ = v___x_3749_;
goto v___jp_3733_;
}
}
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; uint8_t v___x_3752_; 
lean_dec(v___x_3737_);
v___x_3750_ = lean_unsigned_to_nat(0u);
v___x_3751_ = lean_array_get_size(v_params_3723_);
v___x_3752_ = lean_nat_dec_lt(v___x_3750_, v___x_3751_);
if (v___x_3752_ == 0)
{
v___y_3726_ = v___y_3706_;
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
goto v___jp_3725_;
}
else
{
uint8_t v___x_3753_; 
v___x_3753_ = lean_nat_dec_le(v___x_3751_, v___x_3751_);
if (v___x_3753_ == 0)
{
if (v___x_3752_ == 0)
{
v___y_3726_ = v___y_3706_;
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
goto v___jp_3725_;
}
else
{
size_t v___x_3754_; size_t v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = ((size_t)0ULL);
v___x_3755_ = lean_usize_of_nat(v___x_3751_);
v___x_3756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3723_, v___x_3754_, v___x_3755_, v___x_3720_, v___y_3706_, v___y_3707_, v___y_3711_);
v___y_3736_ = v___x_3756_;
goto v___jp_3735_;
}
}
else
{
size_t v___x_3757_; size_t v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = ((size_t)0ULL);
v___x_3758_ = lean_usize_of_nat(v___x_3751_);
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_3723_, v___x_3757_, v___x_3758_, v___x_3720_, v___y_3706_, v___y_3707_, v___y_3711_);
v___y_3736_ = v___x_3759_;
goto v___jp_3735_;
}
}
}
v___jp_3725_:
{
lean_object* v___x_3732_; 
lean_inc_ref(v_code_3724_);
v___x_3732_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3724_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_dec_ref(v___x_3732_);
v_a_3714_ = v___x_3720_;
goto v___jp_3713_;
}
else
{
lean_dec(v_a_3701_);
return v___x_3732_;
}
}
v___jp_3733_:
{
if (lean_obj_tag(v___y_3734_) == 0)
{
lean_dec_ref(v___y_3734_);
v___y_3726_ = v___y_3706_;
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
goto v___jp_3725_;
}
else
{
lean_dec(v_a_3701_);
return v___y_3734_;
}
}
v___jp_3735_:
{
if (lean_obj_tag(v___y_3736_) == 0)
{
lean_dec_ref(v___y_3736_);
v___y_3726_ = v___y_3706_;
v___y_3727_ = v___y_3707_;
v___y_3728_ = v___y_3708_;
v___y_3729_ = v___y_3709_;
v___y_3730_ = v___y_3710_;
v___y_3731_ = v___y_3711_;
goto v___jp_3725_;
}
else
{
lean_dec(v_a_3701_);
return v___y_3736_;
}
}
}
else
{
lean_object* v_code_3760_; lean_object* v___x_3761_; 
v_code_3760_ = lean_ctor_get(v_a_3721_, 0);
lean_inc_ref(v_code_3760_);
v___x_3761_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_3760_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_dec_ref(v___x_3761_);
v_a_3714_ = v___x_3720_;
goto v___jp_3713_;
}
else
{
lean_dec(v_a_3701_);
return v___x_3761_;
}
}
}
v___jp_3713_:
{
size_t v___x_3715_; size_t v___x_3716_; 
v___x_3715_ = ((size_t)1ULL);
v___x_3716_ = lean_usize_add(v_i_3704_, v___x_3715_);
v_i_3704_ = v___x_3716_;
v_b_3705_ = v_a_3714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(lean_object* v_x_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_decl_3771_; lean_object* v_k_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; 
switch(lean_obj_tag(v_x_3762_))
{
case 0:
{
lean_object* v_decl_3782_; lean_object* v_k_3783_; lean_object* v_fvarId_3784_; lean_object* v_value_3785_; lean_object* v___x_3786_; 
v_decl_3782_ = lean_ctor_get(v_x_3762_, 0);
lean_inc_ref(v_decl_3782_);
v_k_3783_ = lean_ctor_get(v_x_3762_, 1);
lean_inc_ref(v_k_3783_);
lean_dec_ref(v_x_3762_);
v_fvarId_3784_ = lean_ctor_get(v_decl_3782_, 0);
lean_inc(v_fvarId_3784_);
v_value_3785_ = lean_ctor_get(v_decl_3782_, 3);
lean_inc(v_value_3785_);
lean_dec_ref(v_decl_3782_);
lean_inc(v_value_3785_);
v___x_3786_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_value_3785_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment___redArg(v_fvarId_3784_, v_a_3787_, v_a_3763_, v_a_3764_, v_a_3768_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_dec_ref(v___x_3788_);
if (lean_obj_tag(v_value_3785_) == 4)
{
lean_object* v_fvarId_3789_; lean_object* v_args_3790_; uint8_t v___x_3791_; lean_object* v___x_3792_; 
v_fvarId_3789_ = lean_ctor_get(v_value_3785_, 0);
lean_inc(v_fvarId_3789_);
v_args_3790_ = lean_ctor_get(v_value_3785_, 1);
lean_inc_ref(v_args_3790_);
lean_dec_ref(v_value_3785_);
v___x_3791_ = 0;
v___x_3792_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3791_, v_fvarId_3789_, v_a_3766_);
lean_dec(v_fvarId_3789_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3792_);
if (lean_obj_tag(v_a_3793_) == 1)
{
lean_object* v_val_3794_; lean_object* v___x_3795_; 
v_val_3794_ = lean_ctor_get(v_a_3793_, 0);
lean_inc(v_val_3794_);
lean_dec_ref(v_a_3793_);
v___x_3795_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_val_3794_, v_args_3790_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_dec_ref(v___x_3795_);
v_x_3762_ = v_k_3783_;
goto _start;
}
else
{
lean_dec_ref(v_k_3783_);
return v___x_3795_;
}
}
else
{
lean_dec(v_a_3793_);
lean_dec_ref(v_args_3790_);
v_x_3762_ = v_k_3783_;
goto _start;
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v_args_3790_);
lean_dec_ref(v_k_3783_);
v_a_3798_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3792_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3792_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_dec(v_value_3785_);
v_x_3762_ = v_k_3783_;
goto _start;
}
}
else
{
lean_dec(v_value_3785_);
lean_dec_ref(v_k_3783_);
return v___x_3788_;
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec(v_value_3785_);
lean_dec(v_fvarId_3784_);
lean_dec_ref(v_k_3783_);
v_a_3807_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3786_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3786_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3815_; lean_object* v_args_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; 
v_fvarId_3815_ = lean_ctor_get(v_x_3762_, 0);
lean_inc(v_fvarId_3815_);
v_args_3816_ = lean_ctor_get(v_x_3762_, 1);
lean_inc_ref(v_args_3816_);
lean_dec_ref(v_x_3762_);
v___x_3817_ = 0;
v___x_3818_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_3817_, v_fvarId_3815_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___y_3821_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
v___x_3823_ = lean_unsigned_to_nat(0u);
v___x_3824_ = lean_array_get_size(v_args_3816_);
v___x_3825_ = lean_nat_dec_lt(v___x_3823_, v___x_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; 
v___x_3826_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3819_, v_args_3816_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
return v___x_3826_;
}
else
{
lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3827_ = lean_box(0);
v___x_3828_ = lean_nat_dec_le(v___x_3824_, v___x_3824_);
if (v___x_3828_ == 0)
{
if (v___x_3825_ == 0)
{
lean_object* v___x_3829_; 
v___x_3829_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3819_, v_args_3816_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
return v___x_3829_;
}
else
{
size_t v___x_3830_; size_t v___x_3831_; lean_object* v___x_3832_; 
v___x_3830_ = ((size_t)0ULL);
v___x_3831_ = lean_usize_of_nat(v___x_3824_);
v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3816_, v___x_3830_, v___x_3831_, v___x_3827_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
v___y_3821_ = v___x_3832_;
goto v___jp_3820_;
}
}
else
{
size_t v___x_3833_; size_t v___x_3834_; lean_object* v___x_3835_; 
v___x_3833_ = ((size_t)0ULL);
v___x_3834_ = lean_usize_of_nat(v___x_3824_);
v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_args_3816_, v___x_3833_, v___x_3834_, v___x_3827_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
v___y_3821_ = v___x_3835_;
goto v___jp_3820_;
}
}
v___jp_3820_:
{
if (lean_obj_tag(v___y_3821_) == 0)
{
lean_object* v___x_3822_; 
lean_dec_ref(v___y_3821_);
v___x_3822_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_a_3819_, v_args_3816_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
return v___x_3822_;
}
else
{
lean_dec(v_a_3819_);
lean_dec_ref(v_args_3816_);
return v___y_3821_;
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v_args_3816_);
v_a_3836_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3818_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3818_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
case 4:
{
lean_object* v_cases_3844_; lean_object* v_discr_3845_; lean_object* v_alts_3846_; lean_object* v___x_3847_; 
v_cases_3844_ = lean_ctor_get(v_x_3762_, 0);
lean_inc_ref(v_cases_3844_);
lean_dec_ref(v_x_3762_);
v_discr_3845_ = lean_ctor_get(v_cases_3844_, 2);
lean_inc(v_discr_3845_);
v_alts_3846_ = lean_ctor_get(v_cases_3844_, 3);
lean_inc_ref(v_alts_3846_);
lean_dec_ref(v_cases_3844_);
v___x_3847_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_discr_3845_, v_a_3763_, v_a_3764_);
lean_dec(v_discr_3845_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; size_t v_sz_3850_; size_t v___x_3851_; lean_object* v___x_3852_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref(v___x_3847_);
v___x_3849_ = lean_box(0);
v_sz_3850_ = lean_array_size(v_alts_3846_);
v___x_3851_ = ((size_t)0ULL);
v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3848_, v_alts_3846_, v_sz_3850_, v___x_3851_, v___x_3849_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
lean_dec_ref(v_alts_3846_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; 
v_unused_3860_ = lean_ctor_get(v___x_3852_, 0);
lean_dec(v_unused_3860_);
v___x_3854_ = v___x_3852_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_dec(v___x_3852_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3849_);
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3849_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
else
{
return v___x_3852_;
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_alts_3846_);
v_a_3861_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3847_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3847_);
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
case 5:
{
lean_object* v_fvarId_3869_; lean_object* v___x_3870_; 
v_fvarId_3869_ = lean_ctor_get(v_x_3762_, 0);
lean_inc(v_fvarId_3869_);
lean_dec_ref(v_x_3762_);
v___x_3870_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3869_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v___x_3871_; 
lean_dec_ref(v___x_3870_);
v___x_3871_ = l_Lean_Compiler_LCNF_UnreachableBranches_findVarValue___redArg(v_fvarId_3869_, v_a_3763_, v_a_3764_);
lean_dec(v_fvarId_3869_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3873_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref(v___x_3871_);
v___x_3873_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v_a_3872_, v_a_3763_, v_a_3764_, v_a_3768_);
return v___x_3873_;
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
v_a_3874_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3871_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3871_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_dec(v_fvarId_3869_);
return v___x_3870_;
}
}
case 6:
{
lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3889_; 
v_isSharedCheck_3889_ = !lean_is_exclusive(v_x_3762_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; 
v_unused_3890_ = lean_ctor_get(v_x_3762_, 0);
lean_dec(v_unused_3890_);
v___x_3883_ = v_x_3762_;
v_isShared_3884_ = v_isSharedCheck_3889_;
goto v_resetjp_3882_;
}
else
{
lean_dec(v_x_3762_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3889_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3885_ = lean_box(0);
if (v_isShared_3884_ == 0)
{
lean_ctor_set_tag(v___x_3883_, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3885_);
v___x_3887_ = v___x_3883_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
default: 
{
lean_object* v_decl_3891_; lean_object* v_k_3892_; 
v_decl_3891_ = lean_ctor_get(v_x_3762_, 0);
lean_inc_ref(v_decl_3891_);
v_k_3892_ = lean_ctor_get(v_x_3762_, 1);
lean_inc_ref(v_k_3892_);
lean_dec_ref(v_x_3762_);
v_decl_3771_ = v_decl_3891_;
v_k_3772_ = v_k_3892_;
v___y_3773_ = v_a_3763_;
v___y_3774_ = v_a_3764_;
v___y_3775_ = v_a_3765_;
v___y_3776_ = v_a_3766_;
v___y_3777_ = v_a_3767_;
v___y_3778_ = v_a_3768_;
goto v___jp_3770_;
}
}
v___jp_3770_:
{
lean_object* v_value_3779_; lean_object* v___x_3780_; 
v_value_3779_ = lean_ctor_get(v_decl_3771_, 4);
lean_inc_ref(v_value_3779_);
lean_dec_ref(v_decl_3771_);
v___x_3780_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3779_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_dec_ref(v___x_3780_);
v_x_3762_ = v_k_3772_;
v_a_3763_ = v___y_3773_;
v_a_3764_ = v___y_3774_;
v_a_3765_ = v___y_3775_;
v_a_3766_ = v___y_3776_;
v_a_3767_ = v___y_3777_;
v_a_3768_ = v___y_3778_;
goto _start;
}
else
{
lean_dec_ref(v_k_3772_);
return v___x_3780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(lean_object* v_var_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
uint8_t v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = 0;
v___x_3902_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_3901_, v_var_3893_, v_a_3897_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3935_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3935_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3935_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_object* v_val_3907_; lean_object* v_params_3908_; lean_object* v_value_3909_; lean_object* v___x_3910_; 
lean_del_object(v___x_3905_);
v_val_3907_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_val_3907_);
lean_dec_ref(v_a_3903_);
v_params_3908_ = lean_ctor_get(v_val_3907_, 2);
lean_inc_ref(v_params_3908_);
v_value_3909_ = lean_ctor_get(v_val_3907_, 4);
lean_inc_ref(v_value_3909_);
lean_dec(v_val_3907_);
v___x_3910_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateFunDeclParamsTop(v_params_3908_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
lean_dec_ref(v_params_3908_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3922_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3922_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3922_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
uint8_t v___x_3915_; 
v___x_3915_ = lean_unbox(v_a_3911_);
lean_dec(v_a_3911_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3918_; 
lean_dec_ref(v_value_3909_);
v___x_3916_ = lean_box(0);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3916_);
v___x_3918_ = v___x_3913_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
else
{
lean_object* v___x_3920_; 
lean_del_object(v___x_3913_);
lean_inc_ref(v_value_3909_);
v___x_3920_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_resetNestedFunDeclParams(v_value_3909_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v___x_3921_; 
lean_dec_ref(v___x_3920_);
v___x_3921_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_value_3909_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
return v___x_3921_;
}
else
{
lean_dec_ref(v_value_3909_);
return v___x_3920_;
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v_value_3909_);
v_a_3923_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3910_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3910_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
lean_dec(v_a_3903_);
v___x_3931_ = lean_box(0);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3931_);
v___x_3933_ = v___x_3905_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
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
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
v_a_3936_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3902_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3902_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(lean_object* v_arg_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
if (lean_obj_tag(v_arg_3944_) == 1)
{
lean_object* v_fvarId_3952_; lean_object* v___x_3953_; 
v_fvarId_3952_ = lean_ctor_get(v_arg_3944_, 0);
v___x_3953_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_fvarId_3952_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_);
return v___x_3953_;
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3954_ = lean_box(0);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg___boxed(lean_object* v_arg_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunArg(v_arg_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_arg_3956_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2___boxed(lean_object* v_as_3965_, lean_object* v_i_3966_, lean_object* v_stop_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
size_t v_i_boxed_3976_; size_t v_stop_boxed_3977_; lean_object* v_res_3978_; 
v_i_boxed_3976_ = lean_unbox_usize(v_i_3966_);
lean_dec(v_i_3966_);
v_stop_boxed_3977_ = lean_unbox_usize(v_stop_3967_);
lean_dec(v_stop_3967_);
v_res_3978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__2(v_as_3965_, v_i_boxed_3976_, v_stop_boxed_3977_, v_b_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec_ref(v_as_3965_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall___boxed(lean_object* v_funDecl_3979_, lean_object* v_args_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpFunCall(v_funDecl_3979_, v_args_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar___boxed(lean_object* v_var_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_handleFunVar(v_var_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
lean_dec(v_var_3989_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8___boxed(lean_object* v_a_3998_, lean_object* v_as_3999_, lean_object* v_sz_4000_, lean_object* v_i_4001_, lean_object* v_b_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
size_t v_sz_boxed_4010_; size_t v_i_boxed_4011_; lean_object* v_res_4012_; 
v_sz_boxed_4010_ = lean_unbox_usize(v_sz_4000_);
lean_dec(v_sz_4000_);
v_i_boxed_4011_ = lean_unbox_usize(v_i_4001_);
lean_dec(v_i_4001_);
v_res_4012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__8(v_a_3998_, v_as_3999_, v_sz_boxed_4010_, v_i_boxed_4011_, v_b_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec_ref(v_as_3999_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_interpCode___boxed(lean_object* v_x_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_x_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue___boxed(lean_object* v_letVal_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue(v_letVal_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_a_4026_);
lean_dec_ref(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0(lean_object* v_inst_4031_, lean_object* v_R_4032_, lean_object* v_a_4033_, lean_object* v_b_4034_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__0___redArg(v_a_4033_, v_b_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(size_t v_sz_4036_, size_t v_i_4037_, lean_object* v_bs_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___redArg(v_sz_4036_, v_i_4037_, v_bs_4038_, v___y_4039_, v___y_4040_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1___boxed(lean_object* v_sz_4047_, lean_object* v_i_4048_, lean_object* v_bs_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
size_t v_sz_boxed_4057_; size_t v_i_boxed_4058_; lean_object* v_res_4059_; 
v_sz_boxed_4057_ = lean_unbox_usize(v_sz_4047_);
lean_dec(v_sz_4047_);
v_i_boxed_4058_ = lean_unbox_usize(v_i_4048_);
lean_dec(v_i_4048_);
v_res_4059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_interpCode_interpLetValue_spec__1(v_sz_boxed_4057_, v_i_boxed_4058_, v_bs_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(lean_object* v_as_4060_, size_t v_i_4061_, size_t v_stop_4062_, lean_object* v_b_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___redArg(v_as_4060_, v_i_4061_, v_stop_4062_, v_b_4063_, v___y_4064_, v___y_4065_, v___y_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6___boxed(lean_object* v_as_4072_, lean_object* v_i_4073_, lean_object* v_stop_4074_, lean_object* v_b_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
size_t v_i_boxed_4083_; size_t v_stop_boxed_4084_; lean_object* v_res_4085_; 
v_i_boxed_4083_ = lean_unbox_usize(v_i_4073_);
lean_dec(v_i_4073_);
v_stop_boxed_4084_ = lean_unbox_usize(v_stop_4074_);
lean_dec(v_stop_4074_);
v_res_4085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__6(v_as_4072_, v_i_boxed_4083_, v_stop_boxed_4084_, v_b_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec_ref(v_as_4072_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(lean_object* v_as_4086_, size_t v_i_4087_, size_t v_stop_4088_, lean_object* v_b_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_as_4086_, v_i_4087_, v_stop_4088_, v_b_4089_, v___y_4090_, v___y_4091_, v___y_4095_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___boxed(lean_object* v_as_4098_, lean_object* v_i_4099_, lean_object* v_stop_4100_, lean_object* v_b_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
size_t v_i_boxed_4109_; size_t v_stop_boxed_4110_; lean_object* v_res_4111_; 
v_i_boxed_4109_ = lean_unbox_usize(v_i_4099_);
lean_dec(v_i_4099_);
v_stop_boxed_4110_ = lean_unbox_usize(v_stop_4100_);
lean_dec(v_stop_4100_);
v_res_4111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7(v_as_4098_, v_i_boxed_4109_, v_stop_boxed_4110_, v_b_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec_ref(v_as_4098_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(lean_object* v_cls_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v_options_4118_; uint8_t v_hasTrace_4119_; 
v_options_4118_ = lean_ctor_get(v___y_4116_, 2);
v_hasTrace_4119_ = lean_ctor_get_uint8(v_options_4118_, sizeof(void*)*1);
if (v_hasTrace_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
lean_dec(v_cls_4115_);
v___x_4120_ = lean_box(v_hasTrace_4119_);
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
return v___x_4121_;
}
else
{
lean_object* v_inheritedTraceOptions_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; uint8_t v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v_inheritedTraceOptions_4122_ = lean_ctor_get(v___y_4116_, 13);
v___x_4123_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1));
v___x_4124_ = l_Lean_Name_append(v___x_4123_, v_cls_4115_);
v___x_4125_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4122_, v_options_4118_, v___x_4124_);
lean_dec(v___x_4124_);
v___x_4126_ = lean_box(v___x_4125_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___boxed(lean_object* v_cls_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_cls_4128_, v___y_4129_);
lean_dec_ref(v___y_4129_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(lean_object* v_cls_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v_cls_4132_, v___y_4137_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___boxed(lean_object* v_cls_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0(v_cls_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
return v_res_4149_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4150_ = lean_unsigned_to_nat(32u);
v___x_4151_ = lean_mk_empty_array_with_capacity(v___x_4150_);
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4153_ = ((size_t)5ULL);
v___x_4154_ = lean_unsigned_to_nat(0u);
v___x_4155_ = lean_unsigned_to_nat(32u);
v___x_4156_ = lean_mk_empty_array_with_capacity(v___x_4155_);
v___x_4157_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__0);
v___x_4158_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
lean_ctor_set(v___x_4158_, 1, v___x_4156_);
lean_ctor_set(v___x_4158_, 2, v___x_4154_);
lean_ctor_set(v___x_4158_, 3, v___x_4154_);
lean_ctor_set_usize(v___x_4158_, 4, v___x_4153_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; lean_object* v_traceState_4162_; lean_object* v_traces_4163_; lean_object* v___x_4164_; lean_object* v_traceState_4165_; lean_object* v_env_4166_; lean_object* v_nextMacroScope_4167_; lean_object* v_ngen_4168_; lean_object* v_auxDeclNGen_4169_; lean_object* v_cache_4170_; lean_object* v_messages_4171_; lean_object* v_infoState_4172_; lean_object* v_snapshotTasks_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4192_; 
v___x_4161_ = lean_st_ref_get(v___y_4159_);
v_traceState_4162_ = lean_ctor_get(v___x_4161_, 4);
lean_inc_ref(v_traceState_4162_);
lean_dec(v___x_4161_);
v_traces_4163_ = lean_ctor_get(v_traceState_4162_, 0);
lean_inc_ref(v_traces_4163_);
lean_dec_ref(v_traceState_4162_);
v___x_4164_ = lean_st_ref_take(v___y_4159_);
v_traceState_4165_ = lean_ctor_get(v___x_4164_, 4);
v_env_4166_ = lean_ctor_get(v___x_4164_, 0);
v_nextMacroScope_4167_ = lean_ctor_get(v___x_4164_, 1);
v_ngen_4168_ = lean_ctor_get(v___x_4164_, 2);
v_auxDeclNGen_4169_ = lean_ctor_get(v___x_4164_, 3);
v_cache_4170_ = lean_ctor_get(v___x_4164_, 5);
v_messages_4171_ = lean_ctor_get(v___x_4164_, 6);
v_infoState_4172_ = lean_ctor_get(v___x_4164_, 7);
v_snapshotTasks_4173_ = lean_ctor_get(v___x_4164_, 8);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4175_ = v___x_4164_;
v_isShared_4176_ = v_isSharedCheck_4192_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_snapshotTasks_4173_);
lean_inc(v_infoState_4172_);
lean_inc(v_messages_4171_);
lean_inc(v_cache_4170_);
lean_inc(v_traceState_4165_);
lean_inc(v_auxDeclNGen_4169_);
lean_inc(v_ngen_4168_);
lean_inc(v_nextMacroScope_4167_);
lean_inc(v_env_4166_);
lean_dec(v___x_4164_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4192_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
uint64_t v_tid_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4190_; 
v_tid_4177_ = lean_ctor_get_uint64(v_traceState_4165_, sizeof(void*)*1);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_traceState_4165_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; 
v_unused_4191_ = lean_ctor_get(v_traceState_4165_, 0);
lean_dec(v_unused_4191_);
v___x_4179_ = v_traceState_4165_;
v_isShared_4180_ = v_isSharedCheck_4190_;
goto v_resetjp_4178_;
}
else
{
lean_dec(v_traceState_4165_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4190_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4181_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___closed__1);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v___x_4181_);
v___x_4183_ = v___x_4179_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4181_);
lean_ctor_set_uint64(v_reuseFailAlloc_4189_, sizeof(void*)*1, v_tid_4177_);
v___x_4183_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4185_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 4, v___x_4183_);
v___x_4185_ = v___x_4175_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_env_4166_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v_nextMacroScope_4167_);
lean_ctor_set(v_reuseFailAlloc_4188_, 2, v_ngen_4168_);
lean_ctor_set(v_reuseFailAlloc_4188_, 3, v_auxDeclNGen_4169_);
lean_ctor_set(v_reuseFailAlloc_4188_, 4, v___x_4183_);
lean_ctor_set(v_reuseFailAlloc_4188_, 5, v_cache_4170_);
lean_ctor_set(v_reuseFailAlloc_4188_, 6, v_messages_4171_);
lean_ctor_set(v_reuseFailAlloc_4188_, 7, v_infoState_4172_);
lean_ctor_set(v_reuseFailAlloc_4188_, 8, v_snapshotTasks_4173_);
v___x_4185_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = lean_st_ref_set(v___y_4159_, v___x_4185_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_traces_4163_);
return v___x_4187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg___boxed(lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v___y_4193_);
lean_dec(v___y_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v___y_4201_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___boxed(lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1(v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
return v_res_4211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(lean_object* v_opts_4212_, lean_object* v_opt_4213_){
_start:
{
lean_object* v_name_4214_; lean_object* v_defValue_4215_; lean_object* v_map_4216_; lean_object* v___x_4217_; 
v_name_4214_ = lean_ctor_get(v_opt_4213_, 0);
v_defValue_4215_ = lean_ctor_get(v_opt_4213_, 1);
v_map_4216_ = lean_ctor_get(v_opts_4212_, 0);
v___x_4217_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4216_, v_name_4214_);
if (lean_obj_tag(v___x_4217_) == 0)
{
uint8_t v___x_4218_; 
v___x_4218_ = lean_unbox(v_defValue_4215_);
return v___x_4218_;
}
else
{
lean_object* v_val_4219_; 
v_val_4219_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_val_4219_);
lean_dec_ref(v___x_4217_);
if (lean_obj_tag(v_val_4219_) == 1)
{
uint8_t v_v_4220_; 
v_v_4220_ = lean_ctor_get_uint8(v_val_4219_, 0);
lean_dec_ref(v_val_4219_);
return v_v_4220_;
}
else
{
uint8_t v___x_4221_; 
lean_dec(v_val_4219_);
v___x_4221_ = lean_unbox(v_defValue_4215_);
return v___x_4221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2___boxed(lean_object* v_opts_4222_, lean_object* v_opt_4223_){
_start:
{
uint8_t v_res_4224_; lean_object* v_r_4225_; 
v_res_4224_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_opts_4222_, v_opt_4223_);
lean_dec_ref(v_opt_4223_);
lean_dec_ref(v_opts_4222_);
v_r_4225_ = lean_box(v_res_4224_);
return v_r_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(size_t v_sz_4226_, size_t v_i_4227_, lean_object* v_bs_4228_){
_start:
{
uint8_t v___x_4229_; 
v___x_4229_ = lean_usize_dec_lt(v_i_4227_, v_sz_4226_);
if (v___x_4229_ == 0)
{
return v_bs_4228_;
}
else
{
lean_object* v_v_4230_; lean_object* v_msg_4231_; lean_object* v___x_4232_; lean_object* v_bs_x27_4233_; size_t v___x_4234_; size_t v___x_4235_; lean_object* v___x_4236_; 
v_v_4230_ = lean_array_uget_borrowed(v_bs_4228_, v_i_4227_);
v_msg_4231_ = lean_ctor_get(v_v_4230_, 1);
lean_inc_ref(v_msg_4231_);
v___x_4232_ = lean_unsigned_to_nat(0u);
v_bs_x27_4233_ = lean_array_uset(v_bs_4228_, v_i_4227_, v___x_4232_);
v___x_4234_ = ((size_t)1ULL);
v___x_4235_ = lean_usize_add(v_i_4227_, v___x_4234_);
v___x_4236_ = lean_array_uset(v_bs_x27_4233_, v_i_4227_, v_msg_4231_);
v_i_4227_ = v___x_4235_;
v_bs_4228_ = v___x_4236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_4238_, lean_object* v_i_4239_, lean_object* v_bs_4240_){
_start:
{
size_t v_sz_boxed_4241_; size_t v_i_boxed_4242_; lean_object* v_res_4243_; 
v_sz_boxed_4241_ = lean_unbox_usize(v_sz_4238_);
lean_dec(v_sz_4238_);
v_i_boxed_4242_ = lean_unbox_usize(v_i_4239_);
lean_dec(v_i_4239_);
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(v_sz_boxed_4241_, v_i_boxed_4242_, v_bs_4240_);
return v_res_4243_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4244_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__0);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4247_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__1);
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4248_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
lean_ctor_set(v___x_4249_, 2, v___x_4248_);
lean_ctor_set(v___x_4249_, 3, v___x_4247_);
lean_ctor_set(v___x_4249_, 4, v___x_4247_);
lean_ctor_set(v___x_4249_, 5, v___x_4247_);
lean_ctor_set(v___x_4249_, 6, v___x_4247_);
lean_ctor_set(v___x_4249_, 7, v___x_4247_);
lean_ctor_set(v___x_4249_, 8, v___x_4247_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(lean_object* v_oldTraces_4250_, lean_object* v_data_4251_, lean_object* v_ref_4252_, lean_object* v_msg_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_options_4259_; lean_object* v___x_4260_; lean_object* v_traceState_4261_; lean_object* v_traces_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v_options_4259_ = lean_ctor_get(v___y_4256_, 2);
v___x_4260_ = lean_st_ref_get(v___y_4257_);
v_traceState_4261_ = lean_ctor_get(v___x_4260_, 4);
lean_inc_ref(v_traceState_4261_);
lean_dec(v___x_4260_);
v_traces_4262_ = lean_ctor_get(v_traceState_4261_, 0);
lean_inc_ref(v_traces_4262_);
lean_dec_ref(v_traceState_4261_);
v___x_4263_ = lean_st_ref_get(v___y_4257_);
v___x_4264_ = lean_st_ref_get(v___y_4255_);
v___x_4265_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4254_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4322_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4268_ = v___x_4265_;
v_isShared_4269_ = v_isSharedCheck_4322_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4265_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4322_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v_env_4270_; lean_object* v_lctx_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4320_; 
v_env_4270_ = lean_ctor_get(v___x_4263_, 0);
lean_inc_ref(v_env_4270_);
lean_dec(v___x_4263_);
v_lctx_4271_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4320_ == 0)
{
lean_object* v_unused_4321_; 
v_unused_4321_ = lean_ctor_get(v___x_4264_, 1);
lean_dec(v_unused_4321_);
v___x_4273_ = v___x_4264_;
v_isShared_4274_ = v_isSharedCheck_4320_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_lctx_4271_);
lean_dec(v___x_4264_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4320_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v_traceState_4277_; lean_object* v_env_4278_; lean_object* v_nextMacroScope_4279_; lean_object* v_ngen_4280_; lean_object* v_auxDeclNGen_4281_; lean_object* v_cache_4282_; lean_object* v_messages_4283_; lean_object* v_infoState_4284_; lean_object* v_snapshotTasks_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4319_; 
v___x_4275_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2);
v___x_4276_ = lean_st_ref_take(v___y_4257_);
v_traceState_4277_ = lean_ctor_get(v___x_4276_, 4);
v_env_4278_ = lean_ctor_get(v___x_4276_, 0);
v_nextMacroScope_4279_ = lean_ctor_get(v___x_4276_, 1);
v_ngen_4280_ = lean_ctor_get(v___x_4276_, 2);
v_auxDeclNGen_4281_ = lean_ctor_get(v___x_4276_, 3);
v_cache_4282_ = lean_ctor_get(v___x_4276_, 5);
v_messages_4283_ = lean_ctor_get(v___x_4276_, 6);
v_infoState_4284_ = lean_ctor_get(v___x_4276_, 7);
v_snapshotTasks_4285_ = lean_ctor_get(v___x_4276_, 8);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4287_ = v___x_4276_;
v_isShared_4288_ = v_isSharedCheck_4319_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_snapshotTasks_4285_);
lean_inc(v_infoState_4284_);
lean_inc(v_messages_4283_);
lean_inc(v_cache_4282_);
lean_inc(v_traceState_4277_);
lean_inc(v_auxDeclNGen_4281_);
lean_inc(v_ngen_4280_);
lean_inc(v_nextMacroScope_4279_);
lean_inc(v_env_4278_);
lean_dec(v___x_4276_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4319_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
uint64_t v_tid_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4317_; 
v_tid_4289_ = lean_ctor_get_uint64(v_traceState_4277_, sizeof(void*)*1);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_traceState_4277_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; 
v_unused_4318_ = lean_ctor_get(v_traceState_4277_, 0);
lean_dec(v_unused_4318_);
v___x_4291_ = v_traceState_4277_;
v_isShared_4292_ = v_isSharedCheck_4317_;
goto v_resetjp_4290_;
}
else
{
lean_dec(v_traceState_4277_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4317_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4293_; size_t v_sz_4294_; size_t v___x_4295_; lean_object* v___x_4296_; lean_object* v_msg_4297_; uint8_t v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4302_; 
v___x_4293_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4262_);
lean_dec_ref(v_traces_4262_);
v_sz_4294_ = lean_array_size(v___x_4293_);
v___x_4295_ = ((size_t)0ULL);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4_spec__5(v_sz_4294_, v___x_4295_, v___x_4293_);
v_msg_4297_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4297_, 0, v_data_4251_);
lean_ctor_set(v_msg_4297_, 1, v_msg_4253_);
lean_ctor_set(v_msg_4297_, 2, v___x_4296_);
v___x_4298_ = lean_unbox(v_a_4266_);
lean_dec(v_a_4266_);
v___x_4299_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4271_, v___x_4298_);
lean_dec_ref(v_lctx_4271_);
lean_inc_ref(v_options_4259_);
v___x_4300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4300_, 0, v_env_4270_);
lean_ctor_set(v___x_4300_, 1, v___x_4275_);
lean_ctor_set(v___x_4300_, 2, v___x_4299_);
lean_ctor_set(v___x_4300_, 3, v_options_4259_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set_tag(v___x_4273_, 3);
lean_ctor_set(v___x_4273_, 1, v_msg_4297_);
lean_ctor_set(v___x_4273_, 0, v___x_4300_);
v___x_4302_ = v___x_4273_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_msg_4297_);
v___x_4302_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v_ref_4252_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
v___x_4304_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4250_, v___x_4303_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v___x_4304_);
v___x_4306_ = v___x_4291_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4304_);
lean_ctor_set_uint64(v_reuseFailAlloc_4315_, sizeof(void*)*1, v_tid_4289_);
v___x_4306_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4308_; 
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 4, v___x_4306_);
v___x_4308_ = v___x_4287_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_env_4278_);
lean_ctor_set(v_reuseFailAlloc_4314_, 1, v_nextMacroScope_4279_);
lean_ctor_set(v_reuseFailAlloc_4314_, 2, v_ngen_4280_);
lean_ctor_set(v_reuseFailAlloc_4314_, 3, v_auxDeclNGen_4281_);
lean_ctor_set(v_reuseFailAlloc_4314_, 4, v___x_4306_);
lean_ctor_set(v_reuseFailAlloc_4314_, 5, v_cache_4282_);
lean_ctor_set(v_reuseFailAlloc_4314_, 6, v_messages_4283_);
lean_ctor_set(v_reuseFailAlloc_4314_, 7, v_infoState_4284_);
lean_ctor_set(v_reuseFailAlloc_4314_, 8, v_snapshotTasks_4285_);
v___x_4308_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4309_ = lean_st_ref_set(v___y_4257_, v___x_4308_);
v___x_4310_ = lean_box(0);
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 0, v___x_4310_);
v___x_4312_ = v___x_4268_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
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
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v___x_4264_);
lean_dec(v___x_4263_);
lean_dec_ref(v_traces_4262_);
lean_dec_ref(v_msg_4253_);
lean_dec(v_ref_4252_);
lean_dec_ref(v_data_4251_);
lean_dec_ref(v_oldTraces_4250_);
v_a_4323_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4265_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4265_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_4331_, lean_object* v_data_4332_, lean_object* v_ref_4333_, lean_object* v_msg_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(v_oldTraces_4331_, v_data_4332_, v_ref_4333_, v_msg_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
return v_res_4340_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(lean_object* v_e_4341_){
_start:
{
if (lean_obj_tag(v_e_4341_) == 0)
{
uint8_t v___x_4342_; 
v___x_4342_ = 2;
return v___x_4342_;
}
else
{
uint8_t v___x_4343_; 
v___x_4343_ = 0;
return v___x_4343_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3___boxed(lean_object* v_e_4344_){
_start:
{
uint8_t v_res_4345_; lean_object* v_r_4346_; 
v_res_4345_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(v_e_4344_);
lean_dec_ref(v_e_4344_);
v_r_4346_ = lean_box(v_res_4345_);
return v_r_4346_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(lean_object* v_x_4347_){
_start:
{
if (lean_obj_tag(v_x_4347_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
v_a_4349_ = lean_ctor_get(v_x_4347_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_x_4347_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v_x_4347_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v_x_4347_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
lean_ctor_set_tag(v___x_4351_, 1);
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v_a_4357_ = lean_ctor_get(v_x_4347_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v_x_4347_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v_x_4347_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v_x_4347_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 0);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg___boxed(lean_object* v_x_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_x_4365_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(lean_object* v_opts_4368_, lean_object* v_opt_4369_){
_start:
{
lean_object* v_name_4370_; lean_object* v_defValue_4371_; lean_object* v_map_4372_; lean_object* v___x_4373_; 
v_name_4370_ = lean_ctor_get(v_opt_4369_, 0);
v_defValue_4371_ = lean_ctor_get(v_opt_4369_, 1);
v_map_4372_ = lean_ctor_get(v_opts_4368_, 0);
v___x_4373_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4372_, v_name_4370_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_inc(v_defValue_4371_);
return v_defValue_4371_;
}
else
{
lean_object* v_val_4374_; 
v_val_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_val_4374_);
lean_dec_ref(v___x_4373_);
if (lean_obj_tag(v_val_4374_) == 3)
{
lean_object* v_v_4375_; 
v_v_4375_ = lean_ctor_get(v_val_4374_, 0);
lean_inc(v_v_4375_);
lean_dec_ref(v_val_4374_);
return v_v_4375_;
}
else
{
lean_dec(v_val_4374_);
lean_inc(v_defValue_4371_);
return v_defValue_4371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6___boxed(lean_object* v_opts_4376_, lean_object* v_opt_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(v_opts_4376_, v_opt_4377_);
lean_dec_ref(v_opt_4377_);
lean_dec_ref(v_opts_4376_);
return v_res_4378_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__0___closed__0));
v___x_4380_ = l_Lean_stringToMessageData(v___x_4379_);
return v___x_4380_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4381_; double v___x_4382_; 
v___x_4381_ = lean_unsigned_to_nat(0u);
v___x_4382_ = lean_float_of_nat(v___x_4381_);
return v___x_4382_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__2));
v___x_4385_ = l_Lean_stringToMessageData(v___x_4384_);
return v___x_4385_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4(void){
_start:
{
lean_object* v___x_4386_; double v___x_4387_; 
v___x_4386_ = lean_unsigned_to_nat(1000u);
v___x_4387_ = lean_float_of_nat(v___x_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(lean_object* v_cls_4388_, uint8_t v_collapsed_4389_, lean_object* v_tag_4390_, lean_object* v_opts_4391_, uint8_t v_clsEnabled_4392_, lean_object* v_oldTraces_4393_, lean_object* v_msg_4394_, lean_object* v_resStartStop_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v_fst_4403_; lean_object* v_snd_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4494_; 
v_fst_4403_ = lean_ctor_get(v_resStartStop_4395_, 0);
v_snd_4404_ = lean_ctor_get(v_resStartStop_4395_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_resStartStop_4395_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4406_ = v_resStartStop_4395_;
v_isShared_4407_ = v_isSharedCheck_4494_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_snd_4404_);
lean_inc(v_fst_4403_);
lean_dec(v_resStartStop_4395_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4494_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v_data_4411_; lean_object* v_fst_4414_; lean_object* v_snd_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4493_; 
v_fst_4414_ = lean_ctor_get(v_snd_4404_, 0);
v_snd_4415_ = lean_ctor_get(v_snd_4404_, 1);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_snd_4404_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4417_ = v_snd_4404_;
v_isShared_4418_ = v_isSharedCheck_4493_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_snd_4415_);
lean_inc(v_fst_4414_);
lean_dec(v_snd_4404_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4493_;
goto v_resetjp_4416_;
}
v___jp_4408_:
{
lean_object* v___x_4412_; 
lean_inc(v___y_4409_);
v___x_4412_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(v_oldTraces_4393_, v_data_4411_, v___y_4409_, v___y_4410_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v___x_4413_; 
lean_dec_ref(v___x_4412_);
v___x_4413_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_fst_4403_);
return v___x_4413_;
}
else
{
lean_dec(v_fst_4403_);
return v___x_4412_;
}
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; uint8_t v___x_4420_; lean_object* v___y_4422_; lean_object* v_a_4423_; uint8_t v___y_4447_; double v___y_4478_; 
v___x_4419_ = l_Lean_trace_profiler;
v___x_4420_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_opts_4391_, v___x_4419_);
if (v___x_4420_ == 0)
{
v___y_4447_ = v___x_4420_;
goto v___jp_4446_;
}
else
{
lean_object* v___x_4483_; uint8_t v___x_4484_; 
v___x_4483_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4484_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_opts_4391_, v___x_4483_);
if (v___x_4484_ == 0)
{
lean_object* v___x_4485_; lean_object* v___x_4486_; double v___x_4487_; double v___x_4488_; double v___x_4489_; 
v___x_4485_ = l_Lean_trace_profiler_threshold;
v___x_4486_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(v_opts_4391_, v___x_4485_);
v___x_4487_ = lean_float_of_nat(v___x_4486_);
v___x_4488_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__4);
v___x_4489_ = lean_float_div(v___x_4487_, v___x_4488_);
v___y_4478_ = v___x_4489_;
goto v___jp_4477_;
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; double v___x_4492_; 
v___x_4490_ = l_Lean_trace_profiler_threshold;
v___x_4491_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__6(v_opts_4391_, v___x_4490_);
v___x_4492_ = lean_float_of_nat(v___x_4491_);
v___y_4478_ = v___x_4492_;
goto v___jp_4477_;
}
}
v___jp_4421_:
{
uint8_t v_result_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4429_; 
v_result_4424_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__3(v_fst_4403_);
v___x_4425_ = l_Lean_TraceResult_toEmoji(v_result_4424_);
v___x_4426_ = l_Lean_stringToMessageData(v___x_4425_);
v___x_4427_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__0);
if (v_isShared_4418_ == 0)
{
lean_ctor_set_tag(v___x_4417_, 7);
lean_ctor_set(v___x_4417_, 1, v___x_4427_);
lean_ctor_set(v___x_4417_, 0, v___x_4426_);
v___x_4429_ = v___x_4417_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v___x_4427_);
v___x_4429_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
lean_object* v_m_4431_; 
if (v_isShared_4407_ == 0)
{
lean_ctor_set_tag(v___x_4406_, 7);
lean_ctor_set(v___x_4406_, 1, v_a_4423_);
lean_ctor_set(v___x_4406_, 0, v___x_4429_);
v_m_4431_ = v___x_4406_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4429_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v_a_4423_);
v_m_4431_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; double v___x_4434_; lean_object* v_data_4435_; 
v___x_4432_ = lean_box(v_result_4424_);
v___x_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
v___x_4434_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1);
lean_inc_ref(v_tag_4390_);
lean_inc_ref(v___x_4433_);
lean_inc(v_cls_4388_);
v_data_4435_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4435_, 0, v_cls_4388_);
lean_ctor_set(v_data_4435_, 1, v___x_4433_);
lean_ctor_set(v_data_4435_, 2, v_tag_4390_);
lean_ctor_set_float(v_data_4435_, sizeof(void*)*3, v___x_4434_);
lean_ctor_set_float(v_data_4435_, sizeof(void*)*3 + 8, v___x_4434_);
lean_ctor_set_uint8(v_data_4435_, sizeof(void*)*3 + 16, v_collapsed_4389_);
if (v___x_4420_ == 0)
{
lean_dec_ref(v___x_4433_);
lean_dec(v_snd_4415_);
lean_dec(v_fst_4414_);
lean_dec_ref(v_tag_4390_);
lean_dec(v_cls_4388_);
v___y_4409_ = v___y_4422_;
v___y_4410_ = v_m_4431_;
v_data_4411_ = v_data_4435_;
goto v___jp_4408_;
}
else
{
lean_object* v_data_4436_; double v___x_4437_; double v___x_4438_; 
lean_dec_ref(v_data_4435_);
v_data_4436_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4436_, 0, v_cls_4388_);
lean_ctor_set(v_data_4436_, 1, v___x_4433_);
lean_ctor_set(v_data_4436_, 2, v_tag_4390_);
v___x_4437_ = lean_unbox_float(v_fst_4414_);
lean_dec(v_fst_4414_);
lean_ctor_set_float(v_data_4436_, sizeof(void*)*3, v___x_4437_);
v___x_4438_ = lean_unbox_float(v_snd_4415_);
lean_dec(v_snd_4415_);
lean_ctor_set_float(v_data_4436_, sizeof(void*)*3 + 8, v___x_4438_);
lean_ctor_set_uint8(v_data_4436_, sizeof(void*)*3 + 16, v_collapsed_4389_);
v___y_4409_ = v___y_4422_;
v___y_4410_ = v_m_4431_;
v_data_4411_ = v_data_4436_;
goto v___jp_4408_;
}
}
}
}
v___jp_4441_:
{
lean_object* v_ref_4442_; lean_object* v___x_4443_; 
v_ref_4442_ = lean_ctor_get(v___y_4400_, 5);
lean_inc(v___y_4401_);
lean_inc_ref(v___y_4400_);
lean_inc(v___y_4399_);
lean_inc_ref(v___y_4398_);
lean_inc(v___y_4397_);
lean_inc_ref(v___y_4396_);
lean_inc(v_fst_4403_);
v___x_4443_ = lean_apply_8(v_msg_4394_, v_fst_4403_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, lean_box(0));
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4444_);
lean_dec_ref(v___x_4443_);
v___y_4422_ = v_ref_4442_;
v_a_4423_ = v_a_4444_;
goto v___jp_4421_;
}
else
{
lean_object* v___x_4445_; 
lean_dec_ref(v___x_4443_);
v___x_4445_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__3);
v___y_4422_ = v_ref_4442_;
v_a_4423_ = v___x_4445_;
goto v___jp_4421_;
}
}
v___jp_4446_:
{
if (v_clsEnabled_4392_ == 0)
{
if (v___y_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v_traceState_4449_; lean_object* v_env_4450_; lean_object* v_nextMacroScope_4451_; lean_object* v_ngen_4452_; lean_object* v_auxDeclNGen_4453_; lean_object* v_cache_4454_; lean_object* v_messages_4455_; lean_object* v_infoState_4456_; lean_object* v_snapshotTasks_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4476_; 
lean_del_object(v___x_4417_);
lean_dec(v_snd_4415_);
lean_dec(v_fst_4414_);
lean_del_object(v___x_4406_);
lean_dec_ref(v_msg_4394_);
lean_dec_ref(v_tag_4390_);
lean_dec(v_cls_4388_);
v___x_4448_ = lean_st_ref_take(v___y_4401_);
v_traceState_4449_ = lean_ctor_get(v___x_4448_, 4);
v_env_4450_ = lean_ctor_get(v___x_4448_, 0);
v_nextMacroScope_4451_ = lean_ctor_get(v___x_4448_, 1);
v_ngen_4452_ = lean_ctor_get(v___x_4448_, 2);
v_auxDeclNGen_4453_ = lean_ctor_get(v___x_4448_, 3);
v_cache_4454_ = lean_ctor_get(v___x_4448_, 5);
v_messages_4455_ = lean_ctor_get(v___x_4448_, 6);
v_infoState_4456_ = lean_ctor_get(v___x_4448_, 7);
v_snapshotTasks_4457_ = lean_ctor_get(v___x_4448_, 8);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4459_ = v___x_4448_;
v_isShared_4460_ = v_isSharedCheck_4476_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_snapshotTasks_4457_);
lean_inc(v_infoState_4456_);
lean_inc(v_messages_4455_);
lean_inc(v_cache_4454_);
lean_inc(v_traceState_4449_);
lean_inc(v_auxDeclNGen_4453_);
lean_inc(v_ngen_4452_);
lean_inc(v_nextMacroScope_4451_);
lean_inc(v_env_4450_);
lean_dec(v___x_4448_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4476_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
uint64_t v_tid_4461_; lean_object* v_traces_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4475_; 
v_tid_4461_ = lean_ctor_get_uint64(v_traceState_4449_, sizeof(void*)*1);
v_traces_4462_ = lean_ctor_get(v_traceState_4449_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_traceState_4449_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4464_ = v_traceState_4449_;
v_isShared_4465_ = v_isSharedCheck_4475_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_traces_4462_);
lean_dec(v_traceState_4449_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4475_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4466_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4393_, v_traces_4462_);
lean_dec_ref(v_traces_4462_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4466_);
v___x_4468_ = v___x_4464_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4466_);
lean_ctor_set_uint64(v_reuseFailAlloc_4474_, sizeof(void*)*1, v_tid_4461_);
v___x_4468_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4470_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 4, v___x_4468_);
v___x_4470_ = v___x_4459_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_env_4450_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v_nextMacroScope_4451_);
lean_ctor_set(v_reuseFailAlloc_4473_, 2, v_ngen_4452_);
lean_ctor_set(v_reuseFailAlloc_4473_, 3, v_auxDeclNGen_4453_);
lean_ctor_set(v_reuseFailAlloc_4473_, 4, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4473_, 5, v_cache_4454_);
lean_ctor_set(v_reuseFailAlloc_4473_, 6, v_messages_4455_);
lean_ctor_set(v_reuseFailAlloc_4473_, 7, v_infoState_4456_);
lean_ctor_set(v_reuseFailAlloc_4473_, 8, v_snapshotTasks_4457_);
v___x_4470_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = lean_st_ref_set(v___y_4401_, v___x_4470_);
v___x_4472_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_fst_4403_);
return v___x_4472_;
}
}
}
}
}
else
{
goto v___jp_4441_;
}
}
else
{
goto v___jp_4441_;
}
}
v___jp_4477_:
{
double v___x_4479_; double v___x_4480_; double v___x_4481_; uint8_t v___x_4482_; 
v___x_4479_ = lean_unbox_float(v_snd_4415_);
v___x_4480_ = lean_unbox_float(v_fst_4414_);
v___x_4481_ = lean_float_sub(v___x_4479_, v___x_4480_);
v___x_4482_ = lean_float_decLt(v___y_4478_, v___x_4481_);
v___y_4447_ = v___x_4482_;
goto v___jp_4446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___boxed(lean_object* v_cls_4495_, lean_object* v_collapsed_4496_, lean_object* v_tag_4497_, lean_object* v_opts_4498_, lean_object* v_clsEnabled_4499_, lean_object* v_oldTraces_4500_, lean_object* v_msg_4501_, lean_object* v_resStartStop_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
uint8_t v_collapsed_boxed_4510_; uint8_t v_clsEnabled_boxed_4511_; lean_object* v_res_4512_; 
v_collapsed_boxed_4510_ = lean_unbox(v_collapsed_4496_);
v_clsEnabled_boxed_4511_ = lean_unbox(v_clsEnabled_4499_);
v_res_4512_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v_cls_4495_, v_collapsed_boxed_4510_, v_tag_4497_, v_opts_4498_, v_clsEnabled_boxed_4511_, v_oldTraces_4500_, v_msg_4501_, v_resStartStop_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec_ref(v_opts_4498_);
return v_res_4512_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__0));
v___x_4515_ = l_Lean_stringToMessageData(v___x_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0(lean_object* v_name_4516_, lean_object* v_x_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4525_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___closed__1);
v___x_4526_ = l_Lean_MessageData_ofName(v_name_4516_);
v___x_4527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4525_);
lean_ctor_set(v___x_4527_, 1, v___x_4526_);
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___boxed(lean_object* v_name_4529_, lean_object* v_x_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0(v_name_4529_, v_x_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v_x_4530_);
return v_res_4538_;
}
}
static double _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4542_; double v___x_4543_; 
v___x_4542_ = lean_unsigned_to_nat(1000000000u);
v___x_4543_ = lean_float_of_nat(v___x_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(lean_object* v_upperBound_4549_, lean_object* v___x_4550_, lean_object* v_a_4551_, lean_object* v_b_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_a_4561_; uint8_t v___x_4565_; 
v___x_4565_ = lean_nat_dec_lt(v_a_4551_, v_upperBound_4549_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
lean_dec(v_a_4551_);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v_b_4552_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; lean_object* v_toSignature_4568_; lean_object* v_value_4569_; lean_object* v_name_4570_; lean_object* v_params_4571_; uint8_t v_safe_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
lean_dec_ref(v_b_4552_);
v___x_4567_ = lean_array_fget_borrowed(v___x_4550_, v_a_4551_);
v_toSignature_4568_ = lean_ctor_get(v___x_4567_, 0);
v_value_4569_ = lean_ctor_get(v___x_4567_, 1);
v_name_4570_ = lean_ctor_get(v_toSignature_4568_, 0);
v_params_4571_ = lean_ctor_get(v_toSignature_4568_, 3);
v_safe_4572_ = lean_ctor_get_uint8(v_toSignature_4568_, sizeof(void*)*4);
v___x_4573_ = lean_box(0);
v___x_4574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0));
if (v_safe_4572_ == 0)
{
v_a_4561_ = v___x_4574_;
goto v___jp_4560_;
}
else
{
lean_object* v___x_4575_; 
v___x_4575_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4551_, v___y_4554_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v___y_4578_; lean_object* v_decls_4608_; lean_object* v___f_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___y_4614_; lean_object* v___y_4615_; uint8_t v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v_a_4620_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; uint8_t v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v_a_4639_; lean_object* v___y_4649_; lean_object* v___y_4650_; uint8_t v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4729_; uint8_t v___x_4738_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref(v___x_4575_);
v_decls_4608_ = lean_ctor_get(v___y_4553_, 0);
lean_inc(v_name_4570_);
v___f_4609_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4609_, 0, v_name_4570_);
v___x_4610_ = lean_unsigned_to_nat(0u);
v___x_4611_ = lean_array_get_size(v_params_4571_);
lean_inc(v_a_4551_);
lean_inc_ref(v_decls_4608_);
v___x_4612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4612_, 0, v_decls_4608_);
lean_ctor_set(v___x_4612_, 1, v_a_4551_);
v___x_4738_ = lean_nat_dec_lt(v___x_4610_, v___x_4611_);
if (v___x_4738_ == 0)
{
goto v___jp_4702_;
}
else
{
uint8_t v___x_4739_; 
v___x_4739_ = lean_nat_dec_le(v___x_4611_, v___x_4611_);
if (v___x_4739_ == 0)
{
if (v___x_4738_ == 0)
{
goto v___jp_4702_;
}
else
{
size_t v___x_4740_; size_t v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = ((size_t)0ULL);
v___x_4741_ = lean_usize_of_nat(v___x_4611_);
v___x_4742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4571_, v___x_4740_, v___x_4741_, v___x_4573_, v___x_4612_, v___y_4554_, v___y_4558_);
v___y_4729_ = v___x_4742_;
goto v___jp_4728_;
}
}
else
{
size_t v___x_4743_; size_t v___x_4744_; lean_object* v___x_4745_; 
v___x_4743_ = ((size_t)0ULL);
v___x_4744_ = lean_usize_of_nat(v___x_4611_);
v___x_4745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_interpCode_spec__7___redArg(v_params_4571_, v___x_4743_, v___x_4744_, v___x_4573_, v___x_4612_, v___y_4554_, v___y_4558_);
v___y_4729_ = v___x_4745_;
goto v___jp_4728_;
}
}
v___jp_4577_:
{
if (lean_obj_tag(v___y_4578_) == 0)
{
lean_object* v___x_4579_; 
lean_dec_ref(v___y_4578_);
v___x_4579_ = l_Lean_Compiler_LCNF_UnreachableBranches_getFunVal___redArg(v_a_4551_, v___y_4554_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4591_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4582_ = v___x_4579_;
v_isShared_4583_ = v_isSharedCheck_4591_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4579_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4591_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
uint8_t v___x_4584_; 
v___x_4584_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_beq(v_a_4576_, v_a_4580_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4589_; 
lean_dec(v_a_4551_);
v___x_4585_ = lean_box(v_safe_4572_);
v___x_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
v___x_4587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
lean_ctor_set(v___x_4587_, 1, v___x_4573_);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 0, v___x_4587_);
v___x_4589_ = v___x_4582_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4587_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
else
{
lean_del_object(v___x_4582_);
v_a_4561_ = v___x_4574_;
goto v___jp_4560_;
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec(v_a_4576_);
lean_dec(v_a_4551_);
v_a_4592_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4579_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4579_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec(v_a_4576_);
lean_dec(v_a_4551_);
v_a_4600_ = lean_ctor_get(v___y_4578_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___y_4578_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___y_4578_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___y_4578_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
v___jp_4613_:
{
lean_object* v___x_4621_; double v___x_4622_; double v___x_4623_; double v___x_4624_; double v___x_4625_; double v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4621_ = lean_io_mono_nanos_now();
v___x_4622_ = lean_float_of_nat(v___y_4618_);
v___x_4623_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1);
v___x_4624_ = lean_float_div(v___x_4622_, v___x_4623_);
v___x_4625_ = lean_float_of_nat(v___x_4621_);
v___x_4626_ = lean_float_div(v___x_4625_, v___x_4623_);
v___x_4627_ = lean_box_float(v___x_4624_);
v___x_4628_ = lean_box_float(v___x_4626_);
v___x_4629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4627_);
lean_ctor_set(v___x_4629_, 1, v___x_4628_);
v___x_4630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4630_, 0, v_a_4620_);
lean_ctor_set(v___x_4630_, 1, v___x_4629_);
v___x_4631_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_4615_, v_safe_4572_, v___y_4614_, v___y_4619_, v___y_4616_, v___y_4617_, v___f_4609_, v___x_4630_, v___x_4612_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v___x_4612_);
v___y_4578_ = v___x_4631_;
goto v___jp_4577_;
}
v___jp_4632_:
{
lean_object* v___x_4640_; double v___x_4641_; double v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4640_ = lean_io_get_num_heartbeats();
v___x_4641_ = lean_float_of_nat(v___y_4635_);
v___x_4642_ = lean_float_of_nat(v___x_4640_);
v___x_4643_ = lean_box_float(v___x_4641_);
v___x_4644_ = lean_box_float(v___x_4642_);
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4643_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
v___x_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4646_, 0, v_a_4639_);
lean_ctor_set(v___x_4646_, 1, v___x_4645_);
v___x_4647_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_4634_, v_safe_4572_, v___y_4633_, v___y_4638_, v___y_4636_, v___y_4637_, v___f_4609_, v___x_4646_, v___x_4612_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v___x_4612_);
v___y_4578_ = v___x_4647_;
goto v___jp_4577_;
}
v___jp_4648_:
{
lean_object* v___x_4654_; 
v___x_4654_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v___y_4558_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_object* v_a_4655_; lean_object* v___x_4656_; uint8_t v___x_4657_; 
v_a_4655_ = lean_ctor_get(v___x_4654_, 0);
lean_inc(v_a_4655_);
lean_dec_ref(v___x_4654_);
v___x_4656_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4657_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_4652_, v___x_4656_);
if (v___x_4657_ == 0)
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = lean_io_mono_nanos_now();
v___x_4659_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4653_, v___x_4612_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4659_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set_tag(v___x_4662_, 1);
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
v___y_4614_ = v___y_4649_;
v___y_4615_ = v___y_4650_;
v___y_4616_ = v___y_4651_;
v___y_4617_ = v_a_4655_;
v___y_4618_ = v___x_4658_;
v___y_4619_ = v___y_4652_;
v_a_4620_ = v___x_4665_;
goto v___jp_4613_;
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
v_a_4668_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4659_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4659_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set_tag(v___x_4670_, 0);
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
v___y_4614_ = v___y_4649_;
v___y_4615_ = v___y_4650_;
v___y_4616_ = v___y_4651_;
v___y_4617_ = v_a_4655_;
v___y_4618_ = v___x_4658_;
v___y_4619_ = v___y_4652_;
v_a_4620_ = v___x_4673_;
goto v___jp_4613_;
}
}
}
}
else
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = lean_io_get_num_heartbeats();
v___x_4677_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v___y_4653_, v___x_4612_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4677_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4677_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
lean_ctor_set_tag(v___x_4680_, 1);
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
v___y_4633_ = v___y_4649_;
v___y_4634_ = v___y_4650_;
v___y_4635_ = v___x_4676_;
v___y_4636_ = v___y_4651_;
v___y_4637_ = v_a_4655_;
v___y_4638_ = v___y_4652_;
v_a_4639_ = v___x_4683_;
goto v___jp_4632_;
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
v_a_4686_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4677_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4677_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
lean_ctor_set_tag(v___x_4688_, 0);
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
v___y_4633_ = v___y_4649_;
v___y_4634_ = v___y_4650_;
v___y_4635_ = v___x_4676_;
v___y_4636_ = v___y_4651_;
v___y_4637_ = v_a_4655_;
v___y_4638_ = v___y_4652_;
v_a_4639_ = v___x_4691_;
goto v___jp_4632_;
}
}
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___f_4609_);
lean_dec(v_a_4576_);
lean_dec(v_a_4551_);
v_a_4694_ = lean_ctor_get(v___x_4654_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4654_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4654_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
v___jp_4702_:
{
if (lean_obj_tag(v_value_4569_) == 0)
{
lean_object* v_options_4703_; uint8_t v_hasTrace_4704_; 
v_options_4703_ = lean_ctor_get(v___y_4557_, 2);
v_hasTrace_4704_ = lean_ctor_get_uint8(v_options_4703_, sizeof(void*)*1);
if (v_hasTrace_4704_ == 0)
{
lean_object* v_code_4705_; lean_object* v___x_4706_; 
lean_dec_ref(v___f_4609_);
v_code_4705_ = lean_ctor_get(v_value_4569_, 0);
lean_inc_ref(v_code_4705_);
v___x_4706_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4705_, v___x_4612_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v___x_4612_);
v___y_4578_ = v___x_4706_;
goto v___jp_4577_;
}
else
{
lean_object* v_code_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v_code_4707_ = lean_ctor_get(v_value_4569_, 0);
v___x_4708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_4709_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___x_4708_, v___y_4557_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
lean_inc(v_a_4710_);
lean_dec_ref(v___x_4709_);
v___x_4711_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
v___x_4712_ = lean_unbox(v_a_4710_);
if (v___x_4712_ == 0)
{
lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___x_4713_ = l_Lean_trace_profiler;
v___x_4714_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_options_4703_, v___x_4713_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; 
lean_dec(v_a_4710_);
lean_dec_ref(v___f_4609_);
lean_inc_ref(v_code_4707_);
v___x_4715_ = l_Lean_Compiler_LCNF_UnreachableBranches_interpCode(v_code_4707_, v___x_4612_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v___x_4612_);
v___y_4578_ = v___x_4715_;
goto v___jp_4577_;
}
else
{
uint8_t v___x_4716_; 
v___x_4716_ = lean_unbox(v_a_4710_);
lean_dec(v_a_4710_);
lean_inc_ref(v_code_4707_);
v___y_4649_ = v___x_4711_;
v___y_4650_ = v___x_4708_;
v___y_4651_ = v___x_4716_;
v___y_4652_ = v_options_4703_;
v___y_4653_ = v_code_4707_;
goto v___jp_4648_;
}
}
else
{
uint8_t v___x_4717_; 
v___x_4717_ = lean_unbox(v_a_4710_);
lean_dec(v_a_4710_);
lean_inc_ref(v_code_4707_);
v___y_4649_ = v___x_4711_;
v___y_4650_ = v___x_4708_;
v___y_4651_ = v___x_4717_;
v___y_4652_ = v_options_4703_;
v___y_4653_ = v_code_4707_;
goto v___jp_4648_;
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___f_4609_);
lean_dec(v_a_4576_);
lean_dec(v_a_4551_);
v_a_4718_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4709_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4709_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
else
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
lean_dec_ref(v___f_4609_);
v___x_4726_ = lean_box(1);
v___x_4727_ = l_Lean_Compiler_LCNF_UnreachableBranches_updateCurrFnSummary___redArg(v___x_4726_, v___x_4612_, v___y_4554_, v___y_4558_);
lean_dec_ref(v___x_4612_);
v___y_4578_ = v___x_4727_;
goto v___jp_4577_;
}
}
v___jp_4728_:
{
if (lean_obj_tag(v___y_4729_) == 0)
{
lean_dec_ref(v___y_4729_);
goto v___jp_4702_;
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___f_4609_);
lean_dec(v_a_4576_);
lean_dec(v_a_4551_);
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
lean_dec(v_a_4551_);
v_a_4746_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4575_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4575_);
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
v___jp_4560_:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = lean_unsigned_to_nat(1u);
v___x_4563_ = lean_nat_add(v_a_4551_, v___x_4562_);
lean_dec(v_a_4551_);
v_a_4551_ = v___x_4563_;
v_b_4552_ = v_a_4561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___boxed(lean_object* v_upperBound_4754_, lean_object* v___x_4755_, lean_object* v_a_4756_, lean_object* v_b_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(v_upperBound_4754_, v___x_4755_, v_a_4756_, v_b_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
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
v___x_4776_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__0));
v___x_4777_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(v___x_4774_, v_decls_4773_, v___x_4775_, v___x_4776_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
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
lean_dec_ref(v_fst_4782_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5(lean_object* v_00_u03b1_4809_, lean_object* v_x_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___redArg(v_x_4810_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4819_, lean_object* v_x_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__5(v_00_u03b1_4819_, v_x_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4(lean_object* v_upperBound_4829_, lean_object* v___x_4830_, lean_object* v_inst_4831_, lean_object* v_R_4832_, lean_object* v_a_4833_, lean_object* v_b_4834_, lean_object* v_c_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg(v_upperBound_4829_, v___x_4830_, v_a_4833_, v_b_4834_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___boxed(lean_object* v_upperBound_4844_, lean_object* v___x_4845_, lean_object* v_inst_4846_, lean_object* v_R_4847_, lean_object* v_a_4848_, lean_object* v_b_4849_, lean_object* v_c_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4(v_upperBound_4844_, v___x_4845_, v_inst_4846_, v_R_4847_, v_a_4848_, v_b_4849_, v_c_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4(lean_object* v_oldTraces_4859_, lean_object* v_data_4860_, lean_object* v_ref_4861_, lean_object* v_msg_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg(v_oldTraces_4859_, v_data_4860_, v_ref_4861_, v_msg_4862_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___boxed(lean_object* v_oldTraces_4871_, lean_object* v_data_4872_, lean_object* v_ref_4873_, lean_object* v_msg_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4(v_oldTraces_4871_, v_data_4872_, v_ref_4873_, v_msg_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
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
v___x_4906_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2);
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
v___x_4931_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1);
v___x_4932_ = 0;
v___x_4933_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
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
v___x_4943_ = lean_st_ref_set(v___y_4890_, v___x_4942_);
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
lean_object* v___x_5032_; lean_object* v_decls_5033_; lean_object* v_funVals_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5079_; 
v___x_5032_ = lean_st_ref_take(v_a_5023_);
v_decls_5033_ = lean_ctor_get(v_a_5022_, 0);
v_funVals_5034_ = lean_ctor_get(v___x_5032_, 1);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5079_ == 0)
{
lean_object* v_unused_5080_; 
v_unused_5080_ = lean_ctor_get(v___x_5032_, 0);
lean_dec(v_unused_5080_);
v___x_5036_ = v___x_5032_;
v_isShared_5037_ = v_isSharedCheck_5079_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_funVals_5034_);
lean_dec(v___x_5032_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5079_;
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
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v___x_5040_);
lean_ctor_set(v_reuseFailAlloc_5078_, 1, v_funVals_5034_);
v___x_5042_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = lean_st_ref_set(v_a_5023_, v___x_5042_);
v___x_5044_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferStep(v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; uint8_t v___x_5046_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref(v___x_5044_);
v___x_5046_ = lean_unbox(v_a_5045_);
lean_dec(v_a_5045_);
if (v___x_5046_ == 0)
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
lean_dec_ref(v_a_5022_);
v___x_5047_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_5048_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___x_5047_, v_a_5026_);
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v_a_5049_; uint8_t v___x_5050_; 
v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
lean_inc(v_a_5049_);
lean_dec_ref(v___x_5048_);
v___x_5050_ = lean_unbox(v_a_5049_);
lean_dec(v_a_5049_);
if (v___x_5050_ == 0)
{
lean_dec(v_n_5021_);
goto v___jp_5029_;
}
else
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5051_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__1);
v___x_5052_ = l_Nat_reprFast(v_n_5021_);
v___x_5053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
v___x_5054_ = l_Lean_MessageData_ofFormat(v___x_5053_);
v___x_5055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5051_);
lean_ctor_set(v___x_5055_, 1, v___x_5054_);
v___x_5056_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3, &l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___closed__3);
v___x_5057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5055_);
lean_ctor_set(v___x_5057_, 1, v___x_5056_);
v___x_5058_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg(v___x_5047_, v___x_5057_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_dec_ref(v___x_5058_);
goto v___jp_5029_;
}
else
{
return v___x_5058_;
}
}
}
else
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
lean_dec(v_n_5021_);
v_a_5059_ = lean_ctor_get(v___x_5048_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_5048_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_5048_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = lean_unsigned_to_nat(1u);
v___x_5068_ = lean_nat_add(v_n_5021_, v___x_5067_);
lean_dec(v_n_5021_);
v_n_5021_ = v___x_5068_;
goto _start;
}
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5077_; 
lean_dec_ref(v_a_5022_);
lean_dec(v_n_5021_);
v_a_5070_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5072_ = v___x_5044_;
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_5044_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_inferMain___boxed(lean_object* v_n_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v_n_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_);
lean_dec(v_a_5087_);
lean_dec_ref(v_a_5086_);
lean_dec(v_a_5085_);
lean_dec_ref(v_a_5084_);
lean_dec(v_a_5083_);
return v_res_5089_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0(void){
_start:
{
uint8_t v___x_5090_; lean_object* v___x_5091_; 
v___x_5090_ = 0;
v___x_5091_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(lean_object* v_msg_5092_){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___closed__0);
v___x_5094_ = lean_panic_fn(v___x_5093_, v_msg_5092_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(lean_object* v_cls_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_options_5098_; uint8_t v_hasTrace_5099_; 
v_options_5098_ = lean_ctor_get(v___y_5096_, 2);
v_hasTrace_5099_ = lean_ctor_get_uint8(v_options_5098_, sizeof(void*)*1);
if (v_hasTrace_5099_ == 0)
{
lean_object* v___x_5100_; lean_object* v___x_5101_; 
lean_dec(v_cls_5095_);
v___x_5100_ = lean_box(v_hasTrace_5099_);
v___x_5101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5100_);
return v___x_5101_;
}
else
{
lean_object* v_inheritedTraceOptions_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v_inheritedTraceOptions_5102_ = lean_ctor_get(v___y_5096_, 13);
v___x_5103_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg___closed__1));
v___x_5104_ = l_Lean_Name_append(v___x_5103_, v_cls_5095_);
v___x_5105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5102_, v_options_5098_, v___x_5104_);
lean_dec(v___x_5104_);
v___x_5106_ = lean_box(v___x_5105_);
v___x_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
return v___x_5107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg___boxed(lean_object* v_cls_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_5108_, v___y_5109_);
lean_dec_ref(v___y_5109_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(lean_object* v_cls_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_5112_, v___y_5115_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___boxed(lean_object* v_cls_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2(v_cls_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
lean_dec(v___y_5121_);
lean_dec_ref(v___y_5120_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(lean_object* v_cls_5126_, lean_object* v_msg_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v_options_5133_; lean_object* v_ref_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v_options_5133_ = lean_ctor_get(v___y_5130_, 2);
v_ref_5134_ = lean_ctor_get(v___y_5130_, 5);
v___x_5135_ = lean_st_ref_get(v___y_5131_);
v___x_5136_ = lean_st_ref_get(v___y_5129_);
v___x_5137_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5128_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5196_; 
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5140_ = v___x_5137_;
v_isShared_5141_ = v_isSharedCheck_5196_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5137_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5196_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v_env_5142_; lean_object* v_lctx_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5194_; 
v_env_5142_ = lean_ctor_get(v___x_5135_, 0);
lean_inc_ref(v_env_5142_);
lean_dec(v___x_5135_);
v_lctx_5143_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5194_ == 0)
{
lean_object* v_unused_5195_; 
v_unused_5195_ = lean_ctor_get(v___x_5136_, 1);
lean_dec(v_unused_5195_);
v___x_5145_ = v___x_5136_;
v_isShared_5146_ = v_isSharedCheck_5194_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_lctx_5143_);
lean_dec(v___x_5136_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5194_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v_traceState_5149_; lean_object* v_env_5150_; lean_object* v_nextMacroScope_5151_; lean_object* v_ngen_5152_; lean_object* v_auxDeclNGen_5153_; lean_object* v_cache_5154_; lean_object* v_messages_5155_; lean_object* v_infoState_5156_; lean_object* v_snapshotTasks_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5193_; 
v___x_5147_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3_spec__4___redArg___closed__2);
v___x_5148_ = lean_st_ref_take(v___y_5131_);
v_traceState_5149_ = lean_ctor_get(v___x_5148_, 4);
v_env_5150_ = lean_ctor_get(v___x_5148_, 0);
v_nextMacroScope_5151_ = lean_ctor_get(v___x_5148_, 1);
v_ngen_5152_ = lean_ctor_get(v___x_5148_, 2);
v_auxDeclNGen_5153_ = lean_ctor_get(v___x_5148_, 3);
v_cache_5154_ = lean_ctor_get(v___x_5148_, 5);
v_messages_5155_ = lean_ctor_get(v___x_5148_, 6);
v_infoState_5156_ = lean_ctor_get(v___x_5148_, 7);
v_snapshotTasks_5157_ = lean_ctor_get(v___x_5148_, 8);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5159_ = v___x_5148_;
v_isShared_5160_ = v_isSharedCheck_5193_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_snapshotTasks_5157_);
lean_inc(v_infoState_5156_);
lean_inc(v_messages_5155_);
lean_inc(v_cache_5154_);
lean_inc(v_traceState_5149_);
lean_inc(v_auxDeclNGen_5153_);
lean_inc(v_ngen_5152_);
lean_inc(v_nextMacroScope_5151_);
lean_inc(v_env_5150_);
lean_dec(v___x_5148_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5193_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
uint64_t v_tid_5161_; lean_object* v_traces_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5192_; 
v_tid_5161_ = lean_ctor_get_uint64(v_traceState_5149_, sizeof(void*)*1);
v_traces_5162_ = lean_ctor_get(v_traceState_5149_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v_traceState_5149_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5164_ = v_traceState_5149_;
v_isShared_5165_ = v_isSharedCheck_5192_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_traces_5162_);
lean_dec(v_traceState_5149_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5192_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
uint8_t v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5170_; 
v___x_5166_ = lean_unbox(v_a_5138_);
lean_dec(v_a_5138_);
v___x_5167_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5143_, v___x_5166_);
lean_dec_ref(v_lctx_5143_);
lean_inc_ref(v_options_5133_);
v___x_5168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5168_, 0, v_env_5142_);
lean_ctor_set(v___x_5168_, 1, v___x_5147_);
lean_ctor_set(v___x_5168_, 2, v___x_5167_);
lean_ctor_set(v___x_5168_, 3, v_options_5133_);
if (v_isShared_5146_ == 0)
{
lean_ctor_set_tag(v___x_5145_, 3);
lean_ctor_set(v___x_5145_, 1, v_msg_5127_);
lean_ctor_set(v___x_5145_, 0, v___x_5168_);
v___x_5170_ = v___x_5145_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5168_);
lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_msg_5127_);
v___x_5170_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; double v___x_5172_; uint8_t v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5181_; 
v___x_5171_ = lean_box(0);
v___x_5172_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3___closed__1);
v___x_5173_ = 0;
v___x_5174_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
v___x_5175_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5175_, 0, v_cls_5126_);
lean_ctor_set(v___x_5175_, 1, v___x_5171_);
lean_ctor_set(v___x_5175_, 2, v___x_5174_);
lean_ctor_set_float(v___x_5175_, sizeof(void*)*3, v___x_5172_);
lean_ctor_set_float(v___x_5175_, sizeof(void*)*3 + 8, v___x_5172_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*3 + 16, v___x_5173_);
v___x_5176_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__1___redArg___closed__0));
v___x_5177_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5175_);
lean_ctor_set(v___x_5177_, 1, v___x_5170_);
lean_ctor_set(v___x_5177_, 2, v___x_5176_);
lean_inc(v_ref_5134_);
v___x_5178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5178_, 0, v_ref_5134_);
lean_ctor_set(v___x_5178_, 1, v___x_5177_);
v___x_5179_ = l_Lean_PersistentArray_push___redArg(v_traces_5162_, v___x_5178_);
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 0, v___x_5179_);
v___x_5181_ = v___x_5164_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5179_);
lean_ctor_set_uint64(v_reuseFailAlloc_5190_, sizeof(void*)*1, v_tid_5161_);
v___x_5181_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
lean_object* v___x_5183_; 
if (v_isShared_5160_ == 0)
{
lean_ctor_set(v___x_5159_, 4, v___x_5181_);
v___x_5183_ = v___x_5159_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_env_5150_);
lean_ctor_set(v_reuseFailAlloc_5189_, 1, v_nextMacroScope_5151_);
lean_ctor_set(v_reuseFailAlloc_5189_, 2, v_ngen_5152_);
lean_ctor_set(v_reuseFailAlloc_5189_, 3, v_auxDeclNGen_5153_);
lean_ctor_set(v_reuseFailAlloc_5189_, 4, v___x_5181_);
lean_ctor_set(v_reuseFailAlloc_5189_, 5, v_cache_5154_);
lean_ctor_set(v_reuseFailAlloc_5189_, 6, v_messages_5155_);
lean_ctor_set(v_reuseFailAlloc_5189_, 7, v_infoState_5156_);
lean_ctor_set(v_reuseFailAlloc_5189_, 8, v_snapshotTasks_5157_);
v___x_5183_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5187_; 
v___x_5184_ = lean_st_ref_set(v___y_5131_, v___x_5183_);
v___x_5185_ = lean_box(0);
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 0, v___x_5185_);
v___x_5187_ = v___x_5140_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
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
}
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
lean_dec(v___x_5136_);
lean_dec(v___x_5135_);
lean_dec_ref(v_msg_5127_);
lean_dec(v_cls_5126_);
v_a_5197_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5137_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5137_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3___boxed(lean_object* v_cls_5205_, lean_object* v_msg_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_cls_5205_, v_msg_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(lean_object* v_as_5213_, size_t v_i_5214_, size_t v_stop_5215_, lean_object* v_b_5216_){
_start:
{
uint8_t v___x_5218_; 
v___x_5218_ = lean_usize_dec_eq(v_i_5214_, v_stop_5215_);
if (v___x_5218_ == 0)
{
lean_object* v_fst_5219_; lean_object* v_snd_5220_; lean_object* v___x_5221_; lean_object* v_snd_5222_; lean_object* v_fst_5223_; lean_object* v_fst_5224_; lean_object* v_snd_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5240_; 
v_fst_5219_ = lean_ctor_get(v_b_5216_, 0);
lean_inc(v_fst_5219_);
v_snd_5220_ = lean_ctor_get(v_b_5216_, 1);
lean_inc(v_snd_5220_);
lean_dec_ref(v_b_5216_);
v___x_5221_ = lean_array_uget_borrowed(v_as_5213_, v_i_5214_);
v_snd_5222_ = lean_ctor_get(v___x_5221_, 1);
lean_inc(v_snd_5222_);
v_fst_5223_ = lean_ctor_get(v___x_5221_, 0);
v_fst_5224_ = lean_ctor_get(v_snd_5222_, 0);
v_snd_5225_ = lean_ctor_get(v_snd_5222_, 1);
v_isSharedCheck_5240_ = !lean_is_exclusive(v_snd_5222_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5227_ = v_snd_5222_;
v_isShared_5228_ = v_isSharedCheck_5240_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_snd_5225_);
lean_inc(v_fst_5224_);
lean_dec(v_snd_5222_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5240_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v_fvarId_5229_; uint8_t v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5235_; 
v_fvarId_5229_ = lean_ctor_get(v_fst_5223_, 0);
v___x_5230_ = 0;
v___x_5231_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_5230_, v_fst_5224_, v_fst_5219_);
lean_dec(v_fst_5224_);
v___x_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5232_, 0, v_snd_5225_);
lean_inc(v_fvarId_5229_);
v___x_5233_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_UnreachableBranches_updateVarAssignment_spec__0___redArg(v_snd_5220_, v_fvarId_5229_, v___x_5232_);
if (v_isShared_5228_ == 0)
{
lean_ctor_set(v___x_5227_, 1, v___x_5233_);
lean_ctor_set(v___x_5227_, 0, v___x_5231_);
v___x_5235_ = v___x_5227_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5231_);
lean_ctor_set(v_reuseFailAlloc_5239_, 1, v___x_5233_);
v___x_5235_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
size_t v___x_5236_; size_t v___x_5237_; 
v___x_5236_ = ((size_t)1ULL);
v___x_5237_ = lean_usize_add(v_i_5214_, v___x_5236_);
v_i_5214_ = v___x_5237_;
v_b_5216_ = v___x_5235_;
goto _start;
}
}
}
else
{
lean_object* v___x_5241_; 
v___x_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5241_, 0, v_b_5216_);
return v___x_5241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg___boxed(lean_object* v_as_5242_, lean_object* v_i_5243_, lean_object* v_stop_5244_, lean_object* v_b_5245_, lean_object* v___y_5246_){
_start:
{
size_t v_i_boxed_5247_; size_t v_stop_boxed_5248_; lean_object* v_res_5249_; 
v_i_boxed_5247_ = lean_unbox_usize(v_i_5243_);
lean_dec(v_i_5243_);
v_stop_boxed_5248_ = lean_unbox_usize(v_stop_5244_);
lean_dec(v_stop_5244_);
v_res_5249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_as_5242_, v_i_boxed_5247_, v_stop_boxed_5248_, v_b_5245_);
lean_dec_ref(v_as_5242_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(lean_object* v_a_5250_, lean_object* v_x_5251_){
_start:
{
if (lean_obj_tag(v_x_5251_) == 0)
{
lean_object* v___x_5252_; 
v___x_5252_ = lean_box(0);
return v___x_5252_;
}
else
{
lean_object* v_key_5253_; lean_object* v_value_5254_; lean_object* v_tail_5255_; uint8_t v___x_5256_; 
v_key_5253_ = lean_ctor_get(v_x_5251_, 0);
v_value_5254_ = lean_ctor_get(v_x_5251_, 1);
v_tail_5255_ = lean_ctor_get(v_x_5251_, 2);
v___x_5256_ = l_Lean_instBEqFVarId_beq(v_key_5253_, v_a_5250_);
if (v___x_5256_ == 0)
{
v_x_5251_ = v_tail_5255_;
goto _start;
}
else
{
lean_object* v___x_5258_; 
lean_inc(v_value_5254_);
v___x_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5258_, 0, v_value_5254_);
return v___x_5258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_5259_, lean_object* v_x_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5259_, v_x_5260_);
lean_dec(v_x_5260_);
lean_dec(v_a_5259_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object* v_m_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v_buckets_5264_; lean_object* v___x_5265_; uint64_t v___x_5266_; uint64_t v___x_5267_; uint64_t v___x_5268_; uint64_t v_fold_5269_; uint64_t v___x_5270_; uint64_t v___x_5271_; uint64_t v___x_5272_; size_t v___x_5273_; size_t v___x_5274_; size_t v___x_5275_; size_t v___x_5276_; size_t v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v_buckets_5264_ = lean_ctor_get(v_m_5262_, 1);
v___x_5265_ = lean_array_get_size(v_buckets_5264_);
v___x_5266_ = l_Lean_instHashableFVarId_hash(v_a_5263_);
v___x_5267_ = 32ULL;
v___x_5268_ = lean_uint64_shift_right(v___x_5266_, v___x_5267_);
v_fold_5269_ = lean_uint64_xor(v___x_5266_, v___x_5268_);
v___x_5270_ = 16ULL;
v___x_5271_ = lean_uint64_shift_right(v_fold_5269_, v___x_5270_);
v___x_5272_ = lean_uint64_xor(v_fold_5269_, v___x_5271_);
v___x_5273_ = lean_uint64_to_usize(v___x_5272_);
v___x_5274_ = lean_usize_of_nat(v___x_5265_);
v___x_5275_ = ((size_t)1ULL);
v___x_5276_ = lean_usize_sub(v___x_5274_, v___x_5275_);
v___x_5277_ = lean_usize_land(v___x_5273_, v___x_5276_);
v___x_5278_ = lean_array_uget_borrowed(v_buckets_5264_, v___x_5277_);
v___x_5279_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5263_, v___x_5278_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg___boxed(lean_object* v_m_5280_, lean_object* v_a_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5280_, v_a_5281_);
lean_dec(v_a_5281_);
lean_dec_ref(v_m_5280_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(lean_object* v_assignment_5283_, lean_object* v_as_5284_, size_t v_i_5285_, size_t v_stop_5286_, lean_object* v_b_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
lean_object* v_a_5294_; uint8_t v___x_5298_; 
v___x_5298_ = lean_usize_dec_eq(v_i_5285_, v_stop_5286_);
if (v___x_5298_ == 0)
{
lean_object* v___x_5299_; lean_object* v_fvarId_5300_; lean_object* v___x_5301_; 
v___x_5299_ = lean_array_uget_borrowed(v_as_5284_, v_i_5285_);
v_fvarId_5300_ = lean_ctor_get(v___x_5299_, 0);
v___x_5301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_assignment_5283_, v_fvarId_5300_);
if (lean_obj_tag(v___x_5301_) == 1)
{
lean_object* v_val_5302_; lean_object* v___x_5303_; 
v_val_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_val_5302_);
lean_dec_ref(v___x_5301_);
v___x_5303_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_getLiteral(v_val_5302_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_a_5304_);
lean_dec_ref(v___x_5303_);
if (lean_obj_tag(v_a_5304_) == 1)
{
lean_object* v_val_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v_val_5305_ = lean_ctor_get(v_a_5304_, 0);
lean_inc(v_val_5305_);
lean_dec_ref(v_a_5304_);
lean_inc(v___x_5299_);
v___x_5306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5299_);
lean_ctor_set(v___x_5306_, 1, v_val_5305_);
v___x_5307_ = lean_array_push(v_b_5287_, v___x_5306_);
v_a_5294_ = v___x_5307_;
goto v___jp_5293_;
}
else
{
lean_dec(v_a_5304_);
v_a_5294_ = v_b_5287_;
goto v___jp_5293_;
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
lean_dec_ref(v_b_5287_);
v_a_5308_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5303_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5303_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
else
{
lean_dec(v___x_5301_);
v_a_5294_ = v_b_5287_;
goto v___jp_5293_;
}
}
else
{
lean_object* v___x_5316_; 
v___x_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5316_, 0, v_b_5287_);
return v___x_5316_;
}
v___jp_5293_:
{
size_t v___x_5295_; size_t v___x_5296_; 
v___x_5295_ = ((size_t)1ULL);
v___x_5296_ = lean_usize_add(v_i_5285_, v___x_5295_);
v_i_5285_ = v___x_5296_;
v_b_5287_ = v_a_5294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5___boxed(lean_object* v_assignment_5317_, lean_object* v_as_5318_, lean_object* v_i_5319_, lean_object* v_stop_5320_, lean_object* v_b_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
size_t v_i_boxed_5327_; size_t v_stop_boxed_5328_; lean_object* v_res_5329_; 
v_i_boxed_5327_ = lean_unbox_usize(v_i_5319_);
lean_dec(v_i_5319_);
v_stop_boxed_5328_ = lean_unbox_usize(v_stop_5320_);
lean_dec(v_stop_5320_);
v_res_5329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(v_assignment_5317_, v_as_5318_, v_i_boxed_5327_, v_stop_boxed_5328_, v_b_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_);
lean_dec(v___y_5325_);
lean_dec_ref(v___y_5324_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
lean_dec_ref(v_as_5318_);
lean_dec_ref(v_assignment_5317_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(lean_object* v_assignment_5332_, lean_object* v_as_5333_, lean_object* v_start_5334_, lean_object* v_stop_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
lean_object* v___x_5341_; uint8_t v___x_5342_; 
v___x_5341_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___closed__0));
v___x_5342_ = lean_nat_dec_lt(v_start_5334_, v_stop_5335_);
if (v___x_5342_ == 0)
{
lean_object* v___x_5343_; 
v___x_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5341_);
return v___x_5343_;
}
else
{
lean_object* v___x_5344_; uint8_t v___x_5345_; 
v___x_5344_ = lean_array_get_size(v_as_5333_);
v___x_5345_ = lean_nat_dec_le(v_stop_5335_, v___x_5344_);
if (v___x_5345_ == 0)
{
uint8_t v___x_5346_; 
v___x_5346_ = lean_nat_dec_lt(v_start_5334_, v___x_5344_);
if (v___x_5346_ == 0)
{
lean_object* v___x_5347_; 
v___x_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5341_);
return v___x_5347_;
}
else
{
size_t v___x_5348_; size_t v___x_5349_; lean_object* v___x_5350_; 
v___x_5348_ = lean_usize_of_nat(v_start_5334_);
v___x_5349_ = lean_usize_of_nat(v___x_5344_);
v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(v_assignment_5332_, v_as_5333_, v___x_5348_, v___x_5349_, v___x_5341_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
return v___x_5350_;
}
}
else
{
size_t v___x_5351_; size_t v___x_5352_; lean_object* v___x_5353_; 
v___x_5351_ = lean_usize_of_nat(v_start_5334_);
v___x_5352_ = lean_usize_of_nat(v_stop_5335_);
v___x_5353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4_spec__5(v_assignment_5332_, v_as_5333_, v___x_5351_, v___x_5352_, v___x_5341_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
return v___x_5353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4___boxed(lean_object* v_assignment_5354_, lean_object* v_as_5355_, lean_object* v_start_5356_, lean_object* v_stop_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_assignment_5354_, v_as_5355_, v_start_5356_, v_stop_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec(v_stop_5357_);
lean_dec(v_start_5356_);
lean_dec_ref(v_as_5355_);
lean_dec_ref(v_assignment_5354_);
return v_res_5363_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2(void){
_start:
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; 
v___x_5366_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_inductValOfCtor___closed__2));
v___x_5367_ = lean_unsigned_to_nat(9u);
v___x_5368_ = lean_unsigned_to_nat(635u);
v___x_5369_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__1));
v___x_5370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__0));
v___x_5371_ = l_mkPanicMessageWithDecl(v___x_5370_, v___x_5369_, v___x_5368_, v___x_5367_, v___x_5366_);
return v___x_5371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(lean_object* v_resultType_5374_, lean_object* v_discrVal_5375_, lean_object* v_discr_5376_, lean_object* v_assignment_5377_, lean_object* v_i_5378_, lean_object* v_as_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5385_ = lean_array_get_size(v_as_5379_);
v___x_5386_ = lean_nat_dec_lt(v_i_5378_, v___x_5385_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; 
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v___x_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5387_, 0, v_as_5379_);
return v___x_5387_;
}
else
{
lean_object* v_a_5388_; lean_object* v_a_5390_; 
v_a_5388_ = lean_array_fget_borrowed(v_as_5379_, v_i_5378_);
if (lean_obj_tag(v_a_5388_) == 0)
{
lean_object* v_ctorName_5401_; lean_object* v_params_5402_; lean_object* v_code_5403_; uint8_t v___x_5404_; lean_object* v___y_5406_; lean_object* v___y_5407_; lean_object* v___y_5420_; uint8_t v___x_5424_; 
v_ctorName_5401_ = lean_ctor_get(v_a_5388_, 0);
v_params_5402_ = lean_ctor_get(v_a_5388_, 1);
v_code_5403_ = lean_ctor_get(v_a_5388_, 2);
v___x_5404_ = 0;
lean_inc(v_ctorName_5401_);
lean_inc(v_discrVal_5375_);
v___x_5424_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_containsCtor(v_discrVal_5375_, v_ctorName_5401_);
if (v___x_5424_ == 0)
{
lean_object* v_cls_5425_; lean_object* v___x_5426_; 
v_cls_5425_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_5426_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_5425_, v___y_5382_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; uint8_t v___x_5428_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_a_5427_);
lean_dec_ref(v___x_5426_);
v___x_5428_ = lean_unbox(v_a_5427_);
if (v___x_5428_ == 0)
{
lean_dec(v_a_5427_);
v___y_5420_ = v___y_5381_;
goto v___jp_5419_;
}
else
{
lean_object* v___x_5429_; 
lean_inc(v_discr_5376_);
v___x_5429_ = l_Lean_Compiler_LCNF_getBinderName(v_discr_5376_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5431_; uint8_t v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; uint8_t v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
lean_inc(v_a_5430_);
lean_dec_ref(v___x_5429_);
v___x_5431_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__0));
v___x_5432_ = lean_unbox(v_a_5427_);
v___x_5433_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5430_, v___x_5432_);
v___x_5434_ = lean_string_append(v___x_5431_, v___x_5433_);
lean_dec_ref(v___x_5433_);
v___x_5435_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___closed__1));
v___x_5436_ = lean_string_append(v___x_5434_, v___x_5435_);
v___x_5437_ = lean_unbox(v_a_5427_);
lean_dec(v_a_5427_);
lean_inc(v_ctorName_5401_);
v___x_5438_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctorName_5401_, v___x_5437_);
v___x_5439_ = lean_string_append(v___x_5436_, v___x_5438_);
lean_dec_ref(v___x_5438_);
v___x_5440_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5440_, 0, v___x_5439_);
v___x_5441_ = l_Lean_MessageData_ofFormat(v___x_5440_);
v___x_5442_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_cls_5425_, v___x_5441_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_dec_ref(v___x_5442_);
v___y_5420_ = v___y_5381_;
goto v___jp_5419_;
}
else
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5450_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5450_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5445_ = v___x_5442_;
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5442_);
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
else
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec(v_a_5427_);
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5451_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5429_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5429_);
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
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5459_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5426_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5426_);
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
else
{
lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5467_ = lean_unsigned_to_nat(0u);
v___x_5468_ = lean_array_get_size(v_params_5402_);
v___x_5469_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__4(v_assignment_5377_, v_params_5402_, v___x_5467_, v___x_5468_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5483_; uint8_t v___x_5484_; lean_object* v_fst_5486_; lean_object* v_snd_5487_; lean_object* v___y_5500_; 
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
lean_inc(v_a_5470_);
lean_dec_ref(v___x_5469_);
v___x_5483_ = lean_array_get_size(v_a_5470_);
v___x_5484_ = lean_nat_dec_eq(v___x_5483_, v___x_5467_);
if (v___x_5484_ == 0)
{
if (v___x_5424_ == 0)
{
lean_dec(v_a_5470_);
goto v___jp_5471_;
}
else
{
lean_object* v___x_5512_; 
lean_inc_ref(v_code_5403_);
v___x_5512_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5377_, v_code_5403_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v_a_5513_; lean_object* v___x_5514_; uint8_t v___x_5515_; 
v_a_5513_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_a_5513_);
lean_dec_ref(v___x_5512_);
v___x_5514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0___closed__1);
v___x_5515_ = lean_nat_dec_lt(v___x_5467_, v___x_5483_);
if (v___x_5515_ == 0)
{
lean_dec(v_a_5470_);
v_fst_5486_ = v_a_5513_;
v_snd_5487_ = v___x_5514_;
goto v___jp_5485_;
}
else
{
lean_object* v___x_5516_; uint8_t v___x_5517_; 
lean_inc(v_a_5513_);
v___x_5516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5516_, 0, v_a_5513_);
lean_ctor_set(v___x_5516_, 1, v___x_5514_);
v___x_5517_ = lean_nat_dec_le(v___x_5483_, v___x_5483_);
if (v___x_5517_ == 0)
{
if (v___x_5515_ == 0)
{
lean_dec_ref(v___x_5516_);
lean_dec(v_a_5470_);
v_fst_5486_ = v_a_5513_;
v_snd_5487_ = v___x_5514_;
goto v___jp_5485_;
}
else
{
size_t v___x_5518_; size_t v___x_5519_; lean_object* v___x_5520_; 
lean_dec(v_a_5513_);
v___x_5518_ = ((size_t)0ULL);
v___x_5519_ = lean_usize_of_nat(v___x_5483_);
v___x_5520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_a_5470_, v___x_5518_, v___x_5519_, v___x_5516_);
lean_dec(v_a_5470_);
v___y_5500_ = v___x_5520_;
goto v___jp_5499_;
}
}
else
{
size_t v___x_5521_; size_t v___x_5522_; lean_object* v___x_5523_; 
lean_dec(v_a_5513_);
v___x_5521_ = ((size_t)0ULL);
v___x_5522_ = lean_usize_of_nat(v___x_5483_);
v___x_5523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_a_5470_, v___x_5521_, v___x_5522_, v___x_5516_);
lean_dec(v_a_5470_);
v___y_5500_ = v___x_5523_;
goto v___jp_5499_;
}
}
}
else
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
lean_dec(v_a_5470_);
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5524_ = lean_ctor_get(v___x_5512_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5512_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5512_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
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
}
else
{
lean_dec(v_a_5470_);
goto v___jp_5471_;
}
v___jp_5471_:
{
lean_object* v___x_5472_; 
lean_inc_ref(v_code_5403_);
v___x_5472_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5377_, v_code_5403_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v_a_5473_; lean_object* v___x_5474_; 
v_a_5473_ = lean_ctor_get(v___x_5472_, 0);
lean_inc(v_a_5473_);
lean_dec_ref(v___x_5472_);
lean_inc_ref(v_a_5388_);
v___x_5474_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5388_, v_a_5473_);
v_a_5390_ = v___x_5474_;
goto v___jp_5389_;
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5475_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5472_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5472_);
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
v___jp_5485_:
{
lean_object* v___x_5488_; 
v___x_5488_ = l_Lean_Compiler_LCNF_replaceFVars(v___x_5404_, v_fst_5486_, v_snd_5487_, v___x_5484_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
lean_dec_ref(v_snd_5487_);
if (lean_obj_tag(v___x_5488_) == 0)
{
lean_object* v_a_5489_; lean_object* v___x_5490_; 
v_a_5489_ = lean_ctor_get(v___x_5488_, 0);
lean_inc(v_a_5489_);
lean_dec_ref(v___x_5488_);
lean_inc_ref(v_a_5388_);
v___x_5490_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5388_, v_a_5489_);
v_a_5390_ = v___x_5490_;
goto v___jp_5389_;
}
else
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5498_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5491_ = lean_ctor_get(v___x_5488_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5493_ = v___x_5488_;
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5488_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5496_; 
if (v_isShared_5494_ == 0)
{
v___x_5496_ = v___x_5493_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
v___jp_5499_:
{
if (lean_obj_tag(v___y_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v_fst_5502_; lean_object* v_snd_5503_; 
v_a_5501_ = lean_ctor_get(v___y_5500_, 0);
lean_inc(v_a_5501_);
lean_dec_ref(v___y_5500_);
v_fst_5502_ = lean_ctor_get(v_a_5501_, 0);
lean_inc(v_fst_5502_);
v_snd_5503_ = lean_ctor_get(v_a_5501_, 1);
lean_inc(v_snd_5503_);
lean_dec(v_a_5501_);
v_fst_5486_ = v_fst_5502_;
v_snd_5487_ = v_snd_5503_;
goto v___jp_5485_;
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5504_ = lean_ctor_get(v___y_5500_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___y_5500_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___y_5500_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___y_5500_);
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
}
else
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5539_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5532_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5469_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5469_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
v___jp_5405_:
{
lean_object* v___x_5408_; 
v___x_5408_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5404_, v___y_5407_, v___y_5406_);
lean_dec_ref(v___y_5407_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v___x_5409_; lean_object* v___x_5410_; 
lean_dec_ref(v___x_5408_);
lean_inc_ref(v_resultType_5374_);
v___x_5409_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_5409_, 0, v_resultType_5374_);
lean_inc_ref(v_a_5388_);
v___x_5410_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5388_, v___x_5409_);
v_a_5390_ = v___x_5410_;
goto v___jp_5389_;
}
else
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5418_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5411_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5413_ = v___x_5408_;
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5408_);
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
v___jp_5419_:
{
switch(lean_obj_tag(v_a_5388_))
{
case 0:
{
lean_object* v_code_5421_; 
v_code_5421_ = lean_ctor_get(v_a_5388_, 2);
lean_inc_ref(v_code_5421_);
v___y_5406_ = v___y_5420_;
v___y_5407_ = v_code_5421_;
goto v___jp_5405_;
}
case 1:
{
lean_object* v_code_5422_; 
v_code_5422_ = lean_ctor_get(v_a_5388_, 1);
lean_inc_ref(v_code_5422_);
v___y_5406_ = v___y_5420_;
v___y_5407_ = v_code_5422_;
goto v___jp_5405_;
}
default: 
{
lean_object* v_code_5423_; 
v_code_5423_ = lean_ctor_get(v_a_5388_, 0);
lean_inc_ref(v_code_5423_);
v___y_5406_ = v___y_5420_;
v___y_5407_ = v_code_5423_;
goto v___jp_5405_;
}
}
}
}
else
{
lean_object* v_code_5540_; lean_object* v___x_5541_; 
v_code_5540_ = lean_ctor_get(v_a_5388_, 0);
lean_inc_ref(v_code_5540_);
v___x_5541_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5377_, v_code_5540_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_a_5542_; lean_object* v___x_5543_; 
v_a_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_a_5542_);
lean_dec_ref(v___x_5541_);
lean_inc_ref(v_a_5388_);
v___x_5543_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5388_, v_a_5542_);
v_a_5390_ = v___x_5543_;
goto v___jp_5389_;
}
else
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5551_; 
lean_dec_ref(v_as_5379_);
lean_dec(v_i_5378_);
lean_dec(v_discr_5376_);
lean_dec(v_discrVal_5375_);
lean_dec_ref(v_resultType_5374_);
v_a_5544_ = lean_ctor_get(v___x_5541_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5546_ = v___x_5541_;
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5541_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5547_ == 0)
{
v___x_5549_ = v___x_5546_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
v___jp_5389_:
{
size_t v___x_5391_; size_t v___x_5392_; uint8_t v___x_5393_; 
v___x_5391_ = lean_ptr_addr(v_a_5388_);
v___x_5392_ = lean_ptr_addr(v_a_5390_);
v___x_5393_ = lean_usize_dec_eq(v___x_5391_, v___x_5392_);
if (v___x_5393_ == 0)
{
lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5394_ = lean_unsigned_to_nat(1u);
v___x_5395_ = lean_nat_add(v_i_5378_, v___x_5394_);
v___x_5396_ = lean_array_fset(v_as_5379_, v_i_5378_, v_a_5390_);
lean_dec(v_i_5378_);
v_i_5378_ = v___x_5395_;
v_as_5379_ = v___x_5396_;
goto _start;
}
else
{
lean_object* v___x_5398_; lean_object* v___x_5399_; 
lean_dec_ref(v_a_5390_);
v___x_5398_ = lean_unsigned_to_nat(1u);
v___x_5399_ = lean_nat_add(v_i_5378_, v___x_5398_);
lean_dec(v_i_5378_);
v_i_5378_ = v___x_5399_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(lean_object* v_assignment_5552_, lean_object* v_code_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_){
_start:
{
lean_object* v___y_5560_; lean_object* v___y_5561_; uint8_t v___y_5562_; lean_object* v___y_5567_; lean_object* v___y_5568_; uint8_t v___y_5569_; lean_object* v_decl_5574_; lean_object* v_k_5575_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; 
switch(lean_obj_tag(v_code_5553_))
{
case 0:
{
lean_object* v_decl_5625_; lean_object* v_k_5626_; lean_object* v___x_5627_; 
v_decl_5625_ = lean_ctor_get(v_code_5553_, 0);
v_k_5626_ = lean_ctor_get(v_code_5553_, 1);
lean_inc_ref(v_k_5626_);
v___x_5627_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5552_, v_k_5626_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5654_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5654_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5654_ == 0)
{
v___x_5630_ = v___x_5627_;
v_isShared_5631_ = v_isSharedCheck_5654_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_a_5628_);
lean_dec(v___x_5627_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5654_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
uint8_t v___y_5633_; size_t v___x_5649_; size_t v___x_5650_; uint8_t v___x_5651_; 
v___x_5649_ = lean_ptr_addr(v_k_5626_);
v___x_5650_ = lean_ptr_addr(v_a_5628_);
v___x_5651_ = lean_usize_dec_eq(v___x_5649_, v___x_5650_);
if (v___x_5651_ == 0)
{
v___y_5633_ = v___x_5651_;
goto v___jp_5632_;
}
else
{
size_t v___x_5652_; uint8_t v___x_5653_; 
v___x_5652_ = lean_ptr_addr(v_decl_5625_);
v___x_5653_ = lean_usize_dec_eq(v___x_5652_, v___x_5652_);
v___y_5633_ = v___x_5653_;
goto v___jp_5632_;
}
v___jp_5632_:
{
if (v___y_5633_ == 0)
{
lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5643_; 
lean_inc_ref(v_decl_5625_);
v_isSharedCheck_5643_ = !lean_is_exclusive(v_code_5553_);
if (v_isSharedCheck_5643_ == 0)
{
lean_object* v_unused_5644_; lean_object* v_unused_5645_; 
v_unused_5644_ = lean_ctor_get(v_code_5553_, 1);
lean_dec(v_unused_5644_);
v_unused_5645_ = lean_ctor_get(v_code_5553_, 0);
lean_dec(v_unused_5645_);
v___x_5635_ = v_code_5553_;
v_isShared_5636_ = v_isSharedCheck_5643_;
goto v_resetjp_5634_;
}
else
{
lean_dec(v_code_5553_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5643_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v___x_5638_; 
if (v_isShared_5636_ == 0)
{
lean_ctor_set(v___x_5635_, 1, v_a_5628_);
v___x_5638_ = v___x_5635_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_decl_5625_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v_a_5628_);
v___x_5638_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
lean_object* v___x_5640_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v___x_5638_);
v___x_5640_ = v___x_5630_;
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
lean_object* v___x_5647_; 
lean_dec(v_a_5628_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v_code_5553_);
v___x_5647_ = v___x_5630_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_code_5553_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_5553_);
return v___x_5627_;
}
}
case 1:
{
lean_object* v_decl_5655_; lean_object* v_k_5656_; 
v_decl_5655_ = lean_ctor_get(v_code_5553_, 0);
v_k_5656_ = lean_ctor_get(v_code_5553_, 1);
lean_inc_ref(v_k_5656_);
lean_inc_ref(v_decl_5655_);
v_decl_5574_ = v_decl_5655_;
v_k_5575_ = v_k_5656_;
v___y_5576_ = v_a_5554_;
v___y_5577_ = v_a_5555_;
v___y_5578_ = v_a_5556_;
v___y_5579_ = v_a_5557_;
goto v___jp_5573_;
}
case 2:
{
lean_object* v_decl_5657_; lean_object* v_k_5658_; 
v_decl_5657_ = lean_ctor_get(v_code_5553_, 0);
v_k_5658_ = lean_ctor_get(v_code_5553_, 1);
lean_inc_ref(v_k_5658_);
lean_inc_ref(v_decl_5657_);
v_decl_5574_ = v_decl_5657_;
v_k_5575_ = v_k_5658_;
v___y_5576_ = v_a_5554_;
v___y_5577_ = v_a_5555_;
v___y_5578_ = v_a_5556_;
v___y_5579_ = v_a_5557_;
goto v___jp_5573_;
}
case 4:
{
lean_object* v_cases_5659_; lean_object* v_typeName_5660_; lean_object* v_resultType_5661_; lean_object* v_discr_5662_; lean_object* v_alts_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5704_; 
v_cases_5659_ = lean_ctor_get(v_code_5553_, 0);
lean_inc_ref(v_cases_5659_);
v_typeName_5660_ = lean_ctor_get(v_cases_5659_, 0);
v_resultType_5661_ = lean_ctor_get(v_cases_5659_, 1);
v_discr_5662_ = lean_ctor_get(v_cases_5659_, 2);
v_alts_5663_ = lean_ctor_get(v_cases_5659_, 3);
v_isSharedCheck_5704_ = !lean_is_exclusive(v_cases_5659_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5665_ = v_cases_5659_;
v_isShared_5666_ = v_isSharedCheck_5704_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_alts_5663_);
lean_inc(v_discr_5662_);
lean_inc(v_resultType_5661_);
lean_inc(v_typeName_5660_);
lean_dec(v_cases_5659_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5704_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5667_; lean_object* v_discrVal_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; 
v___x_5667_ = lean_box(0);
v_discrVal_5668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Compiler_LCNF_UnreachableBranches_findVarValue_spec__0___redArg(v_assignment_5552_, v_discr_5662_, v___x_5667_);
v___x_5669_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_5663_);
lean_inc(v_discr_5662_);
lean_inc_ref(v_resultType_5661_);
v___x_5670_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(v_resultType_5661_, v_discrVal_5668_, v_discr_5662_, v_assignment_5552_, v___x_5669_, v_alts_5663_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_object* v_a_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5695_; 
v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5673_ = v___x_5670_;
v_isShared_5674_ = v_isSharedCheck_5695_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_a_5671_);
lean_dec(v___x_5670_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5695_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
size_t v___x_5675_; size_t v___x_5676_; uint8_t v___x_5677_; 
v___x_5675_ = lean_ptr_addr(v_alts_5663_);
lean_dec_ref(v_alts_5663_);
v___x_5676_ = lean_ptr_addr(v_a_5671_);
v___x_5677_ = lean_usize_dec_eq(v___x_5675_, v___x_5676_);
if (v___x_5677_ == 0)
{
lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5690_; 
v_isSharedCheck_5690_ = !lean_is_exclusive(v_code_5553_);
if (v_isSharedCheck_5690_ == 0)
{
lean_object* v_unused_5691_; 
v_unused_5691_ = lean_ctor_get(v_code_5553_, 0);
lean_dec(v_unused_5691_);
v___x_5679_ = v_code_5553_;
v_isShared_5680_ = v_isSharedCheck_5690_;
goto v_resetjp_5678_;
}
else
{
lean_dec(v_code_5553_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5690_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5682_; 
if (v_isShared_5666_ == 0)
{
lean_ctor_set(v___x_5665_, 3, v_a_5671_);
v___x_5682_ = v___x_5665_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_typeName_5660_);
lean_ctor_set(v_reuseFailAlloc_5689_, 1, v_resultType_5661_);
lean_ctor_set(v_reuseFailAlloc_5689_, 2, v_discr_5662_);
lean_ctor_set(v_reuseFailAlloc_5689_, 3, v_a_5671_);
v___x_5682_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
lean_object* v___x_5684_; 
if (v_isShared_5680_ == 0)
{
lean_ctor_set(v___x_5679_, 0, v___x_5682_);
v___x_5684_ = v___x_5679_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5682_);
v___x_5684_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
lean_object* v___x_5686_; 
if (v_isShared_5674_ == 0)
{
lean_ctor_set(v___x_5673_, 0, v___x_5684_);
v___x_5686_ = v___x_5673_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5684_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
else
{
lean_object* v___x_5693_; 
lean_dec(v_a_5671_);
lean_del_object(v___x_5665_);
lean_dec(v_discr_5662_);
lean_dec_ref(v_resultType_5661_);
lean_dec(v_typeName_5660_);
if (v_isShared_5674_ == 0)
{
lean_ctor_set(v___x_5673_, 0, v_code_5553_);
v___x_5693_ = v___x_5673_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_code_5553_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
lean_del_object(v___x_5665_);
lean_dec_ref(v_alts_5663_);
lean_dec(v_discr_5662_);
lean_dec_ref(v_resultType_5661_);
lean_dec(v_typeName_5660_);
lean_dec_ref(v_code_5553_);
v_a_5696_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___x_5670_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___x_5670_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
}
default: 
{
lean_object* v___x_5705_; 
v___x_5705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5705_, 0, v_code_5553_);
return v___x_5705_;
}
}
v___jp_5559_:
{
if (v___y_5562_ == 0)
{
lean_object* v___x_5563_; lean_object* v___x_5564_; 
lean_dec_ref(v_code_5553_);
v___x_5563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5563_, 0, v___y_5560_);
lean_ctor_set(v___x_5563_, 1, v___y_5561_);
v___x_5564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5563_);
return v___x_5564_;
}
else
{
lean_object* v___x_5565_; 
lean_dec_ref(v___y_5561_);
lean_dec_ref(v___y_5560_);
v___x_5565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5565_, 0, v_code_5553_);
return v___x_5565_;
}
}
v___jp_5566_:
{
if (v___y_5569_ == 0)
{
lean_object* v___x_5570_; lean_object* v___x_5571_; 
lean_dec_ref(v_code_5553_);
v___x_5570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5570_, 0, v___y_5567_);
lean_ctor_set(v___x_5570_, 1, v___y_5568_);
v___x_5571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5571_, 0, v___x_5570_);
return v___x_5571_;
}
else
{
lean_object* v___x_5572_; 
lean_dec_ref(v___y_5568_);
lean_dec_ref(v___y_5567_);
v___x_5572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5572_, 0, v_code_5553_);
return v___x_5572_;
}
}
v___jp_5573_:
{
lean_object* v_params_5580_; lean_object* v_type_5581_; lean_object* v_value_5582_; lean_object* v___x_5583_; 
v_params_5580_ = lean_ctor_get(v_decl_5574_, 2);
lean_inc_ref(v_params_5580_);
v_type_5581_ = lean_ctor_get(v_decl_5574_, 3);
lean_inc_ref(v_type_5581_);
v_value_5582_ = lean_ctor_get(v_decl_5574_, 4);
lean_inc_ref(v_value_5582_);
v___x_5583_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5552_, v_value_5582_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_);
if (lean_obj_tag(v___x_5583_) == 0)
{
lean_object* v_a_5584_; uint8_t v___x_5585_; lean_object* v___x_5586_; 
v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
lean_inc(v_a_5584_);
lean_dec_ref(v___x_5583_);
v___x_5585_ = 0;
v___x_5586_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5585_, v_decl_5574_, v_type_5581_, v_params_5580_, v_a_5584_, v___y_5577_);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_object* v_a_5587_; lean_object* v___x_5588_; 
v_a_5587_ = lean_ctor_get(v___x_5586_, 0);
lean_inc(v_a_5587_);
lean_dec_ref(v___x_5586_);
v___x_5588_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5552_, v_k_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_);
if (lean_obj_tag(v___x_5588_) == 0)
{
switch(lean_obj_tag(v_code_5553_))
{
case 1:
{
lean_object* v_a_5589_; lean_object* v_decl_5590_; lean_object* v_k_5591_; size_t v___x_5592_; size_t v___x_5593_; uint8_t v___x_5594_; 
v_a_5589_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_a_5589_);
lean_dec_ref(v___x_5588_);
v_decl_5590_ = lean_ctor_get(v_code_5553_, 0);
v_k_5591_ = lean_ctor_get(v_code_5553_, 1);
v___x_5592_ = lean_ptr_addr(v_k_5591_);
v___x_5593_ = lean_ptr_addr(v_a_5589_);
v___x_5594_ = lean_usize_dec_eq(v___x_5592_, v___x_5593_);
if (v___x_5594_ == 0)
{
v___y_5560_ = v_a_5587_;
v___y_5561_ = v_a_5589_;
v___y_5562_ = v___x_5594_;
goto v___jp_5559_;
}
else
{
size_t v___x_5595_; size_t v___x_5596_; uint8_t v___x_5597_; 
v___x_5595_ = lean_ptr_addr(v_decl_5590_);
v___x_5596_ = lean_ptr_addr(v_a_5587_);
v___x_5597_ = lean_usize_dec_eq(v___x_5595_, v___x_5596_);
v___y_5560_ = v_a_5587_;
v___y_5561_ = v_a_5589_;
v___y_5562_ = v___x_5597_;
goto v___jp_5559_;
}
}
case 2:
{
lean_object* v_a_5598_; lean_object* v_decl_5599_; lean_object* v_k_5600_; size_t v___x_5601_; size_t v___x_5602_; uint8_t v___x_5603_; 
v_a_5598_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_a_5598_);
lean_dec_ref(v___x_5588_);
v_decl_5599_ = lean_ctor_get(v_code_5553_, 0);
v_k_5600_ = lean_ctor_get(v_code_5553_, 1);
v___x_5601_ = lean_ptr_addr(v_k_5600_);
v___x_5602_ = lean_ptr_addr(v_a_5598_);
v___x_5603_ = lean_usize_dec_eq(v___x_5601_, v___x_5602_);
if (v___x_5603_ == 0)
{
v___y_5567_ = v_a_5587_;
v___y_5568_ = v_a_5598_;
v___y_5569_ = v___x_5603_;
goto v___jp_5566_;
}
else
{
size_t v___x_5604_; size_t v___x_5605_; uint8_t v___x_5606_; 
v___x_5604_ = lean_ptr_addr(v_decl_5599_);
v___x_5605_ = lean_ptr_addr(v_a_5587_);
v___x_5606_ = lean_usize_dec_eq(v___x_5604_, v___x_5605_);
v___y_5567_ = v_a_5587_;
v___y_5568_ = v_a_5598_;
v___y_5569_ = v___x_5606_;
goto v___jp_5566_;
}
}
default: 
{
lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5615_; 
lean_dec(v_a_5587_);
lean_dec_ref(v_code_5553_);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5615_ == 0)
{
lean_object* v_unused_5616_; 
v_unused_5616_ = lean_ctor_get(v___x_5588_, 0);
lean_dec(v_unused_5616_);
v___x_5608_ = v___x_5588_;
v_isShared_5609_ = v_isSharedCheck_5615_;
goto v_resetjp_5607_;
}
else
{
lean_dec(v___x_5588_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5615_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5613_; 
v___x_5610_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___closed__2);
v___x_5611_ = l_panic___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0(v___x_5610_);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 0, v___x_5611_);
v___x_5613_ = v___x_5608_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5611_);
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
else
{
lean_dec(v_a_5587_);
lean_dec_ref(v_code_5553_);
return v___x_5588_;
}
}
else
{
lean_object* v_a_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5624_; 
lean_dec_ref(v_k_5575_);
lean_dec_ref(v_code_5553_);
v_a_5617_ = lean_ctor_get(v___x_5586_, 0);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5619_ = v___x_5586_;
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_a_5617_);
lean_dec(v___x_5586_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5622_; 
if (v_isShared_5620_ == 0)
{
v___x_5622_ = v___x_5619_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
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
else
{
lean_dec_ref(v_type_5581_);
lean_dec_ref(v_params_5580_);
lean_dec_ref(v_k_5575_);
lean_dec_ref(v_decl_5574_);
lean_dec_ref(v_code_5553_);
return v___x_5583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed(lean_object* v_assignment_5706_, lean_object* v_code_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go(v_assignment_5706_, v_code_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec_ref(v_assignment_5706_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6___boxed(lean_object* v_resultType_5714_, lean_object* v_discrVal_5715_, lean_object* v_discr_5716_, lean_object* v_assignment_5717_, lean_object* v_i_5718_, lean_object* v_as_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_){
_start:
{
lean_object* v_res_5725_; 
v_res_5725_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__6(v_resultType_5714_, v_discrVal_5715_, v_discr_5716_, v_assignment_5717_, v_i_5718_, v_as_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
lean_dec(v___y_5723_);
lean_dec_ref(v___y_5722_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
lean_dec_ref(v_assignment_5717_);
return v_res_5725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(lean_object* v_00_u03b2_5726_, lean_object* v_m_5727_, lean_object* v_a_5728_){
_start:
{
lean_object* v___x_5729_; 
v___x_5729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(v_m_5727_, v_a_5728_);
return v___x_5729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___boxed(lean_object* v_00_u03b2_5730_, lean_object* v_m_5731_, lean_object* v_a_5732_){
_start:
{
lean_object* v_res_5733_; 
v_res_5733_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1(v_00_u03b2_5730_, v_m_5731_, v_a_5732_);
lean_dec(v_a_5732_);
lean_dec_ref(v_m_5731_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(lean_object* v_as_5734_, size_t v_i_5735_, size_t v_stop_5736_, lean_object* v_b_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_){
_start:
{
lean_object* v___x_5743_; 
v___x_5743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___redArg(v_as_5734_, v_i_5735_, v_stop_5736_, v_b_5737_);
return v___x_5743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5___boxed(lean_object* v_as_5744_, lean_object* v_i_5745_, lean_object* v_stop_5746_, lean_object* v_b_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_){
_start:
{
size_t v_i_boxed_5753_; size_t v_stop_boxed_5754_; lean_object* v_res_5755_; 
v_i_boxed_5753_ = lean_unbox_usize(v_i_5745_);
lean_dec(v_i_5745_);
v_stop_boxed_5754_ = lean_unbox_usize(v_stop_5746_);
lean_dec(v_stop_5746_);
v_res_5755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__5(v_as_5744_, v_i_boxed_5753_, v_stop_boxed_5754_, v_b_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_);
lean_dec(v___y_5751_);
lean_dec_ref(v___y_5750_);
lean_dec(v___y_5749_);
lean_dec_ref(v___y_5748_);
lean_dec_ref(v_as_5744_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(lean_object* v_00_u03b2_5756_, lean_object* v_a_5757_, lean_object* v_x_5758_){
_start:
{
lean_object* v___x_5759_; 
v___x_5759_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___redArg(v_a_5757_, v_x_5758_);
return v___x_5759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5760_, lean_object* v_a_5761_, lean_object* v_x_5762_){
_start:
{
lean_object* v_res_5763_; 
v_res_5763_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1_spec__1(v_00_u03b2_5760_, v_a_5761_, v_x_5762_);
lean_dec(v_x_5762_);
lean_dec(v_a_5761_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(lean_object* v_f_5764_, lean_object* v_v_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_){
_start:
{
if (lean_obj_tag(v_v_5765_) == 0)
{
lean_object* v_code_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5795_; 
v_code_5771_ = lean_ctor_get(v_v_5765_, 0);
v_isSharedCheck_5795_ = !lean_is_exclusive(v_v_5765_);
if (v_isSharedCheck_5795_ == 0)
{
v___x_5773_ = v_v_5765_;
v_isShared_5774_ = v_isSharedCheck_5795_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_code_5771_);
lean_dec(v_v_5765_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5795_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5775_; 
lean_inc(v___y_5769_);
lean_inc_ref(v___y_5768_);
lean_inc(v___y_5767_);
lean_inc_ref(v___y_5766_);
v___x_5775_ = lean_apply_6(v_f_5764_, v_code_5771_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, lean_box(0));
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5786_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5778_ = v___x_5775_;
v_isShared_5779_ = v_isSharedCheck_5786_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_a_5776_);
lean_dec(v___x_5775_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5786_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5781_; 
if (v_isShared_5774_ == 0)
{
lean_ctor_set(v___x_5773_, 0, v_a_5776_);
v___x_5781_ = v___x_5773_;
goto v_reusejp_5780_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5776_);
v___x_5781_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5780_;
}
v_reusejp_5780_:
{
lean_object* v___x_5783_; 
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 0, v___x_5781_);
v___x_5783_ = v___x_5778_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5781_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
else
{
lean_object* v_a_5787_; lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5794_; 
lean_del_object(v___x_5773_);
v_a_5787_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5794_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5794_ == 0)
{
v___x_5789_ = v___x_5775_;
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
else
{
lean_inc(v_a_5787_);
lean_dec(v___x_5775_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___x_5792_; 
if (v_isShared_5790_ == 0)
{
v___x_5792_ = v___x_5789_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_a_5787_);
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
}
else
{
lean_object* v___x_5796_; 
lean_dec_ref(v_f_5764_);
v___x_5796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5796_, 0, v_v_5765_);
return v___x_5796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg___boxed(lean_object* v_f_5797_, lean_object* v_v_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_){
_start:
{
lean_object* v_res_5804_; 
v_res_5804_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5797_, v_v_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
return v_res_5804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(uint8_t v_pu_5805_, lean_object* v_f_5806_, lean_object* v_v_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_){
_start:
{
lean_object* v___x_5813_; 
v___x_5813_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v_f_5806_, v_v_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
return v___x_5813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___boxed(lean_object* v_pu_5814_, lean_object* v_f_5815_, lean_object* v_v_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
uint8_t v_pu_boxed_5822_; lean_object* v_res_5823_; 
v_pu_boxed_5822_ = lean_unbox(v_pu_5814_);
v_res_5823_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0(v_pu_boxed_5822_, v_f_5815_, v_v_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
return v_res_5823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(lean_object* v_x_5824_, lean_object* v_x_5825_){
_start:
{
if (lean_obj_tag(v_x_5825_) == 0)
{
return v_x_5824_;
}
else
{
lean_object* v_key_5826_; lean_object* v_value_5827_; lean_object* v_tail_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v_key_5826_ = lean_ctor_get(v_x_5825_, 0);
v_value_5827_ = lean_ctor_get(v_x_5825_, 1);
v_tail_5828_ = lean_ctor_get(v_x_5825_, 2);
lean_inc(v_value_5827_);
lean_inc(v_key_5826_);
v___x_5829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5829_, 0, v_key_5826_);
lean_ctor_set(v___x_5829_, 1, v_value_5827_);
v___x_5830_ = lean_array_push(v_x_5824_, v___x_5829_);
v_x_5824_ = v___x_5830_;
v_x_5825_ = v_tail_5828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3___boxed(lean_object* v_x_5832_, lean_object* v_x_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_x_5832_, v_x_5833_);
lean_dec(v_x_5833_);
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(lean_object* v_as_5835_, size_t v_i_5836_, size_t v_stop_5837_, lean_object* v_b_5838_){
_start:
{
uint8_t v___x_5839_; 
v___x_5839_ = lean_usize_dec_eq(v_i_5836_, v_stop_5837_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; lean_object* v___x_5841_; size_t v___x_5842_; size_t v___x_5843_; 
v___x_5840_ = lean_array_uget_borrowed(v_as_5835_, v_i_5836_);
v___x_5841_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__3(v_b_5838_, v___x_5840_);
v___x_5842_ = ((size_t)1ULL);
v___x_5843_ = lean_usize_add(v_i_5836_, v___x_5842_);
v_i_5836_ = v___x_5843_;
v_b_5838_ = v___x_5841_;
goto _start;
}
else
{
return v_b_5838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4___boxed(lean_object* v_as_5845_, lean_object* v_i_5846_, lean_object* v_stop_5847_, lean_object* v_b_5848_){
_start:
{
size_t v_i_boxed_5849_; size_t v_stop_boxed_5850_; lean_object* v_res_5851_; 
v_i_boxed_5849_ = lean_unbox_usize(v_i_5846_);
lean_dec(v_i_5846_);
v_stop_boxed_5850_ = lean_unbox_usize(v_stop_5847_);
lean_dec(v_stop_5847_);
v_res_5851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_as_5845_, v_i_boxed_5849_, v_stop_boxed_5850_, v_b_5848_);
lean_dec_ref(v_as_5845_);
return v_res_5851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(uint8_t v_a_5852_, size_t v_sz_5853_, size_t v_i_5854_, lean_object* v_bs_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_){
_start:
{
uint8_t v___x_5861_; 
v___x_5861_ = lean_usize_dec_lt(v_i_5854_, v_sz_5853_);
if (v___x_5861_ == 0)
{
lean_object* v___x_5862_; 
v___x_5862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5862_, 0, v_bs_5855_);
return v___x_5862_;
}
else
{
lean_object* v_v_5863_; lean_object* v_fst_5864_; lean_object* v_snd_5865_; lean_object* v___x_5867_; uint8_t v_isShared_5868_; uint8_t v_isSharedCheck_5889_; 
v_v_5863_ = lean_array_uget(v_bs_5855_, v_i_5854_);
v_fst_5864_ = lean_ctor_get(v_v_5863_, 0);
v_snd_5865_ = lean_ctor_get(v_v_5863_, 1);
v_isSharedCheck_5889_ = !lean_is_exclusive(v_v_5863_);
if (v_isSharedCheck_5889_ == 0)
{
v___x_5867_ = v_v_5863_;
v_isShared_5868_ = v_isSharedCheck_5889_;
goto v_resetjp_5866_;
}
else
{
lean_inc(v_snd_5865_);
lean_inc(v_fst_5864_);
lean_dec(v_v_5863_);
v___x_5867_ = lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5889_;
goto v_resetjp_5866_;
}
v_resetjp_5866_:
{
lean_object* v___x_5869_; 
v___x_5869_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_5864_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_);
if (lean_obj_tag(v___x_5869_) == 0)
{
lean_object* v_a_5870_; lean_object* v___x_5871_; lean_object* v_bs_x27_5872_; lean_object* v___x_5873_; lean_object* v___x_5875_; 
v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
lean_inc(v_a_5870_);
lean_dec_ref(v___x_5869_);
v___x_5871_ = lean_unsigned_to_nat(0u);
v_bs_x27_5872_ = lean_array_uset(v_bs_5855_, v_i_5854_, v___x_5871_);
v___x_5873_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_5870_, v_a_5852_);
if (v_isShared_5868_ == 0)
{
lean_ctor_set(v___x_5867_, 0, v___x_5873_);
v___x_5875_ = v___x_5867_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v___x_5873_);
lean_ctor_set(v_reuseFailAlloc_5880_, 1, v_snd_5865_);
v___x_5875_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
size_t v___x_5876_; size_t v___x_5877_; lean_object* v___x_5878_; 
v___x_5876_ = ((size_t)1ULL);
v___x_5877_ = lean_usize_add(v_i_5854_, v___x_5876_);
v___x_5878_ = lean_array_uset(v_bs_x27_5872_, v_i_5854_, v___x_5875_);
v_i_5854_ = v___x_5877_;
v_bs_5855_ = v___x_5878_;
goto _start;
}
}
else
{
lean_object* v_a_5881_; lean_object* v___x_5883_; uint8_t v_isShared_5884_; uint8_t v_isSharedCheck_5888_; 
lean_del_object(v___x_5867_);
lean_dec(v_snd_5865_);
lean_dec_ref(v_bs_5855_);
v_a_5881_ = lean_ctor_get(v___x_5869_, 0);
v_isSharedCheck_5888_ = !lean_is_exclusive(v___x_5869_);
if (v_isSharedCheck_5888_ == 0)
{
v___x_5883_ = v___x_5869_;
v_isShared_5884_ = v_isSharedCheck_5888_;
goto v_resetjp_5882_;
}
else
{
lean_inc(v_a_5881_);
lean_dec(v___x_5869_);
v___x_5883_ = lean_box(0);
v_isShared_5884_ = v_isSharedCheck_5888_;
goto v_resetjp_5882_;
}
v_resetjp_5882_:
{
lean_object* v___x_5886_; 
if (v_isShared_5884_ == 0)
{
v___x_5886_ = v___x_5883_;
goto v_reusejp_5885_;
}
else
{
lean_object* v_reuseFailAlloc_5887_; 
v_reuseFailAlloc_5887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_a_5881_);
v___x_5886_ = v_reuseFailAlloc_5887_;
goto v_reusejp_5885_;
}
v_reusejp_5885_:
{
return v___x_5886_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1___boxed(lean_object* v_a_5890_, lean_object* v_sz_5891_, lean_object* v_i_5892_, lean_object* v_bs_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_){
_start:
{
uint8_t v_a_2201__boxed_5899_; size_t v_sz_boxed_5900_; size_t v_i_boxed_5901_; lean_object* v_res_5902_; 
v_a_2201__boxed_5899_ = lean_unbox(v_a_5890_);
v_sz_boxed_5900_ = lean_unbox_usize(v_sz_5891_);
lean_dec(v_sz_5891_);
v_i_boxed_5901_ = lean_unbox_usize(v_i_5892_);
lean_dec(v_i_5892_);
v_res_5902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v_a_2201__boxed_5899_, v_sz_boxed_5900_, v_i_boxed_5901_, v_bs_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_);
lean_dec(v___y_5897_);
lean_dec_ref(v___y_5896_);
lean_dec(v___y_5895_);
lean_dec_ref(v___y_5894_);
return v_res_5902_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(lean_object* v_x_5903_){
_start:
{
lean_object* v_fst_5904_; lean_object* v_snd_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5928_; 
v_fst_5904_ = lean_ctor_get(v_x_5903_, 0);
v_snd_5905_ = lean_ctor_get(v_x_5903_, 1);
v_isSharedCheck_5928_ = !lean_is_exclusive(v_x_5903_);
if (v_isSharedCheck_5928_ == 0)
{
v___x_5907_ = v_x_5903_;
v_isShared_5908_ = v_isSharedCheck_5928_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_snd_5905_);
lean_inc(v_fst_5904_);
lean_dec(v_x_5903_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5928_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5913_; 
v___x_5909_ = l_String_quote(v_fst_5904_);
v___x_5910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5909_);
v___x_5911_ = lean_box(0);
if (v_isShared_5908_ == 0)
{
lean_ctor_set_tag(v___x_5907_, 1);
lean_ctor_set(v___x_5907_, 1, v___x_5911_);
lean_ctor_set(v___x_5907_, 0, v___x_5910_);
v___x_5913_ = v___x_5907_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5927_; 
v_reuseFailAlloc_5927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5927_, 0, v___x_5910_);
lean_ctor_set(v_reuseFailAlloc_5927_, 1, v___x_5911_);
v___x_5913_ = v_reuseFailAlloc_5927_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; uint8_t v___x_5925_; lean_object* v___x_5926_; 
v___x_5914_ = l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat(v_snd_5905_);
v___x_5915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5914_);
lean_ctor_set(v___x_5915_, 1, v___x_5913_);
v___x_5916_ = l_List_reverse___redArg(v___x_5915_);
v___x_5917_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5918_ = l_Std_Format_joinSep___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat_spec__3(v___x_5916_, v___x_5917_);
v___x_5919_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7, &l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__7);
v___x_5920_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__8));
v___x_5921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5920_);
lean_ctor_set(v___x_5921_, 1, v___x_5918_);
v___x_5922_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_Value_toFormat___closed__9));
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5921_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5919_);
lean_ctor_set(v___x_5924_, 1, v___x_5923_);
v___x_5925_ = 0;
v___x_5926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5926_, 0, v___x_5924_);
lean_ctor_set_uint8(v___x_5926_, sizeof(void*)*1, v___x_5925_);
return v___x_5926_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_5929_, lean_object* v_x_5930_, lean_object* v_x_5931_){
_start:
{
if (lean_obj_tag(v_x_5931_) == 0)
{
lean_dec(v_x_5929_);
return v_x_5930_;
}
else
{
lean_object* v_head_5932_; lean_object* v_tail_5933_; lean_object* v___x_5935_; uint8_t v_isShared_5936_; uint8_t v_isSharedCheck_5943_; 
v_head_5932_ = lean_ctor_get(v_x_5931_, 0);
v_tail_5933_ = lean_ctor_get(v_x_5931_, 1);
v_isSharedCheck_5943_ = !lean_is_exclusive(v_x_5931_);
if (v_isSharedCheck_5943_ == 0)
{
v___x_5935_ = v_x_5931_;
v_isShared_5936_ = v_isSharedCheck_5943_;
goto v_resetjp_5934_;
}
else
{
lean_inc(v_tail_5933_);
lean_inc(v_head_5932_);
lean_dec(v_x_5931_);
v___x_5935_ = lean_box(0);
v_isShared_5936_ = v_isSharedCheck_5943_;
goto v_resetjp_5934_;
}
v_resetjp_5934_:
{
lean_object* v___x_5938_; 
lean_inc(v_x_5929_);
if (v_isShared_5936_ == 0)
{
lean_ctor_set_tag(v___x_5935_, 5);
lean_ctor_set(v___x_5935_, 1, v_x_5929_);
lean_ctor_set(v___x_5935_, 0, v_x_5930_);
v___x_5938_ = v___x_5935_;
goto v_reusejp_5937_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_x_5930_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v_x_5929_);
v___x_5938_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5937_;
}
v_reusejp_5937_:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5939_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5932_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5938_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v_x_5930_ = v___x_5940_;
v_x_5931_ = v_tail_5933_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(lean_object* v_x_5944_, lean_object* v_x_5945_, lean_object* v_x_5946_){
_start:
{
if (lean_obj_tag(v_x_5946_) == 0)
{
lean_dec(v_x_5944_);
return v_x_5945_;
}
else
{
lean_object* v_head_5947_; lean_object* v_tail_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5958_; 
v_head_5947_ = lean_ctor_get(v_x_5946_, 0);
v_tail_5948_ = lean_ctor_get(v_x_5946_, 1);
v_isSharedCheck_5958_ = !lean_is_exclusive(v_x_5946_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5950_ = v_x_5946_;
v_isShared_5951_ = v_isSharedCheck_5958_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_tail_5948_);
lean_inc(v_head_5947_);
lean_dec(v_x_5946_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5958_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v___x_5953_; 
lean_inc(v_x_5944_);
if (v_isShared_5951_ == 0)
{
lean_ctor_set_tag(v___x_5950_, 5);
lean_ctor_set(v___x_5950_, 1, v_x_5944_);
lean_ctor_set(v___x_5950_, 0, v_x_5945_);
v___x_5953_ = v___x_5950_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_x_5945_);
lean_ctor_set(v_reuseFailAlloc_5957_, 1, v_x_5944_);
v___x_5953_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; 
v___x_5954_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5947_);
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5953_);
lean_ctor_set(v___x_5955_, 1, v___x_5954_);
v___x_5956_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4_spec__7(v_x_5944_, v___x_5955_, v_tail_5948_);
return v___x_5956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(lean_object* v_x_5959_, lean_object* v_x_5960_){
_start:
{
if (lean_obj_tag(v_x_5959_) == 0)
{
lean_object* v___x_5961_; 
lean_dec(v_x_5960_);
v___x_5961_ = lean_box(0);
return v___x_5961_;
}
else
{
lean_object* v_tail_5962_; 
v_tail_5962_ = lean_ctor_get(v_x_5959_, 1);
if (lean_obj_tag(v_tail_5962_) == 0)
{
lean_object* v_head_5963_; lean_object* v___x_5964_; 
lean_dec(v_x_5960_);
v_head_5963_ = lean_ctor_get(v_x_5959_, 0);
lean_inc(v_head_5963_);
lean_dec_ref(v_x_5959_);
v___x_5964_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5963_);
return v___x_5964_;
}
else
{
lean_object* v_head_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; 
lean_inc(v_tail_5962_);
v_head_5965_ = lean_ctor_get(v_x_5959_, 0);
lean_inc(v_head_5965_);
lean_dec_ref(v_x_5959_);
v___x_5966_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_head_5965_);
v___x_5967_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3_spec__4(v_x_5960_, v___x_5966_, v_tail_5962_);
return v___x_5967_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5969_; lean_object* v___x_5970_; 
v___x_5969_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__0));
v___x_5970_ = lean_string_length(v___x_5969_);
return v___x_5970_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2(void){
_start:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5971_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__1);
v___x_5972_ = lean_nat_to_int(v___x_5971_);
return v___x_5972_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(lean_object* v_xs_5978_){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; uint8_t v___x_5981_; 
v___x_5979_ = lean_array_get_size(v_xs_5978_);
v___x_5980_ = lean_unsigned_to_nat(0u);
v___x_5981_ = lean_nat_dec_eq(v___x_5979_, v___x_5980_);
if (v___x_5981_ == 0)
{
lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; 
v___x_5982_ = lean_array_to_list(v_xs_5978_);
v___x_5983_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__5));
v___x_5984_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__3(v___x_5982_, v___x_5983_);
v___x_5985_ = lean_obj_once(&l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2, &l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2_once, _init_l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__2);
v___x_5986_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__3));
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set(v___x_5987_, 1, v___x_5984_);
v___x_5988_ = ((lean_object*)(l_List_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_Value_addChoice_spec__0___redArg___closed__10));
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5987_);
lean_ctor_set(v___x_5989_, 1, v___x_5988_);
v___x_5990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5985_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v___x_5991_ = l_Std_Format_fill(v___x_5990_);
return v___x_5991_;
}
else
{
lean_object* v___x_5992_; 
lean_dec_ref(v_xs_5978_);
v___x_5992_ = ((lean_object*)(l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2___closed__5));
return v___x_5992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(lean_object* v_assignment_5995_, lean_object* v_decl_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_){
_start:
{
lean_object* v___y_6003_; lean_object* v___y_6004_; lean_object* v___y_6005_; lean_object* v___y_6006_; lean_object* v_cls_6036_; lean_object* v___x_6037_; lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6097_; 
v_cls_6036_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_6037_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__2___redArg(v_cls_6036_, v_a_5999_);
v_a_6038_ = lean_ctor_get(v___x_6037_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v___x_6037_);
if (v_isSharedCheck_6097_ == 0)
{
v___x_6040_ = v___x_6037_;
v_isShared_6041_ = v_isSharedCheck_6097_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_6037_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6097_;
goto v_resetjp_6039_;
}
v___jp_6002_:
{
lean_object* v_toSignature_6007_; lean_object* v_value_6008_; uint8_t v_recursive_6009_; lean_object* v_inlineAttr_x3f_6010_; lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6035_; 
v_toSignature_6007_ = lean_ctor_get(v_decl_5996_, 0);
v_value_6008_ = lean_ctor_get(v_decl_5996_, 1);
v_recursive_6009_ = lean_ctor_get_uint8(v_decl_5996_, sizeof(void*)*3);
v_inlineAttr_x3f_6010_ = lean_ctor_get(v_decl_5996_, 2);
v_isSharedCheck_6035_ = !lean_is_exclusive(v_decl_5996_);
if (v_isSharedCheck_6035_ == 0)
{
v___x_6012_ = v_decl_5996_;
v_isShared_6013_ = v_isSharedCheck_6035_;
goto v_resetjp_6011_;
}
else
{
lean_inc(v_inlineAttr_x3f_6010_);
lean_inc(v_value_6008_);
lean_inc(v_toSignature_6007_);
lean_dec(v_decl_5996_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6035_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6014_; lean_object* v___x_6015_; 
v___x_6014_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go___boxed), 7, 1);
lean_closure_set(v___x_6014_, 0, v_assignment_5995_);
v___x_6015_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__0___redArg(v___x_6014_, v_value_6008_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_);
if (lean_obj_tag(v___x_6015_) == 0)
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6026_; 
v_a_6016_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6026_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6026_ == 0)
{
v___x_6018_ = v___x_6015_;
v_isShared_6019_ = v_isSharedCheck_6026_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v___x_6015_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6026_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
lean_object* v___x_6021_; 
if (v_isShared_6013_ == 0)
{
lean_ctor_set(v___x_6012_, 1, v_a_6016_);
v___x_6021_ = v___x_6012_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v_toSignature_6007_);
lean_ctor_set(v_reuseFailAlloc_6025_, 1, v_a_6016_);
lean_ctor_set(v_reuseFailAlloc_6025_, 2, v_inlineAttr_x3f_6010_);
lean_ctor_set_uint8(v_reuseFailAlloc_6025_, sizeof(void*)*3, v_recursive_6009_);
v___x_6021_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
lean_object* v___x_6023_; 
if (v_isShared_6019_ == 0)
{
lean_ctor_set(v___x_6018_, 0, v___x_6021_);
v___x_6023_ = v___x_6018_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6021_);
v___x_6023_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
return v___x_6023_;
}
}
}
}
else
{
lean_object* v_a_6027_; lean_object* v___x_6029_; uint8_t v_isShared_6030_; uint8_t v_isSharedCheck_6034_; 
lean_del_object(v___x_6012_);
lean_dec(v_inlineAttr_x3f_6010_);
lean_dec_ref(v_toSignature_6007_);
v_a_6027_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6034_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6034_ == 0)
{
v___x_6029_ = v___x_6015_;
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
else
{
lean_inc(v_a_6027_);
lean_dec(v___x_6015_);
v___x_6029_ = lean_box(0);
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
v_resetjp_6028_:
{
lean_object* v___x_6032_; 
if (v_isShared_6030_ == 0)
{
v___x_6032_ = v___x_6029_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_a_6027_);
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
}
v_resetjp_6039_:
{
lean_object* v___y_6043_; uint8_t v___x_6083_; 
v___x_6083_ = lean_unbox(v_a_6038_);
if (v___x_6083_ == 0)
{
lean_del_object(v___x_6040_);
lean_dec(v_a_6038_);
v___y_6003_ = v_a_5997_;
v___y_6004_ = v_a_5998_;
v___y_6005_ = v_a_5999_;
v___y_6006_ = v_a_6000_;
goto v___jp_6002_;
}
else
{
lean_object* v_size_6084_; lean_object* v_buckets_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; uint8_t v___x_6089_; 
v_size_6084_ = lean_ctor_get(v_assignment_5995_, 0);
v_buckets_6085_ = lean_ctor_get(v_assignment_5995_, 1);
v___x_6086_ = lean_mk_empty_array_with_capacity(v_size_6084_);
v___x_6087_ = lean_unsigned_to_nat(0u);
v___x_6088_ = lean_array_get_size(v_buckets_6085_);
v___x_6089_ = lean_nat_dec_lt(v___x_6087_, v___x_6088_);
if (v___x_6089_ == 0)
{
v___y_6043_ = v___x_6086_;
goto v___jp_6042_;
}
else
{
uint8_t v___x_6090_; 
v___x_6090_ = lean_nat_dec_le(v___x_6088_, v___x_6088_);
if (v___x_6090_ == 0)
{
if (v___x_6089_ == 0)
{
v___y_6043_ = v___x_6086_;
goto v___jp_6042_;
}
else
{
size_t v___x_6091_; size_t v___x_6092_; lean_object* v___x_6093_; 
v___x_6091_ = ((size_t)0ULL);
v___x_6092_ = lean_usize_of_nat(v___x_6088_);
v___x_6093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6085_, v___x_6091_, v___x_6092_, v___x_6086_);
v___y_6043_ = v___x_6093_;
goto v___jp_6042_;
}
}
else
{
size_t v___x_6094_; size_t v___x_6095_; lean_object* v___x_6096_; 
v___x_6094_ = ((size_t)0ULL);
v___x_6095_ = lean_usize_of_nat(v___x_6088_);
v___x_6096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__4(v_buckets_6085_, v___x_6094_, v___x_6095_, v___x_6086_);
v___y_6043_ = v___x_6096_;
goto v___jp_6042_;
}
}
}
v___jp_6042_:
{
size_t v_sz_6044_; size_t v___x_6045_; uint8_t v___x_6046_; lean_object* v___x_6047_; 
v_sz_6044_ = lean_array_size(v___y_6043_);
v___x_6045_ = ((size_t)0ULL);
v___x_6046_ = lean_unbox(v_a_6038_);
v___x_6047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__1(v___x_6046_, v_sz_6044_, v___x_6045_, v___y_6043_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_);
if (lean_obj_tag(v___x_6047_) == 0)
{
lean_object* v_toSignature_6048_; lean_object* v_a_6049_; lean_object* v_name_6050_; lean_object* v___x_6051_; uint8_t v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6063_; 
v_toSignature_6048_ = lean_ctor_get(v_decl_5996_, 0);
v_a_6049_ = lean_ctor_get(v___x_6047_, 0);
lean_inc(v_a_6049_);
lean_dec_ref(v___x_6047_);
v_name_6050_ = lean_ctor_get(v_toSignature_6048_, 0);
v___x_6051_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__0));
v___x_6052_ = lean_unbox(v_a_6038_);
lean_dec(v_a_6038_);
lean_inc(v_name_6050_);
v___x_6053_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6050_, v___x_6052_);
v___x_6054_ = lean_string_append(v___x_6051_, v___x_6053_);
lean_dec_ref(v___x_6053_);
v___x_6055_ = ((lean_object*)(l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___closed__1));
v___x_6056_ = lean_string_append(v___x_6054_, v___x_6055_);
v___x_6057_ = l_Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2(v_a_6049_);
v___x_6058_ = l_Std_Format_defWidth;
v___x_6059_ = lean_unsigned_to_nat(0u);
v___x_6060_ = l_Std_Format_pretty(v___x_6057_, v___x_6058_, v___x_6059_, v___x_6059_);
v___x_6061_ = lean_string_append(v___x_6056_, v___x_6060_);
lean_dec_ref(v___x_6060_);
if (v_isShared_6041_ == 0)
{
lean_ctor_set_tag(v___x_6040_, 3);
lean_ctor_set(v___x_6040_, 0, v___x_6061_);
v___x_6063_ = v___x_6040_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v___x_6061_);
v___x_6063_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
lean_object* v___x_6064_; lean_object* v___x_6065_; 
v___x_6064_ = l_Lean_MessageData_ofFormat(v___x_6063_);
v___x_6065_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__3(v_cls_6036_, v___x_6064_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_);
if (lean_obj_tag(v___x_6065_) == 0)
{
lean_dec_ref(v___x_6065_);
v___y_6003_ = v_a_5997_;
v___y_6004_ = v_a_5998_;
v___y_6005_ = v_a_5999_;
v___y_6006_ = v_a_6000_;
goto v___jp_6002_;
}
else
{
lean_object* v_a_6066_; lean_object* v___x_6068_; uint8_t v_isShared_6069_; uint8_t v_isSharedCheck_6073_; 
lean_dec_ref(v_decl_5996_);
lean_dec_ref(v_assignment_5995_);
v_a_6066_ = lean_ctor_get(v___x_6065_, 0);
v_isSharedCheck_6073_ = !lean_is_exclusive(v___x_6065_);
if (v_isSharedCheck_6073_ == 0)
{
v___x_6068_ = v___x_6065_;
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
else
{
lean_inc(v_a_6066_);
lean_dec(v___x_6065_);
v___x_6068_ = lean_box(0);
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
v_resetjp_6067_:
{
lean_object* v___x_6071_; 
if (v_isShared_6069_ == 0)
{
v___x_6071_ = v___x_6068_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
v___x_6071_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
return v___x_6071_;
}
}
}
}
}
else
{
lean_object* v_a_6075_; lean_object* v___x_6077_; uint8_t v_isShared_6078_; uint8_t v_isSharedCheck_6082_; 
lean_del_object(v___x_6040_);
lean_dec(v_a_6038_);
lean_dec_ref(v_decl_5996_);
lean_dec_ref(v_assignment_5995_);
v_a_6075_ = lean_ctor_get(v___x_6047_, 0);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6047_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6077_ = v___x_6047_;
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_a_6075_);
lean_dec(v___x_6047_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_UnreachableBranches_elimDead___boxed(lean_object* v_assignment_6098_, lean_object* v_decl_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_, lean_object* v_a_6103_, lean_object* v_a_6104_){
_start:
{
lean_object* v_res_6105_; 
v_res_6105_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v_assignment_6098_, v_decl_6099_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_);
lean_dec(v_a_6103_);
lean_dec_ref(v_a_6102_);
lean_dec(v_a_6101_);
lean_dec_ref(v_a_6100_);
return v_res_6105_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(lean_object* v_x_6106_, lean_object* v_x_6107_){
_start:
{
lean_object* v___x_6108_; 
v___x_6108_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___redArg(v_x_6106_);
return v___x_6108_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2___boxed(lean_object* v_x_6109_, lean_object* v_x_6110_){
_start:
{
lean_object* v_res_6111_; 
v_res_6111_ = l_Prod_repr___at___00Array_repr___at___00Lean_Compiler_LCNF_UnreachableBranches_elimDead_spec__2_spec__2(v_x_6109_, v_x_6110_);
lean_dec(v_x_6110_);
return v_res_6111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(size_t v_sz_6112_, size_t v_i_6113_, lean_object* v_bs_6114_){
_start:
{
uint8_t v___x_6115_; 
v___x_6115_ = lean_usize_dec_lt(v_i_6113_, v_sz_6112_);
if (v___x_6115_ == 0)
{
return v_bs_6114_;
}
else
{
lean_object* v_v_6116_; lean_object* v_toSignature_6117_; lean_object* v_name_6118_; lean_object* v___x_6119_; lean_object* v_bs_x27_6120_; size_t v___x_6121_; size_t v___x_6122_; lean_object* v___x_6123_; 
v_v_6116_ = lean_array_uget_borrowed(v_bs_6114_, v_i_6113_);
v_toSignature_6117_ = lean_ctor_get(v_v_6116_, 0);
v_name_6118_ = lean_ctor_get(v_toSignature_6117_, 0);
lean_inc(v_name_6118_);
v___x_6119_ = lean_unsigned_to_nat(0u);
v_bs_x27_6120_ = lean_array_uset(v_bs_6114_, v_i_6113_, v___x_6119_);
v___x_6121_ = ((size_t)1ULL);
v___x_6122_ = lean_usize_add(v_i_6113_, v___x_6121_);
v___x_6123_ = lean_array_uset(v_bs_x27_6120_, v_i_6113_, v_name_6118_);
v_i_6113_ = v___x_6122_;
v_bs_6114_ = v___x_6123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0___boxed(lean_object* v_sz_6125_, lean_object* v_i_6126_, lean_object* v_bs_6127_){
_start:
{
size_t v_sz_boxed_6128_; size_t v_i_boxed_6129_; lean_object* v_res_6130_; 
v_sz_boxed_6128_ = lean_unbox_usize(v_sz_6125_);
lean_dec(v_sz_6125_);
v_i_boxed_6129_ = lean_unbox_usize(v_i_6126_);
lean_dec(v_i_6126_);
v_res_6130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_boxed_6128_, v_i_boxed_6129_, v_bs_6127_);
return v_res_6130_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(lean_object* v_a_6131_, lean_object* v_a_6132_){
_start:
{
if (lean_obj_tag(v_a_6131_) == 0)
{
lean_object* v___x_6133_; 
v___x_6133_ = l_List_reverse___redArg(v_a_6132_);
return v___x_6133_;
}
else
{
lean_object* v_head_6134_; lean_object* v_tail_6135_; lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6144_; 
v_head_6134_ = lean_ctor_get(v_a_6131_, 0);
v_tail_6135_ = lean_ctor_get(v_a_6131_, 1);
v_isSharedCheck_6144_ = !lean_is_exclusive(v_a_6131_);
if (v_isSharedCheck_6144_ == 0)
{
v___x_6137_ = v_a_6131_;
v_isShared_6138_ = v_isSharedCheck_6144_;
goto v_resetjp_6136_;
}
else
{
lean_inc(v_tail_6135_);
lean_inc(v_head_6134_);
lean_dec(v_a_6131_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6144_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v___x_6139_; lean_object* v___x_6141_; 
v___x_6139_ = l_Lean_MessageData_ofName(v_head_6134_);
if (v_isShared_6138_ == 0)
{
lean_ctor_set(v___x_6137_, 1, v_a_6132_);
lean_ctor_set(v___x_6137_, 0, v___x_6139_);
v___x_6141_ = v___x_6137_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v___x_6139_);
lean_ctor_set(v_reuseFailAlloc_6143_, 1, v_a_6132_);
v___x_6141_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
v_a_6131_ = v_tail_6135_;
v_a_6132_ = v___x_6141_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6146_; lean_object* v___x_6147_; 
v___x_6146_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__0));
v___x_6147_ = l_Lean_stringToMessageData(v___x_6146_);
return v___x_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(lean_object* v___y_6148_, lean_object* v_x_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_){
_start:
{
lean_object* v___x_6157_; size_t v_sz_6158_; size_t v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; 
v___x_6157_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___closed__1);
v_sz_6158_ = lean_array_size(v___y_6148_);
v___x_6159_ = ((size_t)0ULL);
v___x_6160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__0(v_sz_6158_, v___x_6159_, v___y_6148_);
v___x_6161_ = lean_array_to_list(v___x_6160_);
v___x_6162_ = lean_box(0);
v___x_6163_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__1(v___x_6161_, v___x_6162_);
v___x_6164_ = l_Lean_MessageData_ofList(v___x_6163_);
v___x_6165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6157_);
lean_ctor_set(v___x_6165_, 1, v___x_6164_);
v___x_6166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
return v___x_6166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed(lean_object* v___y_6167_, lean_object* v_x_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_){
_start:
{
lean_object* v_res_6176_; 
v_res_6176_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0(v___y_6167_, v_x_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_);
lean_dec(v___y_6174_);
lean_dec_ref(v___y_6173_);
lean_dec(v___y_6172_);
lean_dec_ref(v___y_6171_);
lean_dec(v___y_6170_);
lean_dec_ref(v___y_6169_);
lean_dec_ref(v_x_6168_);
return v_res_6176_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg___closed__0(void){
_start:
{
uint8_t v___x_6177_; lean_object* v___x_6178_; 
v___x_6177_ = 0;
v___x_6178_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v___x_6177_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(lean_object* v___x_6203_, lean_object* v_as_6204_, lean_object* v_i_6205_, lean_object* v_j_6206_, lean_object* v_bs_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
lean_object* v_zero_6213_; uint8_t v_isZero_6214_; 
v_zero_6213_ = lean_unsigned_to_nat(0u);
v_isZero_6214_ = lean_nat_dec_eq(v_i_6205_, v_zero_6213_);
if (v_isZero_6214_ == 1)
{
lean_object* v___x_6215_; 
lean_dec(v_j_6206_);
lean_dec(v_i_6205_);
v___x_6215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6215_, 0, v_bs_6207_);
return v___x_6215_;
}
else
{
lean_object* v___x_6216_; lean_object* v_toSignature_6217_; uint8_t v_safe_6218_; lean_object* v_one_6219_; lean_object* v_n_6220_; lean_object* v_a_6222_; 
v___x_6216_ = lean_array_fget_borrowed(v_as_6204_, v_j_6206_);
v_toSignature_6217_ = lean_ctor_get(v___x_6216_, 0);
v_safe_6218_ = lean_ctor_get_uint8(v_toSignature_6217_, sizeof(void*)*4);
v_one_6219_ = lean_unsigned_to_nat(1u);
v_n_6220_ = lean_nat_sub(v_i_6205_, v_one_6219_);
lean_dec(v_i_6205_);
if (v_safe_6218_ == 0)
{
lean_inc(v___x_6216_);
v_a_6222_ = v___x_6216_;
goto v___jp_6221_;
}
else
{
lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6226_ = lean_obj_once(&l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2, &l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_UnreachableBranches_getAssignment___redArg___closed__2);
v___x_6227_ = lean_array_get_borrowed(v___x_6226_, v___x_6203_, v_j_6206_);
lean_inc(v___x_6216_);
lean_inc(v___x_6227_);
v___x_6228_ = l_Lean_Compiler_LCNF_UnreachableBranches_elimDead(v___x_6227_, v___x_6216_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
if (lean_obj_tag(v___x_6228_) == 0)
{
lean_object* v_a_6229_; 
v_a_6229_ = lean_ctor_get(v___x_6228_, 0);
lean_inc(v_a_6229_);
lean_dec_ref(v___x_6228_);
v_a_6222_ = v_a_6229_;
goto v___jp_6221_;
}
else
{
lean_object* v_a_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6237_; 
lean_dec(v_n_6220_);
lean_dec_ref(v_bs_6207_);
lean_dec(v_j_6206_);
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
v___jp_6221_:
{
lean_object* v___x_6223_; lean_object* v___x_6224_; 
v___x_6223_ = lean_nat_add(v_j_6206_, v_one_6219_);
lean_dec(v_j_6206_);
v___x_6224_ = lean_array_push(v_bs_6207_, v_a_6222_);
v_i_6205_ = v_n_6220_;
v_j_6206_ = v___x_6223_;
v_bs_6207_ = v___x_6224_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg___boxed(lean_object* v___x_6238_, lean_object* v_as_6239_, lean_object* v_i_6240_, lean_object* v_j_6241_, lean_object* v_bs_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_){
_start:
{
lean_object* v_res_6248_; 
v_res_6248_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6238_, v_as_6239_, v_i_6240_, v_j_6241_, v_bs_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
lean_dec(v___y_6246_);
lean_dec_ref(v___y_6245_);
lean_dec(v___y_6244_);
lean_dec_ref(v___y_6243_);
lean_dec_ref(v_as_6239_);
lean_dec_ref(v___x_6238_);
return v_res_6248_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(uint8_t v___x_6251_, lean_object* v_l_6252_, lean_object* v_r_6253_){
_start:
{
lean_object* v_toSignature_6254_; lean_object* v_toSignature_6255_; lean_object* v_name_6256_; lean_object* v_name_6257_; uint8_t v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; uint8_t v___x_6268_; 
v_toSignature_6254_ = lean_ctor_get(v_l_6252_, 0);
v_toSignature_6255_ = lean_ctor_get(v_r_6253_, 0);
v_name_6256_ = lean_ctor_get(v_toSignature_6254_, 0);
lean_inc(v_name_6256_);
v_name_6257_ = lean_ctor_get(v_toSignature_6255_, 0);
lean_inc(v_name_6257_);
v___x_6258_ = 0;
v___x_6259_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6258_, v_l_6252_);
lean_dec_ref(v_l_6252_);
v___x_6260_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_6261_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__0));
v___x_6262_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___closed__1));
v___x_6263_ = l_Lean_Name_toString(v_name_6256_, v___x_6251_);
v___x_6264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6264_, 0, v___x_6259_);
lean_ctor_set(v___x_6264_, 1, v___x_6263_);
v___x_6265_ = l_Lean_Compiler_LCNF_Decl_size(v___x_6258_, v_r_6253_);
lean_dec_ref(v_r_6253_);
v___x_6266_ = l_Lean_Name_toString(v_name_6257_, v___x_6251_);
v___x_6267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6267_, 0, v___x_6265_);
lean_ctor_set(v___x_6267_, 1, v___x_6266_);
v___x_6268_ = l_Prod_lexLtDec___aux__1___redArg(v___x_6260_, v___x_6261_, v___x_6262_, v___x_6264_, v___x_6267_);
return v___x_6268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed(lean_object* v___x_6269_, lean_object* v_l_6270_, lean_object* v_r_6271_){
_start:
{
uint8_t v___x_11051__boxed_6272_; uint8_t v_res_6273_; lean_object* v_r_6274_; 
v___x_11051__boxed_6272_ = lean_unbox(v___x_6269_);
v_res_6273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0(v___x_11051__boxed_6272_, v_l_6270_, v_r_6271_);
v_r_6274_ = lean_box(v_res_6273_);
return v_r_6274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(lean_object* v_as_6275_, lean_object* v_lo_6276_, lean_object* v_hi_6277_){
_start:
{
uint8_t v___x_6278_; 
v___x_6278_ = lean_nat_dec_lt(v_lo_6276_, v_hi_6277_);
if (v___x_6278_ == 0)
{
lean_dec(v_lo_6276_);
return v_as_6275_;
}
else
{
lean_object* v___x_6279_; lean_object* v___f_6280_; lean_object* v___x_6281_; lean_object* v_fst_6282_; lean_object* v_snd_6283_; uint8_t v___x_6284_; 
v___x_6279_ = lean_box(v___x_6278_);
v___f_6280_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_6280_, 0, v___x_6279_);
lean_inc(v_lo_6276_);
v___x_6281_ = l_Array_qpartition___redArg(v_as_6275_, v___f_6280_, v_lo_6276_, v_hi_6277_);
v_fst_6282_ = lean_ctor_get(v___x_6281_, 0);
lean_inc(v_fst_6282_);
v_snd_6283_ = lean_ctor_get(v___x_6281_, 1);
lean_inc(v_snd_6283_);
lean_dec_ref(v___x_6281_);
v___x_6284_ = lean_nat_dec_le(v_hi_6277_, v_fst_6282_);
if (v___x_6284_ == 0)
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6285_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_snd_6283_, v_lo_6276_, v_fst_6282_);
v___x_6286_ = lean_unsigned_to_nat(1u);
v___x_6287_ = lean_nat_add(v_fst_6282_, v___x_6286_);
lean_dec(v_fst_6282_);
v_as_6275_ = v___x_6285_;
v_lo_6276_ = v___x_6287_;
goto _start;
}
else
{
lean_dec(v_fst_6282_);
lean_dec(v_lo_6276_);
return v_snd_6283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg___boxed(lean_object* v_as_6289_, lean_object* v_lo_6290_, lean_object* v_hi_6291_){
_start:
{
lean_object* v_res_6292_; 
v_res_6292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_as_6289_, v_lo_6290_, v_hi_6291_);
lean_dec(v_hi_6291_);
return v_res_6292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(lean_object* v___y_6293_, lean_object* v___x_6294_, lean_object* v_n_6295_, lean_object* v_j_6296_, lean_object* v_a_6297_){
_start:
{
lean_object* v_zero_6298_; uint8_t v_isZero_6299_; 
v_zero_6298_ = lean_unsigned_to_nat(0u);
v_isZero_6299_ = lean_nat_dec_eq(v_j_6296_, v_zero_6298_);
if (v_isZero_6299_ == 1)
{
lean_dec(v_j_6296_);
return v_a_6297_;
}
else
{
lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v_toSignature_6302_; lean_object* v_name_6303_; lean_object* v___x_6304_; lean_object* v_one_6305_; lean_object* v_n_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; 
v___x_6300_ = lean_nat_sub(v_n_6295_, v_j_6296_);
v___x_6301_ = lean_array_fget_borrowed(v___y_6293_, v___x_6300_);
v_toSignature_6302_ = lean_ctor_get(v___x_6301_, 0);
v_name_6303_ = lean_ctor_get(v_toSignature_6302_, 0);
v___x_6304_ = lean_box(0);
v_one_6305_ = lean_unsigned_to_nat(1u);
v_n_6306_ = lean_nat_sub(v_j_6296_, v_one_6305_);
lean_dec(v_j_6296_);
v___x_6307_ = lean_array_get_borrowed(v___x_6304_, v___x_6294_, v___x_6300_);
lean_dec(v___x_6300_);
lean_inc(v___x_6307_);
lean_inc(v_name_6303_);
v___x_6308_ = l_Lean_Compiler_LCNF_UnreachableBranches_addFunctionSummary(v_a_6297_, v_name_6303_, v___x_6307_);
v_j_6296_ = v_n_6306_;
v_a_6297_ = v___x_6308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg___boxed(lean_object* v___y_6310_, lean_object* v___x_6311_, lean_object* v_n_6312_, lean_object* v_j_6313_, lean_object* v_a_6314_){
_start:
{
lean_object* v_res_6315_; 
v_res_6315_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6310_, v___x_6311_, v_n_6312_, v_j_6313_, v_a_6314_);
lean_dec(v_n_6312_);
lean_dec_ref(v___x_6311_);
lean_dec_ref(v___y_6310_);
return v_res_6315_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0(void){
_start:
{
lean_object* v___x_6316_; 
v___x_6316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6316_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1(void){
_start:
{
lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6317_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__0);
v___x_6318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6318_, 0, v___x_6317_);
return v___x_6318_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2(void){
_start:
{
lean_object* v___x_6319_; lean_object* v___x_6320_; 
v___x_6319_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__1);
v___x_6320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6320_, 0, v___x_6319_);
lean_ctor_set(v___x_6320_, 1, v___x_6319_);
return v___x_6320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches(lean_object* v_decls_6323_, lean_object* v_a_6324_, lean_object* v_a_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_){
_start:
{
lean_object* v___x_6329_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6369_; lean_object* v___y_6370_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v___y_6373_; lean_object* v___y_6374_; lean_object* v___y_6375_; uint8_t v___y_6376_; lean_object* v___y_6377_; lean_object* v___y_6378_; uint8_t v___y_6379_; lean_object* v___y_6380_; lean_object* v_a_6381_; lean_object* v___y_6391_; lean_object* v___y_6392_; lean_object* v___y_6393_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v___y_6396_; lean_object* v___y_6397_; uint8_t v___y_6398_; lean_object* v___y_6399_; lean_object* v___y_6400_; uint8_t v___y_6401_; lean_object* v___y_6402_; lean_object* v_a_6403_; lean_object* v___y_6416_; lean_object* v___y_6417_; lean_object* v___y_6418_; lean_object* v___y_6419_; uint8_t v___y_6420_; lean_object* v___y_6421_; uint8_t v___y_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v___y_6467_; lean_object* v___y_6492_; lean_object* v___y_6493_; lean_object* v___x_6495_; uint8_t v___x_6496_; 
v___x_6329_ = lean_unsigned_to_nat(0u);
v___x_6495_ = lean_array_get_size(v_decls_6323_);
v___x_6496_ = lean_nat_dec_eq(v___x_6495_, v___x_6329_);
if (v___x_6496_ == 0)
{
lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___y_6500_; uint8_t v___x_6502_; 
v___x_6497_ = lean_unsigned_to_nat(1u);
v___x_6498_ = lean_nat_sub(v___x_6495_, v___x_6497_);
v___x_6502_ = lean_nat_dec_le(v___x_6329_, v___x_6498_);
if (v___x_6502_ == 0)
{
lean_inc(v___x_6498_);
v___y_6500_ = v___x_6498_;
goto v___jp_6499_;
}
else
{
v___y_6500_ = v___x_6329_;
goto v___jp_6499_;
}
v___jp_6499_:
{
uint8_t v___x_6501_; 
v___x_6501_ = lean_nat_dec_le(v___y_6500_, v___x_6498_);
if (v___x_6501_ == 0)
{
lean_dec(v___x_6498_);
lean_inc(v___y_6500_);
v___y_6492_ = v___y_6500_;
v___y_6493_ = v___y_6500_;
goto v___jp_6491_;
}
else
{
v___y_6492_ = v___y_6500_;
v___y_6493_ = v___x_6498_;
goto v___jp_6491_;
}
}
}
else
{
v___y_6467_ = v_decls_6323_;
goto v___jp_6466_;
}
v___jp_6330_:
{
if (lean_obj_tag(v___y_6334_) == 0)
{
lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v_assignments_6337_; lean_object* v_funVals_6338_; lean_object* v_env_6339_; lean_object* v_nextMacroScope_6340_; lean_object* v_ngen_6341_; lean_object* v_auxDeclNGen_6342_; lean_object* v_traceState_6343_; lean_object* v_messages_6344_; lean_object* v_infoState_6345_; lean_object* v_snapshotTasks_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6358_; 
lean_dec_ref(v___y_6334_);
v___x_6335_ = lean_st_ref_get(v___y_6333_);
lean_dec(v___y_6333_);
v___x_6336_ = lean_st_ref_take(v_a_6327_);
v_assignments_6337_ = lean_ctor_get(v___x_6335_, 0);
lean_inc_ref(v_assignments_6337_);
v_funVals_6338_ = lean_ctor_get(v___x_6335_, 1);
lean_inc_ref(v_funVals_6338_);
lean_dec(v___x_6335_);
v_env_6339_ = lean_ctor_get(v___x_6336_, 0);
v_nextMacroScope_6340_ = lean_ctor_get(v___x_6336_, 1);
v_ngen_6341_ = lean_ctor_get(v___x_6336_, 2);
v_auxDeclNGen_6342_ = lean_ctor_get(v___x_6336_, 3);
v_traceState_6343_ = lean_ctor_get(v___x_6336_, 4);
v_messages_6344_ = lean_ctor_get(v___x_6336_, 6);
v_infoState_6345_ = lean_ctor_get(v___x_6336_, 7);
v_snapshotTasks_6346_ = lean_ctor_get(v___x_6336_, 8);
v_isSharedCheck_6358_ = !lean_is_exclusive(v___x_6336_);
if (v_isSharedCheck_6358_ == 0)
{
lean_object* v_unused_6359_; 
v_unused_6359_ = lean_ctor_get(v___x_6336_, 5);
lean_dec(v_unused_6359_);
v___x_6348_ = v___x_6336_;
v_isShared_6349_ = v_isSharedCheck_6358_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_snapshotTasks_6346_);
lean_inc(v_infoState_6345_);
lean_inc(v_messages_6344_);
lean_inc(v_traceState_6343_);
lean_inc(v_auxDeclNGen_6342_);
lean_inc(v_ngen_6341_);
lean_inc(v_nextMacroScope_6340_);
lean_inc(v_env_6339_);
lean_dec(v___x_6336_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6358_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6353_; 
lean_inc(v___y_6331_);
v___x_6350_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6332_, v_funVals_6338_, v___y_6331_, v___y_6331_, v_env_6339_);
lean_dec_ref(v_funVals_6338_);
v___x_6351_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2, &l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__2);
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 5, v___x_6351_);
lean_ctor_set(v___x_6348_, 0, v___x_6350_);
v___x_6353_ = v___x_6348_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v___x_6350_);
lean_ctor_set(v_reuseFailAlloc_6357_, 1, v_nextMacroScope_6340_);
lean_ctor_set(v_reuseFailAlloc_6357_, 2, v_ngen_6341_);
lean_ctor_set(v_reuseFailAlloc_6357_, 3, v_auxDeclNGen_6342_);
lean_ctor_set(v_reuseFailAlloc_6357_, 4, v_traceState_6343_);
lean_ctor_set(v_reuseFailAlloc_6357_, 5, v___x_6351_);
lean_ctor_set(v_reuseFailAlloc_6357_, 6, v_messages_6344_);
lean_ctor_set(v_reuseFailAlloc_6357_, 7, v_infoState_6345_);
lean_ctor_set(v_reuseFailAlloc_6357_, 8, v_snapshotTasks_6346_);
v___x_6353_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; 
v___x_6354_ = lean_st_ref_set(v_a_6327_, v___x_6353_);
v___x_6355_ = lean_mk_empty_array_with_capacity(v___y_6331_);
v___x_6356_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v_assignments_6337_, v___y_6332_, v___y_6331_, v___x_6329_, v___x_6355_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
lean_dec_ref(v___y_6332_);
lean_dec_ref(v_assignments_6337_);
return v___x_6356_;
}
}
}
else
{
lean_object* v_a_6360_; lean_object* v___x_6362_; uint8_t v_isShared_6363_; uint8_t v_isSharedCheck_6367_; 
lean_dec(v___y_6333_);
lean_dec_ref(v___y_6332_);
lean_dec(v___y_6331_);
v_a_6360_ = lean_ctor_get(v___y_6334_, 0);
v_isSharedCheck_6367_ = !lean_is_exclusive(v___y_6334_);
if (v_isSharedCheck_6367_ == 0)
{
v___x_6362_ = v___y_6334_;
v_isShared_6363_ = v_isSharedCheck_6367_;
goto v_resetjp_6361_;
}
else
{
lean_inc(v_a_6360_);
lean_dec(v___y_6334_);
v___x_6362_ = lean_box(0);
v_isShared_6363_ = v_isSharedCheck_6367_;
goto v_resetjp_6361_;
}
v_resetjp_6361_:
{
lean_object* v___x_6365_; 
if (v_isShared_6363_ == 0)
{
v___x_6365_ = v___x_6362_;
goto v_reusejp_6364_;
}
else
{
lean_object* v_reuseFailAlloc_6366_; 
v_reuseFailAlloc_6366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6366_, 0, v_a_6360_);
v___x_6365_ = v_reuseFailAlloc_6366_;
goto v_reusejp_6364_;
}
v_reusejp_6364_:
{
return v___x_6365_;
}
}
}
}
v___jp_6368_:
{
lean_object* v___x_6382_; double v___x_6383_; double v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; 
v___x_6382_ = lean_io_get_num_heartbeats();
v___x_6383_ = lean_float_of_nat(v___y_6373_);
v___x_6384_ = lean_float_of_nat(v___x_6382_);
v___x_6385_ = lean_box_float(v___x_6383_);
v___x_6386_ = lean_box_float(v___x_6384_);
v___x_6387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6387_, 0, v___x_6385_);
lean_ctor_set(v___x_6387_, 1, v___x_6386_);
v___x_6388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6388_, 0, v_a_6381_);
lean_ctor_set(v___x_6388_, 1, v___x_6387_);
v___x_6389_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_6371_, v___y_6379_, v___y_6370_, v___y_6378_, v___y_6376_, v___y_6369_, v___y_6372_, v___x_6388_, v___y_6380_, v___y_6377_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
lean_dec_ref(v___y_6380_);
v___y_6331_ = v___y_6374_;
v___y_6332_ = v___y_6375_;
v___y_6333_ = v___y_6377_;
v___y_6334_ = v___x_6389_;
goto v___jp_6330_;
}
v___jp_6390_:
{
lean_object* v___x_6404_; double v___x_6405_; double v___x_6406_; double v___x_6407_; double v___x_6408_; double v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; 
v___x_6404_ = lean_io_mono_nanos_now();
v___x_6405_ = lean_float_of_nat(v___y_6395_);
v___x_6406_ = lean_float_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__1);
v___x_6407_ = lean_float_div(v___x_6405_, v___x_6406_);
v___x_6408_ = lean_float_of_nat(v___x_6404_);
v___x_6409_ = lean_float_div(v___x_6408_, v___x_6406_);
v___x_6410_ = lean_box_float(v___x_6407_);
v___x_6411_ = lean_box_float(v___x_6409_);
v___x_6412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6412_, 0, v___x_6410_);
lean_ctor_set(v___x_6412_, 1, v___x_6411_);
v___x_6413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6413_, 0, v_a_6403_);
lean_ctor_set(v___x_6413_, 1, v___x_6412_);
v___x_6414_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__3(v___y_6393_, v___y_6401_, v___y_6392_, v___y_6400_, v___y_6398_, v___y_6391_, v___y_6394_, v___x_6413_, v___y_6402_, v___y_6399_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
lean_dec_ref(v___y_6402_);
v___y_6331_ = v___y_6396_;
v___y_6332_ = v___y_6397_;
v___y_6333_ = v___y_6399_;
v___y_6334_ = v___x_6414_;
goto v___jp_6330_;
}
v___jp_6415_:
{
lean_object* v___x_6426_; lean_object* v_a_6427_; lean_object* v___x_6428_; uint8_t v___x_6429_; 
v___x_6426_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__1___redArg(v_a_6327_);
v_a_6427_ = lean_ctor_get(v___x_6426_, 0);
lean_inc(v_a_6427_);
lean_dec_ref(v___x_6426_);
v___x_6428_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6429_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v___y_6424_, v___x_6428_);
if (v___x_6429_ == 0)
{
lean_object* v___x_6430_; lean_object* v___x_6431_; 
v___x_6430_ = lean_io_mono_nanos_now();
lean_inc_ref(v___y_6425_);
v___x_6431_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6329_, v___y_6425_, v___y_6423_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
if (lean_obj_tag(v___x_6431_) == 0)
{
lean_object* v_a_6432_; lean_object* v___x_6434_; uint8_t v_isShared_6435_; uint8_t v_isSharedCheck_6439_; 
v_a_6432_ = lean_ctor_get(v___x_6431_, 0);
v_isSharedCheck_6439_ = !lean_is_exclusive(v___x_6431_);
if (v_isSharedCheck_6439_ == 0)
{
v___x_6434_ = v___x_6431_;
v_isShared_6435_ = v_isSharedCheck_6439_;
goto v_resetjp_6433_;
}
else
{
lean_inc(v_a_6432_);
lean_dec(v___x_6431_);
v___x_6434_ = lean_box(0);
v_isShared_6435_ = v_isSharedCheck_6439_;
goto v_resetjp_6433_;
}
v_resetjp_6433_:
{
lean_object* v___x_6437_; 
if (v_isShared_6435_ == 0)
{
lean_ctor_set_tag(v___x_6434_, 1);
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
v___y_6391_ = v_a_6427_;
v___y_6392_ = v___y_6417_;
v___y_6393_ = v___y_6416_;
v___y_6394_ = v___y_6418_;
v___y_6395_ = v___x_6430_;
v___y_6396_ = v___y_6419_;
v___y_6397_ = v___y_6421_;
v___y_6398_ = v___y_6420_;
v___y_6399_ = v___y_6423_;
v___y_6400_ = v___y_6424_;
v___y_6401_ = v___y_6422_;
v___y_6402_ = v___y_6425_;
v_a_6403_ = v___x_6437_;
goto v___jp_6390_;
}
}
}
else
{
lean_object* v_a_6440_; lean_object* v___x_6442_; uint8_t v_isShared_6443_; uint8_t v_isSharedCheck_6447_; 
v_a_6440_ = lean_ctor_get(v___x_6431_, 0);
v_isSharedCheck_6447_ = !lean_is_exclusive(v___x_6431_);
if (v_isSharedCheck_6447_ == 0)
{
v___x_6442_ = v___x_6431_;
v_isShared_6443_ = v_isSharedCheck_6447_;
goto v_resetjp_6441_;
}
else
{
lean_inc(v_a_6440_);
lean_dec(v___x_6431_);
v___x_6442_ = lean_box(0);
v_isShared_6443_ = v_isSharedCheck_6447_;
goto v_resetjp_6441_;
}
v_resetjp_6441_:
{
lean_object* v___x_6445_; 
if (v_isShared_6443_ == 0)
{
lean_ctor_set_tag(v___x_6442_, 0);
v___x_6445_ = v___x_6442_;
goto v_reusejp_6444_;
}
else
{
lean_object* v_reuseFailAlloc_6446_; 
v_reuseFailAlloc_6446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_a_6440_);
v___x_6445_ = v_reuseFailAlloc_6446_;
goto v_reusejp_6444_;
}
v_reusejp_6444_:
{
v___y_6391_ = v_a_6427_;
v___y_6392_ = v___y_6417_;
v___y_6393_ = v___y_6416_;
v___y_6394_ = v___y_6418_;
v___y_6395_ = v___x_6430_;
v___y_6396_ = v___y_6419_;
v___y_6397_ = v___y_6421_;
v___y_6398_ = v___y_6420_;
v___y_6399_ = v___y_6423_;
v___y_6400_ = v___y_6424_;
v___y_6401_ = v___y_6422_;
v___y_6402_ = v___y_6425_;
v_a_6403_ = v___x_6445_;
goto v___jp_6390_;
}
}
}
}
else
{
lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6448_ = lean_io_get_num_heartbeats();
lean_inc_ref(v___y_6425_);
v___x_6449_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6329_, v___y_6425_, v___y_6423_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
if (lean_obj_tag(v___x_6449_) == 0)
{
lean_object* v_a_6450_; lean_object* v___x_6452_; uint8_t v_isShared_6453_; uint8_t v_isSharedCheck_6457_; 
v_a_6450_ = lean_ctor_get(v___x_6449_, 0);
v_isSharedCheck_6457_ = !lean_is_exclusive(v___x_6449_);
if (v_isSharedCheck_6457_ == 0)
{
v___x_6452_ = v___x_6449_;
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
else
{
lean_inc(v_a_6450_);
lean_dec(v___x_6449_);
v___x_6452_ = lean_box(0);
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
v_resetjp_6451_:
{
lean_object* v___x_6455_; 
if (v_isShared_6453_ == 0)
{
lean_ctor_set_tag(v___x_6452_, 1);
v___x_6455_ = v___x_6452_;
goto v_reusejp_6454_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6450_);
v___x_6455_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6454_;
}
v_reusejp_6454_:
{
v___y_6369_ = v_a_6427_;
v___y_6370_ = v___y_6417_;
v___y_6371_ = v___y_6416_;
v___y_6372_ = v___y_6418_;
v___y_6373_ = v___x_6448_;
v___y_6374_ = v___y_6419_;
v___y_6375_ = v___y_6421_;
v___y_6376_ = v___y_6420_;
v___y_6377_ = v___y_6423_;
v___y_6378_ = v___y_6424_;
v___y_6379_ = v___y_6422_;
v___y_6380_ = v___y_6425_;
v_a_6381_ = v___x_6455_;
goto v___jp_6368_;
}
}
}
else
{
lean_object* v_a_6458_; lean_object* v___x_6460_; uint8_t v_isShared_6461_; uint8_t v_isSharedCheck_6465_; 
v_a_6458_ = lean_ctor_get(v___x_6449_, 0);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___x_6449_);
if (v_isSharedCheck_6465_ == 0)
{
v___x_6460_ = v___x_6449_;
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
else
{
lean_inc(v_a_6458_);
lean_dec(v___x_6449_);
v___x_6460_ = lean_box(0);
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
v_resetjp_6459_:
{
lean_object* v___x_6463_; 
if (v_isShared_6461_ == 0)
{
lean_ctor_set_tag(v___x_6460_, 0);
v___x_6463_ = v___x_6460_;
goto v_reusejp_6462_;
}
else
{
lean_object* v_reuseFailAlloc_6464_; 
v_reuseFailAlloc_6464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_a_6458_);
v___x_6463_ = v_reuseFailAlloc_6464_;
goto v_reusejp_6462_;
}
v_reusejp_6462_:
{
v___y_6369_ = v_a_6427_;
v___y_6370_ = v___y_6417_;
v___y_6371_ = v___y_6416_;
v___y_6372_ = v___y_6418_;
v___y_6373_ = v___x_6448_;
v___y_6374_ = v___y_6419_;
v___y_6375_ = v___y_6421_;
v___y_6376_ = v___y_6420_;
v___y_6377_ = v___y_6423_;
v___y_6378_ = v___y_6424_;
v___y_6379_ = v___y_6422_;
v___y_6380_ = v___y_6425_;
v_a_6381_ = v___x_6463_;
goto v___jp_6368_;
}
}
}
}
}
v___jp_6466_:
{
size_t v_sz_6468_; size_t v___x_6469_; lean_object* v_assignments_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v_funVals_6473_; lean_object* v_state_6474_; lean_object* v___x_6475_; lean_object* v_options_6476_; uint8_t v_hasTrace_6477_; lean_object* v_ctx_6478_; 
v_sz_6468_ = lean_array_size(v___y_6467_);
v___x_6469_ = ((size_t)0ULL);
lean_inc_ref(v___y_6467_);
v_assignments_6470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_UnreachableBranches_inferMain_spec__0(v_sz_6468_, v___x_6469_, v___y_6467_);
v___x_6471_ = lean_array_get_size(v___y_6467_);
v___x_6472_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___closed__3));
v_funVals_6473_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6467_, v___x_6471_, v___x_6471_, v___x_6472_);
v_state_6474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_state_6474_, 0, v_assignments_6470_);
lean_ctor_set(v_state_6474_, 1, v_funVals_6473_);
v___x_6475_ = lean_st_mk_ref(v_state_6474_);
v_options_6476_ = lean_ctor_get(v_a_6326_, 2);
v_hasTrace_6477_ = lean_ctor_get_uint8(v_options_6476_, sizeof(void*)*1);
lean_inc_ref(v___y_6467_);
v_ctx_6478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_ctx_6478_, 0, v___y_6467_);
lean_ctor_set(v_ctx_6478_, 1, v___x_6329_);
if (v_hasTrace_6477_ == 0)
{
lean_object* v___x_6479_; 
v___x_6479_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6329_, v_ctx_6478_, v___x_6475_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
v___y_6331_ = v___x_6471_;
v___y_6332_ = v___y_6467_;
v___y_6333_ = v___x_6475_;
v___y_6334_ = v___x_6479_;
goto v___jp_6330_;
}
else
{
lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v_a_6482_; lean_object* v___f_6483_; lean_object* v___x_6484_; uint8_t v___x_6485_; 
v___x_6480_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_6481_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__0___redArg(v___x_6480_, v_a_6326_);
v_a_6482_ = lean_ctor_get(v___x_6481_, 0);
lean_inc(v_a_6482_);
lean_dec_ref(v___x_6481_);
lean_inc_ref(v___y_6467_);
v___f_6483_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadBranches___lam__0___boxed), 9, 1);
lean_closure_set(v___f_6483_, 0, v___y_6467_);
v___x_6484_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__4));
v___x_6485_ = lean_unbox(v_a_6482_);
if (v___x_6485_ == 0)
{
lean_object* v___x_6486_; uint8_t v___x_6487_; 
v___x_6486_ = l_Lean_trace_profiler;
v___x_6487_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__2(v_options_6476_, v___x_6486_);
if (v___x_6487_ == 0)
{
lean_object* v___x_6488_; 
lean_dec_ref(v___f_6483_);
lean_dec(v_a_6482_);
v___x_6488_ = l_Lean_Compiler_LCNF_UnreachableBranches_inferMain(v___x_6329_, v_ctx_6478_, v___x_6475_, v_a_6324_, v_a_6325_, v_a_6326_, v_a_6327_);
v___y_6331_ = v___x_6471_;
v___y_6332_ = v___y_6467_;
v___y_6333_ = v___x_6475_;
v___y_6334_ = v___x_6488_;
goto v___jp_6330_;
}
else
{
uint8_t v___x_6489_; 
v___x_6489_ = lean_unbox(v_a_6482_);
lean_dec(v_a_6482_);
v___y_6416_ = v___x_6480_;
v___y_6417_ = v___x_6484_;
v___y_6418_ = v___f_6483_;
v___y_6419_ = v___x_6471_;
v___y_6420_ = v___x_6489_;
v___y_6421_ = v___y_6467_;
v___y_6422_ = v_hasTrace_6477_;
v___y_6423_ = v___x_6475_;
v___y_6424_ = v_options_6476_;
v___y_6425_ = v_ctx_6478_;
goto v___jp_6415_;
}
}
else
{
uint8_t v___x_6490_; 
v___x_6490_ = lean_unbox(v_a_6482_);
lean_dec(v_a_6482_);
v___y_6416_ = v___x_6480_;
v___y_6417_ = v___x_6484_;
v___y_6418_ = v___f_6483_;
v___y_6419_ = v___x_6471_;
v___y_6420_ = v___x_6490_;
v___y_6421_ = v___y_6467_;
v___y_6422_ = v_hasTrace_6477_;
v___y_6423_ = v___x_6475_;
v___y_6424_ = v_options_6476_;
v___y_6425_ = v_ctx_6478_;
goto v___jp_6415_;
}
}
}
v___jp_6491_:
{
lean_object* v___x_6494_; 
v___x_6494_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_decls_6323_, v___y_6492_, v___y_6493_);
lean_dec(v___y_6493_);
v___y_6467_ = v___x_6494_;
goto v___jp_6466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadBranches___boxed(lean_object* v_decls_6503_, lean_object* v_a_6504_, lean_object* v_a_6505_, lean_object* v_a_6506_, lean_object* v_a_6507_, lean_object* v_a_6508_){
_start:
{
lean_object* v_res_6509_; 
v_res_6509_ = l_Lean_Compiler_LCNF_Decl_elimDeadBranches(v_decls_6503_, v_a_6504_, v_a_6505_, v_a_6506_, v_a_6507_);
lean_dec(v_a_6507_);
lean_dec_ref(v_a_6506_);
lean_dec(v_a_6505_);
lean_dec_ref(v_a_6504_);
return v_res_6509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(lean_object* v___y_6510_, lean_object* v_n_6511_, lean_object* v_j_6512_, lean_object* v_a_6513_, lean_object* v_a_6514_){
_start:
{
lean_object* v___x_6515_; 
v___x_6515_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___redArg(v___y_6510_, v_n_6511_, v_j_6512_, v_a_6514_);
return v___x_6515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2___boxed(lean_object* v___y_6516_, lean_object* v_n_6517_, lean_object* v_j_6518_, lean_object* v_a_6519_, lean_object* v_a_6520_){
_start:
{
lean_object* v_res_6521_; 
v_res_6521_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__2(v___y_6516_, v_n_6517_, v_j_6518_, v_a_6519_, v_a_6520_);
lean_dec(v_n_6517_);
lean_dec_ref(v___y_6516_);
return v_res_6521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(lean_object* v___y_6522_, lean_object* v___x_6523_, lean_object* v_n_6524_, lean_object* v_j_6525_, lean_object* v_a_6526_, lean_object* v_a_6527_){
_start:
{
lean_object* v___x_6528_; 
v___x_6528_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___redArg(v___y_6522_, v___x_6523_, v_n_6524_, v_j_6525_, v_a_6527_);
return v___x_6528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3___boxed(lean_object* v___y_6529_, lean_object* v___x_6530_, lean_object* v_n_6531_, lean_object* v_j_6532_, lean_object* v_a_6533_, lean_object* v_a_6534_){
_start:
{
lean_object* v_res_6535_; 
v_res_6535_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__3(v___y_6529_, v___x_6530_, v_n_6531_, v_j_6532_, v_a_6533_, v_a_6534_);
lean_dec(v_n_6531_);
lean_dec_ref(v___x_6530_);
lean_dec_ref(v___y_6529_);
return v_res_6535_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(lean_object* v___x_6536_, lean_object* v_as_6537_, lean_object* v_i_6538_, lean_object* v_j_6539_, lean_object* v_inv_6540_, lean_object* v_bs_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_, lean_object* v___y_6545_){
_start:
{
lean_object* v___x_6547_; 
v___x_6547_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___redArg(v___x_6536_, v_as_6537_, v_i_6538_, v_j_6539_, v_bs_6541_, v___y_6542_, v___y_6543_, v___y_6544_, v___y_6545_);
return v___x_6547_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4___boxed(lean_object* v___x_6548_, lean_object* v_as_6549_, lean_object* v_i_6550_, lean_object* v_j_6551_, lean_object* v_inv_6552_, lean_object* v_bs_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_){
_start:
{
lean_object* v_res_6559_; 
v_res_6559_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__4(v___x_6548_, v_as_6549_, v_i_6550_, v_j_6551_, v_inv_6552_, v_bs_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_);
lean_dec(v___y_6557_);
lean_dec_ref(v___y_6556_);
lean_dec(v___y_6555_);
lean_dec_ref(v___y_6554_);
lean_dec_ref(v_as_6549_);
lean_dec_ref(v___x_6548_);
return v_res_6559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(lean_object* v_n_6560_, lean_object* v_as_6561_, lean_object* v_lo_6562_, lean_object* v_hi_6563_, lean_object* v_w_6564_, lean_object* v_hlo_6565_, lean_object* v_hhi_6566_){
_start:
{
lean_object* v___x_6567_; 
v___x_6567_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___redArg(v_as_6561_, v_lo_6562_, v_hi_6563_);
return v___x_6567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5___boxed(lean_object* v_n_6568_, lean_object* v_as_6569_, lean_object* v_lo_6570_, lean_object* v_hi_6571_, lean_object* v_w_6572_, lean_object* v_hlo_6573_, lean_object* v_hhi_6574_){
_start:
{
lean_object* v_res_6575_; 
v_res_6575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_Decl_elimDeadBranches_spec__5(v_n_6568_, v_as_6569_, v_lo_6570_, v_hi_6571_, v_w_6572_, v_hlo_6573_, v_hhi_6574_);
lean_dec(v_hi_6571_);
lean_dec(v_n_6568_);
return v_res_6575_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; 
v___x_6635_ = lean_unsigned_to_nat(3955956072u);
v___x_6636_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6637_ = l_Lean_Name_num___override(v___x_6636_, v___x_6635_);
return v___x_6637_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
v___x_6639_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6640_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6641_ = l_Lean_Name_str___override(v___x_6640_, v___x_6639_);
return v___x_6641_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; 
v___x_6643_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_));
v___x_6644_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6645_ = l_Lean_Name_str___override(v___x_6644_, v___x_6643_);
return v___x_6645_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; 
v___x_6646_ = lean_unsigned_to_nat(2u);
v___x_6647_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6648_ = l_Lean_Name_num___override(v___x_6647_, v___x_6646_);
return v___x_6648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6650_; uint8_t v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; 
v___x_6650_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_UnreachableBranches_inferStep_spec__4___redArg___closed__3));
v___x_6651_ = 1;
v___x_6652_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_);
v___x_6653_ = l_Lean_registerTraceClass(v___x_6650_, v___x_6651_, v___x_6652_);
return v___x_6653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2____boxed(lean_object* v_a_6654_){
_start:
{
lean_object* v_res_6655_; 
v_res_6655_ = l___private_Lean_Compiler_LCNF_ElimDeadBranches_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_3955956072____hygCtx___hyg_2_();
return v_res_6655_;
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
res = l_Lean_Compiler_LCNF_UnreachableBranches_initFn_00___x40_Lean_Compiler_LCNF_ElimDeadBranches_1013187147____hygCtx___hyg_2_();
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
