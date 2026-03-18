// Lean compiler output
// Module: Lean.Compiler.LCNF.InferBorrow
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.ExportAttr import Std.Data.Iterators.Producers.Array import Std.Data.Iterators.Combinators.Zip import Lean.Compiler.LCNF.MonadScope import Lean.Compiler.LCNF.FVarUtil import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.PrettyPrinter
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
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_isExport(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_decl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_decl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_jp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_jp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__1;
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.Compiler.LCNF.InferBorrow.0.Lean.Compiler.LCNF.mkInitParamMap.goCode"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Compiler.LCNF.InferBorrow"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Compiler.LCNF.InferBorrow.0.Lean.Compiler.LCNF.apply.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_resetReuse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_resetReuse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorResult_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorResult_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorArg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorArg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_projectionPropagation_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_projectionPropagation_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallResult_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallResult_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallArg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallArg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_fvarCall_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_fvarCall_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_partialApplication_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_partialApplication_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_tailCallPreservation_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_tailCallPreservation_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpArgPropagation_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpArgPropagation_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpTailCallPreservation_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpTailCallPreservation_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "used in reset reuse "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "result of ctor call "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "argument to constructor call "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "projection propagation "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "result of function call "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "owned function argument "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "argument to closure call "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "argument to pap "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "tail call preservation of "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "backward propagation from JP "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "JP tail call preservation "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inferBorrow"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 32, 132, 193, 112, 124, 81, 175)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "own "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.FVarUtil"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Expr.forFVarM"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Failed to find LCNF signature for "};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Compiler.LCNF.InferBorrow.0.Lean.Compiler.LCNF.infer.getParamInfo"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.InferBorrow.0.Lean.Compiler.LCNF.infer.collectCode"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferBorrow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferBorrow___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_inferBorrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_inferBorrow___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_inferBorrow___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_inferBorrow___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_inferBorrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 19, 0, 229, 111, 180, 204, 14)}};
static const lean_object* l_Lean_Compiler_LCNF_inferBorrow___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_inferBorrow___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_inferBorrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_inferBorrow___closed__1_value),((lean_object*)&l_Lean_Compiler_LCNF_inferBorrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_inferBorrow___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_inferBorrow___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_inferBorrow = (const lean_object*)&l_Lean_Compiler_LCNF_inferBorrow___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "InferBorrow"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 208, 17, 126, 164, 187, 75, 189)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 5, 54, 52, 72, 27, 148, 77)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 13, 112, 128, 253, 14, 247, 39)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 114, 118, 32, 189, 66, 203, 24)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 49, 5, 215, 125, 193, 246, 34)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 183, 97, 104, 102, 139, 3, 250)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 67, 163, 36, 136, 199, 248, 0)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 132, 145, 216, 84, 19, 198, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 11, 250, 40, 153, 169, 18, 223)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 115, 234, 75, 87, 80, 193, 39)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 78, 132, 77, 51, 201, 208, 78)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)(((size_t)(419080822) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(191, 60, 25, 5, 219, 182, 243, 114)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 96, 178, 254, 39, 188, 36, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 245, 90, 205, 97, 250, 253, 159)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(49, 8, 28, 105, 107, 189, 96, 137)}};
static const lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_name_8_; lean_object* v___x_9_; 
v_name_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_name_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_name_8_);
return v___x_9_;
}
else
{
lean_object* v_name_10_; lean_object* v_jpId_11_; lean_object* v___x_12_; 
v_name_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_name_10_);
v_jpId_11_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_jpId_11_);
lean_dec_ref(v_t_6_);
v___x_12_ = lean_apply_2(v_k_7_, v_name_10_, v_jpId_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_decl_elim___redArg(lean_object* v_t_25_, lean_object* v_decl_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___redArg(v_t_25_, v_decl_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_decl_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_decl_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___redArg(v_t_29_, v_decl_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_jp_elim___redArg(lean_object* v_t_33_, lean_object* v_jp_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___redArg(v_t_33_, v_jp_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_jp_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_jp_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_Key_ctorElim___redArg(v_t_37_, v_jp_39_);
return v___x_40_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_name_43_; lean_object* v_name_44_; uint8_t v___x_45_; 
v_name_43_ = lean_ctor_get(v_x_41_, 0);
v_name_44_ = lean_ctor_get(v_x_42_, 0);
v___x_45_ = lean_name_eq(v_name_43_, v_name_44_);
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = 0;
return v___x_46_;
}
}
else
{
if (lean_obj_tag(v_x_42_) == 1)
{
lean_object* v_name_47_; lean_object* v_jpId_48_; lean_object* v_name_49_; lean_object* v_jpId_50_; uint8_t v___x_51_; 
v_name_47_ = lean_ctor_get(v_x_41_, 0);
v_jpId_48_ = lean_ctor_get(v_x_41_, 1);
v_name_49_ = lean_ctor_get(v_x_42_, 0);
v_jpId_50_ = lean_ctor_get(v_x_42_, 1);
v___x_51_ = lean_name_eq(v_name_47_, v_name_49_);
if (v___x_51_ == 0)
{
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = l_Lean_instBEqFVarId_beq(v_jpId_48_, v_jpId_50_);
return v___x_52_;
}
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq___boxed(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_x_54_, v_x_55_);
lean_dec_ref(v_x_55_);
lean_dec_ref(v_x_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
static uint64_t _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0(void){
_start:
{
lean_object* v___x_60_; uint64_t v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1723u);
v___x_61_ = lean_uint64_of_nat(v___x_60_);
return v___x_61_;
}
}
static uint64_t _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__1(void){
_start:
{
uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; 
v___x_62_ = lean_uint64_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0);
v___x_63_ = 0ULL;
v___x_64_ = lean_uint64_mix_hash(v___x_63_, v___x_62_);
return v___x_64_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v_name_66_; uint64_t v___x_67_; 
v_name_66_ = lean_ctor_get(v_x_65_, 0);
v___x_67_ = 0ULL;
if (lean_obj_tag(v_name_66_) == 0)
{
uint64_t v___x_68_; 
v___x_68_ = lean_uint64_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__1, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__1);
return v___x_68_;
}
else
{
uint64_t v_hash_69_; uint64_t v___x_70_; 
v_hash_69_ = lean_ctor_get_uint64(v_name_66_, sizeof(void*)*2);
v___x_70_ = lean_uint64_mix_hash(v___x_67_, v_hash_69_);
return v___x_70_;
}
}
else
{
lean_object* v_name_71_; lean_object* v_jpId_72_; uint64_t v___x_73_; uint64_t v___y_75_; 
v_name_71_ = lean_ctor_get(v_x_65_, 0);
v_jpId_72_ = lean_ctor_get(v_x_65_, 1);
v___x_73_ = 1ULL;
if (lean_obj_tag(v_name_71_) == 0)
{
uint64_t v___x_79_; 
v___x_79_ = lean_uint64_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___closed__0);
v___y_75_ = v___x_79_;
goto v___jp_74_;
}
else
{
uint64_t v_hash_80_; 
v_hash_80_ = lean_ctor_get_uint64(v_name_71_, sizeof(void*)*2);
v___y_75_ = v_hash_80_;
goto v___jp_74_;
}
v___jp_74_:
{
uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v___x_78_; 
v___x_76_ = lean_uint64_mix_hash(v___x_73_, v___y_75_);
v___x_77_ = l_Lean_instHashableFVarId_hash(v_jpId_72_);
v___x_78_ = lean_uint64_mix_hash(v___x_76_, v___x_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash___boxed(lean_object* v_x_81_){
_start:
{
uint64_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_x_81_);
lean_dec_ref(v_x_81_);
v_r_83_ = lean_box_uint64(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow_spec__0(size_t v_sz_86_, size_t v_i_87_, lean_object* v_bs_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_usize_dec_lt(v_i_87_, v_sz_86_);
if (v___x_89_ == 0)
{
return v_bs_88_;
}
else
{
lean_object* v_v_90_; lean_object* v_fvarId_91_; lean_object* v_binderName_92_; lean_object* v_type_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_107_; 
v_v_90_ = lean_array_uget(v_bs_88_, v_i_87_);
v_fvarId_91_ = lean_ctor_get(v_v_90_, 0);
v_binderName_92_ = lean_ctor_get(v_v_90_, 1);
v_type_93_ = lean_ctor_get(v_v_90_, 2);
v_isSharedCheck_107_ = !lean_is_exclusive(v_v_90_);
if (v_isSharedCheck_107_ == 0)
{
v___x_95_ = v_v_90_;
v_isShared_96_ = v_isSharedCheck_107_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_type_93_);
lean_inc(v_binderName_92_);
lean_inc(v_fvarId_91_);
lean_dec(v_v_90_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_107_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v_bs_x27_98_; uint8_t v___x_99_; lean_object* v___x_101_; 
v___x_97_ = lean_unsigned_to_nat(0u);
v_bs_x27_98_ = lean_array_uset(v_bs_88_, v_i_87_, v___x_97_);
v___x_99_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_93_);
if (v_isShared_96_ == 0)
{
v___x_101_ = v___x_95_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_fvarId_91_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_binderName_92_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_type_93_);
v___x_101_ = v_reuseFailAlloc_106_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; 
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3, v___x_99_);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_add(v_i_87_, v___x_102_);
v___x_104_ = lean_array_uset(v_bs_x27_98_, v_i_87_, v___x_101_);
v_i_87_ = v___x_103_;
v_bs_88_ = v___x_104_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow_spec__0___boxed(lean_object* v_sz_108_, lean_object* v_i_109_, lean_object* v_bs_110_){
_start:
{
size_t v_sz_boxed_111_; size_t v_i_boxed_112_; lean_object* v_res_113_; 
v_sz_boxed_111_ = lean_unbox_usize(v_sz_108_);
lean_dec(v_sz_108_);
v_i_boxed_112_ = lean_unbox_usize(v_i_109_);
lean_dec(v_i_109_);
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow_spec__0(v_sz_boxed_111_, v_i_boxed_112_, v_bs_110_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow(lean_object* v_ps_114_){
_start:
{
size_t v_sz_115_; size_t v___x_116_; lean_object* v___x_117_; 
v_sz_115_ = lean_array_size(v_ps_114_);
v___x_116_ = ((size_t)0ULL);
v___x_117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow_spec__0(v_sz_115_, v___x_116_, v_ps_114_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParams(lean_object* v_ps_118_){
_start:
{
size_t v_sz_119_; size_t v___x_120_; lean_object* v___x_121_; 
v_sz_119_ = lean_array_size(v_ps_118_);
v___x_120_ = ((size_t)0ULL);
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initBorrow_spec__0(v_sz_119_, v___x_120_, v_ps_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___redArg(lean_object* v_alt_122_, lean_object* v_f_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
switch(lean_obj_tag(v_alt_122_))
{
case 0:
{
lean_object* v_code_130_; lean_object* v___x_131_; 
v_code_130_ = lean_ctor_get(v_alt_122_, 2);
lean_inc_ref(v_code_130_);
lean_dec_ref(v_alt_122_);
v___x_131_ = lean_apply_7(v_f_123_, v_code_130_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_131_;
}
case 1:
{
lean_object* v_code_132_; lean_object* v___x_133_; 
v_code_132_ = lean_ctor_get(v_alt_122_, 1);
lean_inc_ref(v_code_132_);
lean_dec_ref(v_alt_122_);
v___x_133_ = lean_apply_7(v_f_123_, v_code_132_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_133_;
}
default: 
{
lean_object* v_code_134_; lean_object* v___x_135_; 
v_code_134_ = lean_ctor_get(v_alt_122_, 0);
lean_inc_ref(v_code_134_);
lean_dec_ref(v_alt_122_);
v___x_135_ = lean_apply_7(v_f_123_, v_code_134_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___redArg___boxed(lean_object* v_alt_136_, lean_object* v_f_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___redArg(v_alt_136_, v_f_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0(uint8_t v_pu_145_, lean_object* v_alt_146_, lean_object* v_f_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___redArg(v_alt_146_, v_f_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___boxed(lean_object* v_pu_155_, lean_object* v_alt_156_, lean_object* v_f_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
uint8_t v_pu_boxed_164_; lean_object* v_res_165_; 
v_pu_boxed_164_ = lean_unbox(v_pu_155_);
v_res_165_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0(v_pu_boxed_164_, v_alt_156_, v_f_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
return v_res_165_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_toApplicative_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_242_; 
v___x_178_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_179_ = l_ReaderT_instMonad___redArg(v___x_178_);
v_toApplicative_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v___x_179_, 1);
lean_dec(v_unused_243_);
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_242_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_toApplicative_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_242_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_toFunctor_184_; lean_object* v_toSeq_185_; lean_object* v_toSeqLeft_186_; lean_object* v_toSeqRight_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_240_; 
v_toFunctor_184_ = lean_ctor_get(v_toApplicative_180_, 0);
v_toSeq_185_ = lean_ctor_get(v_toApplicative_180_, 2);
v_toSeqLeft_186_ = lean_ctor_get(v_toApplicative_180_, 3);
v_toSeqRight_187_ = lean_ctor_get(v_toApplicative_180_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v_toApplicative_180_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v_toApplicative_180_, 1);
lean_dec(v_unused_241_);
v___x_189_ = v_toApplicative_180_;
v_isShared_190_ = v_isSharedCheck_240_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_toSeqRight_187_);
lean_inc(v_toSeqLeft_186_);
lean_inc(v_toSeq_185_);
lean_inc(v_toFunctor_184_);
lean_dec(v_toApplicative_180_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_240_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___x_200_; 
v___f_191_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_192_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_184_);
v___f_193_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_193_, 0, v_toFunctor_184_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_194_, 0, v_toFunctor_184_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___f_193_);
lean_ctor_set(v___x_195_, 1, v___f_194_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_196_, 0, v_toSeqRight_187_);
v___f_197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_197_, 0, v_toSeqLeft_186_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_198_, 0, v_toSeq_185_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v___f_196_);
lean_ctor_set(v___x_189_, 3, v___f_197_);
lean_ctor_set(v___x_189_, 2, v___f_198_);
lean_ctor_set(v___x_189_, 1, v___f_191_);
lean_ctor_set(v___x_189_, 0, v___x_195_);
v___x_200_ = v___x_189_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___f_191_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v___f_198_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v___f_197_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v___f_196_);
v___x_200_ = v_reuseFailAlloc_239_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v___f_192_);
lean_ctor_set(v___x_182_, 0, v___x_200_);
v___x_202_ = v___x_182_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___f_192_);
v___x_202_ = v_reuseFailAlloc_238_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; lean_object* v_toApplicative_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_236_; 
v___x_203_ = l_ReaderT_instMonad___redArg(v___x_202_);
v_toApplicative_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_203_, 1);
lean_dec(v_unused_237_);
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_236_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_toApplicative_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_236_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_toFunctor_208_; lean_object* v_toSeq_209_; lean_object* v_toSeqLeft_210_; lean_object* v_toSeqRight_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_234_; 
v_toFunctor_208_ = lean_ctor_get(v_toApplicative_204_, 0);
v_toSeq_209_ = lean_ctor_get(v_toApplicative_204_, 2);
v_toSeqLeft_210_ = lean_ctor_get(v_toApplicative_204_, 3);
v_toSeqRight_211_ = lean_ctor_get(v_toApplicative_204_, 4);
v_isSharedCheck_234_ = !lean_is_exclusive(v_toApplicative_204_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v_toApplicative_204_, 1);
lean_dec(v_unused_235_);
v___x_213_ = v_toApplicative_204_;
v_isShared_214_ = v_isSharedCheck_234_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_toSeqRight_211_);
lean_inc(v_toSeqLeft_210_);
lean_inc(v_toSeq_209_);
lean_inc(v_toFunctor_208_);
lean_dec(v_toApplicative_204_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_234_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___x_224_; 
v___f_215_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_216_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_208_);
v___f_217_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_217_, 0, v_toFunctor_208_);
v___f_218_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_218_, 0, v_toFunctor_208_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___f_217_);
lean_ctor_set(v___x_219_, 1, v___f_218_);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_220_, 0, v_toSeqRight_211_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_221_, 0, v_toSeqLeft_210_);
v___f_222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_222_, 0, v_toSeq_209_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 4, v___f_220_);
lean_ctor_set(v___x_213_, 3, v___f_221_);
lean_ctor_set(v___x_213_, 2, v___f_222_);
lean_ctor_set(v___x_213_, 1, v___f_215_);
lean_ctor_set(v___x_213_, 0, v___x_219_);
v___x_224_ = v___x_213_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___f_215_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v___f_222_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v___f_221_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v___f_220_);
v___x_224_ = v_reuseFailAlloc_233_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_226_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___f_216_);
lean_ctor_set(v___x_206_, 0, v___x_224_);
v___x_226_ = v___x_206_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___f_216_);
v___x_226_ = v_reuseFailAlloc_232_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_2771__overap_230_; lean_object* v___x_231_; 
v___x_227_ = l_ReaderT_instMonad___redArg(v___x_226_);
v___x_228_ = lean_box(0);
v___x_229_ = l_instInhabitedOfMonad___redArg(v___x_227_, v___x_228_);
v___x_2771__overap_230_ = lean_panic_fn(v___x_229_, v_msg_171_);
v___x_231_ = lean_apply_6(v___x_2771__overap_230_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, lean_box(0));
return v___x_231_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___boxed(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3(v_msg_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__3___redArg(lean_object* v_a_252_, lean_object* v_b_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_dec(v_b_253_);
lean_dec_ref(v_a_252_);
return v_x_254_;
}
else
{
lean_object* v_key_255_; lean_object* v_value_256_; lean_object* v_tail_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_269_; 
v_key_255_ = lean_ctor_get(v_x_254_, 0);
v_value_256_ = lean_ctor_get(v_x_254_, 1);
v_tail_257_ = lean_ctor_get(v_x_254_, 2);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_269_ == 0)
{
v___x_259_ = v_x_254_;
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_tail_257_);
lean_inc(v_value_256_);
lean_inc(v_key_255_);
lean_dec(v_x_254_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___x_261_; 
v___x_261_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_255_, v_a_252_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__3___redArg(v_a_252_, v_b_253_, v_tail_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 2, v___x_262_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_key_255_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_value_256_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
else
{
lean_object* v___x_267_; 
lean_dec(v_value_256_);
lean_dec(v_key_255_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v_b_253_);
lean_ctor_set(v___x_259_, 0, v_a_252_);
v___x_267_ = v___x_259_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_252_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_b_253_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_tail_257_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
return v_x_270_;
}
else
{
lean_object* v_key_272_; lean_object* v_value_273_; lean_object* v_tail_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_297_; 
v_key_272_ = lean_ctor_get(v_x_271_, 0);
v_value_273_ = lean_ctor_get(v_x_271_, 1);
v_tail_274_ = lean_ctor_get(v_x_271_, 2);
v_isSharedCheck_297_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_297_ == 0)
{
v___x_276_ = v_x_271_;
v_isShared_277_ = v_isSharedCheck_297_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_tail_274_);
lean_inc(v_value_273_);
lean_inc(v_key_272_);
lean_dec(v_x_271_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_297_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; uint64_t v___x_281_; uint64_t v_fold_282_; uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_278_ = lean_array_get_size(v_x_270_);
v___x_279_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_key_272_);
v___x_280_ = 32ULL;
v___x_281_ = lean_uint64_shift_right(v___x_279_, v___x_280_);
v_fold_282_ = lean_uint64_xor(v___x_279_, v___x_281_);
v___x_283_ = 16ULL;
v___x_284_ = lean_uint64_shift_right(v_fold_282_, v___x_283_);
v___x_285_ = lean_uint64_xor(v_fold_282_, v___x_284_);
v___x_286_ = lean_uint64_to_usize(v___x_285_);
v___x_287_ = lean_usize_of_nat(v___x_278_);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_sub(v___x_287_, v___x_288_);
v___x_290_ = lean_usize_land(v___x_286_, v___x_289_);
v___x_291_ = lean_array_uget_borrowed(v_x_270_, v___x_290_);
lean_inc(v___x_291_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 2, v___x_291_);
v___x_293_ = v___x_276_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_key_272_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_value_273_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v___x_291_);
v___x_293_ = v_reuseFailAlloc_296_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = lean_array_uset(v_x_270_, v___x_290_, v___x_293_);
v_x_270_ = v___x_294_;
v_x_271_ = v_tail_274_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4___redArg(lean_object* v_i_298_, lean_object* v_source_299_, lean_object* v_target_300_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_array_get_size(v_source_299_);
v___x_302_ = lean_nat_dec_lt(v_i_298_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec_ref(v_source_299_);
lean_dec(v_i_298_);
return v_target_300_;
}
else
{
lean_object* v_es_303_; lean_object* v___x_304_; lean_object* v_source_305_; lean_object* v_target_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_es_303_ = lean_array_fget(v_source_299_, v_i_298_);
v___x_304_ = lean_box(0);
v_source_305_ = lean_array_fset(v_source_299_, v_i_298_, v___x_304_);
v_target_306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4_spec__6___redArg(v_target_300_, v_es_303_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_i_298_, v___x_307_);
lean_dec(v_i_298_);
v_i_298_ = v___x_308_;
v_source_299_ = v_source_305_;
v_target_300_ = v_target_306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2___redArg(lean_object* v_data_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_nbuckets_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_311_ = lean_array_get_size(v_data_310_);
v___x_312_ = lean_unsigned_to_nat(2u);
v_nbuckets_313_ = lean_nat_mul(v___x_311_, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_box(0);
v___x_316_ = lean_mk_array(v_nbuckets_313_, v___x_315_);
v___x_317_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4___redArg(v___x_314_, v_data_310_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg(lean_object* v_a_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
uint8_t v___x_320_; 
v___x_320_ = 0;
return v___x_320_;
}
else
{
lean_object* v_key_321_; lean_object* v_tail_322_; uint8_t v___x_323_; 
v_key_321_ = lean_ctor_get(v_x_319_, 0);
v_tail_322_ = lean_ctor_get(v_x_319_, 2);
v___x_323_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_321_, v_a_318_);
if (v___x_323_ == 0)
{
v_x_319_ = v_tail_322_;
goto _start;
}
else
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg___boxed(lean_object* v_a_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg(v_a_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec_ref(v_a_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(lean_object* v_m_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_size_332_; lean_object* v_buckets_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_376_; 
v_size_332_ = lean_ctor_get(v_m_329_, 0);
v_buckets_333_ = lean_ctor_get(v_m_329_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_m_329_);
if (v_isSharedCheck_376_ == 0)
{
v___x_335_ = v_m_329_;
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_buckets_333_);
lean_inc(v_size_332_);
lean_dec(v_m_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v_fold_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v_bkt_350_; uint8_t v___x_351_; 
v___x_337_ = lean_array_get_size(v_buckets_333_);
v___x_338_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_a_330_);
v___x_339_ = 32ULL;
v___x_340_ = lean_uint64_shift_right(v___x_338_, v___x_339_);
v_fold_341_ = lean_uint64_xor(v___x_338_, v___x_340_);
v___x_342_ = 16ULL;
v___x_343_ = lean_uint64_shift_right(v_fold_341_, v___x_342_);
v___x_344_ = lean_uint64_xor(v_fold_341_, v___x_343_);
v___x_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = lean_usize_of_nat(v___x_337_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v___x_346_, v___x_347_);
v___x_349_ = lean_usize_land(v___x_345_, v___x_348_);
v_bkt_350_ = lean_array_uget_borrowed(v_buckets_333_, v___x_349_);
v___x_351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg(v_a_330_, v_bkt_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v_size_x27_353_; lean_object* v___x_354_; lean_object* v_buckets_x27_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v_size_x27_353_ = lean_nat_add(v_size_332_, v___x_352_);
lean_dec(v_size_332_);
lean_inc(v_bkt_350_);
v___x_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_354_, 0, v_a_330_);
lean_ctor_set(v___x_354_, 1, v_b_331_);
lean_ctor_set(v___x_354_, 2, v_bkt_350_);
v_buckets_x27_355_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(4u);
v___x_357_ = lean_nat_mul(v_size_x27_353_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(3u);
v___x_359_ = lean_nat_div(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_array_get_size(v_buckets_x27_355_);
v___x_361_ = lean_nat_dec_le(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v_val_362_; lean_object* v___x_364_; 
v_val_362_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2___redArg(v_buckets_x27_355_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_val_362_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_364_ = v___x_335_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_val_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
lean_object* v___x_367_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_buckets_x27_355_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_367_ = v___x_335_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_buckets_x27_355_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v___x_369_; lean_object* v_buckets_x27_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_inc(v_bkt_350_);
v___x_369_ = lean_box(0);
v_buckets_x27_370_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_369_);
v___x_371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__3___redArg(v_a_330_, v_b_331_, v_bkt_350_);
v___x_372_ = lean_array_uset(v_buckets_x27_370_, v___x_349_, v___x_371_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_372_);
v___x_374_ = v___x_335_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_size_332_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__3(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_381_ = lean_unsigned_to_nat(61u);
v___x_382_ = lean_unsigned_to_nat(98u);
v___x_383_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__1));
v___x_384_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0));
v___x_385_ = l_mkPanicMessageWithDecl(v___x_384_, v___x_383_, v___x_382_, v___x_381_, v___x_380_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode(lean_object* v_declName_386_, lean_object* v_code_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
switch(lean_obj_tag(v_code_387_))
{
case 0:
{
lean_object* v_k_394_; 
v_k_394_ = lean_ctor_get(v_code_387_, 1);
lean_inc_ref(v_k_394_);
lean_dec_ref(v_code_387_);
v_code_387_ = v_k_394_;
goto _start;
}
case 2:
{
lean_object* v_decl_396_; lean_object* v_k_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_413_; 
v_decl_396_ = lean_ctor_get(v_code_387_, 0);
v_k_397_ = lean_ctor_get(v_code_387_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_code_387_);
if (v_isSharedCheck_413_ == 0)
{
v___x_399_ = v_code_387_;
v_isShared_400_ = v_isSharedCheck_413_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_k_397_);
lean_inc(v_decl_396_);
lean_dec(v_code_387_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_413_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v_fvarId_402_; lean_object* v_params_403_; lean_object* v_value_404_; lean_object* v___x_406_; 
v___x_401_ = lean_st_ref_take(v_a_388_);
v_fvarId_402_ = lean_ctor_get(v_decl_396_, 0);
lean_inc(v_fvarId_402_);
v_params_403_ = lean_ctor_get(v_decl_396_, 2);
lean_inc_ref(v_params_403_);
v_value_404_ = lean_ctor_get(v_decl_396_, 4);
lean_inc_ref(v_value_404_);
lean_dec_ref(v_decl_396_);
lean_inc(v_declName_386_);
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 1);
lean_ctor_set(v___x_399_, 1, v_fvarId_402_);
lean_ctor_set(v___x_399_, 0, v_declName_386_);
v___x_406_ = v___x_399_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_declName_386_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_fvarId_402_);
v___x_406_ = v_reuseFailAlloc_412_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParams(v_params_403_);
v___x_408_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(v___x_401_, v___x_406_, v___x_407_);
v___x_409_ = lean_st_ref_set(v_a_388_, v___x_408_);
lean_inc(v_a_392_);
lean_inc_ref(v_a_391_);
lean_inc(v_a_390_);
lean_inc_ref(v_a_389_);
lean_inc(v_a_388_);
lean_inc(v_declName_386_);
v___x_410_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode(v_declName_386_, v_value_404_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_dec_ref(v___x_410_);
v_code_387_ = v_k_397_;
goto _start;
}
else
{
lean_dec_ref(v_k_397_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_declName_386_);
return v___x_410_;
}
}
}
}
case 3:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v_code_387_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_declName_386_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
case 4:
{
lean_object* v_cases_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_438_; 
v_cases_416_ = lean_ctor_get(v_code_387_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_code_387_);
if (v_isSharedCheck_438_ == 0)
{
v___x_418_ = v_code_387_;
v_isShared_419_ = v_isSharedCheck_438_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_cases_416_);
lean_dec(v_code_387_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_438_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_alts_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_alts_420_ = lean_ctor_get(v_cases_416_, 3);
lean_inc_ref(v_alts_420_);
lean_dec_ref(v_cases_416_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_array_get_size(v_alts_420_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_nat_dec_lt(v___x_421_, v___x_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_426_; 
lean_dec_ref(v_alts_420_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_declName_386_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 0);
lean_ctor_set(v___x_418_, 0, v___x_423_);
v___x_426_ = v___x_418_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_423_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
else
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_le(v___x_422_, v___x_422_);
if (v___x_428_ == 0)
{
if (v___x_424_ == 0)
{
lean_object* v___x_430_; 
lean_dec_ref(v_alts_420_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_declName_386_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 0);
lean_ctor_set(v___x_418_, 0, v___x_423_);
v___x_430_ = v___x_418_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_423_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
size_t v___x_432_; size_t v___x_433_; lean_object* v___x_434_; 
lean_del_object(v___x_418_);
v___x_432_ = ((size_t)0ULL);
v___x_433_ = lean_usize_of_nat(v___x_422_);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__2(v_declName_386_, v_alts_420_, v___x_432_, v___x_433_, v___x_423_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec_ref(v_alts_420_);
return v___x_434_;
}
}
else
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
lean_del_object(v___x_418_);
v___x_435_ = ((size_t)0ULL);
v___x_436_ = lean_usize_of_nat(v___x_422_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__2(v_declName_386_, v_alts_420_, v___x_435_, v___x_436_, v___x_423_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec_ref(v_alts_420_);
return v___x_437_;
}
}
}
}
case 5:
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_declName_386_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_code_387_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_code_387_, 0);
lean_dec(v_unused_447_);
v___x_440_ = v_code_387_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_code_387_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 0);
lean_ctor_set(v___x_440_, 0, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
case 6:
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_declName_386_);
v_isSharedCheck_455_ = !lean_is_exclusive(v_code_387_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v_code_387_, 0);
lean_dec(v_unused_456_);
v___x_449_ = v_code_387_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_code_387_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_box(0);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 0);
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
case 8:
{
lean_object* v_k_457_; 
v_k_457_ = lean_ctor_get(v_code_387_, 3);
lean_inc_ref(v_k_457_);
lean_dec_ref(v_code_387_);
v_code_387_ = v_k_457_;
goto _start;
}
case 9:
{
lean_object* v_k_459_; 
v_k_459_ = lean_ctor_get(v_code_387_, 5);
lean_inc_ref(v_k_459_);
lean_dec_ref(v_code_387_);
v_code_387_ = v_k_459_;
goto _start;
}
default: 
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec_ref(v_code_387_);
lean_dec(v_declName_386_);
v___x_461_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__3, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__3_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__3);
v___x_462_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3(v___x_461_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___boxed(lean_object* v_declName_463_, lean_object* v_code_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode(v_declName_463_, v_code_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__2(lean_object* v_declName_472_, lean_object* v_as_473_, size_t v_i_474_, size_t v_stop_475_, lean_object* v_b_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_eq(v_i_474_, v_stop_475_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_array_uget_borrowed(v_as_473_, v_i_474_);
lean_inc(v_declName_472_);
v___x_485_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___boxed), 8, 1);
lean_closure_set(v___x_485_, 0, v_declName_472_);
lean_inc(v___y_481_);
lean_inc_ref(v___y_480_);
lean_inc(v___y_479_);
lean_inc_ref(v___y_478_);
lean_inc(v___y_477_);
lean_inc(v___x_484_);
v___x_486_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__0___redArg(v___x_484_, v___x_485_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; size_t v___x_488_; size_t v___x_489_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_add(v_i_474_, v___x_488_);
v_i_474_ = v___x_489_;
v_b_476_ = v_a_487_;
goto _start;
}
else
{
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec(v_declName_472_);
return v___x_486_;
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec(v_declName_472_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_b_476_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__2___boxed(lean_object* v_declName_492_, lean_object* v_as_493_, lean_object* v_i_494_, lean_object* v_stop_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_i_boxed_503_; size_t v_stop_boxed_504_; lean_object* v_res_505_; 
v_i_boxed_503_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_stop_boxed_504_ = lean_unbox_usize(v_stop_495_);
lean_dec(v_stop_495_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__2(v_declName_492_, v_as_493_, v_i_boxed_503_, v_stop_boxed_504_, v_b_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec_ref(v_as_493_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1(lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_a_508_, lean_object* v_b_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(v_m_507_, v_a_508_, v_b_509_);
return v___x_510_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1(lean_object* v_00_u03b2_511_, lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg(v_a_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___boxed(lean_object* v_00_u03b2_515_, lean_object* v_a_516_, lean_object* v_x_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1(v_00_u03b2_515_, v_a_516_, v_x_517_);
lean_dec(v_x_517_);
lean_dec_ref(v_a_516_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2(lean_object* v_00_u03b2_520_, lean_object* v_data_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2___redArg(v_data_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__3(lean_object* v_00_u03b2_523_, lean_object* v_a_524_, lean_object* v_b_525_, lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__3___redArg(v_a_524_, v_b_525_, v_x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_528_, lean_object* v_i_529_, lean_object* v_source_530_, lean_object* v_target_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4___redArg(v_i_529_, v_source_530_, v_target_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__2_spec__4_spec__6___redArg(v_x_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported_spec__0(size_t v_sz_537_, size_t v_i_538_, lean_object* v_bs_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_usize_dec_lt(v_i_538_, v_sz_537_);
if (v___x_540_ == 0)
{
return v_bs_539_;
}
else
{
lean_object* v_v_541_; lean_object* v_fvarId_542_; lean_object* v_binderName_543_; lean_object* v_type_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_558_; 
v_v_541_ = lean_array_uget(v_bs_539_, v_i_538_);
v_fvarId_542_ = lean_ctor_get(v_v_541_, 0);
v_binderName_543_ = lean_ctor_get(v_v_541_, 1);
v_type_544_ = lean_ctor_get(v_v_541_, 2);
v_isSharedCheck_558_ = !lean_is_exclusive(v_v_541_);
if (v_isSharedCheck_558_ == 0)
{
v___x_546_ = v_v_541_;
v_isShared_547_ = v_isSharedCheck_558_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_type_544_);
lean_inc(v_binderName_543_);
lean_inc(v_fvarId_542_);
lean_dec(v_v_541_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_558_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v_bs_x27_549_; uint8_t v___x_550_; lean_object* v___x_552_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v_bs_x27_549_ = lean_array_uset(v_bs_539_, v_i_538_, v___x_548_);
v___x_550_ = 0;
if (v_isShared_547_ == 0)
{
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_fvarId_542_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_binderName_543_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_type_544_);
v___x_552_ = v_reuseFailAlloc_557_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*3, v___x_550_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_538_, v___x_553_);
v___x_555_ = lean_array_uset(v_bs_x27_549_, v_i_538_, v___x_552_);
v_i_538_ = v___x_554_;
v_bs_539_ = v___x_555_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported_spec__0___boxed(lean_object* v_sz_559_, lean_object* v_i_560_, lean_object* v_bs_561_){
_start:
{
size_t v_sz_boxed_562_; size_t v_i_boxed_563_; lean_object* v_res_564_; 
v_sz_boxed_562_ = lean_unbox_usize(v_sz_559_);
lean_dec(v_sz_559_);
v_i_boxed_563_ = lean_unbox_usize(v_i_560_);
lean_dec(v_i_560_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported_spec__0(v_sz_boxed_562_, v_i_boxed_563_, v_bs_561_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported(uint8_t v_exported_565_, lean_object* v_ps_566_){
_start:
{
if (v_exported_565_ == 0)
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParams(v_ps_566_);
return v___x_567_;
}
else
{
size_t v_sz_568_; size_t v___x_569_; lean_object* v___x_570_; 
v_sz_568_ = lean_array_size(v_ps_566_);
v___x_569_ = ((size_t)0ULL);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported_spec__0(v_sz_568_, v___x_569_, v_ps_566_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported___boxed(lean_object* v_exported_571_, lean_object* v_ps_572_){
_start:
{
uint8_t v_exported_boxed_573_; lean_object* v_res_574_; 
v_exported_boxed_573_ = lean_unbox(v_exported_571_);
v_res_574_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported(v_exported_boxed_573_, v_ps_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(lean_object* v_as_575_, size_t v_i_576_, size_t v_stop_577_, lean_object* v_b_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_a_586_; uint8_t v___x_590_; 
v___x_590_ = lean_usize_dec_eq(v_i_576_, v_stop_577_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v_value_592_; 
v___x_591_ = lean_array_uget_borrowed(v_as_575_, v_i_576_);
v_value_592_ = lean_ctor_get(v___x_591_, 1);
lean_inc_ref(v_value_592_);
if (lean_obj_tag(v_value_592_) == 0)
{
lean_object* v_toSignature_593_; lean_object* v_code_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_612_; 
v_toSignature_593_ = lean_ctor_get(v___x_591_, 0);
v_code_594_ = lean_ctor_get(v_value_592_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v_value_592_);
if (v_isSharedCheck_612_ == 0)
{
v___x_596_ = v_value_592_;
v_isShared_597_ = v_isSharedCheck_612_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_code_594_);
lean_dec(v_value_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_612_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_env_600_; lean_object* v_name_601_; lean_object* v_params_602_; uint8_t v___x_603_; lean_object* v___x_605_; 
v___x_598_ = lean_st_ref_get(v___y_583_);
v___x_599_ = lean_st_ref_take(v___y_579_);
v_env_600_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_env_600_);
lean_dec(v___x_598_);
v_name_601_ = lean_ctor_get(v_toSignature_593_, 0);
v_params_602_ = lean_ctor_get(v_toSignature_593_, 3);
lean_inc(v_name_601_);
v___x_603_ = l_Lean_isExport(v_env_600_, v_name_601_);
lean_inc(v_name_601_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v_name_601_);
v___x_605_ = v___x_596_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_name_601_);
v___x_605_ = v_reuseFailAlloc_611_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_inc_ref(v_params_602_);
v___x_606_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported(v___x_603_, v_params_602_);
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(v___x_599_, v___x_605_, v___x_606_);
v___x_608_ = lean_st_ref_set(v___y_579_, v___x_607_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
lean_inc(v___y_579_);
lean_inc(v_name_601_);
v___x_609_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode(v_name_601_, v_code_594_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref(v___x_609_);
v_a_586_ = v_a_610_;
goto v___jp_585_;
}
else
{
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_613_; 
lean_dec_ref(v_value_592_);
v___x_613_ = lean_box(0);
v_a_586_ = v___x_613_;
goto v___jp_585_;
}
}
else
{
lean_object* v___x_614_; 
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_b_578_);
return v___x_614_;
}
v___jp_585_:
{
size_t v___x_587_; size_t v___x_588_; 
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_576_, v___x_587_);
v_i_576_ = v___x_588_;
v_b_578_ = v_a_586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0___boxed(lean_object* v_as_615_, lean_object* v_i_616_, lean_object* v_stop_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
size_t v_i_boxed_625_; size_t v_stop_boxed_626_; lean_object* v_res_627_; 
v_i_boxed_625_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_stop_boxed_626_ = lean_unbox_usize(v_stop_617_);
lean_dec(v_stop_617_);
v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(v_as_615_, v_i_boxed_625_, v_stop_boxed_626_, v_b_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec_ref(v_as_615_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go(lean_object* v_decls_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_array_get_size(v_decls_628_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_nat_dec_lt(v___x_635_, v___x_636_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
return v___x_639_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = lean_nat_dec_le(v___x_636_, v___x_636_);
if (v___x_640_ == 0)
{
if (v___x_638_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_637_);
return v___x_641_;
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_636_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(v_decls_628_, v___x_642_, v___x_643_, v___x_637_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
return v___x_644_;
}
}
else
{
size_t v___x_645_; size_t v___x_646_; lean_object* v___x_647_; 
v___x_645_ = ((size_t)0ULL);
v___x_646_ = lean_usize_of_nat(v___x_636_);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(v_decls_628_, v___x_645_, v___x_646_, v___x_637_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go___boxed(lean_object* v_decls_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go(v_decls_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec_ref(v_decls_648_);
return v_res_655_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = lean_unsigned_to_nat(16u);
v___x_658_ = lean_mk_array(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap(lean_object* v_decls_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1);
v___x_669_ = lean_st_mk_ref(v___x_668_);
lean_inc(v___x_669_);
v___x_670_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go(v_decls_662_, v___x_669_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_679_);
v___x_672_ = v___x_670_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_dec(v___x_670_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_st_ref_get(v___x_669_);
lean_dec(v___x_669_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v___x_669_);
v_a_680_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___boxed(lean_object* v_decls_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap(v_decls_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec_ref(v_decls_688_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(lean_object* v_a_695_, lean_object* v_b_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_memoizedLeft_699_; 
v_memoizedLeft_699_ = lean_ctor_get(v_a_695_, 1);
lean_inc(v_memoizedLeft_699_);
if (lean_obj_tag(v_memoizedLeft_699_) == 0)
{
lean_object* v_left_700_; lean_object* v_right_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_725_; 
v_left_700_ = lean_ctor_get(v_a_695_, 0);
v_right_701_ = lean_ctor_get(v_a_695_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_a_695_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_a_695_, 1);
lean_dec(v_unused_726_);
v___x_703_ = v_a_695_;
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_right_701_);
lean_inc(v_left_700_);
lean_dec(v_a_695_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_array_705_; lean_object* v_pos_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_724_; 
v_array_705_ = lean_ctor_get(v_left_700_, 0);
v_pos_706_ = lean_ctor_get(v_left_700_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_left_700_);
if (v_isSharedCheck_724_ == 0)
{
v___x_708_ = v_left_700_;
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_pos_706_);
lean_inc(v_array_705_);
lean_dec(v_left_700_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_array_get_size(v_array_705_);
v___x_711_ = lean_nat_dec_lt(v_pos_706_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_del_object(v___x_708_);
lean_dec(v_pos_706_);
lean_dec_ref(v_array_705_);
lean_del_object(v___x_703_);
lean_dec(v_right_701_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_b_696_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_nat_add(v_pos_706_, v___x_713_);
lean_inc_ref(v_array_705_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_714_);
v___x_716_ = v___x_708_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_array_705_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_723_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_717_ = lean_array_fget(v_array_705_, v_pos_706_);
lean_dec(v_pos_706_);
lean_dec_ref(v_array_705_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_718_);
lean_ctor_set(v___x_703_, 0, v___x_716_);
v___x_720_ = v___x_703_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_right_701_);
v___x_720_ = v_reuseFailAlloc_722_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_a_695_ = v___x_720_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_right_727_; lean_object* v_left_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_772_; 
v_right_727_ = lean_ctor_get(v_a_695_, 2);
v_left_728_ = lean_ctor_get(v_a_695_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_a_695_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v_a_695_, 1);
lean_dec(v_unused_773_);
v___x_730_ = v_a_695_;
v_isShared_731_ = v_isSharedCheck_772_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_right_727_);
lean_inc(v_left_728_);
lean_dec(v_a_695_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_772_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_val_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_771_; 
v_val_732_ = lean_ctor_get(v_memoizedLeft_699_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_memoizedLeft_699_);
if (v_isSharedCheck_771_ == 0)
{
v___x_734_ = v_memoizedLeft_699_;
v_isShared_735_ = v_isSharedCheck_771_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_val_732_);
lean_dec(v_memoizedLeft_699_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_771_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_array_736_; lean_object* v_pos_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_770_; 
v_array_736_ = lean_ctor_get(v_right_727_, 0);
v_pos_737_ = lean_ctor_get(v_right_727_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_right_727_);
if (v_isSharedCheck_770_ == 0)
{
v___x_739_ = v_right_727_;
v_isShared_740_ = v_isSharedCheck_770_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_pos_737_);
lean_inc(v_array_736_);
lean_dec(v_right_727_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_770_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_array_736_);
v___x_742_ = lean_nat_dec_lt(v_pos_737_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_744_; 
lean_del_object(v___x_739_);
lean_dec(v_pos_737_);
lean_dec_ref(v_array_736_);
lean_dec(v_val_732_);
lean_del_object(v___x_730_);
lean_dec(v_left_728_);
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 0);
lean_ctor_set(v___x_734_, 0, v_b_696_);
v___x_744_ = v___x_734_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_b_696_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v___x_746_; uint8_t v_borrow_747_; uint8_t v___x_748_; lean_object* v___x_749_; 
lean_del_object(v___x_734_);
v___x_746_ = lean_array_fget_borrowed(v_array_736_, v_pos_737_);
v_borrow_747_ = lean_ctor_get_uint8(v___x_746_, sizeof(void*)*3);
v___x_748_ = 1;
v___x_749_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_748_, v_val_732_, v_borrow_747_, v___y_697_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref(v___x_749_);
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_add(v_pos_737_, v___x_751_);
lean_dec(v_pos_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_752_);
v___x_754_ = v___x_739_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_array_736_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_761_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_box(0);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 2, v___x_754_);
lean_ctor_set(v___x_730_, 1, v___x_755_);
v___x_757_ = v___x_730_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_left_728_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v___x_754_);
v___x_757_ = v_reuseFailAlloc_760_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_array_push(v_b_696_, v_a_750_);
v_a_695_ = v___x_757_;
v_b_696_ = v___x_758_;
goto _start;
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_del_object(v___x_739_);
lean_dec(v_pos_737_);
lean_dec_ref(v_array_736_);
lean_del_object(v___x_730_);
lean_dec(v_left_728_);
lean_dec_ref(v_b_696_);
v_a_762_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_749_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_749_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg___boxed(lean_object* v_a_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(v_a_774_, v_b_775_, v___y_776_);
lean_dec(v___y_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(lean_object* v_ps_781_, lean_object* v_borrows_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_ps_781_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_borrows_782_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_792_, 0, v___x_789_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
lean_ctor_set(v___x_792_, 2, v___x_790_);
v___x_793_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___closed__0));
v___x_794_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(v___x_792_, v___x_793_, v_a_784_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___boxed(lean_object* v_ps_795_, lean_object* v_borrows_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(v_ps_795_, v_borrows_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0(lean_object* v_inst_803_, lean_object* v_R_804_, lean_object* v_a_805_, lean_object* v_b_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(v_a_805_, v_b_806_, v___y_808_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___boxed(lean_object* v_inst_813_, lean_object* v_R_814_, lean_object* v_a_815_, lean_object* v_b_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0(v_inst_813_, v_R_814_, v_a_815_, v_b_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(lean_object* v_alt_823_, lean_object* v_f_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___y_831_; 
switch(lean_obj_tag(v_alt_823_))
{
case 0:
{
lean_object* v_code_850_; 
v_code_850_ = lean_ctor_get(v_alt_823_, 2);
lean_inc_ref(v_code_850_);
v___y_831_ = v_code_850_;
goto v___jp_830_;
}
case 1:
{
lean_object* v_code_851_; 
v_code_851_ = lean_ctor_get(v_alt_823_, 1);
lean_inc_ref(v_code_851_);
v___y_831_ = v_code_851_;
goto v___jp_830_;
}
default: 
{
lean_object* v_code_852_; 
v_code_852_ = lean_ctor_get(v_alt_823_, 0);
lean_inc_ref(v_code_852_);
v___y_831_ = v_code_852_;
goto v___jp_830_;
}
}
v___jp_830_:
{
lean_object* v___x_832_; 
v___x_832_ = lean_apply_6(v_f_824_, v___y_831_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, lean_box(0));
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_823_, v_a_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v_alt_823_);
v_a_842_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_832_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_832_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg___boxed(lean_object* v_alt_853_, lean_object* v_f_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(v_alt_853_, v_f_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1(uint8_t v_pu_861_, lean_object* v_alt_862_, lean_object* v_f_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(v_alt_862_, v_f_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___boxed(lean_object* v_pu_870_, lean_object* v_alt_871_, lean_object* v_f_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v_pu_boxed_878_; lean_object* v_res_879_; 
v_pu_boxed_878_ = lean_unbox(v_pu_870_);
v_res_879_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1(v_pu_boxed_878_, v_alt_871_, v_f_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
return v_res_879_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0(void){
_start:
{
uint8_t v___x_880_; lean_object* v___x_881_; 
v___x_880_ = 1;
v___x_881_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3(lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_toApplicative_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_923_; 
v___x_888_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_889_ = l_ReaderT_instMonad___redArg(v___x_888_);
v_toApplicative_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_889_, 1);
lean_dec(v_unused_924_);
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_923_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_toApplicative_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_923_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_toFunctor_894_; lean_object* v_toSeq_895_; lean_object* v_toSeqLeft_896_; lean_object* v_toSeqRight_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_921_; 
v_toFunctor_894_ = lean_ctor_get(v_toApplicative_890_, 0);
v_toSeq_895_ = lean_ctor_get(v_toApplicative_890_, 2);
v_toSeqLeft_896_ = lean_ctor_get(v_toApplicative_890_, 3);
v_toSeqRight_897_ = lean_ctor_get(v_toApplicative_890_, 4);
v_isSharedCheck_921_ = !lean_is_exclusive(v_toApplicative_890_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_toApplicative_890_, 1);
lean_dec(v_unused_922_);
v___x_899_ = v_toApplicative_890_;
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_toSeqRight_897_);
lean_inc(v_toSeqLeft_896_);
lean_inc(v_toSeq_895_);
lean_inc(v_toFunctor_894_);
lean_dec(v_toApplicative_890_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___x_910_; 
v___f_901_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_902_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_894_);
v___f_903_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_903_, 0, v_toFunctor_894_);
v___f_904_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_904_, 0, v_toFunctor_894_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___f_903_);
lean_ctor_set(v___x_905_, 1, v___f_904_);
v___f_906_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_906_, 0, v_toSeqRight_897_);
v___f_907_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_907_, 0, v_toSeqLeft_896_);
v___f_908_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_908_, 0, v_toSeq_895_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 4, v___f_906_);
lean_ctor_set(v___x_899_, 3, v___f_907_);
lean_ctor_set(v___x_899_, 2, v___f_908_);
lean_ctor_set(v___x_899_, 1, v___f_901_);
lean_ctor_set(v___x_899_, 0, v___x_905_);
v___x_910_ = v___x_899_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___f_901_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v___f_908_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v___f_907_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v___f_906_);
v___x_910_ = v_reuseFailAlloc_920_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___f_902_);
lean_ctor_set(v___x_892_, 0, v___x_910_);
v___x_912_ = v___x_892_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___f_902_);
v___x_912_ = v_reuseFailAlloc_919_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_3694__overap_917_; lean_object* v___x_918_; 
v___x_913_ = l_ReaderT_instMonad___redArg(v___x_912_);
v___x_914_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0);
v___x_915_ = l_instInhabitedOfMonad___redArg(v___x_913_, v___x_914_);
v___f_916_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_916_, 0, v___x_915_);
v___x_3694__overap_917_ = lean_panic_fn(v___f_916_, v_msg_882_);
v___x_918_ = lean_apply_5(v___x_3694__overap_917_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___boxed(lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3(v_msg_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v_res_931_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_935_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__2));
v___x_936_ = lean_unsigned_to_nat(11u);
v___x_937_ = lean_unsigned_to_nat(163u);
v___x_938_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__1));
v___x_939_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__0));
v___x_940_ = l_mkPanicMessageWithDecl(v___x_939_, v___x_938_, v___x_937_, v___x_936_, v___x_935_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(lean_object* v_inst_941_, lean_object* v_a_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3);
v___x_945_ = lean_panic_fn(v_inst_941_, v___x_944_);
return v___x_945_;
}
else
{
lean_object* v_key_946_; lean_object* v_value_947_; lean_object* v_tail_948_; uint8_t v___x_949_; 
v_key_946_ = lean_ctor_get(v_x_943_, 0);
v_value_947_ = lean_ctor_get(v_x_943_, 1);
v_tail_948_ = lean_ctor_get(v_x_943_, 2);
v___x_949_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_946_, v_a_942_);
if (v___x_949_ == 0)
{
v_x_943_ = v_tail_948_;
goto _start;
}
else
{
lean_dec(v_inst_941_);
lean_inc(v_value_947_);
return v_value_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___boxed(lean_object* v_inst_951_, lean_object* v_a_952_, lean_object* v_x_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(v_inst_951_, v_a_952_, v_x_953_);
lean_dec(v_x_953_);
lean_dec_ref(v_a_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(lean_object* v_inst_955_, lean_object* v_m_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_buckets_958_; lean_object* v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v_fold_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_buckets_958_ = lean_ctor_get(v_m_956_, 1);
v___x_959_ = lean_array_get_size(v_buckets_958_);
v___x_960_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_a_957_);
v___x_961_ = 32ULL;
v___x_962_ = lean_uint64_shift_right(v___x_960_, v___x_961_);
v_fold_963_ = lean_uint64_xor(v___x_960_, v___x_962_);
v___x_964_ = 16ULL;
v___x_965_ = lean_uint64_shift_right(v_fold_963_, v___x_964_);
v___x_966_ = lean_uint64_xor(v_fold_963_, v___x_965_);
v___x_967_ = lean_uint64_to_usize(v___x_966_);
v___x_968_ = lean_usize_of_nat(v___x_959_);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_sub(v___x_968_, v___x_969_);
v___x_971_ = lean_usize_land(v___x_967_, v___x_970_);
v___x_972_ = lean_array_uget_borrowed(v_buckets_958_, v___x_971_);
v___x_973_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(v_inst_955_, v_a_957_, v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg___boxed(lean_object* v_inst_974_, lean_object* v_m_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v_inst_974_, v_m_975_, v_a_976_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_m_975_);
return v_res_977_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0(void){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Array_instInhabited(lean_box(0));
return v___x_978_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_981_ = lean_unsigned_to_nat(61u);
v___x_982_ = lean_unsigned_to_nat(128u);
v___x_983_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__1));
v___x_984_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0));
v___x_985_ = l_mkPanicMessageWithDecl(v___x_984_, v___x_983_, v___x_982_, v___x_981_, v___x_980_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(lean_object* v_map_986_, lean_object* v_declName_987_, lean_object* v_code_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
switch(lean_obj_tag(v_code_988_))
{
case 0:
{
lean_object* v_decl_994_; lean_object* v_k_995_; lean_object* v___x_996_; 
v_decl_994_ = lean_ctor_get(v_code_988_, 0);
v_k_995_ = lean_ctor_get(v_code_988_, 1);
lean_inc_ref(v_k_995_);
v___x_996_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_986_, v_declName_987_, v_k_995_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1019_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
size_t v___x_1001_; size_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = lean_ptr_addr(v_k_995_);
v___x_1002_ = lean_ptr_addr(v_a_997_);
v___x_1003_ = lean_usize_dec_eq(v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1013_; 
lean_inc_ref(v_decl_994_);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; 
v_unused_1014_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1015_);
v___x_1005_ = v_code_988_;
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_code_988_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_a_997_);
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_decl_994_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_a_997_);
v___x_1008_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1008_);
v___x_1010_ = v___x_999_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v___x_1017_; 
lean_dec(v_a_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_code_988_);
v___x_1017_ = v___x_999_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_code_988_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_dec_ref(v_code_988_);
return v___x_996_;
}
}
case 2:
{
lean_object* v_decl_1020_; lean_object* v_k_1021_; lean_object* v_fvarId_1022_; lean_object* v_params_1023_; lean_object* v_type_1024_; lean_object* v_value_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_decl_1020_ = lean_ctor_get(v_code_988_, 0);
v_k_1021_ = lean_ctor_get(v_code_988_, 1);
v_fvarId_1022_ = lean_ctor_get(v_decl_1020_, 0);
v_params_1023_ = lean_ctor_get(v_decl_1020_, 2);
v_type_1024_ = lean_ctor_get(v_decl_1020_, 3);
v_value_1025_ = lean_ctor_get(v_decl_1020_, 4);
v___x_1026_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0);
lean_inc(v_fvarId_1022_);
lean_inc(v_declName_987_);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_declName_987_);
lean_ctor_set(v___x_1027_, 1, v_fvarId_1022_);
v___x_1028_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v___x_1026_, v_map_986_, v___x_1027_);
lean_dec_ref(v___x_1027_);
lean_inc_ref(v_params_1023_);
v___x_1029_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(v_params_1023_, v___x_1028_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
lean_inc(v_a_992_);
lean_inc_ref(v_a_991_);
lean_inc(v_a_990_);
lean_inc_ref(v_a_989_);
lean_inc_ref(v_value_1025_);
lean_inc(v_declName_987_);
lean_inc_ref(v_map_986_);
v___x_1031_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_986_, v_declName_987_, v_value_1025_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = 1;
lean_inc_ref(v_type_1024_);
lean_inc_ref(v_decl_1020_);
v___x_1034_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1033_, v_decl_1020_, v_type_1024_, v_a_1030_, v_a_1032_, v_a_990_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
lean_inc_ref(v_k_1021_);
v___x_1036_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_986_, v_declName_987_, v_k_1021_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1064_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1064_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1064_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
uint8_t v___y_1042_; size_t v___x_1058_; size_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_ptr_addr(v_k_1021_);
v___x_1059_ = lean_ptr_addr(v_a_1037_);
v___x_1060_ = lean_usize_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
v___y_1042_ = v___x_1060_;
goto v___jp_1041_;
}
else
{
size_t v___x_1061_; size_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_ptr_addr(v_decl_1020_);
v___x_1062_ = lean_ptr_addr(v_a_1035_);
v___x_1063_ = lean_usize_dec_eq(v___x_1061_, v___x_1062_);
v___y_1042_ = v___x_1063_;
goto v___jp_1041_;
}
v___jp_1041_:
{
if (v___y_1042_ == 0)
{
lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1052_; 
v_isSharedCheck_1052_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; lean_object* v_unused_1054_; 
v_unused_1053_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1054_);
v___x_1044_ = v_code_988_;
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
else
{
lean_dec(v_code_988_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v_a_1037_);
lean_ctor_set(v___x_1044_, 0, v_a_1035_);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1035_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_a_1037_);
v___x_1047_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1047_);
v___x_1049_ = v___x_1039_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v_a_1037_);
lean_dec(v_a_1035_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_code_988_);
v___x_1056_ = v___x_1039_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_code_988_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
else
{
lean_dec(v_a_1035_);
lean_dec_ref(v_code_988_);
return v___x_1036_;
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_code_988_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_declName_987_);
lean_dec_ref(v_map_986_);
v_a_1065_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1034_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1034_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_dec(v_a_1030_);
lean_dec_ref(v_code_988_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_declName_987_);
lean_dec_ref(v_map_986_);
return v___x_1031_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_code_988_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_declName_987_);
lean_dec_ref(v_map_986_);
v_a_1073_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1029_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1029_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
case 3:
{
lean_object* v___x_1081_; 
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_declName_987_);
lean_dec_ref(v_map_986_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_code_988_);
return v___x_1081_;
}
case 4:
{
lean_object* v_cases_1082_; lean_object* v_typeName_1083_; lean_object* v_resultType_1084_; lean_object* v_discr_1085_; lean_object* v_alts_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1125_; 
v_cases_1082_ = lean_ctor_get(v_code_988_, 0);
lean_inc_ref(v_cases_1082_);
v_typeName_1083_ = lean_ctor_get(v_cases_1082_, 0);
v_resultType_1084_ = lean_ctor_get(v_cases_1082_, 1);
v_discr_1085_ = lean_ctor_get(v_cases_1082_, 2);
v_alts_1086_ = lean_ctor_get(v_cases_1082_, 3);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_cases_1082_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1088_ = v_cases_1082_;
v_isShared_1089_ = v_isSharedCheck_1125_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_alts_1086_);
lean_inc(v_discr_1085_);
lean_inc(v_resultType_1084_);
lean_inc(v_typeName_1083_);
lean_dec(v_cases_1082_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1125_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1086_);
v___x_1091_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2(v_map_986_, v_declName_987_, v___x_1090_, v_alts_1086_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1116_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1116_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1116_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
size_t v___x_1096_; size_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_ptr_addr(v_alts_1086_);
lean_dec_ref(v_alts_1086_);
v___x_1097_ = lean_ptr_addr(v_a_1092_);
v___x_1098_ = lean_usize_dec_eq(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1111_; 
v_isSharedCheck_1111_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1112_);
v___x_1100_ = v_code_988_;
v_isShared_1101_ = v_isSharedCheck_1111_;
goto v_resetjp_1099_;
}
else
{
lean_dec(v_code_988_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1111_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 3, v_a_1092_);
v___x_1103_ = v___x_1088_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_typeName_1083_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_resultType_1084_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_discr_1085_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_a_1092_);
v___x_1103_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1103_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1105_);
v___x_1107_ = v___x_1094_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
else
{
lean_object* v___x_1114_; 
lean_dec(v_a_1092_);
lean_del_object(v___x_1088_);
lean_dec(v_discr_1085_);
lean_dec_ref(v_resultType_1084_);
lean_dec(v_typeName_1083_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_code_988_);
v___x_1114_ = v___x_1094_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_code_988_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1088_);
lean_dec_ref(v_alts_1086_);
lean_dec(v_discr_1085_);
lean_dec_ref(v_resultType_1084_);
lean_dec(v_typeName_1083_);
lean_dec_ref(v_code_988_);
v_a_1117_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1091_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1091_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
case 5:
{
lean_object* v___x_1126_; 
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_declName_987_);
lean_dec_ref(v_map_986_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_code_988_);
return v___x_1126_;
}
case 6:
{
lean_object* v___x_1127_; 
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_declName_987_);
lean_dec_ref(v_map_986_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_code_988_);
return v___x_1127_;
}
case 8:
{
lean_object* v_fvarId_1128_; lean_object* v_i_1129_; lean_object* v_y_1130_; lean_object* v_k_1131_; lean_object* v___x_1132_; 
v_fvarId_1128_ = lean_ctor_get(v_code_988_, 0);
v_i_1129_ = lean_ctor_get(v_code_988_, 1);
v_y_1130_ = lean_ctor_get(v_code_988_, 2);
v_k_1131_ = lean_ctor_get(v_code_988_, 3);
lean_inc_ref(v_k_1131_);
v___x_1132_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_986_, v_declName_987_, v_k_1131_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1157_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1157_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1157_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
size_t v___x_1137_; size_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = lean_ptr_addr(v_k_1131_);
v___x_1138_ = lean_ptr_addr(v_a_1133_);
v___x_1139_ = lean_usize_dec_eq(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1149_; 
lean_inc(v_y_1130_);
lean_inc(v_i_1129_);
lean_inc(v_fvarId_1128_);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; lean_object* v_unused_1153_; 
v_unused_1150_ = lean_ctor_get(v_code_988_, 3);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_code_988_, 2);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1153_);
v___x_1141_ = v_code_988_;
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_code_988_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 3, v_a_1133_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fvarId_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_i_1129_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_y_1130_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_a_1133_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1144_);
v___x_1146_ = v___x_1135_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec(v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_code_988_);
v___x_1155_ = v___x_1135_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_code_988_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_dec_ref(v_code_988_);
return v___x_1132_;
}
}
case 9:
{
lean_object* v_fvarId_1158_; lean_object* v_i_1159_; lean_object* v_offset_1160_; lean_object* v_y_1161_; lean_object* v_ty_1162_; lean_object* v_k_1163_; lean_object* v___x_1164_; 
v_fvarId_1158_ = lean_ctor_get(v_code_988_, 0);
v_i_1159_ = lean_ctor_get(v_code_988_, 1);
v_offset_1160_ = lean_ctor_get(v_code_988_, 2);
v_y_1161_ = lean_ctor_get(v_code_988_, 3);
v_ty_1162_ = lean_ctor_get(v_code_988_, 4);
v_k_1163_ = lean_ctor_get(v_code_988_, 5);
lean_inc_ref(v_k_1163_);
v___x_1164_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_986_, v_declName_987_, v_k_1163_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1191_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1191_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1191_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
size_t v___x_1169_; size_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = lean_ptr_addr(v_k_1163_);
v___x_1170_ = lean_ptr_addr(v_a_1165_);
v___x_1171_ = lean_usize_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1181_; 
lean_inc_ref(v_ty_1162_);
lean_inc(v_y_1161_);
lean_inc(v_offset_1160_);
lean_inc(v_i_1159_);
lean_inc(v_fvarId_1158_);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_code_988_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; 
v_unused_1182_ = lean_ctor_get(v_code_988_, 5);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_code_988_, 4);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_code_988_, 3);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_code_988_, 2);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_code_988_, 1);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_code_988_, 0);
lean_dec(v_unused_1187_);
v___x_1173_ = v_code_988_;
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
else
{
lean_dec(v_code_988_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 5, v_a_1165_);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_fvarId_1158_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_i_1159_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_offset_1160_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_y_1161_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_ty_1162_);
lean_ctor_set(v_reuseFailAlloc_1180_, 5, v_a_1165_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1176_);
v___x_1178_ = v___x_1167_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1189_; 
lean_dec(v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v_code_988_);
v___x_1189_ = v___x_1167_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_code_988_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_dec_ref(v_code_988_);
return v___x_1164_;
}
}
default: 
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_code_988_);
lean_dec(v_declName_987_);
lean_dec_ref(v_map_986_);
v___x_1192_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2);
v___x_1193_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3(v___x_1192_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___boxed(lean_object* v_map_1194_, lean_object* v_declName_1195_, lean_object* v_code_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_1194_, v_declName_1195_, v_code_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2(lean_object* v_map_1203_, lean_object* v_declName_1204_, lean_object* v_i_1205_, lean_object* v_as_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_array_get_size(v_as_1206_);
v___x_1213_ = lean_nat_dec_lt(v_i_1205_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v_i_1205_);
lean_dec(v_declName_1204_);
lean_dec_ref(v_map_1203_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_as_1206_);
return v___x_1214_;
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_a_1215_ = lean_array_fget_borrowed(v_as_1206_, v_i_1205_);
lean_inc(v_declName_1204_);
lean_inc_ref(v_map_1203_);
v___x_1216_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___boxed), 8, 2);
lean_closure_set(v___x_1216_, 0, v_map_1203_);
lean_closure_set(v___x_1216_, 1, v_declName_1204_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v_a_1215_);
v___x_1217_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(v_a_1215_, v___x_1216_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; size_t v___x_1219_; size_t v___x_1220_; uint8_t v___x_1221_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = lean_ptr_addr(v_a_1215_);
v___x_1220_ = lean_ptr_addr(v_a_1218_);
v___x_1221_ = lean_usize_dec_eq(v___x_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_add(v_i_1205_, v___x_1222_);
v___x_1224_ = lean_array_fset(v_as_1206_, v_i_1205_, v_a_1218_);
lean_dec(v_i_1205_);
v_i_1205_ = v___x_1223_;
v_as_1206_ = v___x_1224_;
goto _start;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_a_1218_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_add(v_i_1205_, v___x_1226_);
lean_dec(v_i_1205_);
v_i_1205_ = v___x_1227_;
goto _start;
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v_as_1206_);
lean_dec(v_i_1205_);
lean_dec(v_declName_1204_);
lean_dec_ref(v_map_1203_);
v_a_1229_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1217_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1217_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2___boxed(lean_object* v_map_1237_, lean_object* v_declName_1238_, lean_object* v_i_1239_, lean_object* v_as_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2(v_map_1237_, v_declName_1238_, v_i_1239_, v_as_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0(lean_object* v_00_u03b2_1247_, lean_object* v_inst_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v_inst_1248_, v_m_1249_, v_a_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_inst_1253_, lean_object* v_m_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0(v_00_u03b2_1252_, v_inst_1253_, v_m_1254_, v_a_1255_);
lean_dec_ref(v_a_1255_);
lean_dec_ref(v_m_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0_spec__3___redArg(lean_object* v_inst_1257_, lean_object* v_msg_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_panic_fn(v_inst_1257_, v_msg_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1260_, lean_object* v_inst_1261_, lean_object* v_msg_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_panic_fn(v_inst_1261_, v_msg_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0(lean_object* v_00_u03b2_1264_, lean_object* v_inst_1265_, lean_object* v_a_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(v_inst_1265_, v_a_1266_, v_x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1269_, lean_object* v_inst_1270_, lean_object* v_a_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0(v_00_u03b2_1269_, v_inst_1270_, v_a_1271_, v_x_1272_);
lean_dec(v_x_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0(lean_object* v_map_1274_, size_t v_sz_1275_, size_t v_i_1276_, lean_object* v_bs_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_usize_dec_lt(v_i_1276_, v_sz_1275_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v_map_1274_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_bs_1277_);
return v___x_1284_;
}
else
{
lean_object* v_v_1285_; lean_object* v_toSignature_1286_; lean_object* v_value_1287_; uint8_t v_recursive_1288_; lean_object* v_inlineAttr_x3f_1289_; lean_object* v___x_1290_; lean_object* v_bs_x27_1291_; lean_object* v_a_1293_; 
v_v_1285_ = lean_array_uget(v_bs_1277_, v_i_1276_);
v_toSignature_1286_ = lean_ctor_get(v_v_1285_, 0);
lean_inc_ref(v_toSignature_1286_);
v_value_1287_ = lean_ctor_get(v_v_1285_, 1);
lean_inc_ref(v_value_1287_);
v_recursive_1288_ = lean_ctor_get_uint8(v_v_1285_, sizeof(void*)*3);
v_inlineAttr_x3f_1289_ = lean_ctor_get(v_v_1285_, 2);
v___x_1290_ = lean_unsigned_to_nat(0u);
v_bs_x27_1291_ = lean_array_uset(v_bs_1277_, v_i_1276_, v___x_1290_);
if (lean_obj_tag(v_value_1287_) == 0)
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1347_; 
lean_inc(v_inlineAttr_x3f_1289_);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_v_1285_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1348_ = lean_ctor_get(v_v_1285_, 2);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_v_1285_, 1);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_v_1285_, 0);
lean_dec(v_unused_1350_);
v___x_1299_ = v_v_1285_;
v_isShared_1300_ = v_isSharedCheck_1347_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_v_1285_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1347_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_code_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1346_; 
v_code_1301_ = lean_ctor_get(v_value_1287_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_value_1287_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1303_ = v_value_1287_;
v_isShared_1304_ = v_isSharedCheck_1346_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_code_1301_);
lean_dec(v_value_1287_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1346_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_name_1305_; lean_object* v_levelParams_1306_; lean_object* v_type_1307_; lean_object* v_params_1308_; uint8_t v_safe_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1345_; 
v_name_1305_ = lean_ctor_get(v_toSignature_1286_, 0);
v_levelParams_1306_ = lean_ctor_get(v_toSignature_1286_, 1);
v_type_1307_ = lean_ctor_get(v_toSignature_1286_, 2);
v_params_1308_ = lean_ctor_get(v_toSignature_1286_, 3);
v_safe_1309_ = lean_ctor_get_uint8(v_toSignature_1286_, sizeof(void*)*4);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_toSignature_1286_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1311_ = v_toSignature_1286_;
v_isShared_1312_ = v_isSharedCheck_1345_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_params_1308_);
lean_inc(v_type_1307_);
lean_inc(v_levelParams_1306_);
lean_inc(v_name_1305_);
lean_dec(v_toSignature_1286_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1345_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; 
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v_name_1305_);
lean_inc_ref(v_map_1274_);
v___x_1313_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_1274_, v_name_1305_, v_code_1301_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0);
lean_inc(v_name_1305_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_name_1305_);
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v___x_1315_, v_map_1274_, v___x_1316_);
lean_dec_ref(v___x_1316_);
v___x_1318_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(v_params_1308_, v___x_1317_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1318_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 3, v_a_1319_);
v___x_1321_ = v___x_1311_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_name_1305_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_levelParams_1306_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_type_1307_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_a_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*4, v_safe_1309_);
v___x_1321_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v_a_1314_);
v___x_1323_ = v___x_1303_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1314_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v___x_1323_);
lean_ctor_set(v___x_1299_, 0, v___x_1321_);
v___x_1325_ = v___x_1299_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_inlineAttr_x3f_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3, v_recursive_1288_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v_a_1293_ = v___x_1325_;
goto v___jp_1292_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1314_);
lean_del_object(v___x_1311_);
lean_dec_ref(v_type_1307_);
lean_dec(v_levelParams_1306_);
lean_dec(v_name_1305_);
lean_del_object(v___x_1303_);
lean_del_object(v___x_1299_);
lean_dec_ref(v_bs_x27_1291_);
lean_dec(v_inlineAttr_x3f_1289_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v_map_1274_);
v_a_1329_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1318_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1318_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_del_object(v___x_1311_);
lean_dec_ref(v_params_1308_);
lean_dec_ref(v_type_1307_);
lean_dec(v_levelParams_1306_);
lean_dec(v_name_1305_);
lean_del_object(v___x_1303_);
lean_del_object(v___x_1299_);
lean_dec_ref(v_bs_x27_1291_);
lean_dec(v_inlineAttr_x3f_1289_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v_map_1274_);
v_a_1337_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1313_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1313_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1287_);
lean_dec_ref(v_toSignature_1286_);
v_a_1293_ = v_v_1285_;
goto v___jp_1292_;
}
v___jp_1292_:
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1276_, v___x_1294_);
v___x_1296_ = lean_array_uset(v_bs_x27_1291_, v_i_1276_, v_a_1293_);
v_i_1276_ = v___x_1295_;
v_bs_1277_ = v___x_1296_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0___boxed(lean_object* v_map_1351_, lean_object* v_sz_1352_, lean_object* v_i_1353_, lean_object* v_bs_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
size_t v_sz_boxed_1360_; size_t v_i_boxed_1361_; lean_object* v_res_1362_; 
v_sz_boxed_1360_ = lean_unbox_usize(v_sz_1352_);
lean_dec(v_sz_1352_);
v_i_boxed_1361_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0(v_map_1351_, v_sz_boxed_1360_, v_i_boxed_1361_, v_bs_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply(lean_object* v_decls_1363_, lean_object* v_map_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
size_t v_sz_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v_sz_1370_ = lean_array_size(v_decls_1363_);
v___x_1371_ = ((size_t)0ULL);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0(v_map_1364_, v_sz_1370_, v___x_1371_, v_decls_1363_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply___boxed(lean_object* v_decls_1373_, lean_object* v_map_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply(v_decls_1373_, v_map_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0(lean_object* v_____do__lift_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_paramSet_1389_; lean_object* v___x_1390_; 
v_paramSet_1389_ = lean_ctor_get(v_____do__lift_1381_, 2);
lean_inc(v_paramSet_1389_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_paramSet_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0___boxed(lean_object* v_____do__lift_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0(v_____do__lift_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec_ref(v_____do__lift_1391_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1(lean_object* v_00_u03b1_1400_, lean_object* v_f_1401_, lean_object* v_mx_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_decls_1410_; lean_object* v_currDecl_1411_; lean_object* v_paramSet_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1421_; 
v_decls_1410_ = lean_ctor_get(v___y_1403_, 0);
v_currDecl_1411_ = lean_ctor_get(v___y_1403_, 1);
v_paramSet_1412_ = lean_ctor_get(v___y_1403_, 2);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___y_1403_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1414_ = v___y_1403_;
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_paramSet_1412_);
lean_inc(v_currDecl_1411_);
lean_inc(v_decls_1410_);
lean_dec(v___y_1403_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_apply_1(v_f_1401_, v_paramSet_1412_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 2, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_decls_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_currDecl_1411_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_apply_7(v_mx_1402_, v___x_1418_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, lean_box(0));
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1___boxed(lean_object* v_00_u03b1_1422_, lean_object* v_f_1423_, lean_object* v_mx_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1(v_00_u03b1_1422_, v_f_1423_, v_mx_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v_res_1432_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_toApplicative_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1500_; 
v___x_1435_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_1436_ = l_ReaderT_instMonad___redArg(v___x_1435_);
v_toApplicative_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v___x_1436_, 1);
lean_dec(v_unused_1501_);
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1500_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_toApplicative_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1500_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_toFunctor_1441_; lean_object* v_toSeq_1442_; lean_object* v_toSeqLeft_1443_; lean_object* v_toSeqRight_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1498_; 
v_toFunctor_1441_ = lean_ctor_get(v_toApplicative_1437_, 0);
v_toSeq_1442_ = lean_ctor_get(v_toApplicative_1437_, 2);
v_toSeqLeft_1443_ = lean_ctor_get(v_toApplicative_1437_, 3);
v_toSeqRight_1444_ = lean_ctor_get(v_toApplicative_1437_, 4);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_toApplicative_1437_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v_toApplicative_1437_, 1);
lean_dec(v_unused_1499_);
v___x_1446_ = v_toApplicative_1437_;
v_isShared_1447_ = v_isSharedCheck_1498_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_toSeqRight_1444_);
lean_inc(v_toSeqLeft_1443_);
lean_inc(v_toSeq_1442_);
lean_inc(v_toFunctor_1441_);
lean_dec(v_toApplicative_1437_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1498_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___f_1448_; lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___x_1457_; 
v___f_1448_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_1449_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_1441_);
v___f_1450_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1450_, 0, v_toFunctor_1441_);
v___f_1451_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1451_, 0, v_toFunctor_1441_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___f_1450_);
lean_ctor_set(v___x_1452_, 1, v___f_1451_);
v___f_1453_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1453_, 0, v_toSeqRight_1444_);
v___f_1454_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1454_, 0, v_toSeqLeft_1443_);
v___f_1455_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1455_, 0, v_toSeq_1442_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 4, v___f_1453_);
lean_ctor_set(v___x_1446_, 3, v___f_1454_);
lean_ctor_set(v___x_1446_, 2, v___f_1455_);
lean_ctor_set(v___x_1446_, 1, v___f_1448_);
lean_ctor_set(v___x_1446_, 0, v___x_1452_);
v___x_1457_ = v___x_1446_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___f_1448_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v___f_1455_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v___f_1454_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v___f_1453_);
v___x_1457_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___f_1449_);
lean_ctor_set(v___x_1439_, 0, v___x_1457_);
v___x_1459_ = v___x_1439_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___f_1449_);
v___x_1459_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v_toApplicative_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1494_; 
v___x_1460_ = l_ReaderT_instMonad___redArg(v___x_1459_);
v_toApplicative_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v___x_1460_, 1);
lean_dec(v_unused_1495_);
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1494_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_toApplicative_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1494_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_toFunctor_1465_; lean_object* v_toSeq_1466_; lean_object* v_toSeqLeft_1467_; lean_object* v_toSeqRight_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1492_; 
v_toFunctor_1465_ = lean_ctor_get(v_toApplicative_1461_, 0);
v_toSeq_1466_ = lean_ctor_get(v_toApplicative_1461_, 2);
v_toSeqLeft_1467_ = lean_ctor_get(v_toApplicative_1461_, 3);
v_toSeqRight_1468_ = lean_ctor_get(v_toApplicative_1461_, 4);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_toApplicative_1461_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v_toApplicative_1461_, 1);
lean_dec(v_unused_1493_);
v___x_1470_ = v_toApplicative_1461_;
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_toSeqRight_1468_);
lean_inc(v_toSeqLeft_1467_);
lean_inc(v_toSeq_1466_);
lean_inc(v_toFunctor_1465_);
lean_dec(v_toApplicative_1461_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___f_1472_; lean_object* v___f_1473_; lean_object* v___f_1474_; lean_object* v___f_1475_; lean_object* v___f_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___x_1483_; 
v___f_1472_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__0));
v___f_1473_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__1));
v___f_1474_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_1475_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_1465_);
v___f_1476_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1476_, 0, v_toFunctor_1465_);
v___f_1477_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1477_, 0, v_toFunctor_1465_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___f_1476_);
lean_ctor_set(v___x_1478_, 1, v___f_1477_);
v___f_1479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1479_, 0, v_toSeqRight_1468_);
v___f_1480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1480_, 0, v_toSeqLeft_1467_);
v___f_1481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1481_, 0, v_toSeq_1466_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v___f_1479_);
lean_ctor_set(v___x_1470_, 3, v___f_1480_);
lean_ctor_set(v___x_1470_, 2, v___f_1481_);
lean_ctor_set(v___x_1470_, 1, v___f_1474_);
lean_ctor_set(v___x_1470_, 0, v___x_1478_);
v___x_1483_ = v___x_1470_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___f_1474_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v___f_1481_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v___f_1480_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v___f_1479_);
v___x_1483_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v___f_1475_);
lean_ctor_set(v___x_1463_, 0, v___x_1483_);
v___x_1485_ = v___x_1463_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___f_1475_);
v___x_1485_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = l_ReaderT_instMonad___redArg(v___x_1485_);
lean_inc_ref(v___x_1486_);
v___x_1487_ = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(v___x_1487_, 0, lean_box(0));
lean_closure_set(v___x_1487_, 1, lean_box(0));
lean_closure_set(v___x_1487_, 2, v___x_1486_);
v___x_1488_ = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(v___x_1488_, 0, lean_box(0));
lean_closure_set(v___x_1488_, 1, lean_box(0));
lean_closure_set(v___x_1488_, 2, v___x_1486_);
lean_closure_set(v___x_1488_, 3, lean_box(0));
lean_closure_set(v___x_1488_, 4, lean_box(0));
lean_closure_set(v___x_1488_, 5, v___x_1487_);
lean_closure_set(v___x_1488_, 6, v___f_1472_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___f_1473_);
return v___x_1489_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx(lean_object* v_x_1502_){
_start:
{
switch(lean_obj_tag(v_x_1502_))
{
case 0:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_unsigned_to_nat(0u);
return v___x_1503_;
}
case 1:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_unsigned_to_nat(1u);
return v___x_1504_;
}
case 2:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_unsigned_to_nat(2u);
return v___x_1505_;
}
case 3:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_unsigned_to_nat(3u);
return v___x_1506_;
}
case 4:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_unsigned_to_nat(4u);
return v___x_1507_;
}
case 5:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_unsigned_to_nat(5u);
return v___x_1508_;
}
case 6:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_unsigned_to_nat(6u);
return v___x_1509_;
}
case 7:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_unsigned_to_nat(7u);
return v___x_1510_;
}
case 8:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_unsigned_to_nat(8u);
return v___x_1511_;
}
case 9:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_unsigned_to_nat(9u);
return v___x_1512_;
}
default: 
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_unsigned_to_nat(10u);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx___boxed(lean_object* v_x_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx(v_x_1514_);
lean_dec_ref(v_x_1514_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(lean_object* v_t_1516_, lean_object* v_k_1517_){
_start:
{
lean_object* v_resultFVar_1518_; lean_object* v___x_1519_; 
v_resultFVar_1518_ = lean_ctor_get(v_t_1516_, 0);
lean_inc(v_resultFVar_1518_);
lean_dec_ref(v_t_1516_);
v___x_1519_ = lean_apply_1(v_k_1517_, v_resultFVar_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim(lean_object* v_motive_1520_, lean_object* v_ctorIdx_1521_, lean_object* v_t_1522_, lean_object* v_h_1523_, lean_object* v_k_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1522_, v_k_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___boxed(lean_object* v_motive_1526_, lean_object* v_ctorIdx_1527_, lean_object* v_t_1528_, lean_object* v_h_1529_, lean_object* v_k_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim(v_motive_1526_, v_ctorIdx_1527_, v_t_1528_, v_h_1529_, v_k_1530_);
lean_dec(v_ctorIdx_1527_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_resetReuse_elim___redArg(lean_object* v_t_1532_, lean_object* v_resetReuse_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1532_, v_resetReuse_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_resetReuse_elim(lean_object* v_motive_1535_, lean_object* v_t_1536_, lean_object* v_h_1537_, lean_object* v_resetReuse_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1536_, v_resetReuse_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorResult_elim___redArg(lean_object* v_t_1540_, lean_object* v_constructorResult_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1540_, v_constructorResult_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorResult_elim(lean_object* v_motive_1543_, lean_object* v_t_1544_, lean_object* v_h_1545_, lean_object* v_constructorResult_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1544_, v_constructorResult_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorArg_elim___redArg(lean_object* v_t_1548_, lean_object* v_constructorArg_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1548_, v_constructorArg_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorArg_elim(lean_object* v_motive_1551_, lean_object* v_t_1552_, lean_object* v_h_1553_, lean_object* v_constructorArg_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1552_, v_constructorArg_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_projectionPropagation_elim___redArg(lean_object* v_t_1556_, lean_object* v_projectionPropagation_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1556_, v_projectionPropagation_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_projectionPropagation_elim(lean_object* v_motive_1559_, lean_object* v_t_1560_, lean_object* v_h_1561_, lean_object* v_projectionPropagation_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1560_, v_projectionPropagation_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallResult_elim___redArg(lean_object* v_t_1564_, lean_object* v_functionCallResult_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1564_, v_functionCallResult_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallResult_elim(lean_object* v_motive_1567_, lean_object* v_t_1568_, lean_object* v_h_1569_, lean_object* v_functionCallResult_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1568_, v_functionCallResult_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallArg_elim___redArg(lean_object* v_t_1572_, lean_object* v_functionCallArg_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1572_, v_functionCallArg_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallArg_elim(lean_object* v_motive_1575_, lean_object* v_t_1576_, lean_object* v_h_1577_, lean_object* v_functionCallArg_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1576_, v_functionCallArg_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_fvarCall_elim___redArg(lean_object* v_t_1580_, lean_object* v_fvarCall_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1580_, v_fvarCall_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_fvarCall_elim(lean_object* v_motive_1583_, lean_object* v_t_1584_, lean_object* v_h_1585_, lean_object* v_fvarCall_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1584_, v_fvarCall_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_partialApplication_elim___redArg(lean_object* v_t_1588_, lean_object* v_partialApplication_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1588_, v_partialApplication_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_partialApplication_elim(lean_object* v_motive_1591_, lean_object* v_t_1592_, lean_object* v_h_1593_, lean_object* v_partialApplication_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1592_, v_partialApplication_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_tailCallPreservation_elim___redArg(lean_object* v_t_1596_, lean_object* v_tailCallPreservation_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1596_, v_tailCallPreservation_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_tailCallPreservation_elim(lean_object* v_motive_1599_, lean_object* v_t_1600_, lean_object* v_h_1601_, lean_object* v_tailCallPreservation_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1600_, v_tailCallPreservation_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpArgPropagation_elim___redArg(lean_object* v_t_1604_, lean_object* v_jpArgPropagation_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1604_, v_jpArgPropagation_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpArgPropagation_elim(lean_object* v_motive_1607_, lean_object* v_t_1608_, lean_object* v_h_1609_, lean_object* v_jpArgPropagation_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1608_, v_jpArgPropagation_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpTailCallPreservation_elim___redArg(lean_object* v_t_1612_, lean_object* v_jpTailCallPreservation_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1612_, v_jpTailCallPreservation_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpTailCallPreservation_elim(lean_object* v_motive_1615_, lean_object* v_t_1616_, lean_object* v_h_1617_, lean_object* v_jpTailCallPreservation_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1616_, v_jpTailCallPreservation_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0(lean_object* v_reason_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
switch(lean_obj_tag(v_reason_1631_))
{
case 0:
{
lean_object* v_resultFVar_1638_; lean_object* v___x_1639_; 
v_resultFVar_1638_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1638_);
lean_dec_ref(v_reason_1631_);
v___x_1639_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1638_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1652_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1652_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1652_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1644_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__0));
v___x_1645_ = l_Std_Format_defWidth;
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = l_Std_Format_pretty(v_a_1640_, v___x_1645_, v___x_1646_, v___x_1646_);
v___x_1648_ = lean_string_append(v___x_1644_, v___x_1647_);
lean_dec_ref(v___x_1647_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1648_);
v___x_1650_ = v___x_1642_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1639_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1639_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
case 1:
{
lean_object* v_resultFVar_1661_; lean_object* v___x_1662_; 
v_resultFVar_1661_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1661_);
lean_dec_ref(v_reason_1631_);
v___x_1662_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1661_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1675_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1675_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1675_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1667_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__1));
v___x_1668_ = l_Std_Format_defWidth;
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = l_Std_Format_pretty(v_a_1663_, v___x_1668_, v___x_1669_, v___x_1669_);
v___x_1671_ = lean_string_append(v___x_1667_, v___x_1670_);
lean_dec_ref(v___x_1670_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1671_);
v___x_1673_ = v___x_1665_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v_a_1676_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1662_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1662_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
case 2:
{
lean_object* v_resultFVar_1684_; lean_object* v___x_1685_; 
v_resultFVar_1684_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1684_);
lean_dec_ref(v_reason_1631_);
v___x_1685_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1684_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1698_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1698_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1698_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__2));
v___x_1691_ = l_Std_Format_defWidth;
v___x_1692_ = lean_unsigned_to_nat(0u);
v___x_1693_ = l_Std_Format_pretty(v_a_1686_, v___x_1691_, v___x_1692_, v___x_1692_);
v___x_1694_ = lean_string_append(v___x_1690_, v___x_1693_);
lean_dec_ref(v___x_1693_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1694_);
v___x_1696_ = v___x_1688_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_a_1699_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1685_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1685_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
case 3:
{
lean_object* v_resultFVar_1707_; lean_object* v___x_1708_; 
v_resultFVar_1707_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1707_);
lean_dec_ref(v_reason_1631_);
v___x_1708_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1707_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1721_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1721_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1721_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1713_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__3));
v___x_1714_ = l_Std_Format_defWidth;
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = l_Std_Format_pretty(v_a_1709_, v___x_1714_, v___x_1715_, v___x_1715_);
v___x_1717_ = lean_string_append(v___x_1713_, v___x_1716_);
lean_dec_ref(v___x_1716_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1717_);
v___x_1719_ = v___x_1711_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1708_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1708_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
case 4:
{
lean_object* v_resultFVar_1730_; lean_object* v___x_1731_; 
v_resultFVar_1730_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1730_);
lean_dec_ref(v_reason_1631_);
v___x_1731_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1730_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1744_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__4));
v___x_1737_ = l_Std_Format_defWidth;
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = l_Std_Format_pretty(v_a_1732_, v___x_1737_, v___x_1738_, v___x_1738_);
v___x_1740_ = lean_string_append(v___x_1736_, v___x_1739_);
lean_dec_ref(v___x_1739_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1740_);
v___x_1742_ = v___x_1734_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1731_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1731_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
case 5:
{
lean_object* v_resultFVar_1753_; lean_object* v___x_1754_; 
v_resultFVar_1753_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1753_);
lean_dec_ref(v_reason_1631_);
v___x_1754_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1753_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1767_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1767_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1767_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__5));
v___x_1760_ = l_Std_Format_defWidth;
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = l_Std_Format_pretty(v_a_1755_, v___x_1760_, v___x_1761_, v___x_1761_);
v___x_1763_ = lean_string_append(v___x_1759_, v___x_1762_);
lean_dec_ref(v___x_1762_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1763_);
v___x_1765_ = v___x_1757_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1754_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1754_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
case 6:
{
lean_object* v_resultFVar_1776_; lean_object* v___x_1777_; 
v_resultFVar_1776_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1776_);
lean_dec_ref(v_reason_1631_);
v___x_1777_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1776_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1790_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1790_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1790_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__6));
v___x_1783_ = l_Std_Format_defWidth;
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = l_Std_Format_pretty(v_a_1778_, v___x_1783_, v___x_1784_, v___x_1784_);
v___x_1786_ = lean_string_append(v___x_1782_, v___x_1785_);
lean_dec_ref(v___x_1785_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1786_);
v___x_1788_ = v___x_1780_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1777_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1777_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
case 7:
{
lean_object* v_resultFVar_1799_; lean_object* v___x_1800_; 
v_resultFVar_1799_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_resultFVar_1799_);
lean_dec_ref(v_reason_1631_);
v___x_1800_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1799_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1813_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__7));
v___x_1806_ = l_Std_Format_defWidth;
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = l_Std_Format_pretty(v_a_1801_, v___x_1806_, v___x_1807_, v___x_1807_);
v___x_1809_ = lean_string_append(v___x_1805_, v___x_1808_);
lean_dec_ref(v___x_1808_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1809_);
v___x_1811_ = v___x_1803_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1800_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1800_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
case 8:
{
lean_object* v_funcName_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1833_; 
v_funcName_1822_ = lean_ctor_get(v_reason_1631_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_reason_1631_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1824_ = v_reason_1631_;
v_isShared_1825_ = v_isSharedCheck_1833_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_funcName_1822_);
lean_dec(v_reason_1631_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1833_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1826_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__8));
v___x_1827_ = 1;
v___x_1828_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_funcName_1822_, v___x_1827_);
v___x_1829_ = lean_string_append(v___x_1826_, v___x_1828_);
lean_dec_ref(v___x_1828_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1829_);
v___x_1831_ = v___x_1824_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
case 9:
{
lean_object* v_jpFVar_1834_; lean_object* v___x_1835_; 
v_jpFVar_1834_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_jpFVar_1834_);
lean_dec_ref(v_reason_1631_);
v___x_1835_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_jpFVar_1834_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1848_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__9));
v___x_1841_ = l_Std_Format_defWidth;
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = l_Std_Format_pretty(v_a_1836_, v___x_1841_, v___x_1842_, v___x_1842_);
v___x_1844_ = lean_string_append(v___x_1840_, v___x_1843_);
lean_dec_ref(v___x_1843_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1844_);
v___x_1846_ = v___x_1838_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1835_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1835_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
default: 
{
lean_object* v_jpFVar_1857_; lean_object* v___x_1858_; 
v_jpFVar_1857_ = lean_ctor_get(v_reason_1631_, 0);
lean_inc(v_jpFVar_1857_);
lean_dec_ref(v_reason_1631_);
v___x_1858_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_jpFVar_1857_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1871_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1871_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1871_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__10));
v___x_1864_ = l_Std_Format_defWidth;
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = l_Std_Format_pretty(v_a_1859_, v___x_1864_, v___x_1865_, v___x_1865_);
v___x_1867_ = lean_string_append(v___x_1863_, v___x_1866_);
lean_dec_ref(v___x_1866_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1867_);
v___x_1869_ = v___x_1861_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1858_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1858_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___boxed(lean_object* v_reason_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0(v_reason_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString(lean_object* v_reason_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___y_1894_; lean_object* v___x_1895_; 
v___y_1894_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___boxed), 7, 1);
lean_closure_set(v___y_1894_, 0, v_reason_1888_);
v___x_1895_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___y_1894_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___boxed(lean_object* v_reason_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString(v_reason_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(lean_object* v_a_1903_, lean_object* v_x_1904_){
_start:
{
if (lean_obj_tag(v_x_1904_) == 0)
{
uint8_t v___x_1905_; 
v___x_1905_ = 0;
return v___x_1905_;
}
else
{
lean_object* v_key_1906_; lean_object* v_tail_1907_; uint8_t v___x_1908_; 
v_key_1906_ = lean_ctor_get(v_x_1904_, 0);
v_tail_1907_ = lean_ctor_get(v_x_1904_, 2);
v___x_1908_ = l_Lean_instBEqFVarId_beq(v_key_1906_, v_a_1903_);
if (v___x_1908_ == 0)
{
v_x_1904_ = v_tail_1907_;
goto _start;
}
else
{
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg___boxed(lean_object* v_a_1910_, lean_object* v_x_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_1910_, v_x_1911_);
lean_dec(v_x_1911_);
lean_dec(v_a_1910_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(lean_object* v_m_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_buckets_1916_; lean_object* v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v___x_1920_; uint64_t v_fold_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; uint64_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_buckets_1916_ = lean_ctor_get(v_m_1914_, 1);
v___x_1917_ = lean_array_get_size(v_buckets_1916_);
v___x_1918_ = l_Lean_instHashableFVarId_hash(v_a_1915_);
v___x_1919_ = 32ULL;
v___x_1920_ = lean_uint64_shift_right(v___x_1918_, v___x_1919_);
v_fold_1921_ = lean_uint64_xor(v___x_1918_, v___x_1920_);
v___x_1922_ = 16ULL;
v___x_1923_ = lean_uint64_shift_right(v_fold_1921_, v___x_1922_);
v___x_1924_ = lean_uint64_xor(v_fold_1921_, v___x_1923_);
v___x_1925_ = lean_uint64_to_usize(v___x_1924_);
v___x_1926_ = lean_usize_of_nat(v___x_1917_);
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_sub(v___x_1926_, v___x_1927_);
v___x_1929_ = lean_usize_land(v___x_1925_, v___x_1928_);
v___x_1930_ = lean_array_uget_borrowed(v_buckets_1916_, v___x_1929_);
v___x_1931_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_1915_, v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg___boxed(lean_object* v_m_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_m_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_m_1932_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(lean_object* v_fvarId_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v_owned_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1939_ = lean_st_ref_get(v_a_1937_);
v_owned_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc_ref(v_owned_1940_);
lean_dec(v___x_1939_);
v___x_1941_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_owned_1940_, v_fvarId_1936_);
lean_dec_ref(v_owned_1940_);
v___x_1942_ = lean_box(v___x_1941_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg___boxed(lean_object* v_fvarId_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_1944_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec(v_fvarId_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned(lean_object* v_fvarId_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_1948_, v_a_1950_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___boxed(lean_object* v_fvarId_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned(v_fvarId_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_fvarId_1957_);
return v_res_1965_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0(lean_object* v_00_u03b2_1966_, lean_object* v_m_1967_, lean_object* v_a_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_m_1967_, v_a_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___boxed(lean_object* v_00_u03b2_1970_, lean_object* v_m_1971_, lean_object* v_a_1972_){
_start:
{
uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_res_1973_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0(v_00_u03b2_1970_, v_m_1971_, v_a_1972_);
lean_dec(v_a_1972_);
lean_dec_ref(v_m_1971_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0(lean_object* v_00_u03b2_1975_, lean_object* v_a_1976_, lean_object* v_x_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_1976_, v_x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1979_, lean_object* v_a_1980_, lean_object* v_x_1981_){
_start:
{
uint8_t v_res_1982_; lean_object* v_r_1983_; 
v_res_1982_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0(v_00_u03b2_1979_, v_a_1980_, v_x_1981_);
lean_dec(v_x_1981_);
lean_dec(v_a_1980_);
v_r_1983_ = lean_box(v_res_1982_);
return v_r_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(size_t v_sz_1984_, size_t v_i_1985_, lean_object* v_bs_1986_, lean_object* v___y_1987_){
_start:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_usize_dec_lt(v_i_1985_, v_sz_1984_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_bs_1986_);
return v___x_1990_;
}
else
{
lean_object* v_v_1991_; lean_object* v_fvarId_1992_; lean_object* v_binderName_1993_; lean_object* v_type_1994_; uint8_t v_borrow_1995_; lean_object* v___x_1996_; lean_object* v_bs_x27_1997_; lean_object* v_a_1999_; 
v_v_1991_ = lean_array_uget(v_bs_1986_, v_i_1985_);
v_fvarId_1992_ = lean_ctor_get(v_v_1991_, 0);
v_binderName_1993_ = lean_ctor_get(v_v_1991_, 1);
v_type_1994_ = lean_ctor_get(v_v_1991_, 2);
v_borrow_1995_ = lean_ctor_get_uint8(v_v_1991_, sizeof(void*)*3);
v___x_1996_ = lean_unsigned_to_nat(0u);
v_bs_x27_1997_ = lean_array_uset(v_bs_1986_, v_i_1985_, v___x_1996_);
if (v_borrow_1995_ == 0)
{
v_a_1999_ = v_v_1991_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2004_; 
v___x_2004_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_1992_, v___y_1987_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; uint8_t v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
if (v___x_2006_ == 0)
{
v_a_1999_ = v_v_1991_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2025_; 
lean_inc_ref(v_type_1994_);
lean_inc(v_binderName_1993_);
lean_inc(v_fvarId_1992_);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_v_1991_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; lean_object* v_unused_2027_; lean_object* v_unused_2028_; 
v_unused_2026_ = lean_ctor_get(v_v_1991_, 2);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_v_1991_, 1);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_v_1991_, 0);
lean_dec(v_unused_2028_);
v___x_2008_ = v_v_1991_;
v_isShared_2009_ = v_isSharedCheck_2025_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v_v_1991_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2025_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v_owned_2011_; lean_object* v_paramMap_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2024_; 
v___x_2010_ = lean_st_ref_take(v___y_1987_);
v_owned_2011_ = lean_ctor_get(v___x_2010_, 0);
v_paramMap_2012_ = lean_ctor_get(v___x_2010_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2014_ = v___x_2010_;
v_isShared_2015_ = v_isSharedCheck_2024_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_paramMap_2012_);
lean_inc(v_owned_2011_);
lean_dec(v___x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2024_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_owned_2011_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_paramMap_2012_);
v___x_2017_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2021_; 
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*2, v_borrow_1995_);
v___x_2018_ = lean_st_ref_set(v___y_1987_, v___x_2017_);
v___x_2019_ = 0;
if (v_isShared_2009_ == 0)
{
v___x_2021_ = v___x_2008_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_fvarId_1992_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_binderName_1993_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_type_1994_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3, v___x_2019_);
v_a_1999_ = v___x_2021_;
goto v___jp_1998_;
}
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v_bs_x27_1997_);
lean_dec(v_v_1991_);
v_a_2029_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2004_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2004_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
v___jp_1998_:
{
size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_add(v_i_1985_, v___x_2000_);
v___x_2002_ = lean_array_uset(v_bs_x27_1997_, v_i_1985_, v_a_1999_);
v_i_1985_ = v___x_2001_;
v_bs_1986_ = v___x_2002_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg___boxed(lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_bs_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(v_sz_boxed_2042_, v_i_boxed_2043_, v_bs_2039_, v___y_2040_);
lean_dec(v___y_2040_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(lean_object* v_a_2045_, lean_object* v_x_2046_){
_start:
{
if (lean_obj_tag(v_x_2046_) == 0)
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_box(0);
return v___x_2047_;
}
else
{
lean_object* v_key_2048_; lean_object* v_value_2049_; lean_object* v_tail_2050_; uint8_t v___x_2051_; 
v_key_2048_ = lean_ctor_get(v_x_2046_, 0);
v_value_2049_ = lean_ctor_get(v_x_2046_, 1);
v_tail_2050_ = lean_ctor_get(v_x_2046_, 2);
v___x_2051_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_2048_, v_a_2045_);
if (v___x_2051_ == 0)
{
v_x_2046_ = v_tail_2050_;
goto _start;
}
else
{
lean_object* v___x_2053_; 
lean_inc(v_value_2049_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_value_2049_);
return v___x_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg___boxed(lean_object* v_a_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(v_a_2054_, v_x_2055_);
lean_dec(v_x_2055_);
lean_dec_ref(v_a_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(lean_object* v_m_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_buckets_2059_; lean_object* v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; uint64_t v___x_2063_; uint64_t v_fold_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; uint64_t v___x_2067_; size_t v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_buckets_2059_ = lean_ctor_get(v_m_2057_, 1);
v___x_2060_ = lean_array_get_size(v_buckets_2059_);
v___x_2061_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_a_2058_);
v___x_2062_ = 32ULL;
v___x_2063_ = lean_uint64_shift_right(v___x_2061_, v___x_2062_);
v_fold_2064_ = lean_uint64_xor(v___x_2061_, v___x_2063_);
v___x_2065_ = 16ULL;
v___x_2066_ = lean_uint64_shift_right(v_fold_2064_, v___x_2065_);
v___x_2067_ = lean_uint64_xor(v_fold_2064_, v___x_2066_);
v___x_2068_ = lean_uint64_to_usize(v___x_2067_);
v___x_2069_ = lean_usize_of_nat(v___x_2060_);
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_sub(v___x_2069_, v___x_2070_);
v___x_2072_ = lean_usize_land(v___x_2068_, v___x_2071_);
v___x_2073_ = lean_array_uget_borrowed(v_buckets_2059_, v___x_2072_);
v___x_2074_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(v_a_2058_, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg___boxed(lean_object* v_m_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_m_2075_, v_a_2076_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_m_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(lean_object* v_a_2078_, lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2079_) == 0)
{
return v_x_2079_;
}
else
{
lean_object* v_key_2080_; lean_object* v_value_2081_; lean_object* v_tail_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2091_; 
v_key_2080_ = lean_ctor_get(v_x_2079_, 0);
v_value_2081_ = lean_ctor_get(v_x_2079_, 1);
v_tail_2082_ = lean_ctor_get(v_x_2079_, 2);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_x_2079_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2084_ = v_x_2079_;
v_isShared_2085_ = v_isSharedCheck_2091_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_tail_2082_);
lean_inc(v_value_2081_);
lean_inc(v_key_2080_);
lean_dec(v_x_2079_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2091_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
uint8_t v___x_2086_; 
v___x_2086_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_2080_, v_a_2078_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2078_, v_tail_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 2, v___x_2087_);
v___x_2089_ = v___x_2084_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_key_2080_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_value_2081_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
else
{
lean_del_object(v___x_2084_);
lean_dec(v_value_2081_);
lean_dec(v_key_2080_);
return v_tail_2082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_2092_, lean_object* v_x_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2092_, v_x_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(lean_object* v_m_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_size_2097_; lean_object* v_buckets_2098_; lean_object* v___x_2099_; uint64_t v___x_2100_; uint64_t v___x_2101_; uint64_t v___x_2102_; uint64_t v_fold_2103_; uint64_t v___x_2104_; uint64_t v___x_2105_; uint64_t v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; size_t v___x_2111_; lean_object* v_bkt_2112_; uint8_t v___x_2113_; 
v_size_2097_ = lean_ctor_get(v_m_2095_, 0);
v_buckets_2098_ = lean_ctor_get(v_m_2095_, 1);
v___x_2099_ = lean_array_get_size(v_buckets_2098_);
v___x_2100_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_a_2096_);
v___x_2101_ = 32ULL;
v___x_2102_ = lean_uint64_shift_right(v___x_2100_, v___x_2101_);
v_fold_2103_ = lean_uint64_xor(v___x_2100_, v___x_2102_);
v___x_2104_ = 16ULL;
v___x_2105_ = lean_uint64_shift_right(v_fold_2103_, v___x_2104_);
v___x_2106_ = lean_uint64_xor(v_fold_2103_, v___x_2105_);
v___x_2107_ = lean_uint64_to_usize(v___x_2106_);
v___x_2108_ = lean_usize_of_nat(v___x_2099_);
v___x_2109_ = ((size_t)1ULL);
v___x_2110_ = lean_usize_sub(v___x_2108_, v___x_2109_);
v___x_2111_ = lean_usize_land(v___x_2107_, v___x_2110_);
v_bkt_2112_ = lean_array_uget_borrowed(v_buckets_2098_, v___x_2111_);
v___x_2113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg(v_a_2096_, v_bkt_2112_);
if (v___x_2113_ == 0)
{
return v_m_2095_;
}
else
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2126_; 
lean_inc(v_bkt_2112_);
lean_inc_ref(v_buckets_2098_);
lean_inc(v_size_2097_);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_m_2095_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; lean_object* v_unused_2128_; 
v_unused_2127_ = lean_ctor_get(v_m_2095_, 1);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_m_2095_, 0);
lean_dec(v_unused_2128_);
v___x_2115_ = v_m_2095_;
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v_m_2095_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v_buckets_x27_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2117_ = lean_box(0);
v_buckets_x27_2118_ = lean_array_uset(v_buckets_2098_, v___x_2111_, v___x_2117_);
v___x_2119_ = lean_unsigned_to_nat(1u);
v___x_2120_ = lean_nat_sub(v_size_2097_, v___x_2119_);
lean_dec(v_size_2097_);
v___x_2121_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2096_, v_bkt_2112_);
v___x_2122_ = lean_array_uset(v_buckets_x27_2118_, v___x_2111_, v___x_2121_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v___x_2122_);
lean_ctor_set(v___x_2115_, 0, v___x_2120_);
v___x_2124_ = v___x_2115_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg___boxed(lean_object* v_m_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(v_m_2129_, v_a_2130_);
lean_dec_ref(v_a_2130_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(lean_object* v_k_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v_paramMap_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_st_ref_get(v_a_2134_);
v_paramMap_2141_ = lean_ctor_get(v___x_2140_, 1);
lean_inc_ref(v_paramMap_2141_);
lean_dec(v___x_2140_);
v___x_2142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_paramMap_2141_, v_k_2132_);
lean_dec_ref(v_paramMap_2141_);
if (lean_obj_tag(v___x_2142_) == 1)
{
lean_object* v_val_2143_; lean_object* v___x_2144_; lean_object* v_owned_2145_; uint8_t v_modified_2146_; lean_object* v_paramMap_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2189_; 
v_val_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2143_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = lean_st_ref_take(v_a_2134_);
v_owned_2145_ = lean_ctor_get(v___x_2144_, 0);
v_modified_2146_ = lean_ctor_get_uint8(v___x_2144_, sizeof(void*)*2);
v_paramMap_2147_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2149_ = v___x_2144_;
v_isShared_2150_ = v_isSharedCheck_2189_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_paramMap_2147_);
lean_inc(v_owned_2145_);
lean_dec(v___x_2144_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2189_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(v_paramMap_2147_, v_k_2132_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v___x_2151_);
v___x_2153_ = v___x_2149_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_owned_2145_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2188_, sizeof(void*)*2, v_modified_2146_);
v___x_2153_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; size_t v_sz_2155_; size_t v___x_2156_; lean_object* v___x_2157_; 
v___x_2154_ = lean_st_ref_set(v_a_2134_, v___x_2153_);
v_sz_2155_ = lean_array_size(v_val_2143_);
v___x_2156_ = ((size_t)0ULL);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(v_sz_2155_, v___x_2156_, v_val_2143_, v_a_2134_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2179_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2179_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2179_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v_owned_2163_; uint8_t v_modified_2164_; lean_object* v_paramMap_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2178_; 
v___x_2162_ = lean_st_ref_take(v_a_2134_);
v_owned_2163_ = lean_ctor_get(v___x_2162_, 0);
v_modified_2164_ = lean_ctor_get_uint8(v___x_2162_, sizeof(void*)*2);
v_paramMap_2165_ = lean_ctor_get(v___x_2162_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2167_ = v___x_2162_;
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_paramMap_2165_);
lean_inc(v_owned_2163_);
lean_dec(v___x_2162_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(v_paramMap_2165_, v_k_2132_, v_a_2158_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_owned_2163_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2177_, sizeof(void*)*2, v_modified_2164_);
v___x_2171_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2172_ = lean_st_ref_set(v_a_2134_, v___x_2171_);
v___x_2173_ = lean_box(0);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2173_);
v___x_2175_ = v___x_2160_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_k_2132_);
v_a_2180_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2157_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2157_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v___x_2142_);
lean_dec_ref(v_k_2132_);
v___x_2190_ = lean_box(0);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap___boxed(lean_object* v_k_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(v_k_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0(lean_object* v_00_u03b2_2201_, lean_object* v_m_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_m_2202_, v_a_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_m_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0(v_00_u03b2_2205_, v_m_2206_, v_a_2207_);
lean_dec_ref(v_a_2207_);
lean_dec_ref(v_m_2206_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1(lean_object* v_00_u03b2_2209_, lean_object* v_m_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(v_m_2210_, v_a_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___boxed(lean_object* v_00_u03b2_2213_, lean_object* v_m_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1(v_00_u03b2_2213_, v_m_2214_, v_a_2215_);
lean_dec_ref(v_a_2215_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2(size_t v_sz_2217_, size_t v_i_2218_, lean_object* v_bs_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(v_sz_2217_, v_i_2218_, v_bs_2219_, v___y_2221_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___boxed(lean_object* v_sz_2228_, lean_object* v_i_2229_, lean_object* v_bs_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; lean_object* v_res_2240_; 
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2228_);
lean_dec(v_sz_2228_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2(v_sz_boxed_2238_, v_i_boxed_2239_, v_bs_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0(lean_object* v_00_u03b2_2241_, lean_object* v_a_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(v_a_2242_, v_x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2245_, lean_object* v_a_2246_, lean_object* v_x_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0(v_00_u03b2_2245_, v_a_2246_, v_x_2247_);
lean_dec(v_x_2247_);
lean_dec_ref(v_a_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2(lean_object* v_00_u03b2_2249_, lean_object* v_a_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2250_, v_x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2253_, lean_object* v_a_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2(v_00_u03b2_2253_, v_a_2254_, v_x_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(lean_object* v_cls_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_options_2263_; uint8_t v_hasTrace_2264_; 
v_options_2263_ = lean_ctor_get(v___y_2261_, 2);
v_hasTrace_2264_ = lean_ctor_get_uint8(v_options_2263_, sizeof(void*)*1);
if (v_hasTrace_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec(v_cls_2260_);
v___x_2265_ = lean_box(v_hasTrace_2264_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
else
{
lean_object* v_inheritedTraceOptions_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_inheritedTraceOptions_2267_ = lean_ctor_get(v___y_2261_, 13);
v___x_2268_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__1));
v___x_2269_ = l_Lean_Name_append(v___x_2268_, v_cls_2260_);
v___x_2270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2267_, v_options_2263_, v___x_2269_);
lean_dec(v___x_2269_);
v___x_2271_ = lean_box(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___boxed(lean_object* v_cls_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(v_cls_2273_, v___y_2274_);
lean_dec_ref(v___y_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0(lean_object* v_cls_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(v_cls_2277_, v___y_2282_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___boxed(lean_object* v_cls_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0(v_cls_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2294_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1);
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
lean_ctor_set(v___x_2300_, 2, v___x_2299_);
lean_ctor_set(v___x_2300_, 3, v___x_2298_);
lean_ctor_set(v___x_2300_, 4, v___x_2298_);
lean_ctor_set(v___x_2300_, 5, v___x_2298_);
lean_ctor_set(v___x_2300_, 6, v___x_2298_);
lean_ctor_set(v___x_2300_, 7, v___x_2298_);
lean_ctor_set(v___x_2300_, 8, v___x_2298_);
return v___x_2300_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2301_; double v___x_2302_; 
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = lean_float_of_nat(v___x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(lean_object* v_cls_2306_, lean_object* v_msg_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_options_2313_; lean_object* v_ref_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_options_2313_ = lean_ctor_get(v___y_2310_, 2);
v_ref_2314_ = lean_ctor_get(v___y_2310_, 5);
v___x_2315_ = lean_st_ref_get(v___y_2311_);
v___x_2316_ = lean_st_ref_get(v___y_2309_);
v___x_2317_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2308_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2376_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2376_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2376_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_env_2322_; lean_object* v_lctx_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2374_; 
v_env_2322_ = lean_ctor_get(v___x_2315_, 0);
lean_inc_ref(v_env_2322_);
lean_dec(v___x_2315_);
v_lctx_2323_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___x_2316_, 1);
lean_dec(v_unused_2375_);
v___x_2325_ = v___x_2316_;
v_isShared_2326_ = v_isSharedCheck_2374_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_lctx_2323_);
lean_dec(v___x_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2374_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v_traceState_2329_; lean_object* v_env_2330_; lean_object* v_nextMacroScope_2331_; lean_object* v_ngen_2332_; lean_object* v_auxDeclNGen_2333_; lean_object* v_cache_2334_; lean_object* v_messages_2335_; lean_object* v_infoState_2336_; lean_object* v_snapshotTasks_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2373_; 
v___x_2327_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2);
v___x_2328_ = lean_st_ref_take(v___y_2311_);
v_traceState_2329_ = lean_ctor_get(v___x_2328_, 4);
v_env_2330_ = lean_ctor_get(v___x_2328_, 0);
v_nextMacroScope_2331_ = lean_ctor_get(v___x_2328_, 1);
v_ngen_2332_ = lean_ctor_get(v___x_2328_, 2);
v_auxDeclNGen_2333_ = lean_ctor_get(v___x_2328_, 3);
v_cache_2334_ = lean_ctor_get(v___x_2328_, 5);
v_messages_2335_ = lean_ctor_get(v___x_2328_, 6);
v_infoState_2336_ = lean_ctor_get(v___x_2328_, 7);
v_snapshotTasks_2337_ = lean_ctor_get(v___x_2328_, 8);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2339_ = v___x_2328_;
v_isShared_2340_ = v_isSharedCheck_2373_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_snapshotTasks_2337_);
lean_inc(v_infoState_2336_);
lean_inc(v_messages_2335_);
lean_inc(v_cache_2334_);
lean_inc(v_traceState_2329_);
lean_inc(v_auxDeclNGen_2333_);
lean_inc(v_ngen_2332_);
lean_inc(v_nextMacroScope_2331_);
lean_inc(v_env_2330_);
lean_dec(v___x_2328_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2373_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
uint64_t v_tid_2341_; lean_object* v_traces_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2372_; 
v_tid_2341_ = lean_ctor_get_uint64(v_traceState_2329_, sizeof(void*)*1);
v_traces_2342_ = lean_ctor_get(v_traceState_2329_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_traceState_2329_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2344_ = v_traceState_2329_;
v_isShared_2345_ = v_isSharedCheck_2372_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_traces_2342_);
lean_dec(v_traceState_2329_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2372_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2346_ = lean_unbox(v_a_2318_);
lean_dec(v_a_2318_);
v___x_2347_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2323_, v___x_2346_);
lean_dec_ref(v_lctx_2323_);
lean_inc_ref(v_options_2313_);
v___x_2348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2348_, 0, v_env_2322_);
lean_ctor_set(v___x_2348_, 1, v___x_2327_);
lean_ctor_set(v___x_2348_, 2, v___x_2347_);
lean_ctor_set(v___x_2348_, 3, v_options_2313_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set_tag(v___x_2325_, 3);
lean_ctor_set(v___x_2325_, 1, v_msg_2307_);
lean_ctor_set(v___x_2325_, 0, v___x_2348_);
v___x_2350_ = v___x_2325_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_msg_2307_);
v___x_2350_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; double v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3);
v___x_2353_ = 0;
v___x_2354_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__4));
v___x_2355_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2355_, 0, v_cls_2306_);
lean_ctor_set(v___x_2355_, 1, v___x_2351_);
lean_ctor_set(v___x_2355_, 2, v___x_2354_);
lean_ctor_set_float(v___x_2355_, sizeof(void*)*3, v___x_2352_);
lean_ctor_set_float(v___x_2355_, sizeof(void*)*3 + 8, v___x_2352_);
lean_ctor_set_uint8(v___x_2355_, sizeof(void*)*3 + 16, v___x_2353_);
v___x_2356_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__5));
v___x_2357_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2350_);
lean_ctor_set(v___x_2357_, 2, v___x_2356_);
lean_inc(v_ref_2314_);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_ref_2314_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l_Lean_PersistentArray_push___redArg(v_traces_2342_, v___x_2358_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2359_);
v___x_2361_ = v___x_2344_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2359_);
lean_ctor_set_uint64(v_reuseFailAlloc_2370_, sizeof(void*)*1, v_tid_2341_);
v___x_2361_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 4, v___x_2361_);
v___x_2363_ = v___x_2339_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_env_2330_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_nextMacroScope_2331_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_ngen_2332_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v_auxDeclNGen_2333_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2369_, 5, v_cache_2334_);
lean_ctor_set(v_reuseFailAlloc_2369_, 6, v_messages_2335_);
lean_ctor_set(v_reuseFailAlloc_2369_, 7, v_infoState_2336_);
lean_ctor_set(v_reuseFailAlloc_2369_, 8, v_snapshotTasks_2337_);
v___x_2363_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2364_ = lean_st_ref_set(v___y_2311_, v___x_2363_);
v___x_2365_ = lean_box(0);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2365_);
v___x_2367_ = v___x_2320_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
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
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v___x_2316_);
lean_dec(v___x_2315_);
lean_dec_ref(v_msg_2307_);
lean_dec(v_cls_2306_);
v_a_2377_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2317_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2317_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___boxed(lean_object* v_cls_2385_, lean_object* v_msg_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(v_cls_2385_, v_msg_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2(lean_object* v_cls_2393_, lean_object* v_msg_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(v_cls_2393_, v_msg_2394_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___boxed(lean_object* v_cls_2403_, lean_object* v_msg_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2(v_cls_2403_, v_msg_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
return v_x_2413_;
}
else
{
lean_object* v_key_2415_; lean_object* v_value_2416_; lean_object* v_tail_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2440_; 
v_key_2415_ = lean_ctor_get(v_x_2414_, 0);
v_value_2416_ = lean_ctor_get(v_x_2414_, 1);
v_tail_2417_ = lean_ctor_get(v_x_2414_, 2);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2419_ = v_x_2414_;
v_isShared_2420_ = v_isSharedCheck_2440_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_tail_2417_);
lean_inc(v_value_2416_);
lean_inc(v_key_2415_);
lean_dec(v_x_2414_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2440_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; uint64_t v___x_2422_; uint64_t v___x_2423_; uint64_t v___x_2424_; uint64_t v_fold_2425_; uint64_t v___x_2426_; uint64_t v___x_2427_; uint64_t v___x_2428_; size_t v___x_2429_; size_t v___x_2430_; size_t v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2421_ = lean_array_get_size(v_x_2413_);
v___x_2422_ = l_Lean_instHashableFVarId_hash(v_key_2415_);
v___x_2423_ = 32ULL;
v___x_2424_ = lean_uint64_shift_right(v___x_2422_, v___x_2423_);
v_fold_2425_ = lean_uint64_xor(v___x_2422_, v___x_2424_);
v___x_2426_ = 16ULL;
v___x_2427_ = lean_uint64_shift_right(v_fold_2425_, v___x_2426_);
v___x_2428_ = lean_uint64_xor(v_fold_2425_, v___x_2427_);
v___x_2429_ = lean_uint64_to_usize(v___x_2428_);
v___x_2430_ = lean_usize_of_nat(v___x_2421_);
v___x_2431_ = ((size_t)1ULL);
v___x_2432_ = lean_usize_sub(v___x_2430_, v___x_2431_);
v___x_2433_ = lean_usize_land(v___x_2429_, v___x_2432_);
v___x_2434_ = lean_array_uget_borrowed(v_x_2413_, v___x_2433_);
lean_inc(v___x_2434_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 2, v___x_2434_);
v___x_2436_ = v___x_2419_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_key_2415_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_value_2416_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_array_uset(v_x_2413_, v___x_2433_, v___x_2436_);
v_x_2413_ = v___x_2437_;
v_x_2414_ = v_tail_2417_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3___redArg(lean_object* v_i_2441_, lean_object* v_source_2442_, lean_object* v_target_2443_){
_start:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = lean_array_get_size(v_source_2442_);
v___x_2445_ = lean_nat_dec_lt(v_i_2441_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_dec_ref(v_source_2442_);
lean_dec(v_i_2441_);
return v_target_2443_;
}
else
{
lean_object* v_es_2446_; lean_object* v___x_2447_; lean_object* v_source_2448_; lean_object* v_target_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_es_2446_ = lean_array_fget(v_source_2442_, v_i_2441_);
v___x_2447_ = lean_box(0);
v_source_2448_ = lean_array_fset(v_source_2442_, v_i_2441_, v___x_2447_);
v_target_2449_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4___redArg(v_target_2443_, v_es_2446_);
v___x_2450_ = lean_unsigned_to_nat(1u);
v___x_2451_ = lean_nat_add(v_i_2441_, v___x_2450_);
lean_dec(v_i_2441_);
v_i_2441_ = v___x_2451_;
v_source_2442_ = v_source_2448_;
v_target_2443_ = v_target_2449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1___redArg(lean_object* v_data_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v_nbuckets_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2454_ = lean_array_get_size(v_data_2453_);
v___x_2455_ = lean_unsigned_to_nat(2u);
v_nbuckets_2456_ = lean_nat_mul(v___x_2454_, v___x_2455_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_box(0);
v___x_2459_ = lean_mk_array(v_nbuckets_2456_, v___x_2458_);
v___x_2460_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3___redArg(v___x_2457_, v_data_2453_, v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1___redArg(lean_object* v_m_2461_, lean_object* v_a_2462_, lean_object* v_b_2463_){
_start:
{
lean_object* v_size_2464_; lean_object* v_buckets_2465_; lean_object* v___x_2466_; uint64_t v___x_2467_; uint64_t v___x_2468_; uint64_t v___x_2469_; uint64_t v_fold_2470_; uint64_t v___x_2471_; uint64_t v___x_2472_; uint64_t v___x_2473_; size_t v___x_2474_; size_t v___x_2475_; size_t v___x_2476_; size_t v___x_2477_; size_t v___x_2478_; lean_object* v_bkt_2479_; uint8_t v___x_2480_; 
v_size_2464_ = lean_ctor_get(v_m_2461_, 0);
v_buckets_2465_ = lean_ctor_get(v_m_2461_, 1);
v___x_2466_ = lean_array_get_size(v_buckets_2465_);
v___x_2467_ = l_Lean_instHashableFVarId_hash(v_a_2462_);
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
v_bkt_2479_ = lean_array_uget_borrowed(v_buckets_2465_, v___x_2478_);
v___x_2480_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_2462_, v_bkt_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2501_; 
lean_inc_ref(v_buckets_2465_);
lean_inc(v_size_2464_);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_m_2461_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; lean_object* v_unused_2503_; 
v_unused_2502_ = lean_ctor_get(v_m_2461_, 1);
lean_dec(v_unused_2502_);
v_unused_2503_ = lean_ctor_get(v_m_2461_, 0);
lean_dec(v_unused_2503_);
v___x_2482_ = v_m_2461_;
v_isShared_2483_ = v_isSharedCheck_2501_;
goto v_resetjp_2481_;
}
else
{
lean_dec(v_m_2461_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2501_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v_size_x27_2485_; lean_object* v___x_2486_; lean_object* v_buckets_x27_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2484_ = lean_unsigned_to_nat(1u);
v_size_x27_2485_ = lean_nat_add(v_size_2464_, v___x_2484_);
lean_dec(v_size_2464_);
lean_inc(v_bkt_2479_);
v___x_2486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2486_, 0, v_a_2462_);
lean_ctor_set(v___x_2486_, 1, v_b_2463_);
lean_ctor_set(v___x_2486_, 2, v_bkt_2479_);
v_buckets_x27_2487_ = lean_array_uset(v_buckets_2465_, v___x_2478_, v___x_2486_);
v___x_2488_ = lean_unsigned_to_nat(4u);
v___x_2489_ = lean_nat_mul(v_size_x27_2485_, v___x_2488_);
v___x_2490_ = lean_unsigned_to_nat(3u);
v___x_2491_ = lean_nat_div(v___x_2489_, v___x_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_array_get_size(v_buckets_x27_2487_);
v___x_2493_ = lean_nat_dec_le(v___x_2491_, v___x_2492_);
lean_dec(v___x_2491_);
if (v___x_2493_ == 0)
{
lean_object* v_val_2494_; lean_object* v___x_2496_; 
v_val_2494_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1___redArg(v_buckets_x27_2487_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_val_2494_);
lean_ctor_set(v___x_2482_, 0, v_size_x27_2485_);
v___x_2496_ = v___x_2482_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_size_x27_2485_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_val_2494_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
else
{
lean_object* v___x_2499_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_buckets_x27_2487_);
lean_ctor_set(v___x_2482_, 0, v_size_x27_2485_);
v___x_2499_ = v___x_2482_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_size_x27_2485_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_buckets_x27_2487_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_dec(v_b_2463_);
lean_dec(v_a_2462_);
return v_m_2461_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__3));
v___x_2511_ = l_Lean_stringToMessageData(v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__5));
v___x_2514_ = l_Lean_stringToMessageData(v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(lean_object* v_fvarId_2515_, lean_object* v_reason_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v___x_2524_; lean_object* v_owned_2525_; uint8_t v___x_2526_; 
v___x_2524_ = lean_st_ref_get(v_a_2518_);
v_owned_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc_ref(v_owned_2525_);
lean_dec(v___x_2524_);
v___x_2526_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_owned_2525_, v_fvarId_2515_);
lean_dec_ref(v_owned_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2582_; 
v___x_2527_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2));
v___x_2528_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(v___x_2527_, v_a_2521_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2582_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2582_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
uint8_t v___x_2533_; lean_object* v___y_2535_; uint8_t v___x_2552_; 
v___x_2533_ = 1;
v___x_2552_ = lean_unbox(v_a_2529_);
lean_dec(v_a_2529_);
if (v___x_2552_ == 0)
{
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec_ref(v_reason_2516_);
v___y_2535_ = v_a_2518_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_inc(v_fvarId_2515_);
v___x_2553_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___boxed), 7, 1);
lean_closure_set(v___x_2553_, 0, v_fvarId_2515_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
v___x_2554_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2553_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2554_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
v___x_2556_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString(v_reason_2516_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref(v___x_2556_);
v___x_2558_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4);
v___x_2559_ = l_Lean_MessageData_ofFormat(v_a_2555_);
v___x_2560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6);
v___x_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2560_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = l_Lean_stringToMessageData(v_a_2557_);
v___x_2564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(v___x_2527_, v___x_2564_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_dec_ref(v___x_2565_);
v___y_2535_ = v_a_2518_;
goto v___jp_2534_;
}
else
{
lean_del_object(v___x_2531_);
lean_dec(v_fvarId_2515_);
return v___x_2565_;
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2555_);
lean_del_object(v___x_2531_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_fvarId_2515_);
v_a_2566_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2556_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2556_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_del_object(v___x_2531_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec_ref(v_reason_2516_);
lean_dec(v_fvarId_2515_);
v_a_2574_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2554_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2554_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
v___jp_2534_:
{
lean_object* v___x_2536_; lean_object* v_owned_2537_; lean_object* v_paramMap_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2551_; 
v___x_2536_ = lean_st_ref_take(v___y_2535_);
v_owned_2537_ = lean_ctor_get(v___x_2536_, 0);
v_paramMap_2538_ = lean_ctor_get(v___x_2536_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2551_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_paramMap_2538_);
lean_inc(v_owned_2537_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2551_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2542_ = lean_box(0);
v___x_2543_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1___redArg(v_owned_2537_, v_fvarId_2515_, v___x_2542_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2543_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_paramMap_2538_);
v___x_2545_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
lean_ctor_set_uint8(v___x_2545_, sizeof(void*)*2, v___x_2533_);
v___x_2546_ = lean_st_ref_set(v___y_2535_, v___x_2545_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2542_);
v___x_2548_ = v___x_2531_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2542_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec_ref(v_reason_2516_);
lean_dec(v_fvarId_2515_);
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___boxed(lean_object* v_fvarId_2585_, lean_object* v_reason_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_2585_, v_reason_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1(lean_object* v_00_u03b2_2595_, lean_object* v_m_2596_, lean_object* v_a_2597_, lean_object* v_b_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1___redArg(v_m_2596_, v_a_2597_, v_b_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1(lean_object* v_00_u03b2_2600_, lean_object* v_data_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1___redArg(v_data_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2603_, lean_object* v_i_2604_, lean_object* v_source_2605_, lean_object* v_target_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3___redArg(v_i_2604_, v_source_2605_, v_target_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2608_, lean_object* v_x_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4___redArg(v_x_2609_, v_x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0(void){
_start:
{
uint8_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = 1;
v___x_2613_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(lean_object* v_upperBound_2614_, lean_object* v_args_2615_, lean_object* v_ps_2616_, lean_object* v_reason_2617_, lean_object* v_a_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_a_2628_; uint8_t v___x_2632_; 
v___x_2632_ = lean_nat_dec_lt(v_a_2618_, v_upperBound_2614_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v_a_2618_);
lean_dec_ref(v_reason_2617_);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_b_2619_);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_array_fget_borrowed(v_args_2615_, v_a_2618_);
if (lean_obj_tag(v___x_2635_) == 1)
{
lean_object* v_fvarId_2636_; lean_object* v___x_2637_; 
v_fvarId_2636_ = lean_ctor_get(v___x_2635_, 0);
v___x_2637_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_2636_, v___y_2621_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; uint8_t v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = lean_unbox(v_a_2638_);
lean_dec(v_a_2638_);
if (v___x_2639_ == 0)
{
v_a_2628_ = v___x_2634_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_fvarId_2642_; lean_object* v___x_2643_; 
v___x_2640_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0);
v___x_2641_ = lean_array_get_borrowed(v___x_2640_, v_ps_2616_, v_a_2618_);
v_fvarId_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v___y_2625_);
lean_inc_ref(v___y_2624_);
lean_inc(v___y_2623_);
lean_inc_ref(v___y_2622_);
lean_inc_ref(v_reason_2617_);
lean_inc(v_fvarId_2642_);
v___x_2643_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_2642_, v_reason_2617_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_dec_ref(v___x_2643_);
v_a_2628_ = v___x_2634_;
goto v___jp_2627_;
}
else
{
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v_a_2618_);
lean_dec_ref(v_reason_2617_);
return v___x_2643_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v_a_2618_);
lean_dec_ref(v_reason_2617_);
v_a_2644_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2637_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2637_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
v_a_2628_ = v___x_2634_;
goto v___jp_2627_;
}
}
v___jp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_add(v_a_2618_, v___x_2629_);
lean_dec(v_a_2618_);
v_a_2618_ = v___x_2630_;
v_b_2619_ = v_a_2628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___boxed(lean_object* v_upperBound_2652_, lean_object* v_args_2653_, lean_object* v_ps_2654_, lean_object* v_reason_2655_, lean_object* v_a_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(v_upperBound_2652_, v_args_2653_, v_ps_2654_, v_reason_2655_, v_a_2656_, v_b_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec_ref(v_ps_2654_);
lean_dec_ref(v_args_2653_);
lean_dec(v_upperBound_2652_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(lean_object* v_args_2666_, lean_object* v_ps_2667_, lean_object* v_reason_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_array_get_size(v_args_2666_);
v___x_2678_ = lean_box(0);
v___x_2679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(v___x_2677_, v_args_2666_, v_ps_2667_, v_reason_2668_, v___x_2676_, v___x_2678_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2679_, 0);
lean_dec(v_unused_2687_);
v___x_2681_ = v___x_2679_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v___x_2679_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2678_);
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2678_);
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
return v___x_2679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs___boxed(lean_object* v_args_2688_, lean_object* v_ps_2689_, lean_object* v_reason_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(v_args_2688_, v_ps_2689_, v_reason_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec_ref(v_ps_2689_);
lean_dec_ref(v_args_2688_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0(lean_object* v_upperBound_2699_, lean_object* v_args_2700_, lean_object* v_ps_2701_, lean_object* v_reason_2702_, lean_object* v_inst_2703_, lean_object* v_R_2704_, lean_object* v_a_2705_, lean_object* v_b_2706_, lean_object* v_c_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(v_upperBound_2699_, v_args_2700_, v_ps_2701_, v_reason_2702_, v_a_2705_, v_b_2706_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___boxed(lean_object* v_upperBound_2716_, lean_object* v_args_2717_, lean_object* v_ps_2718_, lean_object* v_reason_2719_, lean_object* v_inst_2720_, lean_object* v_R_2721_, lean_object* v_a_2722_, lean_object* v_b_2723_, lean_object* v_c_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0(v_upperBound_2716_, v_args_2717_, v_ps_2718_, v_reason_2719_, v_inst_2720_, v_R_2721_, v_a_2722_, v_b_2723_, v_c_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v_ps_2718_);
lean_dec_ref(v_args_2717_);
lean_dec(v_upperBound_2716_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0(lean_object* v_reason_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_x_2734_, v_reason_2733_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0___boxed(lean_object* v_reason_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0(v_reason_2743_, v_x_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(lean_object* v_msg_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v_toApplicative_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2826_; 
v___x_2761_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_2762_ = l_ReaderT_instMonad___redArg(v___x_2761_);
v_toApplicative_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2762_, 1);
lean_dec(v_unused_2827_);
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2826_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_toApplicative_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2826_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_toFunctor_2767_; lean_object* v_toSeq_2768_; lean_object* v_toSeqLeft_2769_; lean_object* v_toSeqRight_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2824_; 
v_toFunctor_2767_ = lean_ctor_get(v_toApplicative_2763_, 0);
v_toSeq_2768_ = lean_ctor_get(v_toApplicative_2763_, 2);
v_toSeqLeft_2769_ = lean_ctor_get(v_toApplicative_2763_, 3);
v_toSeqRight_2770_ = lean_ctor_get(v_toApplicative_2763_, 4);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_toApplicative_2763_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; 
v_unused_2825_ = lean_ctor_get(v_toApplicative_2763_, 1);
lean_dec(v_unused_2825_);
v___x_2772_ = v_toApplicative_2763_;
v_isShared_2773_ = v_isSharedCheck_2824_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_toSeqRight_2770_);
lean_inc(v_toSeqLeft_2769_);
lean_inc(v_toSeq_2768_);
lean_inc(v_toFunctor_2767_);
lean_dec(v_toApplicative_2763_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2824_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___f_2774_; lean_object* v___f_2775_; lean_object* v___f_2776_; lean_object* v___f_2777_; lean_object* v___x_2778_; lean_object* v___f_2779_; lean_object* v___f_2780_; lean_object* v___f_2781_; lean_object* v___x_2783_; 
v___f_2774_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_2775_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2767_);
v___f_2776_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2776_, 0, v_toFunctor_2767_);
v___f_2777_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2777_, 0, v_toFunctor_2767_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___f_2776_);
lean_ctor_set(v___x_2778_, 1, v___f_2777_);
v___f_2779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2779_, 0, v_toSeqRight_2770_);
v___f_2780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2780_, 0, v_toSeqLeft_2769_);
v___f_2781_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2781_, 0, v_toSeq_2768_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v___f_2779_);
lean_ctor_set(v___x_2772_, 3, v___f_2780_);
lean_ctor_set(v___x_2772_, 2, v___f_2781_);
lean_ctor_set(v___x_2772_, 1, v___f_2774_);
lean_ctor_set(v___x_2772_, 0, v___x_2778_);
v___x_2783_ = v___x_2772_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v___f_2774_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v___f_2781_);
lean_ctor_set(v_reuseFailAlloc_2823_, 3, v___f_2780_);
lean_ctor_set(v_reuseFailAlloc_2823_, 4, v___f_2779_);
v___x_2783_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2785_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___f_2775_);
lean_ctor_set(v___x_2765_, 0, v___x_2783_);
v___x_2785_ = v___x_2765_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___f_2775_);
v___x_2785_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v_toApplicative_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2820_; 
v___x_2786_ = l_ReaderT_instMonad___redArg(v___x_2785_);
v_toApplicative_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v___x_2786_, 1);
lean_dec(v_unused_2821_);
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2820_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_toApplicative_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2820_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v_toFunctor_2791_; lean_object* v_toSeq_2792_; lean_object* v_toSeqLeft_2793_; lean_object* v_toSeqRight_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2818_; 
v_toFunctor_2791_ = lean_ctor_get(v_toApplicative_2787_, 0);
v_toSeq_2792_ = lean_ctor_get(v_toApplicative_2787_, 2);
v_toSeqLeft_2793_ = lean_ctor_get(v_toApplicative_2787_, 3);
v_toSeqRight_2794_ = lean_ctor_get(v_toApplicative_2787_, 4);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_toApplicative_2787_);
if (v_isSharedCheck_2818_ == 0)
{
lean_object* v_unused_2819_; 
v_unused_2819_ = lean_ctor_get(v_toApplicative_2787_, 1);
lean_dec(v_unused_2819_);
v___x_2796_ = v_toApplicative_2787_;
v_isShared_2797_ = v_isSharedCheck_2818_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_toSeqRight_2794_);
lean_inc(v_toSeqLeft_2793_);
lean_inc(v_toSeq_2792_);
lean_inc(v_toFunctor_2791_);
lean_dec(v_toApplicative_2787_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2818_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___f_2798_; lean_object* v___f_2799_; lean_object* v___f_2800_; lean_object* v___f_2801_; lean_object* v___x_2802_; lean_object* v___f_2803_; lean_object* v___f_2804_; lean_object* v___f_2805_; lean_object* v___x_2807_; 
v___f_2798_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_2799_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_2791_);
v___f_2800_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2800_, 0, v_toFunctor_2791_);
v___f_2801_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2801_, 0, v_toFunctor_2791_);
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___f_2800_);
lean_ctor_set(v___x_2802_, 1, v___f_2801_);
v___f_2803_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2803_, 0, v_toSeqRight_2794_);
v___f_2804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2804_, 0, v_toSeqLeft_2793_);
v___f_2805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2805_, 0, v_toSeq_2792_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 4, v___f_2803_);
lean_ctor_set(v___x_2796_, 3, v___f_2804_);
lean_ctor_set(v___x_2796_, 2, v___f_2805_);
lean_ctor_set(v___x_2796_, 1, v___f_2798_);
lean_ctor_set(v___x_2796_, 0, v___x_2802_);
v___x_2807_ = v___x_2796_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v___f_2798_);
lean_ctor_set(v_reuseFailAlloc_2817_, 2, v___f_2805_);
lean_ctor_set(v_reuseFailAlloc_2817_, 3, v___f_2804_);
lean_ctor_set(v_reuseFailAlloc_2817_, 4, v___f_2803_);
v___x_2807_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 1, v___f_2799_);
lean_ctor_set(v___x_2789_, 0, v___x_2807_);
v___x_2809_ = v___x_2789_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v___f_2799_);
v___x_2809_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_915__overap_2814_; lean_object* v___x_2815_; 
v___x_2810_ = l_ReaderT_instMonad___redArg(v___x_2809_);
v___x_2811_ = l_ReaderT_instMonad___redArg(v___x_2810_);
v___x_2812_ = lean_box(0);
v___x_2813_ = l_instInhabitedOfMonad___redArg(v___x_2811_, v___x_2812_);
v___x_915__overap_2814_ = lean_panic_fn(v___x_2813_, v_msg_2753_);
v___x_2815_ = lean_apply_7(v___x_915__overap_2814_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
return v___x_2815_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v_msg_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
return v_res_2836_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2839_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_2840_ = lean_unsigned_to_nat(40u);
v___x_2841_ = lean_unsigned_to_nat(49u);
v___x_2842_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__1));
v___x_2843_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__0));
v___x_2844_ = l_mkPanicMessageWithDecl(v___x_2843_, v___x_2842_, v___x_2841_, v___x_2840_, v___x_2839_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(lean_object* v_f_2845_, lean_object* v_e_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_ty_2855_; lean_object* v_body_2856_; uint8_t v___x_2859_; 
v___x_2859_ = l_Lean_Expr_hasFVar(v_e_2846_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_e_2846_);
lean_dec_ref(v_f_2845_);
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
else
{
switch(lean_obj_tag(v_e_2846_))
{
case 1:
{
lean_object* v_fvarId_2862_; lean_object* v___x_2863_; 
v_fvarId_2862_ = lean_ctor_get(v_e_2846_, 0);
lean_inc(v_fvarId_2862_);
lean_dec_ref(v_e_2846_);
v___x_2863_ = lean_apply_8(v_f_2845_, v_fvarId_2862_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, lean_box(0));
return v___x_2863_;
}
case 2:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v_e_2846_);
lean_dec_ref(v_f_2845_);
v___x_2864_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2);
v___x_2865_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v___x_2864_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2865_;
}
case 5:
{
lean_object* v_fn_2866_; lean_object* v_arg_2867_; lean_object* v___x_2868_; 
v_fn_2866_ = lean_ctor_get(v_e_2846_, 0);
lean_inc_ref(v_fn_2866_);
v_arg_2867_ = lean_ctor_get(v_e_2846_, 1);
lean_inc_ref(v_arg_2867_);
lean_dec_ref(v_e_2846_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc_ref(v_f_2845_);
v___x_2868_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2845_, v_fn_2866_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_dec_ref(v___x_2868_);
v_e_2846_ = v_arg_2867_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2867_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_f_2845_);
return v___x_2868_;
}
}
case 6:
{
lean_object* v_binderType_2870_; lean_object* v_body_2871_; 
v_binderType_2870_ = lean_ctor_get(v_e_2846_, 1);
lean_inc_ref(v_binderType_2870_);
v_body_2871_ = lean_ctor_get(v_e_2846_, 2);
lean_inc_ref(v_body_2871_);
lean_dec_ref(v_e_2846_);
v_ty_2855_ = v_binderType_2870_;
v_body_2856_ = v_body_2871_;
goto v___jp_2854_;
}
case 7:
{
lean_object* v_binderType_2872_; lean_object* v_body_2873_; 
v_binderType_2872_ = lean_ctor_get(v_e_2846_, 1);
lean_inc_ref(v_binderType_2872_);
v_body_2873_ = lean_ctor_get(v_e_2846_, 2);
lean_inc_ref(v_body_2873_);
lean_dec_ref(v_e_2846_);
v_ty_2855_ = v_binderType_2872_;
v_body_2856_ = v_body_2873_;
goto v___jp_2854_;
}
case 8:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_dec_ref(v_e_2846_);
lean_dec_ref(v_f_2845_);
v___x_2874_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2);
v___x_2875_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v___x_2874_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2875_;
}
case 11:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v_e_2846_);
lean_dec_ref(v_f_2845_);
v___x_2876_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2);
v___x_2877_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v___x_2876_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2877_;
}
default: 
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_e_2846_);
lean_dec_ref(v_f_2845_);
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
}
v___jp_2854_:
{
lean_object* v___x_2857_; 
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc_ref(v_f_2845_);
v___x_2857_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2845_, v_ty_2855_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref(v___x_2857_);
v_e_2846_ = v_body_2856_;
goto _start;
}
else
{
lean_dec_ref(v_body_2856_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_f_2845_);
return v___x_2857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___boxed(lean_object* v_f_2880_, lean_object* v_e_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2880_, v_e_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(lean_object* v_f_2890_, lean_object* v_arg_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
switch(lean_obj_tag(v_arg_2891_))
{
case 0:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v_f_2890_);
v___x_2899_ = lean_box(0);
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
return v___x_2900_;
}
case 1:
{
lean_object* v_fvarId_2901_; lean_object* v___x_2902_; 
v_fvarId_2901_ = lean_ctor_get(v_arg_2891_, 0);
lean_inc(v_fvarId_2901_);
lean_dec_ref(v_arg_2891_);
v___x_2902_ = lean_apply_8(v_f_2890_, v_fvarId_2901_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, lean_box(0));
return v___x_2902_;
}
default: 
{
lean_object* v_expr_2903_; lean_object* v___x_2904_; 
v_expr_2903_ = lean_ctor_get(v_arg_2891_, 0);
lean_inc_ref(v_expr_2903_);
lean_dec_ref(v_arg_2891_);
v___x_2904_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2890_, v_expr_2903_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v___x_2904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg___boxed(lean_object* v_f_2905_, lean_object* v_arg_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(v_f_2905_, v_arg_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(lean_object* v_reason_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v___f_2924_; lean_object* v___x_2925_; 
v___f_2924_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2924_, 0, v_reason_2915_);
v___x_2925_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(v___f_2924_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___boxed(lean_object* v_reason_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(v_reason_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0(uint8_t v_pu_2936_, lean_object* v_f_2937_, lean_object* v_arg_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(v_f_2937_, v_arg_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___boxed(lean_object* v_pu_2947_, lean_object* v_f_2948_, lean_object* v_arg_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
uint8_t v_pu_boxed_2957_; lean_object* v_res_2958_; 
v_pu_boxed_2957_ = lean_unbox(v_pu_2947_);
v_res_2958_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0(v_pu_boxed_2957_, v_f_2948_, v_arg_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(lean_object* v_upperBound_2959_, lean_object* v_ps_2960_, lean_object* v_args_2961_, lean_object* v_reason_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_a_2973_; uint8_t v___x_2977_; 
v___x_2977_ = lean_nat_dec_lt(v_a_2963_, v_upperBound_2959_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_a_2963_);
lean_dec_ref(v_reason_2962_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_b_2964_);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_type_2981_; uint8_t v_borrow_2982_; lean_object* v___x_2983_; 
v___x_2979_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0);
v___x_2980_ = lean_array_get_borrowed(v___x_2979_, v_ps_2960_, v_a_2963_);
v_type_2981_ = lean_ctor_get(v___x_2980_, 2);
v_borrow_2982_ = lean_ctor_get_uint8(v___x_2980_, sizeof(void*)*3);
v___x_2983_ = lean_box(0);
if (v_borrow_2982_ == 0)
{
uint8_t v___x_2984_; 
v___x_2984_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_2981_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_array_fget_borrowed(v_args_2961_, v_a_2963_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___x_2985_);
lean_inc_ref(v_reason_2962_);
v___x_2986_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(v_reason_2962_, v___x_2985_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_dec_ref(v___x_2986_);
v_a_2973_ = v___x_2983_;
goto v___jp_2972_;
}
else
{
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_a_2963_);
lean_dec_ref(v_reason_2962_);
return v___x_2986_;
}
}
else
{
v_a_2973_ = v___x_2983_;
goto v___jp_2972_;
}
}
else
{
v_a_2973_ = v___x_2983_;
goto v___jp_2972_;
}
}
v___jp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = lean_unsigned_to_nat(1u);
v___x_2975_ = lean_nat_add(v_a_2963_, v___x_2974_);
lean_dec(v_a_2963_);
v_a_2963_ = v___x_2975_;
v_b_2964_ = v_a_2973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg___boxed(lean_object* v_upperBound_2987_, lean_object* v_ps_2988_, lean_object* v_args_2989_, lean_object* v_reason_2990_, lean_object* v_a_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(v_upperBound_2987_, v_ps_2988_, v_args_2989_, v_reason_2990_, v_a_2991_, v_b_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec_ref(v_args_2989_);
lean_dec_ref(v_ps_2988_);
lean_dec(v_upperBound_2987_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(lean_object* v_args_3001_, lean_object* v_ps_3002_, lean_object* v_reason_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_array_get_size(v_args_3001_);
v___x_3013_ = lean_box(0);
v___x_3014_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(v___x_3012_, v_ps_3002_, v_args_3001_, v_reason_3003_, v___x_3011_, v___x_3013_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; 
v_unused_3022_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3022_);
v___x_3016_ = v___x_3014_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3014_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3013_);
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3013_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
else
{
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams___boxed(lean_object* v_args_3023_, lean_object* v_ps_3024_, lean_object* v_reason_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(v_args_3023_, v_ps_3024_, v_reason_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec_ref(v_ps_3024_);
lean_dec_ref(v_args_3023_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0(lean_object* v_upperBound_3034_, lean_object* v_ps_3035_, lean_object* v_args_3036_, lean_object* v_reason_3037_, lean_object* v_inst_3038_, lean_object* v_R_3039_, lean_object* v_a_3040_, lean_object* v_b_3041_, lean_object* v_c_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(v_upperBound_3034_, v_ps_3035_, v_args_3036_, v_reason_3037_, v_a_3040_, v_b_3041_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___boxed(lean_object* v_upperBound_3051_, lean_object* v_ps_3052_, lean_object* v_args_3053_, lean_object* v_reason_3054_, lean_object* v_inst_3055_, lean_object* v_R_3056_, lean_object* v_a_3057_, lean_object* v_b_3058_, lean_object* v_c_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0(v_upperBound_3051_, v_ps_3052_, v_args_3053_, v_reason_3054_, v_inst_3055_, v_R_3056_, v_a_3057_, v_b_3058_, v_c_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec_ref(v_args_3053_);
lean_dec_ref(v_ps_3052_);
lean_dec(v_upperBound_3051_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(lean_object* v_msg_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_options_3074_; lean_object* v_ref_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_options_3074_ = lean_ctor_get(v___y_3071_, 2);
v_ref_3075_ = lean_ctor_get(v___y_3071_, 5);
v___x_3076_ = lean_st_ref_get(v___y_3072_);
v___x_3077_ = lean_st_ref_get(v___y_3070_);
v___x_3078_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3069_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3101_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3101_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3101_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v_env_3083_; lean_object* v_lctx_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3099_; 
v_env_3083_ = lean_ctor_get(v___x_3076_, 0);
lean_inc_ref(v_env_3083_);
lean_dec(v___x_3076_);
v_lctx_3084_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3077_, 1);
lean_dec(v_unused_3100_);
v___x_3086_ = v___x_3077_;
v_isShared_3087_ = v_isSharedCheck_3099_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_lctx_3084_);
lean_dec(v___x_3077_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3099_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3088_ = lean_unbox(v_a_3079_);
lean_dec(v_a_3079_);
v___x_3089_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3084_, v___x_3088_);
lean_dec_ref(v_lctx_3084_);
v___x_3090_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2);
lean_inc_ref(v_options_3074_);
v___x_3091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3091_, 0, v_env_3083_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
lean_ctor_set(v___x_3091_, 2, v___x_3089_);
lean_ctor_set(v___x_3091_, 3, v_options_3074_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set_tag(v___x_3086_, 3);
lean_ctor_set(v___x_3086_, 1, v_msg_3068_);
lean_ctor_set(v___x_3086_, 0, v___x_3091_);
v___x_3093_ = v___x_3086_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_msg_3068_);
v___x_3093_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_inc(v_ref_3075_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_ref_3075_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 1);
lean_ctor_set(v___x_3081_, 0, v___x_3094_);
v___x_3096_ = v___x_3081_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
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
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v___x_3077_);
lean_dec(v___x_3076_);
lean_dec_ref(v_msg_3068_);
v_a_3102_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3078_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3078_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg___boxed(lean_object* v_msg_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(v_msg_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0(lean_object* v_00_u03b1_3117_, lean_object* v_msg_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(v_msg_3118_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___boxed(lean_object* v_00_u03b1_3127_, lean_object* v_msg_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0(v_00_u03b1_3127_, v_msg_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1(lean_object* v_msg_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v_toApplicative_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3210_; 
v___x_3145_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_3146_ = l_ReaderT_instMonad___redArg(v___x_3145_);
v_toApplicative_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v___x_3146_, 1);
lean_dec(v_unused_3211_);
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3210_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_toApplicative_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3210_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_toFunctor_3151_; lean_object* v_toSeq_3152_; lean_object* v_toSeqLeft_3153_; lean_object* v_toSeqRight_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3208_; 
v_toFunctor_3151_ = lean_ctor_get(v_toApplicative_3147_, 0);
v_toSeq_3152_ = lean_ctor_get(v_toApplicative_3147_, 2);
v_toSeqLeft_3153_ = lean_ctor_get(v_toApplicative_3147_, 3);
v_toSeqRight_3154_ = lean_ctor_get(v_toApplicative_3147_, 4);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_toApplicative_3147_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_toApplicative_3147_, 1);
lean_dec(v_unused_3209_);
v___x_3156_ = v_toApplicative_3147_;
v_isShared_3157_ = v_isSharedCheck_3208_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_toSeqRight_3154_);
lean_inc(v_toSeqLeft_3153_);
lean_inc(v_toSeq_3152_);
lean_inc(v_toFunctor_3151_);
lean_dec(v_toApplicative_3147_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3208_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___f_3158_; lean_object* v___f_3159_; lean_object* v___f_3160_; lean_object* v___f_3161_; lean_object* v___x_3162_; lean_object* v___f_3163_; lean_object* v___f_3164_; lean_object* v___f_3165_; lean_object* v___x_3167_; 
v___f_3158_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_3159_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_3151_);
v___f_3160_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3160_, 0, v_toFunctor_3151_);
v___f_3161_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3161_, 0, v_toFunctor_3151_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___f_3160_);
lean_ctor_set(v___x_3162_, 1, v___f_3161_);
v___f_3163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3163_, 0, v_toSeqRight_3154_);
v___f_3164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3164_, 0, v_toSeqLeft_3153_);
v___f_3165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3165_, 0, v_toSeq_3152_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 4, v___f_3163_);
lean_ctor_set(v___x_3156_, 3, v___f_3164_);
lean_ctor_set(v___x_3156_, 2, v___f_3165_);
lean_ctor_set(v___x_3156_, 1, v___f_3158_);
lean_ctor_set(v___x_3156_, 0, v___x_3162_);
v___x_3167_ = v___x_3156_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___f_3158_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v___f_3165_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v___f_3164_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v___f_3163_);
v___x_3167_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v___f_3159_);
lean_ctor_set(v___x_3149_, 0, v___x_3167_);
v___x_3169_ = v___x_3149_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___f_3159_);
v___x_3169_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v_toApplicative_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3204_; 
v___x_3170_ = l_ReaderT_instMonad___redArg(v___x_3169_);
v_toApplicative_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; 
v_unused_3205_ = lean_ctor_get(v___x_3170_, 1);
lean_dec(v_unused_3205_);
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3204_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_toApplicative_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3204_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_toFunctor_3175_; lean_object* v_toSeq_3176_; lean_object* v_toSeqLeft_3177_; lean_object* v_toSeqRight_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3202_; 
v_toFunctor_3175_ = lean_ctor_get(v_toApplicative_3171_, 0);
v_toSeq_3176_ = lean_ctor_get(v_toApplicative_3171_, 2);
v_toSeqLeft_3177_ = lean_ctor_get(v_toApplicative_3171_, 3);
v_toSeqRight_3178_ = lean_ctor_get(v_toApplicative_3171_, 4);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_toApplicative_3171_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v_toApplicative_3171_, 1);
lean_dec(v_unused_3203_);
v___x_3180_ = v_toApplicative_3171_;
v_isShared_3181_ = v_isSharedCheck_3202_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_toSeqRight_3178_);
lean_inc(v_toSeqLeft_3177_);
lean_inc(v_toSeq_3176_);
lean_inc(v_toFunctor_3175_);
lean_dec(v_toApplicative_3171_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3202_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; lean_object* v___x_3191_; 
v___f_3182_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_3183_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_3175_);
v___f_3184_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3184_, 0, v_toFunctor_3175_);
v___f_3185_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3185_, 0, v_toFunctor_3175_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___f_3184_);
lean_ctor_set(v___x_3186_, 1, v___f_3185_);
v___f_3187_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3187_, 0, v_toSeqRight_3178_);
v___f_3188_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3188_, 0, v_toSeqLeft_3177_);
v___f_3189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3189_, 0, v_toSeq_3176_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 4, v___f_3187_);
lean_ctor_set(v___x_3180_, 3, v___f_3188_);
lean_ctor_set(v___x_3180_, 2, v___f_3189_);
lean_ctor_set(v___x_3180_, 1, v___f_3182_);
lean_ctor_set(v___x_3180_, 0, v___x_3186_);
v___x_3191_ = v___x_3180_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___f_3182_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v___f_3189_);
lean_ctor_set(v_reuseFailAlloc_3201_, 3, v___f_3188_);
lean_ctor_set(v_reuseFailAlloc_3201_, 4, v___f_3187_);
v___x_3191_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3193_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___f_3183_);
lean_ctor_set(v___x_3173_, 0, v___x_3191_);
v___x_3193_ = v___x_3173_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___f_3183_);
v___x_3193_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___f_3197_; lean_object* v___x_3957__overap_3198_; lean_object* v___x_3199_; 
v___x_3194_ = l_ReaderT_instMonad___redArg(v___x_3193_);
v___x_3195_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0);
v___x_3196_ = l_instInhabitedOfMonad___redArg(v___x_3194_, v___x_3195_);
v___f_3197_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3197_, 0, v___x_3196_);
v___x_3957__overap_3198_ = lean_panic_fn(v___f_3197_, v_msg_3137_);
v___x_3199_ = lean_apply_7(v___x_3957__overap_3198_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, lean_box(0));
return v___x_3199_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1___boxed(lean_object* v_msg_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1(v_msg_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v_res_3220_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__0));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3225_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_3226_ = lean_unsigned_to_nat(26u);
v___x_3227_ = lean_unsigned_to_nat(261u);
v___x_3228_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__2));
v___x_3229_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0));
v___x_3230_ = l_mkPanicMessageWithDecl(v___x_3229_, v___x_3228_, v___x_3227_, v___x_3226_, v___x_3225_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(lean_object* v_k_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v___x_3239_; lean_object* v_paramMap_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_st_ref_get(v_a_3233_);
v_paramMap_3240_ = lean_ctor_get(v___x_3239_, 1);
lean_inc_ref(v_paramMap_3240_);
lean_dec(v___x_3239_);
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_paramMap_3240_, v_k_3231_);
lean_dec_ref(v_paramMap_3240_);
if (lean_obj_tag(v___x_3241_) == 0)
{
if (lean_obj_tag(v_k_3231_) == 0)
{
lean_object* v_name_3242_; lean_object* v___x_3243_; 
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
v_name_3242_ = lean_ctor_get(v_k_3231_, 0);
lean_inc(v_name_3242_);
lean_dec_ref(v_k_3231_);
lean_inc(v_name_3242_);
v___x_3243_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_name_3242_, v_a_3237_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3257_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3257_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3257_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
if (lean_obj_tag(v_a_3244_) == 1)
{
lean_object* v_val_3248_; lean_object* v_params_3249_; lean_object* v___x_3251_; 
lean_dec(v_name_3242_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
v_val_3248_ = lean_ctor_get(v_a_3244_, 0);
lean_inc(v_val_3248_);
lean_dec_ref(v_a_3244_);
v_params_3249_ = lean_ctor_get(v_val_3248_, 3);
lean_inc_ref(v_params_3249_);
lean_dec(v_val_3248_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v_params_3249_);
v___x_3251_ = v___x_3246_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_params_3249_);
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
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_del_object(v___x_3246_);
lean_dec(v_a_3244_);
v___x_3253_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1);
v___x_3254_ = l_Lean_MessageData_ofName(v_name_3242_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(v___x_3255_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
return v___x_3256_;
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_name_3242_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
v_a_3258_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3243_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3243_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_dec_ref(v_k_3231_);
v___x_3266_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3);
v___x_3267_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1(v___x_3266_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
return v___x_3267_;
}
}
else
{
lean_object* v_val_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec_ref(v_k_3231_);
v_val_3268_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3241_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_val_3268_);
lean_dec(v___x_3241_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
lean_ctor_set_tag(v___x_3270_, 0);
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_val_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___boxed(lean_object* v_k_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v_k_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall(lean_object* v_x_3285_, lean_object* v_v_3286_, lean_object* v_k_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
if (lean_obj_tag(v_v_3286_) == 9)
{
lean_object* v_fn_3298_; lean_object* v_args_3299_; uint8_t v___y_3301_; 
v_fn_3298_ = lean_ctor_get(v_v_3286_, 0);
v_args_3299_ = lean_ctor_get(v_v_3286_, 1);
if (lean_obj_tag(v_k_3287_) == 5)
{
lean_object* v_fvarId_3317_; lean_object* v_currDecl_3318_; uint8_t v___x_3319_; 
v_fvarId_3317_ = lean_ctor_get(v_k_3287_, 0);
v_currDecl_3318_ = lean_ctor_get(v_a_3288_, 1);
v___x_3319_ = lean_name_eq(v_currDecl_3318_, v_fn_3298_);
if (v___x_3319_ == 0)
{
v___y_3301_ = v___x_3319_;
goto v___jp_3300_;
}
else
{
uint8_t v___x_3320_; 
v___x_3320_ = l_Lean_instBEqFVarId_beq(v_x_3285_, v_fvarId_3317_);
v___y_3301_ = v___x_3320_;
goto v___jp_3300_;
}
}
else
{
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
goto v___jp_3295_;
}
v___jp_3300_:
{
if (v___y_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
return v___x_3303_;
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_inc(v_fn_3298_);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v_fn_3298_);
lean_inc(v_a_3293_);
lean_inc_ref(v_a_3292_);
lean_inc(v_a_3291_);
lean_inc_ref(v_a_3290_);
lean_inc(v_a_3289_);
lean_inc_ref(v_a_3288_);
v___x_3305_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v___x_3304_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
lean_inc(v_fn_3298_);
v___x_3307_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3307_, 0, v_fn_3298_);
v___x_3308_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(v_args_3299_, v_a_3306_, v___x_3307_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3306_);
return v___x_3308_;
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
v_a_3309_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3305_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3305_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
goto v___jp_3295_;
}
v___jp_3295_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall___boxed(lean_object* v_x_3321_, lean_object* v_v_3322_, lean_object* v_k_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall(v_x_3321_, v_v_3322_, v_k_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
lean_dec_ref(v_k_3323_);
lean_dec(v_v_3322_);
lean_dec(v_x_3321_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(lean_object* v_reason_3332_, lean_object* v_as_3333_, size_t v_i_3334_, size_t v_stop_3335_, lean_object* v_b_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
uint8_t v___x_3344_; 
v___x_3344_ = lean_usize_dec_eq(v_i_3334_, v_stop_3335_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = lean_array_uget_borrowed(v_as_3333_, v_i_3334_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc(v___y_3340_);
lean_inc_ref(v___y_3339_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___x_3345_);
lean_inc_ref(v_reason_3332_);
v___x_3346_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(v_reason_3332_, v___x_3345_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; size_t v___x_3348_; size_t v___x_3349_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = ((size_t)1ULL);
v___x_3349_ = lean_usize_add(v_i_3334_, v___x_3348_);
v_i_3334_ = v___x_3349_;
v_b_3336_ = v_a_3347_;
goto _start;
}
else
{
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v_reason_3332_);
return v___x_3346_;
}
}
else
{
lean_object* v___x_3351_; 
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v_reason_3332_);
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v_b_3336_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0___boxed(lean_object* v_reason_3352_, lean_object* v_as_3353_, lean_object* v_i_3354_, lean_object* v_stop_3355_, lean_object* v_b_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
size_t v_i_boxed_3364_; size_t v_stop_boxed_3365_; lean_object* v_res_3366_; 
v_i_boxed_3364_ = lean_unbox_usize(v_i_3354_);
lean_dec(v_i_3354_);
v_stop_boxed_3365_ = lean_unbox_usize(v_stop_3355_);
lean_dec(v_stop_3355_);
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(v_reason_3352_, v_as_3353_, v_i_boxed_3364_, v_stop_boxed_3365_, v_b_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec_ref(v_as_3353_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(lean_object* v_reason_3367_, lean_object* v_as_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3376_ = lean_unsigned_to_nat(0u);
v___x_3377_ = lean_array_get_size(v_as_3368_);
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_nat_dec_lt(v___x_3376_, v___x_3377_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; 
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec_ref(v_reason_3367_);
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
return v___x_3380_;
}
else
{
uint8_t v___x_3381_; 
v___x_3381_ = lean_nat_dec_le(v___x_3377_, v___x_3377_);
if (v___x_3381_ == 0)
{
if (v___x_3379_ == 0)
{
lean_object* v___x_3382_; 
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec_ref(v_reason_3367_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3378_);
return v___x_3382_;
}
else
{
size_t v___x_3383_; size_t v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = ((size_t)0ULL);
v___x_3384_ = lean_usize_of_nat(v___x_3377_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(v_reason_3367_, v_as_3368_, v___x_3383_, v___x_3384_, v___x_3378_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3385_;
}
}
else
{
size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = lean_usize_of_nat(v___x_3377_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(v_reason_3367_, v_as_3368_, v___x_3386_, v___x_3387_, v___x_3378_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs___boxed(lean_object* v_reason_3389_, lean_object* v_as_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(v_reason_3389_, v_as_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec_ref(v_as_3390_);
return v_res_3398_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(lean_object* v_k_3399_, lean_object* v_t_3400_){
_start:
{
if (lean_obj_tag(v_t_3400_) == 0)
{
lean_object* v_k_3401_; lean_object* v_l_3402_; lean_object* v_r_3403_; uint8_t v___x_3404_; 
v_k_3401_ = lean_ctor_get(v_t_3400_, 1);
v_l_3402_ = lean_ctor_get(v_t_3400_, 3);
v_r_3403_ = lean_ctor_get(v_t_3400_, 4);
v___x_3404_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3399_, v_k_3401_);
switch(v___x_3404_)
{
case 0:
{
v_t_3400_ = v_l_3402_;
goto _start;
}
case 1:
{
uint8_t v___x_3406_; 
v___x_3406_ = 1;
return v___x_3406_;
}
default: 
{
v_t_3400_ = v_r_3403_;
goto _start;
}
}
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = 0;
return v___x_3408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg___boxed(lean_object* v_k_3409_, lean_object* v_t_3410_){
_start:
{
uint8_t v_res_3411_; lean_object* v_r_3412_; 
v_res_3411_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(v_k_3409_, v_t_3410_);
lean_dec(v_t_3410_);
lean_dec(v_k_3409_);
v_r_3412_ = lean_box(v_res_3411_);
return v_r_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1(lean_object* v_z_3413_, lean_object* v_as_3414_, size_t v_sz_3415_, size_t v_i_3416_, lean_object* v_b_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_a_3426_; uint8_t v___x_3430_; 
v___x_3430_ = lean_usize_dec_lt(v_i_3416_, v_sz_3415_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; 
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v_z_3413_);
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v_b_3417_);
return v___x_3431_;
}
else
{
lean_object* v___x_3432_; lean_object* v_a_3433_; 
v___x_3432_ = lean_box(0);
v_a_3433_ = lean_array_uget(v_as_3414_, v_i_3416_);
if (lean_obj_tag(v_a_3433_) == 1)
{
lean_object* v_fvarId_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3444_; 
v_fvarId_3434_ = lean_ctor_get(v_a_3433_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3433_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3436_ = v_a_3433_;
v_isShared_3437_ = v_isSharedCheck_3444_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_fvarId_3434_);
lean_dec(v_a_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3444_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_paramSet_3438_; uint8_t v___x_3439_; 
v_paramSet_3438_ = lean_ctor_get(v___y_3418_, 2);
v___x_3439_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(v_fvarId_3434_, v_paramSet_3438_);
if (v___x_3439_ == 0)
{
lean_del_object(v___x_3436_);
lean_dec(v_fvarId_3434_);
v_a_3426_ = v___x_3432_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3441_; 
lean_inc(v_z_3413_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set_tag(v___x_3436_, 2);
lean_ctor_set(v___x_3436_, 0, v_z_3413_);
v___x_3441_ = v___x_3436_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_z_3413_);
v___x_3441_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3442_; 
lean_inc(v___y_3423_);
lean_inc_ref(v___y_3422_);
lean_inc(v___y_3421_);
lean_inc_ref(v___y_3420_);
v___x_3442_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_3434_, v___x_3441_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_dec_ref(v___x_3442_);
v_a_3426_ = v___x_3432_;
goto v___jp_3425_;
}
else
{
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v_z_3413_);
return v___x_3442_;
}
}
}
}
}
else
{
lean_dec(v_a_3433_);
v_a_3426_ = v___x_3432_;
goto v___jp_3425_;
}
}
v___jp_3425_:
{
size_t v___x_3427_; size_t v___x_3428_; 
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3416_, v___x_3427_);
v_i_3416_ = v___x_3428_;
v_b_3417_ = v_a_3426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1___boxed(lean_object* v_z_3445_, lean_object* v_as_3446_, lean_object* v_sz_3447_, lean_object* v_i_3448_, lean_object* v_b_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
size_t v_sz_boxed_3457_; size_t v_i_boxed_3458_; lean_object* v_res_3459_; 
v_sz_boxed_3457_ = lean_unbox_usize(v_sz_3447_);
lean_dec(v_sz_3447_);
v_i_boxed_3458_ = lean_unbox_usize(v_i_3448_);
lean_dec(v_i_3448_);
v_res_3459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1(v_z_3445_, v_as_3446_, v_sz_boxed_3457_, v_i_boxed_3458_, v_b_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_as_3446_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(lean_object* v_z_3460_, lean_object* v_args_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v___x_3469_; size_t v_sz_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3469_ = lean_box(0);
v_sz_3470_ = lean_array_size(v_args_3461_);
v___x_3471_ = ((size_t)0ULL);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1(v_z_3460_, v_args_3461_, v_sz_3470_, v___x_3471_, v___x_3469_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v___x_3472_, 0);
lean_dec(v_unused_3480_);
v___x_3474_ = v___x_3472_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_dec(v___x_3472_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3469_);
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3469_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
else
{
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam___boxed(lean_object* v_z_3481_, lean_object* v_args_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(v_z_3481_, v_args_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec_ref(v_args_3482_);
return v_res_3490_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0(lean_object* v_00_u03b2_3491_, lean_object* v_k_3492_, lean_object* v_t_3493_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(v_k_3492_, v_t_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___boxed(lean_object* v_00_u03b2_3495_, lean_object* v_k_3496_, lean_object* v_t_3497_){
_start:
{
uint8_t v_res_3498_; lean_object* v_r_3499_; 
v_res_3498_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0(v_00_u03b2_3495_, v_k_3496_, v_t_3497_);
lean_dec(v_t_3497_);
lean_dec(v_k_3496_);
v_r_3499_ = lean_box(v_res_3498_);
return v_r_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue(lean_object* v_z_3500_, lean_object* v_v_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
switch(lean_obj_tag(v_v_3501_))
{
case 11:
{
lean_object* v_var_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_var_3509_ = lean_ctor_get(v_v_3501_, 1);
lean_inc(v_var_3509_);
lean_dec_ref(v_v_3501_);
lean_inc(v_z_3500_);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_z_3500_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc_ref(v___x_3510_);
v___x_3511_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3500_, v___x_3510_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v___x_3512_; 
lean_dec_ref(v___x_3511_);
v___x_3512_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_var_3509_, v___x_3510_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v___x_3512_;
}
else
{
lean_dec_ref(v___x_3510_);
lean_dec(v_var_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v___x_3511_;
}
}
case 12:
{
lean_object* v_var_3513_; lean_object* v_args_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_var_3513_ = lean_ctor_get(v_v_3501_, 0);
lean_inc(v_var_3513_);
v_args_3514_ = lean_ctor_get(v_v_3501_, 2);
lean_inc_ref(v_args_3514_);
lean_dec_ref(v_v_3501_);
lean_inc(v_z_3500_);
v___x_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3515_, 0, v_z_3500_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc_ref(v___x_3515_);
lean_inc(v_z_3500_);
v___x_3516_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3500_, v___x_3515_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; 
lean_dec_ref(v___x_3516_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
v___x_3517_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_var_3513_, v___x_3515_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v___x_3518_; 
lean_dec_ref(v___x_3517_);
v___x_3518_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(v_z_3500_, v_args_3514_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec_ref(v_args_3514_);
return v___x_3518_;
}
else
{
lean_dec_ref(v_args_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
return v___x_3517_;
}
}
else
{
lean_dec_ref(v___x_3515_);
lean_dec_ref(v_args_3514_);
lean_dec(v_var_3513_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
return v___x_3516_;
}
}
case 5:
{
lean_object* v_args_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_args_3519_ = lean_ctor_get(v_v_3501_, 1);
lean_inc_ref(v_args_3519_);
lean_dec_ref(v_v_3501_);
lean_inc(v_z_3500_);
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_z_3500_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_z_3500_);
v___x_3521_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3500_, v___x_3520_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; 
lean_dec_ref(v___x_3521_);
v___x_3522_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(v_z_3500_, v_args_3519_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec_ref(v_args_3519_);
return v___x_3522_;
}
else
{
lean_dec_ref(v_args_3519_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
return v___x_3521_;
}
}
case 6:
{
lean_object* v_var_3523_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___x_3544_; lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3554_; 
v_var_3523_ = lean_ctor_get(v_v_3501_, 1);
lean_inc(v_var_3523_);
lean_dec_ref(v_v_3501_);
v___x_3544_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_var_3523_, v_a_3503_);
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3554_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3554_;
goto v_resetjp_3546_;
}
v___jp_3524_:
{
lean_object* v___x_3531_; lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3543_; 
v___x_3531_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_z_3500_, v___y_3526_);
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3543_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3543_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
uint8_t v___x_3536_; 
v___x_3536_ = lean_unbox(v_a_3532_);
lean_dec(v_a_3532_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v_var_3523_);
lean_dec(v_z_3500_);
v___x_3537_ = lean_box(0);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3537_);
v___x_3539_ = v___x_3534_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_del_object(v___x_3534_);
v___x_3541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_z_3500_);
v___x_3542_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_var_3523_, v___x_3541_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
return v___x_3542_;
}
}
}
v_resetjp_3546_:
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_unbox(v_a_3545_);
lean_dec(v_a_3545_);
if (v___x_3549_ == 0)
{
lean_del_object(v___x_3547_);
v___y_3525_ = v_a_3502_;
v___y_3526_ = v_a_3503_;
v___y_3527_ = v_a_3504_;
v___y_3528_ = v_a_3505_;
v___y_3529_ = v_a_3506_;
v___y_3530_ = v_a_3507_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3551_; 
lean_inc(v_z_3500_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set_tag(v___x_3547_, 3);
lean_ctor_set(v___x_3547_, 0, v_z_3500_);
v___x_3551_ = v___x_3547_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_z_3500_);
v___x_3551_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; 
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_z_3500_);
v___x_3552_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3500_, v___x_3551_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_dec_ref(v___x_3552_);
v___y_3525_ = v_a_3502_;
v___y_3526_ = v_a_3503_;
v___y_3527_ = v_a_3504_;
v___y_3528_ = v_a_3505_;
v___y_3529_ = v_a_3506_;
v___y_3530_ = v_a_3507_;
goto v___jp_3524_;
}
else
{
lean_dec(v_var_3523_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
return v___x_3552_;
}
}
}
}
}
case 9:
{
lean_object* v_fn_3555_; lean_object* v_args_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_fn_3555_ = lean_ctor_get(v_v_3501_, 0);
lean_inc(v_fn_3555_);
v_args_3556_ = lean_ctor_get(v_v_3501_, 1);
lean_inc_ref(v_args_3556_);
lean_dec_ref(v_v_3501_);
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_fn_3555_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_a_3503_);
lean_inc_ref(v_a_3502_);
v___x_3558_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v___x_3557_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref(v___x_3558_);
lean_inc(v_z_3500_);
v___x_3560_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3560_, 0, v_z_3500_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_z_3500_);
v___x_3561_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3500_, v___x_3560_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3569_; 
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v___x_3561_, 0);
lean_dec(v_unused_3570_);
v___x_3563_ = v___x_3561_;
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
else
{
lean_dec(v___x_3561_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 5);
lean_ctor_set(v___x_3563_, 0, v_z_3500_);
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_z_3500_);
v___x_3566_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; 
v___x_3567_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(v_args_3556_, v_a_3559_, v___x_3566_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3559_);
lean_dec_ref(v_args_3556_);
return v___x_3567_;
}
}
}
else
{
lean_dec(v_a_3559_);
lean_dec_ref(v_args_3556_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
return v___x_3561_;
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v_args_3556_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
v_a_3571_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3558_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3558_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_3579_; lean_object* v_args_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v_fvarId_3579_ = lean_ctor_get(v_v_3501_, 0);
lean_inc(v_fvarId_3579_);
v_args_3580_ = lean_ctor_get(v_v_3501_, 1);
lean_inc_ref(v_args_3580_);
lean_dec_ref(v_v_3501_);
lean_inc(v_z_3500_);
v___x_3581_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3581_, 0, v_z_3500_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_z_3500_);
v___x_3582_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3500_, v___x_3581_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3591_; 
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v___x_3582_, 0);
lean_dec(v_unused_3592_);
v___x_3584_ = v___x_3582_;
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v___x_3582_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 6);
lean_ctor_set(v___x_3584_, 0, v_z_3500_);
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_z_3500_);
v___x_3587_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; 
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc_ref(v___x_3587_);
v___x_3588_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_3579_, v___x_3587_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3589_; 
lean_dec_ref(v___x_3588_);
v___x_3589_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(v___x_3587_, v_args_3580_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec_ref(v_args_3580_);
return v___x_3589_;
}
else
{
lean_dec_ref(v___x_3587_);
lean_dec_ref(v_args_3580_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v___x_3588_;
}
}
}
}
else
{
lean_dec_ref(v_args_3580_);
lean_dec(v_fvarId_3579_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
return v___x_3582_;
}
}
case 10:
{
lean_object* v_args_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_args_3593_ = lean_ctor_get(v_v_3501_, 1);
lean_inc_ref(v_args_3593_);
lean_dec_ref(v_v_3501_);
lean_inc(v_z_3500_);
v___x_3594_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3594_, 0, v_z_3500_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_z_3500_);
v___x_3595_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3500_, v___x_3594_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3603_; 
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3595_, 0);
lean_dec(v_unused_3604_);
v___x_3597_ = v___x_3595_;
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
else
{
lean_dec(v___x_3595_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 7);
lean_ctor_set(v___x_3597_, 0, v_z_3500_);
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_z_3500_);
v___x_3600_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3601_; 
v___x_3601_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(v___x_3600_, v_args_3593_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec_ref(v_args_3593_);
return v___x_3601_;
}
}
}
else
{
lean_dec_ref(v_args_3593_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_z_3500_);
return v___x_3595_;
}
}
default: 
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_v_3501_);
lean_dec(v_z_3500_);
v___x_3605_ = lean_box(0);
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
return v___x_3606_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue___boxed(lean_object* v_z_3607_, lean_object* v_v_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue(v_z_3607_, v_v_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(lean_object* v_alt_3617_, lean_object* v_f_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
switch(lean_obj_tag(v_alt_3617_))
{
case 0:
{
lean_object* v_code_3626_; lean_object* v___x_3627_; 
v_code_3626_ = lean_ctor_get(v_alt_3617_, 2);
lean_inc_ref(v_code_3626_);
lean_dec_ref(v_alt_3617_);
v___x_3627_ = lean_apply_8(v_f_3618_, v_code_3626_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, lean_box(0));
return v___x_3627_;
}
case 1:
{
lean_object* v_code_3628_; lean_object* v___x_3629_; 
v_code_3628_ = lean_ctor_get(v_alt_3617_, 1);
lean_inc_ref(v_code_3628_);
lean_dec_ref(v_alt_3617_);
v___x_3629_ = lean_apply_8(v_f_3618_, v_code_3628_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, lean_box(0));
return v___x_3629_;
}
default: 
{
lean_object* v_code_3630_; lean_object* v___x_3631_; 
v_code_3630_ = lean_ctor_get(v_alt_3617_, 0);
lean_inc_ref(v_code_3630_);
lean_dec_ref(v_alt_3617_);
v___x_3631_ = lean_apply_8(v_f_3618_, v_code_3630_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, lean_box(0));
return v___x_3631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg___boxed(lean_object* v_alt_3632_, lean_object* v_f_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(v_alt_3632_, v_f_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0(uint8_t v_pu_3642_, lean_object* v_alt_3643_, lean_object* v_f_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(v_alt_3643_, v_f_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___boxed(lean_object* v_pu_3653_, lean_object* v_alt_3654_, lean_object* v_f_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
uint8_t v_pu_boxed_3663_; lean_object* v_res_3664_; 
v_pu_boxed_3663_ = lean_unbox(v_pu_3653_);
v_res_3664_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0(v_pu_boxed_3663_, v_alt_3654_, v_f_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3(lean_object* v_msg_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v_toApplicative_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3738_; 
v___x_3673_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_3674_ = l_ReaderT_instMonad___redArg(v___x_3673_);
v_toApplicative_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; 
v_unused_3739_ = lean_ctor_get(v___x_3674_, 1);
lean_dec(v_unused_3739_);
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3738_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_toApplicative_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3738_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v_toFunctor_3679_; lean_object* v_toSeq_3680_; lean_object* v_toSeqLeft_3681_; lean_object* v_toSeqRight_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3736_; 
v_toFunctor_3679_ = lean_ctor_get(v_toApplicative_3675_, 0);
v_toSeq_3680_ = lean_ctor_get(v_toApplicative_3675_, 2);
v_toSeqLeft_3681_ = lean_ctor_get(v_toApplicative_3675_, 3);
v_toSeqRight_3682_ = lean_ctor_get(v_toApplicative_3675_, 4);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_toApplicative_3675_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; 
v_unused_3737_ = lean_ctor_get(v_toApplicative_3675_, 1);
lean_dec(v_unused_3737_);
v___x_3684_ = v_toApplicative_3675_;
v_isShared_3685_ = v_isSharedCheck_3736_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_toSeqRight_3682_);
lean_inc(v_toSeqLeft_3681_);
lean_inc(v_toSeq_3680_);
lean_inc(v_toFunctor_3679_);
lean_dec(v_toApplicative_3675_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3736_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___f_3686_; lean_object* v___f_3687_; lean_object* v___f_3688_; lean_object* v___f_3689_; lean_object* v___x_3690_; lean_object* v___f_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___x_3695_; 
v___f_3686_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_3687_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_3679_);
v___f_3688_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3688_, 0, v_toFunctor_3679_);
v___f_3689_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3689_, 0, v_toFunctor_3679_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___f_3688_);
lean_ctor_set(v___x_3690_, 1, v___f_3689_);
v___f_3691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3691_, 0, v_toSeqRight_3682_);
v___f_3692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3692_, 0, v_toSeqLeft_3681_);
v___f_3693_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3693_, 0, v_toSeq_3680_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 4, v___f_3691_);
lean_ctor_set(v___x_3684_, 3, v___f_3692_);
lean_ctor_set(v___x_3684_, 2, v___f_3693_);
lean_ctor_set(v___x_3684_, 1, v___f_3686_);
lean_ctor_set(v___x_3684_, 0, v___x_3690_);
v___x_3695_ = v___x_3684_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___f_3686_);
lean_ctor_set(v_reuseFailAlloc_3735_, 2, v___f_3693_);
lean_ctor_set(v_reuseFailAlloc_3735_, 3, v___f_3692_);
lean_ctor_set(v_reuseFailAlloc_3735_, 4, v___f_3691_);
v___x_3695_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
lean_object* v___x_3697_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 1, v___f_3687_);
lean_ctor_set(v___x_3677_, 0, v___x_3695_);
v___x_3697_ = v___x_3677_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___f_3687_);
v___x_3697_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3698_; lean_object* v_toApplicative_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3732_; 
v___x_3698_ = l_ReaderT_instMonad___redArg(v___x_3697_);
v_toApplicative_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; 
v_unused_3733_ = lean_ctor_get(v___x_3698_, 1);
lean_dec(v_unused_3733_);
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3732_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_toApplicative_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3732_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_toFunctor_3703_; lean_object* v_toSeq_3704_; lean_object* v_toSeqLeft_3705_; lean_object* v_toSeqRight_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3730_; 
v_toFunctor_3703_ = lean_ctor_get(v_toApplicative_3699_, 0);
v_toSeq_3704_ = lean_ctor_get(v_toApplicative_3699_, 2);
v_toSeqLeft_3705_ = lean_ctor_get(v_toApplicative_3699_, 3);
v_toSeqRight_3706_ = lean_ctor_get(v_toApplicative_3699_, 4);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_toApplicative_3699_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v_toApplicative_3699_, 1);
lean_dec(v_unused_3731_);
v___x_3708_ = v_toApplicative_3699_;
v_isShared_3709_ = v_isSharedCheck_3730_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_toSeqRight_3706_);
lean_inc(v_toSeqLeft_3705_);
lean_inc(v_toSeq_3704_);
lean_inc(v_toFunctor_3703_);
lean_dec(v_toApplicative_3699_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3730_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___f_3712_; lean_object* v___f_3713_; lean_object* v___x_3714_; lean_object* v___f_3715_; lean_object* v___f_3716_; lean_object* v___f_3717_; lean_object* v___x_3719_; 
v___f_3710_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_3711_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_3703_);
v___f_3712_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3712_, 0, v_toFunctor_3703_);
v___f_3713_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3713_, 0, v_toFunctor_3703_);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___f_3712_);
lean_ctor_set(v___x_3714_, 1, v___f_3713_);
v___f_3715_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3715_, 0, v_toSeqRight_3706_);
v___f_3716_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3716_, 0, v_toSeqLeft_3705_);
v___f_3717_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3717_, 0, v_toSeq_3704_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 4, v___f_3715_);
lean_ctor_set(v___x_3708_, 3, v___f_3716_);
lean_ctor_set(v___x_3708_, 2, v___f_3717_);
lean_ctor_set(v___x_3708_, 1, v___f_3710_);
lean_ctor_set(v___x_3708_, 0, v___x_3714_);
v___x_3719_ = v___x_3708_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v___f_3710_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v___f_3717_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v___f_3716_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v___f_3715_);
v___x_3719_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___f_3711_);
lean_ctor_set(v___x_3701_, 0, v___x_3719_);
v___x_3721_ = v___x_3701_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v___f_3711_);
v___x_3721_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___f_3725_; lean_object* v___x_4789__overap_3726_; lean_object* v___x_3727_; 
v___x_3722_ = l_ReaderT_instMonad___redArg(v___x_3721_);
v___x_3723_ = lean_box(0);
v___x_3724_ = l_instInhabitedOfMonad___redArg(v___x_3722_, v___x_3723_);
v___f_3725_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3725_, 0, v___x_3724_);
v___x_4789__overap_3726_ = lean_panic_fn(v___f_3725_, v_msg_3665_);
v___x_3727_ = lean_apply_7(v___x_4789__overap_3726_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, lean_box(0));
return v___x_3727_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3___boxed(lean_object* v_msg_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3(v_msg_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(lean_object* v_as_3749_, size_t v_i_3750_, size_t v_stop_3751_, lean_object* v_b_3752_){
_start:
{
uint8_t v___x_3753_; 
v___x_3753_ = lean_usize_dec_eq(v_i_3750_, v_stop_3751_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v_fvarId_3755_; lean_object* v___x_3756_; size_t v___x_3757_; size_t v___x_3758_; 
v___x_3754_ = lean_array_uget_borrowed(v_as_3749_, v_i_3750_);
v_fvarId_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_fvarId_3755_);
v___x_3756_ = l_Lean_FVarIdSet_insert(v_b_3752_, v_fvarId_3755_);
v___x_3757_ = ((size_t)1ULL);
v___x_3758_ = lean_usize_add(v_i_3750_, v___x_3757_);
v_i_3750_ = v___x_3758_;
v_b_3752_ = v___x_3756_;
goto _start;
}
else
{
return v_b_3752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1___boxed(lean_object* v_as_3760_, lean_object* v_i_3761_, lean_object* v_stop_3762_, lean_object* v_b_3763_){
_start:
{
size_t v_i_boxed_3764_; size_t v_stop_boxed_3765_; lean_object* v_res_3766_; 
v_i_boxed_3764_ = lean_unbox_usize(v_i_3761_);
lean_dec(v_i_3761_);
v_stop_boxed_3765_ = lean_unbox_usize(v_stop_3762_);
lean_dec(v_stop_3762_);
v_res_3766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_as_3760_, v_i_boxed_3764_, v_stop_boxed_3765_, v_b_3763_);
lean_dec_ref(v_as_3760_);
return v_res_3766_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3768_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_3769_ = lean_unsigned_to_nat(61u);
v___x_3770_ = lean_unsigned_to_nat(350u);
v___x_3771_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__0));
v___x_3772_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0));
v___x_3773_ = l_mkPanicMessageWithDecl(v___x_3772_, v___x_3771_, v___x_3770_, v___x_3769_, v___x_3768_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(lean_object* v_code_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
switch(lean_obj_tag(v_code_3774_))
{
case 0:
{
lean_object* v_decl_3782_; lean_object* v_k_3783_; lean_object* v___x_3784_; 
v_decl_3782_ = lean_ctor_get(v_code_3774_, 0);
lean_inc_ref(v_decl_3782_);
v_k_3783_ = lean_ctor_get(v_code_3774_, 1);
lean_inc_ref(v_k_3783_);
lean_dec_ref(v_code_3774_);
lean_inc(v_a_3780_);
lean_inc_ref(v_a_3779_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
lean_inc_ref(v_k_3783_);
v___x_3784_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_k_3783_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_fvarId_3785_; lean_object* v_value_3786_; lean_object* v___x_3787_; 
lean_dec_ref(v___x_3784_);
v_fvarId_3785_ = lean_ctor_get(v_decl_3782_, 0);
lean_inc(v_fvarId_3785_);
v_value_3786_ = lean_ctor_get(v_decl_3782_, 3);
lean_inc(v_value_3786_);
lean_dec_ref(v_decl_3782_);
lean_inc(v_a_3780_);
lean_inc_ref(v_a_3779_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
lean_inc(v_value_3786_);
lean_inc(v_fvarId_3785_);
v___x_3787_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue(v_fvarId_3785_, v_value_3786_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3788_; 
lean_dec_ref(v___x_3787_);
v___x_3788_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall(v_fvarId_3785_, v_value_3786_, v_k_3783_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec_ref(v_k_3783_);
lean_dec(v_value_3786_);
lean_dec(v_fvarId_3785_);
return v___x_3788_;
}
else
{
lean_dec(v_value_3786_);
lean_dec(v_fvarId_3785_);
lean_dec_ref(v_k_3783_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
return v___x_3787_;
}
}
else
{
lean_dec_ref(v_k_3783_);
lean_dec_ref(v_decl_3782_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
return v___x_3784_;
}
}
case 2:
{
lean_object* v_decl_3789_; lean_object* v_k_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3819_; 
v_decl_3789_ = lean_ctor_get(v_code_3774_, 0);
v_k_3790_ = lean_ctor_get(v_code_3774_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_code_3774_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3792_ = v_code_3774_;
v_isShared_3793_ = v_isSharedCheck_3819_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_k_3790_);
lean_inc(v_decl_3789_);
lean_dec(v_code_3774_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3819_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_fvarId_3794_; lean_object* v_params_3795_; lean_object* v_value_3796_; lean_object* v_decls_3797_; lean_object* v_currDecl_3798_; lean_object* v_paramSet_3799_; lean_object* v___y_3801_; lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_fvarId_3794_ = lean_ctor_get(v_decl_3789_, 0);
lean_inc(v_fvarId_3794_);
v_params_3795_ = lean_ctor_get(v_decl_3789_, 2);
lean_inc_ref(v_params_3795_);
v_value_3796_ = lean_ctor_get(v_decl_3789_, 4);
lean_inc_ref(v_value_3796_);
lean_dec_ref(v_decl_3789_);
v_decls_3797_ = lean_ctor_get(v_a_3775_, 0);
v_currDecl_3798_ = lean_ctor_get(v_a_3775_, 1);
v_paramSet_3799_ = lean_ctor_get(v_a_3775_, 2);
v___x_3809_ = lean_unsigned_to_nat(0u);
v___x_3810_ = lean_array_get_size(v_params_3795_);
v___x_3811_ = lean_nat_dec_lt(v___x_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_dec_ref(v_params_3795_);
lean_inc(v_paramSet_3799_);
v___y_3801_ = v_paramSet_3799_;
goto v___jp_3800_;
}
else
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_nat_dec_le(v___x_3810_, v___x_3810_);
if (v___x_3812_ == 0)
{
if (v___x_3811_ == 0)
{
lean_dec_ref(v_params_3795_);
lean_inc(v_paramSet_3799_);
v___y_3801_ = v_paramSet_3799_;
goto v___jp_3800_;
}
else
{
size_t v___x_3813_; size_t v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = ((size_t)0ULL);
v___x_3814_ = lean_usize_of_nat(v___x_3810_);
lean_inc(v_paramSet_3799_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3795_, v___x_3813_, v___x_3814_, v_paramSet_3799_);
lean_dec_ref(v_params_3795_);
v___y_3801_ = v___x_3815_;
goto v___jp_3800_;
}
}
else
{
size_t v___x_3816_; size_t v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = ((size_t)0ULL);
v___x_3817_ = lean_usize_of_nat(v___x_3810_);
lean_inc(v_paramSet_3799_);
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3795_, v___x_3816_, v___x_3817_, v_paramSet_3799_);
lean_dec_ref(v_params_3795_);
v___y_3801_ = v___x_3818_;
goto v___jp_3800_;
}
}
v___jp_3800_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_inc(v_currDecl_3798_);
lean_inc_ref(v_decls_3797_);
v___x_3802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3802_, 0, v_decls_3797_);
lean_ctor_set(v___x_3802_, 1, v_currDecl_3798_);
lean_ctor_set(v___x_3802_, 2, v___y_3801_);
lean_inc(v_a_3780_);
lean_inc_ref(v_a_3779_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
v___x_3803_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_value_3796_, v___x_3802_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3805_; 
lean_dec_ref(v___x_3803_);
lean_inc(v_currDecl_3798_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set_tag(v___x_3792_, 1);
lean_ctor_set(v___x_3792_, 1, v_fvarId_3794_);
lean_ctor_set(v___x_3792_, 0, v_currDecl_3798_);
v___x_3805_ = v___x_3792_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_currDecl_3798_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_fvarId_3794_);
v___x_3805_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; 
v___x_3806_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(v___x_3805_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec_ref(v___x_3806_);
v_code_3774_ = v_k_3790_;
goto _start;
}
else
{
lean_dec_ref(v_k_3790_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
return v___x_3806_;
}
}
}
else
{
lean_dec(v_fvarId_3794_);
lean_del_object(v___x_3792_);
lean_dec_ref(v_k_3790_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
return v___x_3803_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3820_; lean_object* v_args_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3850_; 
v_fvarId_3820_ = lean_ctor_get(v_code_3774_, 0);
v_args_3821_ = lean_ctor_get(v_code_3774_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_code_3774_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3823_ = v_code_3774_;
v_isShared_3824_ = v_isSharedCheck_3850_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_args_3821_);
lean_inc(v_fvarId_3820_);
lean_dec(v_code_3774_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3850_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v_currDecl_3825_; lean_object* v___x_3827_; 
v_currDecl_3825_ = lean_ctor_get(v_a_3775_, 1);
lean_inc(v_fvarId_3820_);
lean_inc(v_currDecl_3825_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set_tag(v___x_3823_, 1);
lean_ctor_set(v___x_3823_, 1, v_fvarId_3820_);
lean_ctor_set(v___x_3823_, 0, v_currDecl_3825_);
v___x_3827_ = v___x_3823_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_currDecl_3825_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_fvarId_3820_);
v___x_3827_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3828_; 
lean_inc(v_a_3780_);
lean_inc_ref(v_a_3779_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
v___x_3828_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v___x_3827_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
lean_inc(v_fvarId_3820_);
v___x_3830_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3830_, 0, v_fvarId_3820_);
lean_inc(v_a_3780_);
lean_inc_ref(v_a_3779_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
v___x_3831_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(v_args_3821_, v_a_3829_, v___x_3830_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3839_; 
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v___x_3831_, 0);
lean_dec(v_unused_3840_);
v___x_3833_ = v___x_3831_;
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
else
{
lean_dec(v___x_3831_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
lean_ctor_set_tag(v___x_3833_, 10);
lean_ctor_set(v___x_3833_, 0, v_fvarId_3820_);
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_fvarId_3820_);
v___x_3836_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; 
v___x_3837_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(v_args_3821_, v_a_3829_, v___x_3836_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3829_);
lean_dec_ref(v_args_3821_);
return v___x_3837_;
}
}
}
else
{
lean_dec(v_a_3829_);
lean_dec_ref(v_args_3821_);
lean_dec(v_fvarId_3820_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
return v___x_3831_;
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v_args_3821_);
lean_dec(v_fvarId_3820_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
v_a_3841_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3828_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3828_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3873_; 
v_cases_3851_ = lean_ctor_get(v_code_3774_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_code_3774_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3853_ = v_code_3774_;
v_isShared_3854_ = v_isSharedCheck_3873_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_cases_3851_);
lean_dec(v_code_3774_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3873_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v_alts_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_alts_3855_ = lean_ctor_get(v_cases_3851_, 3);
lean_inc_ref(v_alts_3855_);
lean_dec_ref(v_cases_3851_);
v___x_3856_ = lean_unsigned_to_nat(0u);
v___x_3857_ = lean_array_get_size(v_alts_3855_);
v___x_3858_ = lean_box(0);
v___x_3859_ = lean_nat_dec_lt(v___x_3856_, v___x_3857_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3861_; 
lean_dec_ref(v_alts_3855_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3858_);
v___x_3861_ = v___x_3853_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3858_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
else
{
uint8_t v___x_3863_; 
v___x_3863_ = lean_nat_dec_le(v___x_3857_, v___x_3857_);
if (v___x_3863_ == 0)
{
if (v___x_3859_ == 0)
{
lean_object* v___x_3865_; 
lean_dec_ref(v_alts_3855_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3858_);
v___x_3865_ = v___x_3853_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3858_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
else
{
size_t v___x_3867_; size_t v___x_3868_; lean_object* v___x_3869_; 
lean_del_object(v___x_3853_);
v___x_3867_ = ((size_t)0ULL);
v___x_3868_ = lean_usize_of_nat(v___x_3857_);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(v_alts_3855_, v___x_3867_, v___x_3868_, v___x_3858_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec_ref(v_alts_3855_);
return v___x_3869_;
}
}
else
{
size_t v___x_3870_; size_t v___x_3871_; lean_object* v___x_3872_; 
lean_del_object(v___x_3853_);
v___x_3870_ = ((size_t)0ULL);
v___x_3871_ = lean_usize_of_nat(v___x_3857_);
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(v_alts_3855_, v___x_3870_, v___x_3871_, v___x_3858_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec_ref(v_alts_3855_);
return v___x_3872_;
}
}
}
}
case 5:
{
lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_code_3774_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v_code_3774_, 0);
lean_dec(v_unused_3882_);
v___x_3875_ = v_code_3774_;
v_isShared_3876_ = v_isSharedCheck_3881_;
goto v_resetjp_3874_;
}
else
{
lean_dec(v_code_3774_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3881_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3877_ = lean_box(0);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3877_);
v___x_3879_ = v___x_3875_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
case 6:
{
lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_code_3774_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v_code_3774_, 0);
lean_dec(v_unused_3891_);
v___x_3884_ = v_code_3774_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_dec(v_code_3774_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = lean_box(0);
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
case 8:
{
lean_object* v_k_3892_; 
v_k_3892_ = lean_ctor_get(v_code_3774_, 3);
lean_inc_ref(v_k_3892_);
lean_dec_ref(v_code_3774_);
v_code_3774_ = v_k_3892_;
goto _start;
}
case 9:
{
lean_object* v_k_3894_; 
v_k_3894_ = lean_ctor_get(v_code_3774_, 5);
lean_inc_ref(v_k_3894_);
lean_dec_ref(v_code_3774_);
v_code_3774_ = v_k_3894_;
goto _start;
}
default: 
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_dec_ref(v_code_3774_);
v___x_3896_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1);
v___x_3897_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3(v___x_3896_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
return v___x_3897_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___boxed(lean_object* v_code_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_code_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(lean_object* v_as_3907_, size_t v_i_3908_, size_t v_stop_3909_, lean_object* v_b_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
uint8_t v___x_3918_; 
v___x_3918_ = lean_usize_dec_eq(v_i_3908_, v_stop_3909_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = lean_array_uget_borrowed(v_as_3907_, v_i_3908_);
v___x_3920_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___boxed), 8, 0);
lean_inc(v___y_3916_);
lean_inc_ref(v___y_3915_);
lean_inc(v___y_3914_);
lean_inc_ref(v___y_3913_);
lean_inc(v___y_3912_);
lean_inc_ref(v___y_3911_);
lean_inc(v___x_3919_);
v___x_3921_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(v___x_3919_, v___x_3920_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; size_t v___x_3923_; size_t v___x_3924_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref(v___x_3921_);
v___x_3923_ = ((size_t)1ULL);
v___x_3924_ = lean_usize_add(v_i_3908_, v___x_3923_);
v_i_3908_ = v___x_3924_;
v_b_3910_ = v_a_3922_;
goto _start;
}
else
{
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
return v___x_3921_;
}
}
else
{
lean_object* v___x_3926_; 
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v_b_3910_);
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2___boxed(lean_object* v_as_3927_, lean_object* v_i_3928_, lean_object* v_stop_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
size_t v_i_boxed_3938_; size_t v_stop_boxed_3939_; lean_object* v_res_3940_; 
v_i_boxed_3938_ = lean_unbox_usize(v_i_3928_);
lean_dec(v_i_3928_);
v_stop_boxed_3939_ = lean_unbox_usize(v_stop_3929_);
lean_dec(v_stop_3929_);
v_res_3940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(v_as_3927_, v_i_boxed_3938_, v_stop_boxed_3939_, v_b_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
lean_dec_ref(v_as_3927_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl(lean_object* v_decl_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v_value_3949_; 
v_value_3949_ = lean_ctor_get(v_decl_3941_, 1);
lean_inc_ref(v_value_3949_);
if (lean_obj_tag(v_value_3949_) == 0)
{
lean_object* v_toSignature_3950_; lean_object* v_code_3951_; lean_object* v_name_3952_; lean_object* v_params_3953_; lean_object* v_decls_3954_; lean_object* v_paramSet_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3984_; 
v_toSignature_3950_ = lean_ctor_get(v_decl_3941_, 0);
lean_inc_ref(v_toSignature_3950_);
lean_dec_ref(v_decl_3941_);
v_code_3951_ = lean_ctor_get(v_value_3949_, 0);
lean_inc_ref(v_code_3951_);
lean_dec_ref(v_value_3949_);
v_name_3952_ = lean_ctor_get(v_toSignature_3950_, 0);
lean_inc(v_name_3952_);
v_params_3953_ = lean_ctor_get(v_toSignature_3950_, 3);
lean_inc_ref(v_params_3953_);
lean_dec_ref(v_toSignature_3950_);
v_decls_3954_ = lean_ctor_get(v_a_3942_, 0);
v_paramSet_3955_ = lean_ctor_get(v_a_3942_, 2);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_a_3942_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v_a_3942_, 1);
lean_dec(v_unused_3985_);
v___x_3957_ = v_a_3942_;
v_isShared_3958_ = v_isSharedCheck_3984_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_paramSet_3955_);
lean_inc(v_decls_3954_);
lean_dec(v_a_3942_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3984_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___y_3960_; lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3974_ = lean_unsigned_to_nat(0u);
v___x_3975_ = lean_array_get_size(v_params_3953_);
v___x_3976_ = lean_nat_dec_lt(v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_dec_ref(v_params_3953_);
v___y_3960_ = v_paramSet_3955_;
goto v___jp_3959_;
}
else
{
uint8_t v___x_3977_; 
v___x_3977_ = lean_nat_dec_le(v___x_3975_, v___x_3975_);
if (v___x_3977_ == 0)
{
if (v___x_3976_ == 0)
{
lean_dec_ref(v_params_3953_);
v___y_3960_ = v_paramSet_3955_;
goto v___jp_3959_;
}
else
{
size_t v___x_3978_; size_t v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = lean_usize_of_nat(v___x_3975_);
v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3953_, v___x_3978_, v___x_3979_, v_paramSet_3955_);
lean_dec_ref(v_params_3953_);
v___y_3960_ = v___x_3980_;
goto v___jp_3959_;
}
}
else
{
size_t v___x_3981_; size_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = ((size_t)0ULL);
v___x_3982_ = lean_usize_of_nat(v___x_3975_);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3953_, v___x_3981_, v___x_3982_, v_paramSet_3955_);
lean_dec_ref(v_params_3953_);
v___y_3960_ = v___x_3983_;
goto v___jp_3959_;
}
}
v___jp_3959_:
{
lean_object* v___x_3962_; 
lean_inc(v_name_3952_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 2, v___y_3960_);
lean_ctor_set(v___x_3957_, 1, v_name_3952_);
v___x_3962_ = v___x_3957_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_decls_3954_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_name_3952_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v___y_3960_);
v___x_3962_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; 
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc(v_a_3943_);
lean_inc_ref(v___x_3962_);
v___x_3963_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_code_3951_, v___x_3962_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3971_; 
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3971_ == 0)
{
lean_object* v_unused_3972_; 
v_unused_3972_ = lean_ctor_get(v___x_3963_, 0);
lean_dec(v_unused_3972_);
v___x_3965_ = v___x_3963_;
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
else
{
lean_dec(v___x_3963_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 0, v_name_3952_);
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_name_3952_);
v___x_3968_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3969_; 
v___x_3969_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(v___x_3968_, v___x_3962_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v___x_3962_);
return v___x_3969_;
}
}
}
else
{
lean_dec_ref(v___x_3962_);
lean_dec(v_name_3952_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
return v___x_3963_;
}
}
}
}
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
lean_dec_ref(v_value_3949_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec_ref(v_decl_3941_);
v___x_3986_ = lean_box(0);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
return v___x_3987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl___boxed(lean_object* v_decl_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl(v_decl_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(lean_object* v_as_3997_, size_t v_i_3998_, size_t v_stop_3999_, lean_object* v_b_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
uint8_t v___x_4008_; 
v___x_4008_ = lean_usize_dec_eq(v_i_3998_, v_stop_3999_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_array_uget_borrowed(v_as_3997_, v_i_3998_);
lean_inc(v___y_4006_);
lean_inc_ref(v___y_4005_);
lean_inc(v___y_4004_);
lean_inc_ref(v___y_4003_);
lean_inc(v___y_4002_);
lean_inc_ref(v___y_4001_);
lean_inc(v___x_4009_);
v___x_4010_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl(v___x_4009_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; size_t v___x_4012_; size_t v___x_4013_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref(v___x_4010_);
v___x_4012_ = ((size_t)1ULL);
v___x_4013_ = lean_usize_add(v_i_3998_, v___x_4012_);
v_i_3998_ = v___x_4013_;
v_b_4000_ = v_a_4011_;
goto _start;
}
else
{
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
return v___x_4010_;
}
}
else
{
lean_object* v___x_4015_; 
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_b_4000_);
return v___x_4015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0___boxed(lean_object* v_as_4016_, lean_object* v_i_4017_, lean_object* v_stop_4018_, lean_object* v_b_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
size_t v_i_boxed_4027_; size_t v_stop_boxed_4028_; lean_object* v_res_4029_; 
v_i_boxed_4027_ = lean_unbox_usize(v_i_4017_);
lean_dec(v_i_4017_);
v_stop_boxed_4028_ = lean_unbox_usize(v_stop_4018_);
lean_dec(v_stop_4018_);
v_res_4029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(v_as_4016_, v_i_boxed_4027_, v_stop_boxed_4028_, v_b_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec_ref(v_as_4016_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step(lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_decls_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v_decls_4037_ = lean_ctor_get(v_a_4030_, 0);
lean_inc_ref(v_decls_4037_);
v___x_4038_ = lean_unsigned_to_nat(0u);
v___x_4039_ = lean_array_get_size(v_decls_4037_);
v___x_4040_ = lean_box(0);
v___x_4041_ = lean_nat_dec_lt(v___x_4038_, v___x_4039_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; 
lean_dec_ref(v_decls_4037_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
return v___x_4042_;
}
else
{
uint8_t v___x_4043_; 
v___x_4043_ = lean_nat_dec_le(v___x_4039_, v___x_4039_);
if (v___x_4043_ == 0)
{
if (v___x_4041_ == 0)
{
lean_object* v___x_4044_; 
lean_dec_ref(v_decls_4037_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4040_);
return v___x_4044_;
}
else
{
size_t v___x_4045_; size_t v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = ((size_t)0ULL);
v___x_4046_ = lean_usize_of_nat(v___x_4039_);
v___x_4047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(v_decls_4037_, v___x_4045_, v___x_4046_, v___x_4040_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
lean_dec_ref(v_decls_4037_);
return v___x_4047_;
}
}
else
{
size_t v___x_4048_; size_t v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = ((size_t)0ULL);
v___x_4049_ = lean_usize_of_nat(v___x_4039_);
v___x_4050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(v_decls_4037_, v___x_4048_, v___x_4049_, v___x_4040_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
lean_dec_ref(v_decls_4037_);
return v___x_4050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step___boxed(lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step(v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go(lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_){
_start:
{
lean_object* v___x_4066_; 
lean_inc(v_a_4064_);
lean_inc_ref(v_a_4063_);
lean_inc(v_a_4062_);
lean_inc_ref(v_a_4061_);
lean_inc(v_a_4060_);
lean_inc_ref(v_a_4059_);
v___x_4066_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step(v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4089_; 
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v___x_4066_, 0);
lean_dec(v_unused_4090_);
v___x_4068_ = v___x_4066_;
v_isShared_4069_ = v_isSharedCheck_4089_;
goto v_resetjp_4067_;
}
else
{
lean_dec(v___x_4066_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4089_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; uint8_t v_modified_4071_; 
v___x_4070_ = lean_st_ref_get(v_a_4060_);
v_modified_4071_ = lean_ctor_get_uint8(v___x_4070_, sizeof(void*)*2);
lean_dec(v___x_4070_);
if (v_modified_4071_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4074_; 
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
v___x_4072_ = lean_box(0);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v___x_4072_);
v___x_4074_ = v___x_4068_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
else
{
lean_object* v___x_4076_; lean_object* v_owned_4077_; lean_object* v_paramMap_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4088_; 
lean_del_object(v___x_4068_);
v___x_4076_ = lean_st_ref_take(v_a_4060_);
v_owned_4077_ = lean_ctor_get(v___x_4076_, 0);
v_paramMap_4078_ = lean_ctor_get(v___x_4076_, 1);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4080_ = v___x_4076_;
v_isShared_4081_ = v_isSharedCheck_4088_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_paramMap_4078_);
lean_inc(v_owned_4077_);
lean_dec(v___x_4076_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4088_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
uint8_t v___x_4082_; lean_object* v___x_4084_; 
v___x_4082_ = 0;
if (v_isShared_4081_ == 0)
{
v___x_4084_ = v___x_4080_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_owned_4077_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_paramMap_4078_);
v___x_4084_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; 
lean_ctor_set_uint8(v___x_4084_, sizeof(void*)*2, v___x_4082_);
v___x_4085_ = lean_st_ref_set(v_a_4060_, v___x_4084_);
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
return v___x_4066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go___boxed(lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go(v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer(lean_object* v_decls_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v___x_4105_; 
lean_inc(v_a_4103_);
lean_inc_ref(v_a_4102_);
lean_inc(v_a_4101_);
lean_inc_ref(v_a_4100_);
v___x_4105_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap(v_decls_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref(v___x_4105_);
v___x_4107_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4108_ = 0;
v___x_4109_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4109_, 0, v___x_4107_);
lean_ctor_set(v___x_4109_, 1, v_a_4106_);
lean_ctor_set_uint8(v___x_4109_, sizeof(void*)*2, v___x_4108_);
v___x_4110_ = lean_st_mk_ref(v___x_4109_);
v___x_4111_ = lean_box(1);
v___x_4112_ = lean_box(0);
v___x_4113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4113_, 0, v_decls_4099_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
lean_ctor_set(v___x_4113_, 2, v___x_4111_);
lean_inc(v___x_4110_);
v___x_4114_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go(v___x_4113_, v___x_4110_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4123_; 
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4123_ == 0)
{
lean_object* v_unused_4124_; 
v_unused_4124_ = lean_ctor_get(v___x_4114_, 0);
lean_dec(v_unused_4124_);
v___x_4116_ = v___x_4114_;
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
else
{
lean_dec(v___x_4114_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v_paramMap_4119_; lean_object* v___x_4121_; 
v___x_4118_ = lean_st_ref_get(v___x_4110_);
lean_dec(v___x_4110_);
v_paramMap_4119_ = lean_ctor_get(v___x_4118_, 1);
lean_inc_ref(v_paramMap_4119_);
lean_dec(v___x_4118_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v_paramMap_4119_);
v___x_4121_ = v___x_4116_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_paramMap_4119_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec(v___x_4110_);
v_a_4125_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4114_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4114_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
else
{
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec_ref(v_decls_4099_);
return v___x_4105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer___boxed(lean_object* v_decls_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer(v_decls_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(lean_object* v_as_4140_, size_t v_i_4141_, size_t v_stop_4142_, lean_object* v_b_4143_, lean_object* v___y_4144_){
_start:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_usize_dec_eq(v_i_4141_, v_stop_4142_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_array_uget_borrowed(v_as_4140_, v_i_4141_);
lean_inc(v___x_4147_);
v___x_4148_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_4147_, v___y_4144_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; size_t v___x_4150_; size_t v___x_4151_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref(v___x_4148_);
v___x_4150_ = ((size_t)1ULL);
v___x_4151_ = lean_usize_add(v_i_4141_, v___x_4150_);
v_i_4141_ = v___x_4151_;
v_b_4143_ = v_a_4149_;
goto _start;
}
else
{
return v___x_4148_;
}
}
else
{
lean_object* v___x_4153_; 
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v_b_4143_);
return v___x_4153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg___boxed(lean_object* v_as_4154_, lean_object* v_i_4155_, lean_object* v_stop_4156_, lean_object* v_b_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
size_t v_i_boxed_4160_; size_t v_stop_boxed_4161_; lean_object* v_res_4162_; 
v_i_boxed_4160_ = lean_unbox_usize(v_i_4155_);
lean_dec(v_i_4155_);
v_stop_boxed_4161_ = lean_unbox_usize(v_stop_4156_);
lean_dec(v_stop_4156_);
v_res_4162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_as_4154_, v_i_boxed_4160_, v_stop_boxed_4161_, v_b_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v_as_4154_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferBorrow___lam__0(lean_object* v___x_4163_, lean_object* v_decls_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___x_4170_; 
lean_inc(v___y_4168_);
lean_inc_ref(v___y_4167_);
lean_inc(v___y_4166_);
lean_inc_ref(v___y_4165_);
lean_inc_ref(v_decls_4164_);
v___x_4170_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer(v_decls_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4172_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref(v___x_4170_);
lean_inc(v___y_4168_);
v___x_4172_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply(v_decls_4164_, v_a_4171_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___y_4175_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
v___x_4192_ = lean_array_get_size(v_a_4173_);
v___x_4193_ = lean_nat_dec_lt(v___x_4163_, v___x_4192_);
if (v___x_4193_ == 0)
{
lean_dec(v_a_4173_);
lean_dec(v___y_4168_);
return v___x_4172_;
}
else
{
lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4194_ = lean_box(0);
v___x_4195_ = lean_nat_dec_le(v___x_4192_, v___x_4192_);
if (v___x_4195_ == 0)
{
if (v___x_4193_ == 0)
{
lean_dec(v_a_4173_);
lean_dec(v___y_4168_);
return v___x_4172_;
}
else
{
size_t v___x_4196_; size_t v___x_4197_; lean_object* v___x_4198_; 
lean_dec_ref(v___x_4172_);
v___x_4196_ = ((size_t)0ULL);
v___x_4197_ = lean_usize_of_nat(v___x_4192_);
v___x_4198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_a_4173_, v___x_4196_, v___x_4197_, v___x_4194_, v___y_4168_);
lean_dec(v___y_4168_);
v___y_4175_ = v___x_4198_;
goto v___jp_4174_;
}
}
else
{
size_t v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
lean_dec_ref(v___x_4172_);
v___x_4199_ = ((size_t)0ULL);
v___x_4200_ = lean_usize_of_nat(v___x_4192_);
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_a_4173_, v___x_4199_, v___x_4200_, v___x_4194_, v___y_4168_);
lean_dec(v___y_4168_);
v___y_4175_ = v___x_4201_;
goto v___jp_4174_;
}
}
v___jp_4174_:
{
if (lean_obj_tag(v___y_4175_) == 0)
{
lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_isSharedCheck_4182_ = !lean_is_exclusive(v___y_4175_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; 
v_unused_4183_ = lean_ctor_get(v___y_4175_, 0);
lean_dec(v_unused_4183_);
v___x_4177_ = v___y_4175_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_dec(v___y_4175_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v_a_4173_);
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4173_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec(v_a_4173_);
v_a_4184_ = lean_ctor_get(v___y_4175_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___y_4175_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___y_4175_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___y_4175_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
else
{
lean_dec(v___y_4168_);
return v___x_4172_;
}
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec_ref(v_decls_4164_);
v_a_4202_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4170_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4170_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferBorrow___lam__0___boxed(lean_object* v___x_4210_, lean_object* v_decls_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_Compiler_LCNF_inferBorrow___lam__0(v___x_4210_, v_decls_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___x_4210_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0(lean_object* v_as_4229_, size_t v_i_4230_, size_t v_stop_4231_, lean_object* v_b_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_as_4229_, v_i_4230_, v_stop_4231_, v_b_4232_, v___y_4236_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___boxed(lean_object* v_as_4239_, lean_object* v_i_4240_, lean_object* v_stop_4241_, lean_object* v_b_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
size_t v_i_boxed_4248_; size_t v_stop_boxed_4249_; lean_object* v_res_4250_; 
v_i_boxed_4248_ = lean_unbox_usize(v_i_4240_);
lean_dec(v_i_4240_);
v_stop_boxed_4249_ = lean_unbox_usize(v_stop_4241_);
lean_dec(v_stop_4241_);
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0(v_as_4239_, v_i_boxed_4248_, v_stop_boxed_4249_, v_b_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec_ref(v_as_4239_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4317_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2));
v___x_4318_ = 1;
v___x_4319_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_));
v___x_4320_ = l_Lean_registerTraceClass(v___x_4317_, v___x_4318_, v___x_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2____boxed(lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_();
return v_res_4322_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_InferBorrow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM = _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM);
res = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_InferBorrow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_InferBorrow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonadScope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_InferBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_InferBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_InferBorrow(builtin);
}
#ifdef __cplusplus
}
#endif
