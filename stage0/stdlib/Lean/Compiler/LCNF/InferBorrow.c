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
v___x_382_ = lean_unsigned_to_nat(95u);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported(uint8_t v_exported_537_, lean_object* v_ps_538_){
_start:
{
if (v_exported_537_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParams(v_ps_538_);
return v___x_539_;
}
else
{
return v_ps_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported___boxed(lean_object* v_exported_540_, lean_object* v_ps_541_){
_start:
{
uint8_t v_exported_boxed_542_; lean_object* v_res_543_; 
v_exported_boxed_542_ = lean_unbox(v_exported_540_);
v_res_543_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported(v_exported_boxed_542_, v_ps_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(lean_object* v_as_544_, size_t v_i_545_, size_t v_stop_546_, lean_object* v_b_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_a_555_; uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_eq(v_i_545_, v_stop_546_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v_value_561_; 
v___x_560_ = lean_array_uget_borrowed(v_as_544_, v_i_545_);
v_value_561_ = lean_ctor_get(v___x_560_, 1);
lean_inc_ref(v_value_561_);
if (lean_obj_tag(v_value_561_) == 0)
{
lean_object* v_toSignature_562_; lean_object* v_code_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_581_; 
v_toSignature_562_ = lean_ctor_get(v___x_560_, 0);
v_code_563_ = lean_ctor_get(v_value_561_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v_value_561_);
if (v_isSharedCheck_581_ == 0)
{
v___x_565_ = v_value_561_;
v_isShared_566_ = v_isSharedCheck_581_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_code_563_);
lean_dec(v_value_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_581_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_env_569_; lean_object* v_name_570_; lean_object* v_params_571_; uint8_t v___x_572_; lean_object* v___x_574_; 
v___x_567_ = lean_st_ref_get(v___y_552_);
v___x_568_ = lean_st_ref_take(v___y_548_);
v_env_569_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_569_);
lean_dec(v___x_567_);
v_name_570_ = lean_ctor_get(v_toSignature_562_, 0);
v_params_571_ = lean_ctor_get(v_toSignature_562_, 3);
lean_inc(v_name_570_);
v___x_572_ = l_Lean_isExport(v_env_569_, v_name_570_);
lean_inc(v_name_570_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_name_570_);
v___x_574_ = v___x_565_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_name_570_);
v___x_574_ = v_reuseFailAlloc_580_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_inc_ref(v_params_571_);
v___x_575_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_initParamsIfNotExported(v___x_572_, v_params_571_);
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(v___x_568_, v___x_574_, v___x_575_);
v___x_577_ = lean_st_ref_set(v___y_548_, v___x_576_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc(v_name_570_);
v___x_578_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode(v_name_570_, v_code_563_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v_a_555_ = v_a_579_;
goto v___jp_554_;
}
else
{
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
return v___x_578_;
}
}
}
}
else
{
lean_object* v___x_582_; 
lean_dec_ref(v_value_561_);
v___x_582_ = lean_box(0);
v_a_555_ = v___x_582_;
goto v___jp_554_;
}
}
else
{
lean_object* v___x_583_; 
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_b_547_);
return v___x_583_;
}
v___jp_554_:
{
size_t v___x_556_; size_t v___x_557_; 
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_545_, v___x_556_);
v_i_545_ = v___x_557_;
v_b_547_ = v_a_555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0___boxed(lean_object* v_as_584_, lean_object* v_i_585_, lean_object* v_stop_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
size_t v_i_boxed_594_; size_t v_stop_boxed_595_; lean_object* v_res_596_; 
v_i_boxed_594_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_stop_boxed_595_ = lean_unbox_usize(v_stop_586_);
lean_dec(v_stop_586_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(v_as_584_, v_i_boxed_594_, v_stop_boxed_595_, v_b_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec_ref(v_as_584_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go(lean_object* v_decls_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_array_get_size(v_decls_597_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_nat_dec_lt(v___x_604_, v___x_605_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
return v___x_608_;
}
else
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_le(v___x_605_, v___x_605_);
if (v___x_609_ == 0)
{
if (v___x_607_ == 0)
{
lean_object* v___x_610_; 
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_606_);
return v___x_610_;
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_605_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(v_decls_597_, v___x_611_, v___x_612_, v___x_606_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
return v___x_613_;
}
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_605_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go_spec__0(v_decls_597_, v___x_614_, v___x_615_, v___x_606_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go___boxed(lean_object* v_decls_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go(v_decls_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec_ref(v_decls_617_);
return v_res_624_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_box(0);
v___x_626_ = lean_unsigned_to_nat(16u);
v___x_627_ = lean_mk_array(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__0);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap(lean_object* v_decls_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___closed__1);
v___x_638_ = lean_st_mk_ref(v___x_637_);
lean_inc(v___x_638_);
v___x_639_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_go(v_decls_631_, v___x_638_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_648_);
v___x_641_ = v___x_639_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_dec(v___x_639_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_st_ref_get(v___x_638_);
lean_dec(v___x_638_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v___x_638_);
v_a_649_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_639_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_639_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap___boxed(lean_object* v_decls_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap(v_decls_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec_ref(v_decls_657_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(lean_object* v_a_664_, lean_object* v_b_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_memoizedLeft_668_; 
v_memoizedLeft_668_ = lean_ctor_get(v_a_664_, 1);
lean_inc(v_memoizedLeft_668_);
if (lean_obj_tag(v_memoizedLeft_668_) == 0)
{
lean_object* v_left_669_; lean_object* v_right_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_694_; 
v_left_669_ = lean_ctor_get(v_a_664_, 0);
v_right_670_ = lean_ctor_get(v_a_664_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_a_664_, 1);
lean_dec(v_unused_695_);
v___x_672_ = v_a_664_;
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_right_670_);
lean_inc(v_left_669_);
lean_dec(v_a_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_array_674_; lean_object* v_pos_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_693_; 
v_array_674_ = lean_ctor_get(v_left_669_, 0);
v_pos_675_ = lean_ctor_get(v_left_669_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_left_669_);
if (v_isSharedCheck_693_ == 0)
{
v___x_677_ = v_left_669_;
v_isShared_678_ = v_isSharedCheck_693_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_pos_675_);
lean_inc(v_array_674_);
lean_dec(v_left_669_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_693_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_array_get_size(v_array_674_);
v___x_680_ = lean_nat_dec_lt(v_pos_675_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_del_object(v___x_677_);
lean_dec(v_pos_675_);
lean_dec_ref(v_array_674_);
lean_del_object(v___x_672_);
lean_dec(v_right_670_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_b_665_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_add(v_pos_675_, v___x_682_);
lean_inc_ref(v_array_674_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_683_);
v___x_685_ = v___x_677_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_array_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_692_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_686_ = lean_array_fget(v_array_674_, v_pos_675_);
lean_dec(v_pos_675_);
lean_dec_ref(v_array_674_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v___x_687_);
lean_ctor_set(v___x_672_, 0, v___x_685_);
v___x_689_ = v___x_672_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_right_670_);
v___x_689_ = v_reuseFailAlloc_691_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_a_664_ = v___x_689_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_right_696_; lean_object* v_left_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_741_; 
v_right_696_ = lean_ctor_get(v_a_664_, 2);
v_left_697_ = lean_ctor_get(v_a_664_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_a_664_, 1);
lean_dec(v_unused_742_);
v___x_699_ = v_a_664_;
v_isShared_700_ = v_isSharedCheck_741_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_right_696_);
lean_inc(v_left_697_);
lean_dec(v_a_664_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_741_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_val_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_740_; 
v_val_701_ = lean_ctor_get(v_memoizedLeft_668_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_memoizedLeft_668_);
if (v_isSharedCheck_740_ == 0)
{
v___x_703_ = v_memoizedLeft_668_;
v_isShared_704_ = v_isSharedCheck_740_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_val_701_);
lean_dec(v_memoizedLeft_668_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_740_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_array_705_; lean_object* v_pos_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_739_; 
v_array_705_ = lean_ctor_get(v_right_696_, 0);
v_pos_706_ = lean_ctor_get(v_right_696_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_right_696_);
if (v_isSharedCheck_739_ == 0)
{
v___x_708_ = v_right_696_;
v_isShared_709_ = v_isSharedCheck_739_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_pos_706_);
lean_inc(v_array_705_);
lean_dec(v_right_696_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_739_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_array_get_size(v_array_705_);
v___x_711_ = lean_nat_dec_lt(v_pos_706_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_713_; 
lean_del_object(v___x_708_);
lean_dec(v_pos_706_);
lean_dec_ref(v_array_705_);
lean_dec(v_val_701_);
lean_del_object(v___x_699_);
lean_dec(v_left_697_);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
lean_ctor_set(v___x_703_, 0, v_b_665_);
v___x_713_ = v___x_703_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_b_665_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
lean_object* v___x_715_; uint8_t v_borrow_716_; uint8_t v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_703_);
v___x_715_ = lean_array_fget_borrowed(v_array_705_, v_pos_706_);
v_borrow_716_ = lean_ctor_get_uint8(v___x_715_, sizeof(void*)*3);
v___x_717_ = 1;
v___x_718_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_717_, v_val_701_, v_borrow_716_, v___y_666_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_pos_706_, v___x_720_);
lean_dec(v_pos_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_721_);
v___x_723_ = v___x_708_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_array_705_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_730_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_box(0);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 2, v___x_723_);
lean_ctor_set(v___x_699_, 1, v___x_724_);
v___x_726_ = v___x_699_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_left_697_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v___x_723_);
v___x_726_ = v_reuseFailAlloc_729_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = lean_array_push(v_b_665_, v_a_719_);
v_a_664_ = v___x_726_;
v_b_665_ = v___x_727_;
goto _start;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_del_object(v___x_708_);
lean_dec(v_pos_706_);
lean_dec_ref(v_array_705_);
lean_del_object(v___x_699_);
lean_dec(v_left_697_);
lean_dec_ref(v_b_665_);
v_a_731_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_718_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_718_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg___boxed(lean_object* v_a_743_, lean_object* v_b_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(v_a_743_, v_b_744_, v___y_745_);
lean_dec(v___y_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(lean_object* v_ps_750_, lean_object* v_borrows_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_ps_750_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_borrows_751_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
lean_ctor_set(v___x_761_, 2, v___x_759_);
v___x_762_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___closed__0));
v___x_763_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(v___x_761_, v___x_762_, v_a_753_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams___boxed(lean_object* v_ps_764_, lean_object* v_borrows_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(v_ps_764_, v_borrows_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0(lean_object* v_inst_772_, lean_object* v_R_773_, lean_object* v_a_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___redArg(v_a_774_, v_b_775_, v___y_777_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0___boxed(lean_object* v_inst_782_, lean_object* v_R_783_, lean_object* v_a_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams_spec__0(v_inst_782_, v_R_783_, v_a_784_, v_b_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(lean_object* v_alt_792_, lean_object* v_f_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___y_800_; 
switch(lean_obj_tag(v_alt_792_))
{
case 0:
{
lean_object* v_code_819_; 
v_code_819_ = lean_ctor_get(v_alt_792_, 2);
lean_inc_ref(v_code_819_);
v___y_800_ = v_code_819_;
goto v___jp_799_;
}
case 1:
{
lean_object* v_code_820_; 
v_code_820_ = lean_ctor_get(v_alt_792_, 1);
lean_inc_ref(v_code_820_);
v___y_800_ = v_code_820_;
goto v___jp_799_;
}
default: 
{
lean_object* v_code_821_; 
v_code_821_ = lean_ctor_get(v_alt_792_, 0);
lean_inc_ref(v_code_821_);
v___y_800_ = v_code_821_;
goto v___jp_799_;
}
}
v___jp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_apply_6(v_f_793_, v___y_800_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, lean_box(0));
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_810_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_792_, v_a_802_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_alt_792_);
v_a_811_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_801_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_801_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg___boxed(lean_object* v_alt_822_, lean_object* v_f_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(v_alt_822_, v_f_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1(uint8_t v_pu_830_, lean_object* v_alt_831_, lean_object* v_f_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(v_alt_831_, v_f_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___boxed(lean_object* v_pu_839_, lean_object* v_alt_840_, lean_object* v_f_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v_pu_boxed_847_; lean_object* v_res_848_; 
v_pu_boxed_847_ = lean_unbox(v_pu_839_);
v_res_848_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1(v_pu_boxed_847_, v_alt_840_, v_f_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v_res_848_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0(void){
_start:
{
uint8_t v___x_849_; lean_object* v___x_850_; 
v___x_849_ = 1;
v___x_850_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3(lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_toApplicative_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_892_; 
v___x_857_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_858_ = l_ReaderT_instMonad___redArg(v___x_857_);
v_toApplicative_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_858_, 1);
lean_dec(v_unused_893_);
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_892_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_toApplicative_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_892_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_toFunctor_863_; lean_object* v_toSeq_864_; lean_object* v_toSeqLeft_865_; lean_object* v_toSeqRight_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_890_; 
v_toFunctor_863_ = lean_ctor_get(v_toApplicative_859_, 0);
v_toSeq_864_ = lean_ctor_get(v_toApplicative_859_, 2);
v_toSeqLeft_865_ = lean_ctor_get(v_toApplicative_859_, 3);
v_toSeqRight_866_ = lean_ctor_get(v_toApplicative_859_, 4);
v_isSharedCheck_890_ = !lean_is_exclusive(v_toApplicative_859_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v_toApplicative_859_, 1);
lean_dec(v_unused_891_);
v___x_868_ = v_toApplicative_859_;
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_toSeqRight_866_);
lean_inc(v_toSeqLeft_865_);
lean_inc(v_toSeq_864_);
lean_inc(v_toFunctor_863_);
lean_dec(v_toApplicative_859_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___f_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_879_; 
v___f_870_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_871_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_863_);
v___f_872_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_872_, 0, v_toFunctor_863_);
v___f_873_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_873_, 0, v_toFunctor_863_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___f_872_);
lean_ctor_set(v___x_874_, 1, v___f_873_);
v___f_875_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_875_, 0, v_toSeqRight_866_);
v___f_876_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_876_, 0, v_toSeqLeft_865_);
v___f_877_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_877_, 0, v_toSeq_864_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 4, v___f_875_);
lean_ctor_set(v___x_868_, 3, v___f_876_);
lean_ctor_set(v___x_868_, 2, v___f_877_);
lean_ctor_set(v___x_868_, 1, v___f_870_);
lean_ctor_set(v___x_868_, 0, v___x_874_);
v___x_879_ = v___x_868_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___f_870_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v___f_877_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v___f_876_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v___f_875_);
v___x_879_ = v_reuseFailAlloc_889_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___f_871_);
lean_ctor_set(v___x_861_, 0, v___x_879_);
v___x_881_ = v___x_861_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___f_871_);
v___x_881_ = v_reuseFailAlloc_888_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___f_885_; lean_object* v___x_3694__overap_886_; lean_object* v___x_887_; 
v___x_882_ = l_ReaderT_instMonad___redArg(v___x_881_);
v___x_883_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___closed__0);
v___x_884_ = l_instInhabitedOfMonad___redArg(v___x_882_, v___x_883_);
v___f_885_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_885_, 0, v___x_884_);
v___x_3694__overap_886_ = lean_panic_fn(v___f_885_, v_msg_851_);
v___x_887_ = lean_apply_5(v___x_3694__overap_886_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, lean_box(0));
return v___x_887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3___boxed(lean_object* v_msg_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3(v_msg_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v_res_900_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_904_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__2));
v___x_905_ = lean_unsigned_to_nat(11u);
v___x_906_ = lean_unsigned_to_nat(163u);
v___x_907_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__1));
v___x_908_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__0));
v___x_909_ = l_mkPanicMessageWithDecl(v___x_908_, v___x_907_, v___x_906_, v___x_905_, v___x_904_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(lean_object* v_inst_910_, lean_object* v_a_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___closed__3);
v___x_914_ = lean_panic_fn(v_inst_910_, v___x_913_);
return v___x_914_;
}
else
{
lean_object* v_key_915_; lean_object* v_value_916_; lean_object* v_tail_917_; uint8_t v___x_918_; 
v_key_915_ = lean_ctor_get(v_x_912_, 0);
v_value_916_ = lean_ctor_get(v_x_912_, 1);
v_tail_917_ = lean_ctor_get(v_x_912_, 2);
v___x_918_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_915_, v_a_911_);
if (v___x_918_ == 0)
{
v_x_912_ = v_tail_917_;
goto _start;
}
else
{
lean_dec(v_inst_910_);
lean_inc(v_value_916_);
return v_value_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg___boxed(lean_object* v_inst_920_, lean_object* v_a_921_, lean_object* v_x_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(v_inst_920_, v_a_921_, v_x_922_);
lean_dec(v_x_922_);
lean_dec_ref(v_a_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(lean_object* v_inst_924_, lean_object* v_m_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_buckets_927_; lean_object* v___x_928_; uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v_fold_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_buckets_927_ = lean_ctor_get(v_m_925_, 1);
v___x_928_ = lean_array_get_size(v_buckets_927_);
v___x_929_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_a_926_);
v___x_930_ = 32ULL;
v___x_931_ = lean_uint64_shift_right(v___x_929_, v___x_930_);
v_fold_932_ = lean_uint64_xor(v___x_929_, v___x_931_);
v___x_933_ = 16ULL;
v___x_934_ = lean_uint64_shift_right(v_fold_932_, v___x_933_);
v___x_935_ = lean_uint64_xor(v_fold_932_, v___x_934_);
v___x_936_ = lean_uint64_to_usize(v___x_935_);
v___x_937_ = lean_usize_of_nat(v___x_928_);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_sub(v___x_937_, v___x_938_);
v___x_940_ = lean_usize_land(v___x_936_, v___x_939_);
v___x_941_ = lean_array_uget_borrowed(v_buckets_927_, v___x_940_);
v___x_942_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(v_inst_924_, v_a_926_, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg___boxed(lean_object* v_inst_943_, lean_object* v_m_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v_inst_943_, v_m_944_, v_a_945_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_m_944_);
return v_res_946_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Array_instInhabited(lean_box(0));
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_949_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_950_ = lean_unsigned_to_nat(61u);
v___x_951_ = lean_unsigned_to_nat(125u);
v___x_952_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__1));
v___x_953_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0));
v___x_954_ = l_mkPanicMessageWithDecl(v___x_953_, v___x_952_, v___x_951_, v___x_950_, v___x_949_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(lean_object* v_map_955_, lean_object* v_declName_956_, lean_object* v_code_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
switch(lean_obj_tag(v_code_957_))
{
case 0:
{
lean_object* v_decl_963_; lean_object* v_k_964_; lean_object* v___x_965_; 
v_decl_963_ = lean_ctor_get(v_code_957_, 0);
v_k_964_ = lean_ctor_get(v_code_957_, 1);
lean_inc_ref(v_k_964_);
v___x_965_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_955_, v_declName_956_, v_k_964_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_988_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_988_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_988_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_988_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
size_t v___x_970_; size_t v___x_971_; uint8_t v___x_972_; 
v___x_970_ = lean_ptr_addr(v_k_964_);
v___x_971_ = lean_ptr_addr(v_a_966_);
v___x_972_ = lean_usize_dec_eq(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_982_; 
lean_inc_ref(v_decl_963_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; 
v_unused_983_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_984_);
v___x_974_ = v_code_957_;
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
else
{
lean_dec(v_code_957_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_a_966_);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_decl_963_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_a_966_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_977_);
v___x_979_ = v___x_968_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v___x_986_; 
lean_dec(v_a_966_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_code_957_);
v___x_986_ = v___x_968_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_code_957_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_dec_ref(v_code_957_);
return v___x_965_;
}
}
case 2:
{
lean_object* v_decl_989_; lean_object* v_k_990_; lean_object* v_fvarId_991_; lean_object* v_params_992_; lean_object* v_type_993_; lean_object* v_value_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_decl_989_ = lean_ctor_get(v_code_957_, 0);
v_k_990_ = lean_ctor_get(v_code_957_, 1);
v_fvarId_991_ = lean_ctor_get(v_decl_989_, 0);
v_params_992_ = lean_ctor_get(v_decl_989_, 2);
v_type_993_ = lean_ctor_get(v_decl_989_, 3);
v_value_994_ = lean_ctor_get(v_decl_989_, 4);
v___x_995_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0);
lean_inc(v_fvarId_991_);
lean_inc(v_declName_956_);
v___x_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_996_, 0, v_declName_956_);
lean_ctor_set(v___x_996_, 1, v_fvarId_991_);
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v___x_995_, v_map_955_, v___x_996_);
lean_dec_ref(v___x_996_);
lean_inc_ref(v_params_992_);
v___x_998_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(v_params_992_, v___x_997_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
lean_inc(v_a_961_);
lean_inc_ref(v_a_960_);
lean_inc(v_a_959_);
lean_inc_ref(v_a_958_);
lean_inc_ref(v_value_994_);
lean_inc(v_declName_956_);
lean_inc_ref(v_map_955_);
v___x_1000_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_955_, v_declName_956_, v_value_994_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = 1;
lean_inc_ref(v_type_993_);
lean_inc_ref(v_decl_989_);
v___x_1003_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1002_, v_decl_989_, v_type_993_, v_a_999_, v_a_1001_, v_a_959_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
lean_inc_ref(v_k_990_);
v___x_1005_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_955_, v_declName_956_, v_k_990_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1033_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1033_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1033_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___y_1011_; size_t v___x_1027_; size_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = lean_ptr_addr(v_k_990_);
v___x_1028_ = lean_ptr_addr(v_a_1006_);
v___x_1029_ = lean_usize_dec_eq(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
v___y_1011_ = v___x_1029_;
goto v___jp_1010_;
}
else
{
size_t v___x_1030_; size_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_ptr_addr(v_decl_989_);
v___x_1031_ = lean_ptr_addr(v_a_1004_);
v___x_1032_ = lean_usize_dec_eq(v___x_1030_, v___x_1031_);
v___y_1011_ = v___x_1032_;
goto v___jp_1010_;
}
v___jp_1010_:
{
if (v___y_1011_ == 0)
{
lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1021_; 
v_isSharedCheck_1021_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; lean_object* v_unused_1023_; 
v_unused_1022_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1023_);
v___x_1013_ = v_code_957_;
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v_code_957_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_a_1006_);
lean_ctor_set(v___x_1013_, 0, v_a_1004_);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1004_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_a_1006_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1016_);
v___x_1018_ = v___x_1008_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v___x_1025_; 
lean_dec(v_a_1006_);
lean_dec(v_a_1004_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v_code_957_);
v___x_1025_ = v___x_1008_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_code_957_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
else
{
lean_dec(v_a_1004_);
lean_dec_ref(v_code_957_);
return v___x_1005_;
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_code_957_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_declName_956_);
lean_dec_ref(v_map_955_);
v_a_1034_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1003_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1003_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_dec(v_a_999_);
lean_dec_ref(v_code_957_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_declName_956_);
lean_dec_ref(v_map_955_);
return v___x_1000_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_code_957_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_declName_956_);
lean_dec_ref(v_map_955_);
v_a_1042_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_998_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_998_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
case 3:
{
lean_object* v___x_1050_; 
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_declName_956_);
lean_dec_ref(v_map_955_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_code_957_);
return v___x_1050_;
}
case 4:
{
lean_object* v_cases_1051_; lean_object* v_typeName_1052_; lean_object* v_resultType_1053_; lean_object* v_discr_1054_; lean_object* v_alts_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1094_; 
v_cases_1051_ = lean_ctor_get(v_code_957_, 0);
lean_inc_ref(v_cases_1051_);
v_typeName_1052_ = lean_ctor_get(v_cases_1051_, 0);
v_resultType_1053_ = lean_ctor_get(v_cases_1051_, 1);
v_discr_1054_ = lean_ctor_get(v_cases_1051_, 2);
v_alts_1055_ = lean_ctor_get(v_cases_1051_, 3);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_cases_1051_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1057_ = v_cases_1051_;
v_isShared_1058_ = v_isSharedCheck_1094_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_alts_1055_);
lean_inc(v_discr_1054_);
lean_inc(v_resultType_1053_);
lean_inc(v_typeName_1052_);
lean_dec(v_cases_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1094_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1055_);
v___x_1060_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2(v_map_955_, v_declName_956_, v___x_1059_, v_alts_1055_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1085_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
size_t v___x_1065_; size_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_ptr_addr(v_alts_1055_);
lean_dec_ref(v_alts_1055_);
v___x_1066_ = lean_ptr_addr(v_a_1061_);
v___x_1067_ = lean_usize_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1080_; 
v_isSharedCheck_1080_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1081_);
v___x_1069_ = v_code_957_;
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_code_957_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 3, v_a_1061_);
v___x_1072_ = v___x_1057_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_typeName_1052_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_resultType_1053_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_discr_1054_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_a_1061_);
v___x_1072_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1072_);
v___x_1074_ = v___x_1069_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1074_);
v___x_1076_ = v___x_1063_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
else
{
lean_object* v___x_1083_; 
lean_dec(v_a_1061_);
lean_del_object(v___x_1057_);
lean_dec(v_discr_1054_);
lean_dec_ref(v_resultType_1053_);
lean_dec(v_typeName_1052_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v_code_957_);
v___x_1083_ = v___x_1063_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_code_957_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_del_object(v___x_1057_);
lean_dec_ref(v_alts_1055_);
lean_dec(v_discr_1054_);
lean_dec_ref(v_resultType_1053_);
lean_dec(v_typeName_1052_);
lean_dec_ref(v_code_957_);
v_a_1086_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1060_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1060_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
case 5:
{
lean_object* v___x_1095_; 
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_declName_956_);
lean_dec_ref(v_map_955_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_code_957_);
return v___x_1095_;
}
case 6:
{
lean_object* v___x_1096_; 
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_declName_956_);
lean_dec_ref(v_map_955_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_code_957_);
return v___x_1096_;
}
case 8:
{
lean_object* v_fvarId_1097_; lean_object* v_i_1098_; lean_object* v_y_1099_; lean_object* v_k_1100_; lean_object* v___x_1101_; 
v_fvarId_1097_ = lean_ctor_get(v_code_957_, 0);
v_i_1098_ = lean_ctor_get(v_code_957_, 1);
v_y_1099_ = lean_ctor_get(v_code_957_, 2);
v_k_1100_ = lean_ctor_get(v_code_957_, 3);
lean_inc_ref(v_k_1100_);
v___x_1101_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_955_, v_declName_956_, v_k_1100_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1126_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1126_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1126_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
size_t v___x_1106_; size_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_ptr_addr(v_k_1100_);
v___x_1107_ = lean_ptr_addr(v_a_1102_);
v___x_1108_ = lean_usize_dec_eq(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1118_; 
lean_inc(v_y_1099_);
lean_inc(v_i_1098_);
lean_inc(v_fvarId_1097_);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; 
v_unused_1119_ = lean_ctor_get(v_code_957_, 3);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_code_957_, 2);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1122_);
v___x_1110_ = v_code_957_;
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
else
{
lean_dec(v_code_957_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 3, v_a_1102_);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_fvarId_1097_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_i_1098_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_y_1099_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_a_1102_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1113_);
v___x_1115_ = v___x_1104_;
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
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_code_957_);
v___x_1124_ = v___x_1104_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_code_957_);
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
else
{
lean_dec_ref(v_code_957_);
return v___x_1101_;
}
}
case 9:
{
lean_object* v_fvarId_1127_; lean_object* v_i_1128_; lean_object* v_offset_1129_; lean_object* v_y_1130_; lean_object* v_ty_1131_; lean_object* v_k_1132_; lean_object* v___x_1133_; 
v_fvarId_1127_ = lean_ctor_get(v_code_957_, 0);
v_i_1128_ = lean_ctor_get(v_code_957_, 1);
v_offset_1129_ = lean_ctor_get(v_code_957_, 2);
v_y_1130_ = lean_ctor_get(v_code_957_, 3);
v_ty_1131_ = lean_ctor_get(v_code_957_, 4);
v_k_1132_ = lean_ctor_get(v_code_957_, 5);
lean_inc_ref(v_k_1132_);
v___x_1133_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_955_, v_declName_956_, v_k_1132_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1160_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1160_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1160_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
size_t v___x_1138_; size_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_ptr_addr(v_k_1132_);
v___x_1139_ = lean_ptr_addr(v_a_1134_);
v___x_1140_ = lean_usize_dec_eq(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
lean_inc_ref(v_ty_1131_);
lean_inc(v_y_1130_);
lean_inc(v_offset_1129_);
lean_inc(v_i_1128_);
lean_inc(v_fvarId_1127_);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_code_957_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; lean_object* v_unused_1152_; lean_object* v_unused_1153_; lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; 
v_unused_1151_ = lean_ctor_get(v_code_957_, 5);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_code_957_, 4);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_code_957_, 3);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_code_957_, 2);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_code_957_, 1);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_code_957_, 0);
lean_dec(v_unused_1156_);
v___x_1142_ = v_code_957_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_code_957_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 5, v_a_1134_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_fvarId_1127_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_i_1128_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_offset_1129_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_y_1130_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_ty_1131_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_a_1134_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1145_);
v___x_1147_ = v___x_1136_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec(v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v_code_957_);
v___x_1158_ = v___x_1136_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_code_957_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_dec_ref(v_code_957_);
return v___x_1133_;
}
}
default: 
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v_code_957_);
lean_dec(v_declName_956_);
lean_dec_ref(v_map_955_);
v___x_1161_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__2);
v___x_1162_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__3(v___x_1161_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___boxed(lean_object* v_map_1163_, lean_object* v_declName_1164_, lean_object* v_code_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_1163_, v_declName_1164_, v_code_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2(lean_object* v_map_1172_, lean_object* v_declName_1173_, lean_object* v_i_1174_, lean_object* v_as_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_array_get_size(v_as_1175_);
v___x_1182_ = lean_nat_dec_lt(v_i_1174_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v_i_1174_);
lean_dec(v_declName_1173_);
lean_dec_ref(v_map_1172_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_as_1175_);
return v___x_1183_;
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1184_ = lean_array_fget_borrowed(v_as_1175_, v_i_1174_);
lean_inc(v_declName_1173_);
lean_inc_ref(v_map_1172_);
v___x_1185_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___boxed), 8, 2);
lean_closure_set(v___x_1185_, 0, v_map_1172_);
lean_closure_set(v___x_1185_, 1, v_declName_1173_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc(v___y_1177_);
lean_inc_ref(v___y_1176_);
lean_inc(v_a_1184_);
v___x_1186_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__1___redArg(v_a_1184_, v___x_1185_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; size_t v___x_1188_; size_t v___x_1189_; uint8_t v___x_1190_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = lean_ptr_addr(v_a_1184_);
v___x_1189_ = lean_ptr_addr(v_a_1187_);
v___x_1190_ = lean_usize_dec_eq(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_i_1174_, v___x_1191_);
v___x_1193_ = lean_array_fset(v_as_1175_, v_i_1174_, v_a_1187_);
lean_dec(v_i_1174_);
v_i_1174_ = v___x_1192_;
v_as_1175_ = v___x_1193_;
goto _start;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v_a_1187_);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_nat_add(v_i_1174_, v___x_1195_);
lean_dec(v_i_1174_);
v_i_1174_ = v___x_1196_;
goto _start;
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_as_1175_);
lean_dec(v_i_1174_);
lean_dec(v_declName_1173_);
lean_dec_ref(v_map_1172_);
v_a_1198_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1186_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1186_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2___boxed(lean_object* v_map_1206_, lean_object* v_declName_1207_, lean_object* v_i_1208_, lean_object* v_as_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__2(v_map_1206_, v_declName_1207_, v_i_1208_, v_as_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0(lean_object* v_00_u03b2_1216_, lean_object* v_inst_1217_, lean_object* v_m_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v_inst_1217_, v_m_1218_, v_a_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___boxed(lean_object* v_00_u03b2_1221_, lean_object* v_inst_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0(v_00_u03b2_1221_, v_inst_1222_, v_m_1223_, v_a_1224_);
lean_dec_ref(v_a_1224_);
lean_dec_ref(v_m_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0_spec__3___redArg(lean_object* v_inst_1226_, lean_object* v_msg_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_panic_fn(v_inst_1226_, v_msg_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1229_, lean_object* v_inst_1230_, lean_object* v_msg_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_panic_fn(v_inst_1230_, v_msg_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0(lean_object* v_00_u03b2_1233_, lean_object* v_inst_1234_, lean_object* v_a_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___redArg(v_inst_1234_, v_a_1235_, v_x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1238_, lean_object* v_inst_1239_, lean_object* v_a_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0_spec__0(v_00_u03b2_1238_, v_inst_1239_, v_a_1240_, v_x_1241_);
lean_dec(v_x_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0(lean_object* v_map_1243_, size_t v_sz_1244_, size_t v_i_1245_, lean_object* v_bs_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1245_, v_sz_1244_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_map_1243_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_bs_1246_);
return v___x_1253_;
}
else
{
lean_object* v_v_1254_; lean_object* v_toSignature_1255_; lean_object* v_value_1256_; uint8_t v_recursive_1257_; lean_object* v_inlineAttr_x3f_1258_; lean_object* v___x_1259_; lean_object* v_bs_x27_1260_; lean_object* v_a_1262_; 
v_v_1254_ = lean_array_uget(v_bs_1246_, v_i_1245_);
v_toSignature_1255_ = lean_ctor_get(v_v_1254_, 0);
lean_inc_ref(v_toSignature_1255_);
v_value_1256_ = lean_ctor_get(v_v_1254_, 1);
lean_inc_ref(v_value_1256_);
v_recursive_1257_ = lean_ctor_get_uint8(v_v_1254_, sizeof(void*)*3);
v_inlineAttr_x3f_1258_ = lean_ctor_get(v_v_1254_, 2);
v___x_1259_ = lean_unsigned_to_nat(0u);
v_bs_x27_1260_ = lean_array_uset(v_bs_1246_, v_i_1245_, v___x_1259_);
if (lean_obj_tag(v_value_1256_) == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1316_; 
lean_inc(v_inlineAttr_x3f_1258_);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_v_1254_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; 
v_unused_1317_ = lean_ctor_get(v_v_1254_, 2);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_v_1254_, 1);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_v_1254_, 0);
lean_dec(v_unused_1319_);
v___x_1268_ = v_v_1254_;
v_isShared_1269_ = v_isSharedCheck_1316_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v_v_1254_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1316_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_code_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1315_; 
v_code_1270_ = lean_ctor_get(v_value_1256_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_value_1256_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1272_ = v_value_1256_;
v_isShared_1273_ = v_isSharedCheck_1315_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_code_1270_);
lean_dec(v_value_1256_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1315_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_name_1274_; lean_object* v_levelParams_1275_; lean_object* v_type_1276_; lean_object* v_params_1277_; uint8_t v_safe_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1314_; 
v_name_1274_ = lean_ctor_get(v_toSignature_1255_, 0);
v_levelParams_1275_ = lean_ctor_get(v_toSignature_1255_, 1);
v_type_1276_ = lean_ctor_get(v_toSignature_1255_, 2);
v_params_1277_ = lean_ctor_get(v_toSignature_1255_, 3);
v_safe_1278_ = lean_ctor_get_uint8(v_toSignature_1255_, sizeof(void*)*4);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_toSignature_1255_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1280_ = v_toSignature_1255_;
v_isShared_1281_ = v_isSharedCheck_1314_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_params_1277_);
lean_inc(v_type_1276_);
lean_inc(v_levelParams_1275_);
lean_inc(v_name_1274_);
lean_dec(v_toSignature_1255_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1314_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; 
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v_name_1274_);
lean_inc_ref(v_map_1243_);
v___x_1282_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go(v_map_1243_, v_name_1274_, v_code_1270_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0);
lean_inc(v_name_1274_);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_name_1274_);
v___x_1286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go_spec__0___redArg(v___x_1284_, v_map_1243_, v___x_1285_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_updateParams(v_params_1277_, v___x_1286_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1287_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 3, v_a_1288_);
v___x_1290_ = v___x_1280_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_name_1274_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_levelParams_1275_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_type_1276_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_a_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*4, v_safe_1278_);
v___x_1290_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v_a_1283_);
v___x_1292_ = v___x_1272_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1283_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1292_);
lean_ctor_set(v___x_1268_, 0, v___x_1290_);
v___x_1294_ = v___x_1268_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_inlineAttr_x3f_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*3, v_recursive_1257_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
v_a_1262_ = v___x_1294_;
goto v___jp_1261_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_a_1283_);
lean_del_object(v___x_1280_);
lean_dec_ref(v_type_1276_);
lean_dec(v_levelParams_1275_);
lean_dec(v_name_1274_);
lean_del_object(v___x_1272_);
lean_del_object(v___x_1268_);
lean_dec_ref(v_bs_x27_1260_);
lean_dec(v_inlineAttr_x3f_1258_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_map_1243_);
v_a_1298_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1287_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1287_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_del_object(v___x_1280_);
lean_dec_ref(v_params_1277_);
lean_dec_ref(v_type_1276_);
lean_dec(v_levelParams_1275_);
lean_dec(v_name_1274_);
lean_del_object(v___x_1272_);
lean_del_object(v___x_1268_);
lean_dec_ref(v_bs_x27_1260_);
lean_dec(v_inlineAttr_x3f_1258_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_map_1243_);
v_a_1306_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1282_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1282_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1256_);
lean_dec_ref(v_toSignature_1255_);
v_a_1262_ = v_v_1254_;
goto v___jp_1261_;
}
v___jp_1261_:
{
size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_i_1245_, v___x_1263_);
v___x_1265_ = lean_array_uset(v_bs_x27_1260_, v_i_1245_, v_a_1262_);
v_i_1245_ = v___x_1264_;
v_bs_1246_ = v___x_1265_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0___boxed(lean_object* v_map_1320_, lean_object* v_sz_1321_, lean_object* v_i_1322_, lean_object* v_bs_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
size_t v_sz_boxed_1329_; size_t v_i_boxed_1330_; lean_object* v_res_1331_; 
v_sz_boxed_1329_ = lean_unbox_usize(v_sz_1321_);
lean_dec(v_sz_1321_);
v_i_boxed_1330_ = lean_unbox_usize(v_i_1322_);
lean_dec(v_i_1322_);
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0(v_map_1320_, v_sz_boxed_1329_, v_i_boxed_1330_, v_bs_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply(lean_object* v_decls_1332_, lean_object* v_map_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
size_t v_sz_1339_; size_t v___x_1340_; lean_object* v___x_1341_; 
v_sz_1339_ = lean_array_size(v_decls_1332_);
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_spec__0(v_map_1333_, v_sz_1339_, v___x_1340_, v_decls_1332_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply___boxed(lean_object* v_decls_1342_, lean_object* v_map_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply(v_decls_1342_, v_map_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0(lean_object* v_____do__lift_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_paramSet_1358_; lean_object* v___x_1359_; 
v_paramSet_1358_ = lean_ctor_get(v_____do__lift_1350_, 2);
lean_inc(v_paramSet_1358_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_paramSet_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0___boxed(lean_object* v_____do__lift_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__0(v_____do__lift_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec_ref(v_____do__lift_1360_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1(lean_object* v_00_u03b1_1369_, lean_object* v_f_1370_, lean_object* v_mx_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_decls_1379_; lean_object* v_currDecl_1380_; lean_object* v_paramSet_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1390_; 
v_decls_1379_ = lean_ctor_get(v___y_1372_, 0);
v_currDecl_1380_ = lean_ctor_get(v___y_1372_, 1);
v_paramSet_1381_ = lean_ctor_get(v___y_1372_, 2);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___y_1372_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1383_ = v___y_1372_;
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_paramSet_1381_);
lean_inc(v_currDecl_1380_);
lean_inc(v_decls_1379_);
lean_dec(v___y_1372_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_apply_1(v_f_1370_, v_paramSet_1381_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 2, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_decls_1379_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_currDecl_1380_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_apply_7(v_mx_1371_, v___x_1387_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, lean_box(0));
return v___x_1388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_f_1392_, lean_object* v_mx_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___lam__1(v_00_u03b1_1391_, v_f_1392_, v_mx_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v_res_1401_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_toApplicative_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1469_; 
v___x_1404_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_1405_ = l_ReaderT_instMonad___redArg(v___x_1404_);
v_toApplicative_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1405_, 1);
lean_dec(v_unused_1470_);
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1469_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_toApplicative_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1469_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_toFunctor_1410_; lean_object* v_toSeq_1411_; lean_object* v_toSeqLeft_1412_; lean_object* v_toSeqRight_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1467_; 
v_toFunctor_1410_ = lean_ctor_get(v_toApplicative_1406_, 0);
v_toSeq_1411_ = lean_ctor_get(v_toApplicative_1406_, 2);
v_toSeqLeft_1412_ = lean_ctor_get(v_toApplicative_1406_, 3);
v_toSeqRight_1413_ = lean_ctor_get(v_toApplicative_1406_, 4);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_toApplicative_1406_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_toApplicative_1406_, 1);
lean_dec(v_unused_1468_);
v___x_1415_ = v_toApplicative_1406_;
v_isShared_1416_ = v_isSharedCheck_1467_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_toSeqRight_1413_);
lean_inc(v_toSeqLeft_1412_);
lean_inc(v_toSeq_1411_);
lean_inc(v_toFunctor_1410_);
lean_dec(v_toApplicative_1406_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1467_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v___f_1423_; lean_object* v___f_1424_; lean_object* v___x_1426_; 
v___f_1417_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_1418_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_1410_);
v___f_1419_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1419_, 0, v_toFunctor_1410_);
v___f_1420_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1420_, 0, v_toFunctor_1410_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___f_1419_);
lean_ctor_set(v___x_1421_, 1, v___f_1420_);
v___f_1422_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1422_, 0, v_toSeqRight_1413_);
v___f_1423_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1423_, 0, v_toSeqLeft_1412_);
v___f_1424_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1424_, 0, v_toSeq_1411_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___f_1422_);
lean_ctor_set(v___x_1415_, 3, v___f_1423_);
lean_ctor_set(v___x_1415_, 2, v___f_1424_);
lean_ctor_set(v___x_1415_, 1, v___f_1417_);
lean_ctor_set(v___x_1415_, 0, v___x_1421_);
v___x_1426_ = v___x_1415_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___f_1417_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v___f_1424_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v___f_1423_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v___f_1422_);
v___x_1426_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___f_1418_);
lean_ctor_set(v___x_1408_, 0, v___x_1426_);
v___x_1428_ = v___x_1408_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___f_1418_);
v___x_1428_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v_toApplicative_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1463_; 
v___x_1429_ = l_ReaderT_instMonad___redArg(v___x_1428_);
v_toApplicative_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1429_, 1);
lean_dec(v_unused_1464_);
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1463_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_toApplicative_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1463_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_toFunctor_1434_; lean_object* v_toSeq_1435_; lean_object* v_toSeqLeft_1436_; lean_object* v_toSeqRight_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1461_; 
v_toFunctor_1434_ = lean_ctor_get(v_toApplicative_1430_, 0);
v_toSeq_1435_ = lean_ctor_get(v_toApplicative_1430_, 2);
v_toSeqLeft_1436_ = lean_ctor_get(v_toApplicative_1430_, 3);
v_toSeqRight_1437_ = lean_ctor_get(v_toApplicative_1430_, 4);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_toApplicative_1430_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_dec(v_unused_1462_);
v___x_1439_ = v_toApplicative_1430_;
v_isShared_1440_ = v_isSharedCheck_1461_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_toSeqRight_1437_);
lean_inc(v_toSeqLeft_1436_);
lean_inc(v_toSeq_1435_);
lean_inc(v_toFunctor_1434_);
lean_dec(v_toApplicative_1430_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1461_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___x_1452_; 
v___f_1441_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__0));
v___f_1442_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_instMonadScopeInferM___closed__1));
v___f_1443_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_1444_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_1434_);
v___f_1445_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1445_, 0, v_toFunctor_1434_);
v___f_1446_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1446_, 0, v_toFunctor_1434_);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___f_1445_);
lean_ctor_set(v___x_1447_, 1, v___f_1446_);
v___f_1448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1448_, 0, v_toSeqRight_1437_);
v___f_1449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1449_, 0, v_toSeqLeft_1436_);
v___f_1450_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1450_, 0, v_toSeq_1435_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___f_1448_);
lean_ctor_set(v___x_1439_, 3, v___f_1449_);
lean_ctor_set(v___x_1439_, 2, v___f_1450_);
lean_ctor_set(v___x_1439_, 1, v___f_1443_);
lean_ctor_set(v___x_1439_, 0, v___x_1447_);
v___x_1452_ = v___x_1439_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___f_1443_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v___f_1450_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v___f_1449_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___f_1448_);
v___x_1452_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___f_1444_);
lean_ctor_set(v___x_1432_, 0, v___x_1452_);
v___x_1454_ = v___x_1432_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___f_1444_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1455_ = l_ReaderT_instMonad___redArg(v___x_1454_);
lean_inc_ref(v___x_1455_);
v___x_1456_ = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(v___x_1456_, 0, lean_box(0));
lean_closure_set(v___x_1456_, 1, lean_box(0));
lean_closure_set(v___x_1456_, 2, v___x_1455_);
v___x_1457_ = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(v___x_1457_, 0, lean_box(0));
lean_closure_set(v___x_1457_, 1, lean_box(0));
lean_closure_set(v___x_1457_, 2, v___x_1455_);
lean_closure_set(v___x_1457_, 3, lean_box(0));
lean_closure_set(v___x_1457_, 4, lean_box(0));
lean_closure_set(v___x_1457_, 5, v___x_1456_);
lean_closure_set(v___x_1457_, 6, v___f_1441_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v___f_1442_);
return v___x_1458_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx(lean_object* v_x_1471_){
_start:
{
switch(lean_obj_tag(v_x_1471_))
{
case 0:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
return v___x_1472_;
}
case 1:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
return v___x_1473_;
}
case 2:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_unsigned_to_nat(2u);
return v___x_1474_;
}
case 3:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_unsigned_to_nat(3u);
return v___x_1475_;
}
case 4:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_unsigned_to_nat(4u);
return v___x_1476_;
}
case 5:
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_unsigned_to_nat(5u);
return v___x_1477_;
}
case 6:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_unsigned_to_nat(6u);
return v___x_1478_;
}
case 7:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_unsigned_to_nat(7u);
return v___x_1479_;
}
case 8:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_unsigned_to_nat(8u);
return v___x_1480_;
}
case 9:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_unsigned_to_nat(9u);
return v___x_1481_;
}
default: 
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_unsigned_to_nat(10u);
return v___x_1482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx___boxed(lean_object* v_x_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorIdx(v_x_1483_);
lean_dec_ref(v_x_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(lean_object* v_t_1485_, lean_object* v_k_1486_){
_start:
{
lean_object* v_resultFVar_1487_; lean_object* v___x_1488_; 
v_resultFVar_1487_ = lean_ctor_get(v_t_1485_, 0);
lean_inc(v_resultFVar_1487_);
lean_dec_ref(v_t_1485_);
v___x_1488_ = lean_apply_1(v_k_1486_, v_resultFVar_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim(lean_object* v_motive_1489_, lean_object* v_ctorIdx_1490_, lean_object* v_t_1491_, lean_object* v_h_1492_, lean_object* v_k_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1491_, v_k_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___boxed(lean_object* v_motive_1495_, lean_object* v_ctorIdx_1496_, lean_object* v_t_1497_, lean_object* v_h_1498_, lean_object* v_k_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim(v_motive_1495_, v_ctorIdx_1496_, v_t_1497_, v_h_1498_, v_k_1499_);
lean_dec(v_ctorIdx_1496_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_resetReuse_elim___redArg(lean_object* v_t_1501_, lean_object* v_resetReuse_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1501_, v_resetReuse_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_resetReuse_elim(lean_object* v_motive_1504_, lean_object* v_t_1505_, lean_object* v_h_1506_, lean_object* v_resetReuse_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1505_, v_resetReuse_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorResult_elim___redArg(lean_object* v_t_1509_, lean_object* v_constructorResult_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1509_, v_constructorResult_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorResult_elim(lean_object* v_motive_1512_, lean_object* v_t_1513_, lean_object* v_h_1514_, lean_object* v_constructorResult_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1513_, v_constructorResult_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorArg_elim___redArg(lean_object* v_t_1517_, lean_object* v_constructorArg_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1517_, v_constructorArg_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_constructorArg_elim(lean_object* v_motive_1520_, lean_object* v_t_1521_, lean_object* v_h_1522_, lean_object* v_constructorArg_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1521_, v_constructorArg_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_projectionPropagation_elim___redArg(lean_object* v_t_1525_, lean_object* v_projectionPropagation_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1525_, v_projectionPropagation_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_projectionPropagation_elim(lean_object* v_motive_1528_, lean_object* v_t_1529_, lean_object* v_h_1530_, lean_object* v_projectionPropagation_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1529_, v_projectionPropagation_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallResult_elim___redArg(lean_object* v_t_1533_, lean_object* v_functionCallResult_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1533_, v_functionCallResult_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallResult_elim(lean_object* v_motive_1536_, lean_object* v_t_1537_, lean_object* v_h_1538_, lean_object* v_functionCallResult_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1537_, v_functionCallResult_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallArg_elim___redArg(lean_object* v_t_1541_, lean_object* v_functionCallArg_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1541_, v_functionCallArg_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_functionCallArg_elim(lean_object* v_motive_1544_, lean_object* v_t_1545_, lean_object* v_h_1546_, lean_object* v_functionCallArg_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1545_, v_functionCallArg_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_fvarCall_elim___redArg(lean_object* v_t_1549_, lean_object* v_fvarCall_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1549_, v_fvarCall_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_fvarCall_elim(lean_object* v_motive_1552_, lean_object* v_t_1553_, lean_object* v_h_1554_, lean_object* v_fvarCall_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1553_, v_fvarCall_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_partialApplication_elim___redArg(lean_object* v_t_1557_, lean_object* v_partialApplication_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1557_, v_partialApplication_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_partialApplication_elim(lean_object* v_motive_1560_, lean_object* v_t_1561_, lean_object* v_h_1562_, lean_object* v_partialApplication_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1561_, v_partialApplication_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_tailCallPreservation_elim___redArg(lean_object* v_t_1565_, lean_object* v_tailCallPreservation_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1565_, v_tailCallPreservation_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_tailCallPreservation_elim(lean_object* v_motive_1568_, lean_object* v_t_1569_, lean_object* v_h_1570_, lean_object* v_tailCallPreservation_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1569_, v_tailCallPreservation_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpArgPropagation_elim___redArg(lean_object* v_t_1573_, lean_object* v_jpArgPropagation_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1573_, v_jpArgPropagation_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpArgPropagation_elim(lean_object* v_motive_1576_, lean_object* v_t_1577_, lean_object* v_h_1578_, lean_object* v_jpArgPropagation_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1577_, v_jpArgPropagation_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpTailCallPreservation_elim___redArg(lean_object* v_t_1581_, lean_object* v_jpTailCallPreservation_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1581_, v_jpTailCallPreservation_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_jpTailCallPreservation_elim(lean_object* v_motive_1584_, lean_object* v_t_1585_, lean_object* v_h_1586_, lean_object* v_jpTailCallPreservation_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_ctorElim___redArg(v_t_1585_, v_jpTailCallPreservation_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0(lean_object* v_reason_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
switch(lean_obj_tag(v_reason_1600_))
{
case 0:
{
lean_object* v_resultFVar_1607_; lean_object* v___x_1608_; 
v_resultFVar_1607_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1607_);
lean_dec_ref(v_reason_1600_);
v___x_1608_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1607_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1621_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__0));
v___x_1614_ = l_Std_Format_defWidth;
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = l_Std_Format_pretty(v_a_1609_, v___x_1614_, v___x_1615_, v___x_1615_);
v___x_1617_ = lean_string_append(v___x_1613_, v___x_1616_);
lean_dec_ref(v___x_1616_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1617_);
v___x_1619_ = v___x_1611_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1608_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1608_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
case 1:
{
lean_object* v_resultFVar_1630_; lean_object* v___x_1631_; 
v_resultFVar_1630_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1630_);
lean_dec_ref(v_reason_1600_);
v___x_1631_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1630_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1644_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1644_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1644_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__1));
v___x_1637_ = l_Std_Format_defWidth;
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = l_Std_Format_pretty(v_a_1632_, v___x_1637_, v___x_1638_, v___x_1638_);
v___x_1640_ = lean_string_append(v___x_1636_, v___x_1639_);
lean_dec_ref(v___x_1639_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1640_);
v___x_1642_ = v___x_1634_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1631_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1631_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
case 2:
{
lean_object* v_resultFVar_1653_; lean_object* v___x_1654_; 
v_resultFVar_1653_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1653_);
lean_dec_ref(v_reason_1600_);
v___x_1654_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1653_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1667_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1667_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1667_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__2));
v___x_1660_ = l_Std_Format_defWidth;
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l_Std_Format_pretty(v_a_1655_, v___x_1660_, v___x_1661_, v___x_1661_);
v___x_1663_ = lean_string_append(v___x_1659_, v___x_1662_);
lean_dec_ref(v___x_1662_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1663_);
v___x_1665_ = v___x_1657_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1654_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1654_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
case 3:
{
lean_object* v_resultFVar_1676_; lean_object* v___x_1677_; 
v_resultFVar_1676_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1676_);
lean_dec_ref(v_reason_1600_);
v___x_1677_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1676_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1690_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1690_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1690_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__3));
v___x_1683_ = l_Std_Format_defWidth;
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = l_Std_Format_pretty(v_a_1678_, v___x_1683_, v___x_1684_, v___x_1684_);
v___x_1686_ = lean_string_append(v___x_1682_, v___x_1685_);
lean_dec_ref(v___x_1685_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1686_);
v___x_1688_ = v___x_1680_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1677_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1677_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
case 4:
{
lean_object* v_resultFVar_1699_; lean_object* v___x_1700_; 
v_resultFVar_1699_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1699_);
lean_dec_ref(v_reason_1600_);
v___x_1700_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1699_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1713_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1713_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1713_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__4));
v___x_1706_ = l_Std_Format_defWidth;
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = l_Std_Format_pretty(v_a_1701_, v___x_1706_, v___x_1707_, v___x_1707_);
v___x_1709_ = lean_string_append(v___x_1705_, v___x_1708_);
lean_dec_ref(v___x_1708_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1709_);
v___x_1711_ = v___x_1703_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1700_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1700_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
case 5:
{
lean_object* v_resultFVar_1722_; lean_object* v___x_1723_; 
v_resultFVar_1722_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1722_);
lean_dec_ref(v_reason_1600_);
v___x_1723_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1722_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1736_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1736_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1736_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1728_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__5));
v___x_1729_ = l_Std_Format_defWidth;
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = l_Std_Format_pretty(v_a_1724_, v___x_1729_, v___x_1730_, v___x_1730_);
v___x_1732_ = lean_string_append(v___x_1728_, v___x_1731_);
lean_dec_ref(v___x_1731_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1732_);
v___x_1734_ = v___x_1726_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1723_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1723_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
case 6:
{
lean_object* v_resultFVar_1745_; lean_object* v___x_1746_; 
v_resultFVar_1745_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1745_);
lean_dec_ref(v_reason_1600_);
v___x_1746_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1745_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1759_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1759_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1759_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__6));
v___x_1752_ = l_Std_Format_defWidth;
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = l_Std_Format_pretty(v_a_1747_, v___x_1752_, v___x_1753_, v___x_1753_);
v___x_1755_ = lean_string_append(v___x_1751_, v___x_1754_);
lean_dec_ref(v___x_1754_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1755_);
v___x_1757_ = v___x_1749_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
v_a_1760_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1746_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1746_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
case 7:
{
lean_object* v_resultFVar_1768_; lean_object* v___x_1769_; 
v_resultFVar_1768_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_resultFVar_1768_);
lean_dec_ref(v_reason_1600_);
v___x_1769_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_resultFVar_1768_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1782_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1782_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1782_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__7));
v___x_1775_ = l_Std_Format_defWidth;
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = l_Std_Format_pretty(v_a_1770_, v___x_1775_, v___x_1776_, v___x_1776_);
v___x_1778_ = lean_string_append(v___x_1774_, v___x_1777_);
lean_dec_ref(v___x_1777_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1778_);
v___x_1780_ = v___x_1772_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1769_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1769_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
case 8:
{
lean_object* v_funcName_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1802_; 
v_funcName_1791_ = lean_ctor_get(v_reason_1600_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_reason_1600_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1793_ = v_reason_1600_;
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_funcName_1791_);
lean_dec(v_reason_1600_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__8));
v___x_1796_ = 1;
v___x_1797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_funcName_1791_, v___x_1796_);
v___x_1798_ = lean_string_append(v___x_1795_, v___x_1797_);
lean_dec_ref(v___x_1797_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1798_);
v___x_1800_ = v___x_1793_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
case 9:
{
lean_object* v_jpFVar_1803_; lean_object* v___x_1804_; 
v_jpFVar_1803_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_jpFVar_1803_);
lean_dec_ref(v_reason_1600_);
v___x_1804_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_jpFVar_1803_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1817_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1817_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1817_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__9));
v___x_1810_ = l_Std_Format_defWidth;
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = l_Std_Format_pretty(v_a_1805_, v___x_1810_, v___x_1811_, v___x_1811_);
v___x_1813_ = lean_string_append(v___x_1809_, v___x_1812_);
lean_dec_ref(v___x_1812_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1813_);
v___x_1815_ = v___x_1807_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_a_1818_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1804_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1804_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
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
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
default: 
{
lean_object* v_jpFVar_1826_; lean_object* v___x_1827_; 
v_jpFVar_1826_ = lean_ctor_get(v_reason_1600_, 0);
lean_inc(v_jpFVar_1826_);
lean_dec_ref(v_reason_1600_);
v___x_1827_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(v_jpFVar_1826_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1840_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___closed__10));
v___x_1833_ = l_Std_Format_defWidth;
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = l_Std_Format_pretty(v_a_1828_, v___x_1833_, v___x_1834_, v___x_1834_);
v___x_1836_ = lean_string_append(v___x_1832_, v___x_1835_);
lean_dec_ref(v___x_1835_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1836_);
v___x_1838_ = v___x_1830_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1827_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1827_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___boxed(lean_object* v_reason_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0(v_reason_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString(lean_object* v_reason_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___y_1863_; lean_object* v___x_1864_; 
v___y_1863_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___lam__0___boxed), 7, 1);
lean_closure_set(v___y_1863_, 0, v_reason_1857_);
v___x_1864_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___y_1863_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString___boxed(lean_object* v_reason_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString(v_reason_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(lean_object* v_a_1872_, lean_object* v_x_1873_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
uint8_t v___x_1874_; 
v___x_1874_ = 0;
return v___x_1874_;
}
else
{
lean_object* v_key_1875_; lean_object* v_tail_1876_; uint8_t v___x_1877_; 
v_key_1875_ = lean_ctor_get(v_x_1873_, 0);
v_tail_1876_ = lean_ctor_get(v_x_1873_, 2);
v___x_1877_ = l_Lean_instBEqFVarId_beq(v_key_1875_, v_a_1872_);
if (v___x_1877_ == 0)
{
v_x_1873_ = v_tail_1876_;
goto _start;
}
else
{
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg___boxed(lean_object* v_a_1879_, lean_object* v_x_1880_){
_start:
{
uint8_t v_res_1881_; lean_object* v_r_1882_; 
v_res_1881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_1879_, v_x_1880_);
lean_dec(v_x_1880_);
lean_dec(v_a_1879_);
v_r_1882_ = lean_box(v_res_1881_);
return v_r_1882_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(lean_object* v_m_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_buckets_1885_; lean_object* v___x_1886_; uint64_t v___x_1887_; uint64_t v___x_1888_; uint64_t v___x_1889_; uint64_t v_fold_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; uint64_t v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v_buckets_1885_ = lean_ctor_get(v_m_1883_, 1);
v___x_1886_ = lean_array_get_size(v_buckets_1885_);
v___x_1887_ = l_Lean_instHashableFVarId_hash(v_a_1884_);
v___x_1888_ = 32ULL;
v___x_1889_ = lean_uint64_shift_right(v___x_1887_, v___x_1888_);
v_fold_1890_ = lean_uint64_xor(v___x_1887_, v___x_1889_);
v___x_1891_ = 16ULL;
v___x_1892_ = lean_uint64_shift_right(v_fold_1890_, v___x_1891_);
v___x_1893_ = lean_uint64_xor(v_fold_1890_, v___x_1892_);
v___x_1894_ = lean_uint64_to_usize(v___x_1893_);
v___x_1895_ = lean_usize_of_nat(v___x_1886_);
v___x_1896_ = ((size_t)1ULL);
v___x_1897_ = lean_usize_sub(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_usize_land(v___x_1894_, v___x_1897_);
v___x_1899_ = lean_array_uget_borrowed(v_buckets_1885_, v___x_1898_);
v___x_1900_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_1884_, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg___boxed(lean_object* v_m_1901_, lean_object* v_a_1902_){
_start:
{
uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_res_1903_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_m_1901_, v_a_1902_);
lean_dec(v_a_1902_);
lean_dec_ref(v_m_1901_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(lean_object* v_fvarId_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v_owned_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1908_ = lean_st_ref_get(v_a_1906_);
v_owned_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_ref(v_owned_1909_);
lean_dec(v___x_1908_);
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_owned_1909_, v_fvarId_1905_);
lean_dec_ref(v_owned_1909_);
v___x_1911_ = lean_box(v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg___boxed(lean_object* v_fvarId_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec(v_fvarId_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned(lean_object* v_fvarId_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_1917_, v_a_1919_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___boxed(lean_object* v_fvarId_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned(v_fvarId_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_fvarId_1926_);
return v_res_1934_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0(lean_object* v_00_u03b2_1935_, lean_object* v_m_1936_, lean_object* v_a_1937_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_m_1936_, v_a_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___boxed(lean_object* v_00_u03b2_1939_, lean_object* v_m_1940_, lean_object* v_a_1941_){
_start:
{
uint8_t v_res_1942_; lean_object* v_r_1943_; 
v_res_1942_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0(v_00_u03b2_1939_, v_m_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_m_1940_);
v_r_1943_ = lean_box(v_res_1942_);
return v_r_1943_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0(lean_object* v_00_u03b2_1944_, lean_object* v_a_1945_, lean_object* v_x_1946_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_1945_, v_x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1948_, lean_object* v_a_1949_, lean_object* v_x_1950_){
_start:
{
uint8_t v_res_1951_; lean_object* v_r_1952_; 
v_res_1951_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0(v_00_u03b2_1948_, v_a_1949_, v_x_1950_);
lean_dec(v_x_1950_);
lean_dec(v_a_1949_);
v_r_1952_ = lean_box(v_res_1951_);
return v_r_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(size_t v_sz_1953_, size_t v_i_1954_, lean_object* v_bs_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_lt(v_i_1954_, v_sz_1953_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_bs_1955_);
return v___x_1959_;
}
else
{
lean_object* v_v_1960_; lean_object* v_fvarId_1961_; lean_object* v_binderName_1962_; lean_object* v_type_1963_; uint8_t v_borrow_1964_; lean_object* v___x_1965_; lean_object* v_bs_x27_1966_; lean_object* v_a_1968_; 
v_v_1960_ = lean_array_uget(v_bs_1955_, v_i_1954_);
v_fvarId_1961_ = lean_ctor_get(v_v_1960_, 0);
v_binderName_1962_ = lean_ctor_get(v_v_1960_, 1);
v_type_1963_ = lean_ctor_get(v_v_1960_, 2);
v_borrow_1964_ = lean_ctor_get_uint8(v_v_1960_, sizeof(void*)*3);
v___x_1965_ = lean_unsigned_to_nat(0u);
v_bs_x27_1966_ = lean_array_uset(v_bs_1955_, v_i_1954_, v___x_1965_);
if (v_borrow_1964_ == 0)
{
v_a_1968_ = v_v_1960_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_1961_, v___y_1956_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; uint8_t v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v___x_1975_ = lean_unbox(v_a_1974_);
lean_dec(v_a_1974_);
if (v___x_1975_ == 0)
{
v_a_1968_ = v_v_1960_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1994_; 
lean_inc_ref(v_type_1963_);
lean_inc(v_binderName_1962_);
lean_inc(v_fvarId_1961_);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_v_1960_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; lean_object* v_unused_1996_; lean_object* v_unused_1997_; 
v_unused_1995_ = lean_ctor_get(v_v_1960_, 2);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_v_1960_, 1);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_v_1960_, 0);
lean_dec(v_unused_1997_);
v___x_1977_ = v_v_1960_;
v_isShared_1978_ = v_isSharedCheck_1994_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v_v_1960_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1994_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v_owned_1980_; lean_object* v_paramMap_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1993_; 
v___x_1979_ = lean_st_ref_take(v___y_1956_);
v_owned_1980_ = lean_ctor_get(v___x_1979_, 0);
v_paramMap_1981_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1983_ = v___x_1979_;
v_isShared_1984_ = v_isSharedCheck_1993_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_paramMap_1981_);
lean_inc(v_owned_1980_);
lean_dec(v___x_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1993_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_owned_1980_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_paramMap_1981_);
v___x_1986_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1990_; 
lean_ctor_set_uint8(v___x_1986_, sizeof(void*)*2, v_borrow_1964_);
v___x_1987_ = lean_st_ref_set(v___y_1956_, v___x_1986_);
v___x_1988_ = 0;
if (v_isShared_1978_ == 0)
{
v___x_1990_ = v___x_1977_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_fvarId_1961_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_binderName_1962_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_type_1963_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3, v___x_1988_);
v_a_1968_ = v___x_1990_;
goto v___jp_1967_;
}
}
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v_bs_x27_1966_);
lean_dec(v_v_1960_);
v_a_1998_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1973_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1973_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
v___jp_1967_:
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1954_, v___x_1969_);
v___x_1971_ = lean_array_uset(v_bs_x27_1966_, v_i_1954_, v_a_1968_);
v_i_1954_ = v___x_1970_;
v_bs_1955_ = v___x_1971_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg___boxed(lean_object* v_sz_2006_, lean_object* v_i_2007_, lean_object* v_bs_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
size_t v_sz_boxed_2011_; size_t v_i_boxed_2012_; lean_object* v_res_2013_; 
v_sz_boxed_2011_ = lean_unbox_usize(v_sz_2006_);
lean_dec(v_sz_2006_);
v_i_boxed_2012_ = lean_unbox_usize(v_i_2007_);
lean_dec(v_i_2007_);
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(v_sz_boxed_2011_, v_i_boxed_2012_, v_bs_2008_, v___y_2009_);
lean_dec(v___y_2009_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(lean_object* v_a_2014_, lean_object* v_x_2015_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_box(0);
return v___x_2016_;
}
else
{
lean_object* v_key_2017_; lean_object* v_value_2018_; lean_object* v_tail_2019_; uint8_t v___x_2020_; 
v_key_2017_ = lean_ctor_get(v_x_2015_, 0);
v_value_2018_ = lean_ctor_get(v_x_2015_, 1);
v_tail_2019_ = lean_ctor_get(v_x_2015_, 2);
v___x_2020_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_2017_, v_a_2014_);
if (v___x_2020_ == 0)
{
v_x_2015_ = v_tail_2019_;
goto _start;
}
else
{
lean_object* v___x_2022_; 
lean_inc(v_value_2018_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_value_2018_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg___boxed(lean_object* v_a_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(v_a_2023_, v_x_2024_);
lean_dec(v_x_2024_);
lean_dec_ref(v_a_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(lean_object* v_m_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_buckets_2028_; lean_object* v___x_2029_; uint64_t v___x_2030_; uint64_t v___x_2031_; uint64_t v___x_2032_; uint64_t v_fold_2033_; uint64_t v___x_2034_; uint64_t v___x_2035_; uint64_t v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_buckets_2028_ = lean_ctor_get(v_m_2026_, 1);
v___x_2029_ = lean_array_get_size(v_buckets_2028_);
v___x_2030_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_a_2027_);
v___x_2031_ = 32ULL;
v___x_2032_ = lean_uint64_shift_right(v___x_2030_, v___x_2031_);
v_fold_2033_ = lean_uint64_xor(v___x_2030_, v___x_2032_);
v___x_2034_ = 16ULL;
v___x_2035_ = lean_uint64_shift_right(v_fold_2033_, v___x_2034_);
v___x_2036_ = lean_uint64_xor(v_fold_2033_, v___x_2035_);
v___x_2037_ = lean_uint64_to_usize(v___x_2036_);
v___x_2038_ = lean_usize_of_nat(v___x_2029_);
v___x_2039_ = ((size_t)1ULL);
v___x_2040_ = lean_usize_sub(v___x_2038_, v___x_2039_);
v___x_2041_ = lean_usize_land(v___x_2037_, v___x_2040_);
v___x_2042_ = lean_array_uget_borrowed(v_buckets_2028_, v___x_2041_);
v___x_2043_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(v_a_2027_, v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg___boxed(lean_object* v_m_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_m_2044_, v_a_2045_);
lean_dec_ref(v_a_2045_);
lean_dec_ref(v_m_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(lean_object* v_a_2047_, lean_object* v_x_2048_){
_start:
{
if (lean_obj_tag(v_x_2048_) == 0)
{
return v_x_2048_;
}
else
{
lean_object* v_key_2049_; lean_object* v_value_2050_; lean_object* v_tail_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2060_; 
v_key_2049_ = lean_ctor_get(v_x_2048_, 0);
v_value_2050_ = lean_ctor_get(v_x_2048_, 1);
v_tail_2051_ = lean_ctor_get(v_x_2048_, 2);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_x_2048_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2053_ = v_x_2048_;
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_tail_2051_);
lean_inc(v_value_2050_);
lean_inc(v_key_2049_);
lean_dec(v_x_2048_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___x_2055_; 
v___x_2055_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instBEqKey_beq(v_key_2049_, v_a_2047_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2047_, v_tail_2051_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 2, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_key_2049_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_value_2050_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
else
{
lean_del_object(v___x_2053_);
lean_dec(v_value_2050_);
lean_dec(v_key_2049_);
return v_tail_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_2061_, lean_object* v_x_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2061_, v_x_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(lean_object* v_m_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_size_2066_; lean_object* v_buckets_2067_; lean_object* v___x_2068_; uint64_t v___x_2069_; uint64_t v___x_2070_; uint64_t v___x_2071_; uint64_t v_fold_2072_; uint64_t v___x_2073_; uint64_t v___x_2074_; uint64_t v___x_2075_; size_t v___x_2076_; size_t v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; lean_object* v_bkt_2081_; uint8_t v___x_2082_; 
v_size_2066_ = lean_ctor_get(v_m_2064_, 0);
v_buckets_2067_ = lean_ctor_get(v_m_2064_, 1);
v___x_2068_ = lean_array_get_size(v_buckets_2067_);
v___x_2069_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_ParamMap_instHashableKey_hash(v_a_2065_);
v___x_2070_ = 32ULL;
v___x_2071_ = lean_uint64_shift_right(v___x_2069_, v___x_2070_);
v_fold_2072_ = lean_uint64_xor(v___x_2069_, v___x_2071_);
v___x_2073_ = 16ULL;
v___x_2074_ = lean_uint64_shift_right(v_fold_2072_, v___x_2073_);
v___x_2075_ = lean_uint64_xor(v_fold_2072_, v___x_2074_);
v___x_2076_ = lean_uint64_to_usize(v___x_2075_);
v___x_2077_ = lean_usize_of_nat(v___x_2068_);
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_sub(v___x_2077_, v___x_2078_);
v___x_2080_ = lean_usize_land(v___x_2076_, v___x_2079_);
v_bkt_2081_ = lean_array_uget_borrowed(v_buckets_2067_, v___x_2080_);
v___x_2082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1_spec__1___redArg(v_a_2065_, v_bkt_2081_);
if (v___x_2082_ == 0)
{
return v_m_2064_;
}
else
{
lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2095_; 
lean_inc(v_bkt_2081_);
lean_inc_ref(v_buckets_2067_);
lean_inc(v_size_2066_);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_m_2064_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; lean_object* v_unused_2097_; 
v_unused_2096_ = lean_ctor_get(v_m_2064_, 1);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_m_2064_, 0);
lean_dec(v_unused_2097_);
v___x_2084_ = v_m_2064_;
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
else
{
lean_dec(v_m_2064_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v_buckets_x27_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2086_ = lean_box(0);
v_buckets_x27_2087_ = lean_array_uset(v_buckets_2067_, v___x_2080_, v___x_2086_);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_sub(v_size_2066_, v___x_2088_);
lean_dec(v_size_2066_);
v___x_2090_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2065_, v_bkt_2081_);
v___x_2091_ = lean_array_uset(v_buckets_x27_2087_, v___x_2080_, v___x_2090_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v___x_2091_);
lean_ctor_set(v___x_2084_, 0, v___x_2089_);
v___x_2093_ = v___x_2084_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg___boxed(lean_object* v_m_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(v_m_2098_, v_a_2099_);
lean_dec_ref(v_a_2099_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(lean_object* v_k_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v_paramMap_2110_; lean_object* v___x_2111_; 
v___x_2109_ = lean_st_ref_get(v_a_2103_);
v_paramMap_2110_ = lean_ctor_get(v___x_2109_, 1);
lean_inc_ref(v_paramMap_2110_);
lean_dec(v___x_2109_);
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_paramMap_2110_, v_k_2101_);
lean_dec_ref(v_paramMap_2110_);
if (lean_obj_tag(v___x_2111_) == 1)
{
lean_object* v_val_2112_; lean_object* v___x_2113_; lean_object* v_owned_2114_; uint8_t v_modified_2115_; lean_object* v_paramMap_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2158_; 
v_val_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_val_2112_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = lean_st_ref_take(v_a_2103_);
v_owned_2114_ = lean_ctor_get(v___x_2113_, 0);
v_modified_2115_ = lean_ctor_get_uint8(v___x_2113_, sizeof(void*)*2);
v_paramMap_2116_ = lean_ctor_get(v___x_2113_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2118_ = v___x_2113_;
v_isShared_2119_ = v_isSharedCheck_2158_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_paramMap_2116_);
lean_inc(v_owned_2114_);
lean_dec(v___x_2113_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2158_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(v_paramMap_2116_, v_k_2101_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_owned_2114_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v___x_2120_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*2, v_modified_2115_);
v___x_2122_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; size_t v_sz_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_st_ref_set(v_a_2103_, v___x_2122_);
v_sz_2124_ = lean_array_size(v_val_2112_);
v___x_2125_ = ((size_t)0ULL);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(v_sz_2124_, v___x_2125_, v_val_2112_, v_a_2103_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2148_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2148_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2148_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v_owned_2132_; uint8_t v_modified_2133_; lean_object* v_paramMap_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2147_; 
v___x_2131_ = lean_st_ref_take(v_a_2103_);
v_owned_2132_ = lean_ctor_get(v___x_2131_, 0);
v_modified_2133_ = lean_ctor_get_uint8(v___x_2131_, sizeof(void*)*2);
v_paramMap_2134_ = lean_ctor_get(v___x_2131_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2136_ = v___x_2131_;
v_isShared_2137_ = v_isSharedCheck_2147_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_paramMap_2134_);
lean_inc(v_owned_2132_);
lean_dec(v___x_2131_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2147_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__1___redArg(v_paramMap_2134_, v_k_2101_, v_a_2127_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v___x_2138_);
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_owned_2132_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*2, v_modified_2133_);
v___x_2140_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2141_ = lean_st_ref_set(v_a_2103_, v___x_2140_);
v___x_2142_ = lean_box(0);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2142_);
v___x_2144_ = v___x_2129_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v_k_2101_);
v_a_2149_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2126_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2126_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v___x_2111_);
lean_dec_ref(v_k_2101_);
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap___boxed(lean_object* v_k_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(v_k_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0(lean_object* v_00_u03b2_2170_, lean_object* v_m_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_m_2171_, v_a_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___boxed(lean_object* v_00_u03b2_2174_, lean_object* v_m_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0(v_00_u03b2_2174_, v_m_2175_, v_a_2176_);
lean_dec_ref(v_a_2176_);
lean_dec_ref(v_m_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1(lean_object* v_00_u03b2_2178_, lean_object* v_m_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___redArg(v_m_2179_, v_a_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1___boxed(lean_object* v_00_u03b2_2182_, lean_object* v_m_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1(v_00_u03b2_2182_, v_m_2183_, v_a_2184_);
lean_dec_ref(v_a_2184_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2(size_t v_sz_2186_, size_t v_i_2187_, lean_object* v_bs_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___redArg(v_sz_2186_, v_i_2187_, v_bs_2188_, v___y_2190_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2___boxed(lean_object* v_sz_2197_, lean_object* v_i_2198_, lean_object* v_bs_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
size_t v_sz_boxed_2207_; size_t v_i_boxed_2208_; lean_object* v_res_2209_; 
v_sz_boxed_2207_ = lean_unbox_usize(v_sz_2197_);
lean_dec(v_sz_2197_);
v_i_boxed_2208_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__2(v_sz_boxed_2207_, v_i_boxed_2208_, v_bs_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0(lean_object* v_00_u03b2_2210_, lean_object* v_a_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___redArg(v_a_2211_, v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2214_, lean_object* v_a_2215_, lean_object* v_x_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0_spec__0(v_00_u03b2_2214_, v_a_2215_, v_x_2216_);
lean_dec(v_x_2216_);
lean_dec_ref(v_a_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2(lean_object* v_00_u03b2_2218_, lean_object* v_a_2219_, lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___redArg(v_a_2219_, v_x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2222_, lean_object* v_a_2223_, lean_object* v_x_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__1_spec__2(v_00_u03b2_2222_, v_a_2223_, v_x_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(lean_object* v_cls_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_options_2232_; uint8_t v_hasTrace_2233_; 
v_options_2232_ = lean_ctor_get(v___y_2230_, 2);
v_hasTrace_2233_ = lean_ctor_get_uint8(v_options_2232_, sizeof(void*)*1);
if (v_hasTrace_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec(v_cls_2229_);
v___x_2234_ = lean_box(v_hasTrace_2233_);
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
else
{
lean_object* v_inheritedTraceOptions_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_inheritedTraceOptions_2236_ = lean_ctor_get(v___y_2230_, 13);
v___x_2237_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___closed__1));
v___x_2238_ = l_Lean_Name_append(v___x_2237_, v_cls_2229_);
v___x_2239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2236_, v_options_2232_, v___x_2238_);
lean_dec(v___x_2238_);
v___x_2240_ = lean_box(v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg___boxed(lean_object* v_cls_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(v_cls_2242_, v___y_2243_);
lean_dec_ref(v___y_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0(lean_object* v_cls_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(v_cls_2246_, v___y_2251_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___boxed(lean_object* v_cls_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0(v_cls_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2263_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__0);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__1);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
lean_ctor_set(v___x_2269_, 2, v___x_2268_);
lean_ctor_set(v___x_2269_, 3, v___x_2267_);
lean_ctor_set(v___x_2269_, 4, v___x_2267_);
lean_ctor_set(v___x_2269_, 5, v___x_2267_);
lean_ctor_set(v___x_2269_, 6, v___x_2267_);
lean_ctor_set(v___x_2269_, 7, v___x_2267_);
lean_ctor_set(v___x_2269_, 8, v___x_2267_);
return v___x_2269_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2270_; double v___x_2271_; 
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_float_of_nat(v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(lean_object* v_cls_2275_, lean_object* v_msg_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_options_2282_; lean_object* v_ref_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_options_2282_ = lean_ctor_get(v___y_2279_, 2);
v_ref_2283_ = lean_ctor_get(v___y_2279_, 5);
v___x_2284_ = lean_st_ref_get(v___y_2280_);
v___x_2285_ = lean_st_ref_get(v___y_2278_);
v___x_2286_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2277_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2345_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2345_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2345_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v_env_2291_; lean_object* v_lctx_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2343_; 
v_env_2291_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_ref(v_env_2291_);
lean_dec(v___x_2284_);
v_lctx_2292_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v___x_2285_, 1);
lean_dec(v_unused_2344_);
v___x_2294_ = v___x_2285_;
v_isShared_2295_ = v_isSharedCheck_2343_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_lctx_2292_);
lean_dec(v___x_2285_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2343_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_traceState_2298_; lean_object* v_env_2299_; lean_object* v_nextMacroScope_2300_; lean_object* v_ngen_2301_; lean_object* v_auxDeclNGen_2302_; lean_object* v_cache_2303_; lean_object* v_messages_2304_; lean_object* v_infoState_2305_; lean_object* v_snapshotTasks_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2342_; 
v___x_2296_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2);
v___x_2297_ = lean_st_ref_take(v___y_2280_);
v_traceState_2298_ = lean_ctor_get(v___x_2297_, 4);
v_env_2299_ = lean_ctor_get(v___x_2297_, 0);
v_nextMacroScope_2300_ = lean_ctor_get(v___x_2297_, 1);
v_ngen_2301_ = lean_ctor_get(v___x_2297_, 2);
v_auxDeclNGen_2302_ = lean_ctor_get(v___x_2297_, 3);
v_cache_2303_ = lean_ctor_get(v___x_2297_, 5);
v_messages_2304_ = lean_ctor_get(v___x_2297_, 6);
v_infoState_2305_ = lean_ctor_get(v___x_2297_, 7);
v_snapshotTasks_2306_ = lean_ctor_get(v___x_2297_, 8);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2308_ = v___x_2297_;
v_isShared_2309_ = v_isSharedCheck_2342_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_snapshotTasks_2306_);
lean_inc(v_infoState_2305_);
lean_inc(v_messages_2304_);
lean_inc(v_cache_2303_);
lean_inc(v_traceState_2298_);
lean_inc(v_auxDeclNGen_2302_);
lean_inc(v_ngen_2301_);
lean_inc(v_nextMacroScope_2300_);
lean_inc(v_env_2299_);
lean_dec(v___x_2297_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2342_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
uint64_t v_tid_2310_; lean_object* v_traces_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2341_; 
v_tid_2310_ = lean_ctor_get_uint64(v_traceState_2298_, sizeof(void*)*1);
v_traces_2311_ = lean_ctor_get(v_traceState_2298_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_traceState_2298_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2313_ = v_traceState_2298_;
v_isShared_2314_ = v_isSharedCheck_2341_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_traces_2311_);
lean_dec(v_traceState_2298_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2341_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2315_ = lean_unbox(v_a_2287_);
lean_dec(v_a_2287_);
v___x_2316_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2292_, v___x_2315_);
lean_dec_ref(v_lctx_2292_);
lean_inc_ref(v_options_2282_);
v___x_2317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2317_, 0, v_env_2291_);
lean_ctor_set(v___x_2317_, 1, v___x_2296_);
lean_ctor_set(v___x_2317_, 2, v___x_2316_);
lean_ctor_set(v___x_2317_, 3, v_options_2282_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set_tag(v___x_2294_, 3);
lean_ctor_set(v___x_2294_, 1, v_msg_2276_);
lean_ctor_set(v___x_2294_, 0, v___x_2317_);
v___x_2319_ = v___x_2294_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_msg_2276_);
v___x_2319_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; double v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__3);
v___x_2322_ = 0;
v___x_2323_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__4));
v___x_2324_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2324_, 0, v_cls_2275_);
lean_ctor_set(v___x_2324_, 1, v___x_2320_);
lean_ctor_set(v___x_2324_, 2, v___x_2323_);
lean_ctor_set_float(v___x_2324_, sizeof(void*)*3, v___x_2321_);
lean_ctor_set_float(v___x_2324_, sizeof(void*)*3 + 8, v___x_2321_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*3 + 16, v___x_2322_);
v___x_2325_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__5));
v___x_2326_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2319_);
lean_ctor_set(v___x_2326_, 2, v___x_2325_);
lean_inc(v_ref_2283_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_ref_2283_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = l_Lean_PersistentArray_push___redArg(v_traces_2311_, v___x_2327_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2328_);
v___x_2330_ = v___x_2313_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2328_);
lean_ctor_set_uint64(v_reuseFailAlloc_2339_, sizeof(void*)*1, v_tid_2310_);
v___x_2330_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 4, v___x_2330_);
v___x_2332_ = v___x_2308_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_env_2299_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_nextMacroScope_2300_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_ngen_2301_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_auxDeclNGen_2302_);
lean_ctor_set(v_reuseFailAlloc_2338_, 4, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2338_, 5, v_cache_2303_);
lean_ctor_set(v_reuseFailAlloc_2338_, 6, v_messages_2304_);
lean_ctor_set(v_reuseFailAlloc_2338_, 7, v_infoState_2305_);
lean_ctor_set(v_reuseFailAlloc_2338_, 8, v_snapshotTasks_2306_);
v___x_2332_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_st_ref_set(v___y_2280_, v___x_2332_);
v___x_2334_ = lean_box(0);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2334_);
v___x_2336_ = v___x_2289_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
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
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v___x_2285_);
lean_dec(v___x_2284_);
lean_dec_ref(v_msg_2276_);
lean_dec(v_cls_2275_);
v_a_2346_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2286_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2286_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___boxed(lean_object* v_cls_2354_, lean_object* v_msg_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(v_cls_2354_, v_msg_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2(lean_object* v_cls_2362_, lean_object* v_msg_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(v_cls_2362_, v_msg_2363_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___boxed(lean_object* v_cls_2372_, lean_object* v_msg_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2(v_cls_2372_, v_msg_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
return v_x_2382_;
}
else
{
lean_object* v_key_2384_; lean_object* v_value_2385_; lean_object* v_tail_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2409_; 
v_key_2384_ = lean_ctor_get(v_x_2383_, 0);
v_value_2385_ = lean_ctor_get(v_x_2383_, 1);
v_tail_2386_ = lean_ctor_get(v_x_2383_, 2);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_x_2383_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2388_ = v_x_2383_;
v_isShared_2389_ = v_isSharedCheck_2409_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_tail_2386_);
lean_inc(v_value_2385_);
lean_inc(v_key_2384_);
lean_dec(v_x_2383_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2409_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; uint64_t v___x_2391_; uint64_t v___x_2392_; uint64_t v___x_2393_; uint64_t v_fold_2394_; uint64_t v___x_2395_; uint64_t v___x_2396_; uint64_t v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; size_t v___x_2400_; size_t v___x_2401_; size_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2390_ = lean_array_get_size(v_x_2382_);
v___x_2391_ = l_Lean_instHashableFVarId_hash(v_key_2384_);
v___x_2392_ = 32ULL;
v___x_2393_ = lean_uint64_shift_right(v___x_2391_, v___x_2392_);
v_fold_2394_ = lean_uint64_xor(v___x_2391_, v___x_2393_);
v___x_2395_ = 16ULL;
v___x_2396_ = lean_uint64_shift_right(v_fold_2394_, v___x_2395_);
v___x_2397_ = lean_uint64_xor(v_fold_2394_, v___x_2396_);
v___x_2398_ = lean_uint64_to_usize(v___x_2397_);
v___x_2399_ = lean_usize_of_nat(v___x_2390_);
v___x_2400_ = ((size_t)1ULL);
v___x_2401_ = lean_usize_sub(v___x_2399_, v___x_2400_);
v___x_2402_ = lean_usize_land(v___x_2398_, v___x_2401_);
v___x_2403_ = lean_array_uget_borrowed(v_x_2382_, v___x_2402_);
lean_inc(v___x_2403_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 2, v___x_2403_);
v___x_2405_ = v___x_2388_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_key_2384_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_value_2385_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_array_uset(v_x_2382_, v___x_2402_, v___x_2405_);
v_x_2382_ = v___x_2406_;
v_x_2383_ = v_tail_2386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3___redArg(lean_object* v_i_2410_, lean_object* v_source_2411_, lean_object* v_target_2412_){
_start:
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = lean_array_get_size(v_source_2411_);
v___x_2414_ = lean_nat_dec_lt(v_i_2410_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_dec_ref(v_source_2411_);
lean_dec(v_i_2410_);
return v_target_2412_;
}
else
{
lean_object* v_es_2415_; lean_object* v___x_2416_; lean_object* v_source_2417_; lean_object* v_target_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_es_2415_ = lean_array_fget(v_source_2411_, v_i_2410_);
v___x_2416_ = lean_box(0);
v_source_2417_ = lean_array_fset(v_source_2411_, v_i_2410_, v___x_2416_);
v_target_2418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4___redArg(v_target_2412_, v_es_2415_);
v___x_2419_ = lean_unsigned_to_nat(1u);
v___x_2420_ = lean_nat_add(v_i_2410_, v___x_2419_);
lean_dec(v_i_2410_);
v_i_2410_ = v___x_2420_;
v_source_2411_ = v_source_2417_;
v_target_2412_ = v_target_2418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1___redArg(lean_object* v_data_2422_){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_nbuckets_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2423_ = lean_array_get_size(v_data_2422_);
v___x_2424_ = lean_unsigned_to_nat(2u);
v_nbuckets_2425_ = lean_nat_mul(v___x_2423_, v___x_2424_);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_mk_array(v_nbuckets_2425_, v___x_2427_);
v___x_2429_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3___redArg(v___x_2426_, v_data_2422_, v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1___redArg(lean_object* v_m_2430_, lean_object* v_a_2431_, lean_object* v_b_2432_){
_start:
{
lean_object* v_size_2433_; lean_object* v_buckets_2434_; lean_object* v___x_2435_; uint64_t v___x_2436_; uint64_t v___x_2437_; uint64_t v___x_2438_; uint64_t v_fold_2439_; uint64_t v___x_2440_; uint64_t v___x_2441_; uint64_t v___x_2442_; size_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; lean_object* v_bkt_2448_; uint8_t v___x_2449_; 
v_size_2433_ = lean_ctor_get(v_m_2430_, 0);
v_buckets_2434_ = lean_ctor_get(v_m_2430_, 1);
v___x_2435_ = lean_array_get_size(v_buckets_2434_);
v___x_2436_ = l_Lean_instHashableFVarId_hash(v_a_2431_);
v___x_2437_ = 32ULL;
v___x_2438_ = lean_uint64_shift_right(v___x_2436_, v___x_2437_);
v_fold_2439_ = lean_uint64_xor(v___x_2436_, v___x_2438_);
v___x_2440_ = 16ULL;
v___x_2441_ = lean_uint64_shift_right(v_fold_2439_, v___x_2440_);
v___x_2442_ = lean_uint64_xor(v_fold_2439_, v___x_2441_);
v___x_2443_ = lean_uint64_to_usize(v___x_2442_);
v___x_2444_ = lean_usize_of_nat(v___x_2435_);
v___x_2445_ = ((size_t)1ULL);
v___x_2446_ = lean_usize_sub(v___x_2444_, v___x_2445_);
v___x_2447_ = lean_usize_land(v___x_2443_, v___x_2446_);
v_bkt_2448_ = lean_array_uget_borrowed(v_buckets_2434_, v___x_2447_);
v___x_2449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0_spec__0___redArg(v_a_2431_, v_bkt_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2470_; 
lean_inc_ref(v_buckets_2434_);
lean_inc(v_size_2433_);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_m_2430_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; lean_object* v_unused_2472_; 
v_unused_2471_ = lean_ctor_get(v_m_2430_, 1);
lean_dec(v_unused_2471_);
v_unused_2472_ = lean_ctor_get(v_m_2430_, 0);
lean_dec(v_unused_2472_);
v___x_2451_ = v_m_2430_;
v_isShared_2452_ = v_isSharedCheck_2470_;
goto v_resetjp_2450_;
}
else
{
lean_dec(v_m_2430_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2470_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v_size_x27_2454_; lean_object* v___x_2455_; lean_object* v_buckets_x27_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2453_ = lean_unsigned_to_nat(1u);
v_size_x27_2454_ = lean_nat_add(v_size_2433_, v___x_2453_);
lean_dec(v_size_2433_);
lean_inc(v_bkt_2448_);
v___x_2455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2455_, 0, v_a_2431_);
lean_ctor_set(v___x_2455_, 1, v_b_2432_);
lean_ctor_set(v___x_2455_, 2, v_bkt_2448_);
v_buckets_x27_2456_ = lean_array_uset(v_buckets_2434_, v___x_2447_, v___x_2455_);
v___x_2457_ = lean_unsigned_to_nat(4u);
v___x_2458_ = lean_nat_mul(v_size_x27_2454_, v___x_2457_);
v___x_2459_ = lean_unsigned_to_nat(3u);
v___x_2460_ = lean_nat_div(v___x_2458_, v___x_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_array_get_size(v_buckets_x27_2456_);
v___x_2462_ = lean_nat_dec_le(v___x_2460_, v___x_2461_);
lean_dec(v___x_2460_);
if (v___x_2462_ == 0)
{
lean_object* v_val_2463_; lean_object* v___x_2465_; 
v_val_2463_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1___redArg(v_buckets_x27_2456_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v_val_2463_);
lean_ctor_set(v___x_2451_, 0, v_size_x27_2454_);
v___x_2465_ = v___x_2451_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_size_x27_2454_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_val_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
else
{
lean_object* v___x_2468_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v_buckets_x27_2456_);
lean_ctor_set(v___x_2451_, 0, v_size_x27_2454_);
v___x_2468_ = v___x_2451_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_size_x27_2454_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_buckets_x27_2456_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_dec(v_b_2432_);
lean_dec(v_a_2431_);
return v_m_2430_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__3));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__5));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(lean_object* v_fvarId_2484_, lean_object* v_reason_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v_owned_2494_; uint8_t v___x_2495_; 
v___x_2493_ = lean_st_ref_get(v_a_2487_);
v_owned_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc_ref(v_owned_2494_);
lean_dec(v___x_2493_);
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned_spec__0___redArg(v_owned_2494_, v_fvarId_2484_);
lean_dec_ref(v_owned_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2551_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2));
v___x_2497_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__0___redArg(v___x_2496_, v_a_2490_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2551_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2551_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
uint8_t v___x_2502_; lean_object* v___y_2504_; uint8_t v___x_2521_; 
v___x_2502_ = 1;
v___x_2521_ = lean_unbox(v_a_2498_);
lean_dec(v_a_2498_);
if (v___x_2521_ == 0)
{
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_reason_2485_);
v___y_2504_ = v_a_2487_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_inc(v_fvarId_2484_);
v___x_2522_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___boxed), 7, 1);
lean_closure_set(v___x_2522_, 0, v_fvarId_2484_);
lean_inc(v_a_2491_);
lean_inc_ref(v_a_2490_);
lean_inc(v_a_2489_);
lean_inc_ref(v_a_2488_);
v___x_2523_ = l_Lean_Compiler_LCNF_PP_run___redArg(v___x_2522_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2523_);
lean_inc(v_a_2491_);
lean_inc_ref(v_a_2490_);
lean_inc(v_a_2489_);
lean_inc_ref(v_a_2488_);
v___x_2525_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_OwnReason_toString(v_reason_2485_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__4);
v___x_2528_ = l_Lean_MessageData_ofFormat(v_a_2524_);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__6);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = l_Lean_stringToMessageData(v_a_2526_);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg(v___x_2496_, v___x_2533_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_dec_ref(v___x_2534_);
v___y_2504_ = v_a_2487_;
goto v___jp_2503_;
}
else
{
lean_del_object(v___x_2500_);
lean_dec(v_fvarId_2484_);
return v___x_2534_;
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_a_2524_);
lean_del_object(v___x_2500_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_fvarId_2484_);
v_a_2535_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2525_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2525_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_del_object(v___x_2500_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_reason_2485_);
lean_dec(v_fvarId_2484_);
v_a_2543_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2523_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2523_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
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
v___jp_2503_:
{
lean_object* v___x_2505_; lean_object* v_owned_2506_; lean_object* v_paramMap_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2520_; 
v___x_2505_ = lean_st_ref_take(v___y_2504_);
v_owned_2506_ = lean_ctor_get(v___x_2505_, 0);
v_paramMap_2507_ = lean_ctor_get(v___x_2505_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2509_ = v___x_2505_;
v_isShared_2510_ = v_isSharedCheck_2520_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_paramMap_2507_);
lean_inc(v_owned_2506_);
lean_dec(v___x_2505_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2520_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2511_ = lean_box(0);
v___x_2512_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1___redArg(v_owned_2506_, v_fvarId_2484_, v___x_2511_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2512_);
v___x_2514_ = v___x_2509_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_paramMap_2507_);
v___x_2514_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*2, v___x_2502_);
v___x_2515_ = lean_st_ref_set(v___y_2504_, v___x_2514_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2511_);
v___x_2517_ = v___x_2500_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2511_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_reason_2485_);
lean_dec(v_fvarId_2484_);
v___x_2552_ = lean_box(0);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___boxed(lean_object* v_fvarId_2554_, lean_object* v_reason_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_2554_, v_reason_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1(lean_object* v_00_u03b2_2564_, lean_object* v_m_2565_, lean_object* v_a_2566_, lean_object* v_b_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1___redArg(v_m_2565_, v_a_2566_, v_b_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1(lean_object* v_00_u03b2_2569_, lean_object* v_data_2570_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1___redArg(v_data_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2572_, lean_object* v_i_2573_, lean_object* v_source_2574_, lean_object* v_target_2575_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3___redArg(v_i_2573_, v_source_2574_, v_target_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__1_spec__1_spec__3_spec__4___redArg(v_x_2578_, v_x_2579_);
return v___x_2580_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0(void){
_start:
{
uint8_t v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = 1;
v___x_2582_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(lean_object* v_upperBound_2583_, lean_object* v_args_2584_, lean_object* v_ps_2585_, lean_object* v_reason_2586_, lean_object* v_a_2587_, lean_object* v_b_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_a_2597_; uint8_t v___x_2601_; 
v___x_2601_ = lean_nat_dec_lt(v_a_2587_, v_upperBound_2583_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v_a_2587_);
lean_dec_ref(v_reason_2586_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_b_2588_);
return v___x_2602_;
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_array_fget_borrowed(v_args_2584_, v_a_2587_);
if (lean_obj_tag(v___x_2604_) == 1)
{
lean_object* v_fvarId_2605_; lean_object* v___x_2606_; 
v_fvarId_2605_ = lean_ctor_get(v___x_2604_, 0);
v___x_2606_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_fvarId_2605_, v___y_2590_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; uint8_t v___x_2608_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = lean_unbox(v_a_2607_);
lean_dec(v_a_2607_);
if (v___x_2608_ == 0)
{
v_a_2597_ = v___x_2603_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v_fvarId_2611_; lean_object* v___x_2612_; 
v___x_2609_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0);
v___x_2610_ = lean_array_get_borrowed(v___x_2609_, v_ps_2585_, v_a_2587_);
v_fvarId_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
lean_inc(v___y_2592_);
lean_inc_ref(v___y_2591_);
lean_inc_ref(v_reason_2586_);
lean_inc(v_fvarId_2611_);
v___x_2612_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_2611_, v_reason_2586_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_dec_ref(v___x_2612_);
v_a_2597_ = v___x_2603_;
goto v___jp_2596_;
}
else
{
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v_a_2587_);
lean_dec_ref(v_reason_2586_);
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v_a_2587_);
lean_dec_ref(v_reason_2586_);
v_a_2613_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2606_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2606_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
v_a_2597_ = v___x_2603_;
goto v___jp_2596_;
}
}
v___jp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_unsigned_to_nat(1u);
v___x_2599_ = lean_nat_add(v_a_2587_, v___x_2598_);
lean_dec(v_a_2587_);
v_a_2587_ = v___x_2599_;
v_b_2588_ = v_a_2597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___boxed(lean_object* v_upperBound_2621_, lean_object* v_args_2622_, lean_object* v_ps_2623_, lean_object* v_reason_2624_, lean_object* v_a_2625_, lean_object* v_b_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(v_upperBound_2621_, v_args_2622_, v_ps_2623_, v_reason_2624_, v_a_2625_, v_b_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_ps_2623_);
lean_dec_ref(v_args_2622_);
lean_dec(v_upperBound_2621_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(lean_object* v_args_2635_, lean_object* v_ps_2636_, lean_object* v_reason_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = lean_array_get_size(v_args_2635_);
v___x_2647_ = lean_box(0);
v___x_2648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(v___x_2646_, v_args_2635_, v_ps_2636_, v_reason_2637_, v___x_2645_, v___x_2647_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v___x_2648_, 0);
lean_dec(v_unused_2656_);
v___x_2650_ = v___x_2648_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_dec(v___x_2648_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2647_);
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2647_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
return v___x_2648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs___boxed(lean_object* v_args_2657_, lean_object* v_ps_2658_, lean_object* v_reason_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(v_args_2657_, v_ps_2658_, v_reason_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec_ref(v_ps_2658_);
lean_dec_ref(v_args_2657_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0(lean_object* v_upperBound_2668_, lean_object* v_args_2669_, lean_object* v_ps_2670_, lean_object* v_reason_2671_, lean_object* v_inst_2672_, lean_object* v_R_2673_, lean_object* v_a_2674_, lean_object* v_b_2675_, lean_object* v_c_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg(v_upperBound_2668_, v_args_2669_, v_ps_2670_, v_reason_2671_, v_a_2674_, v_b_2675_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___boxed(lean_object* v_upperBound_2685_, lean_object* v_args_2686_, lean_object* v_ps_2687_, lean_object* v_reason_2688_, lean_object* v_inst_2689_, lean_object* v_R_2690_, lean_object* v_a_2691_, lean_object* v_b_2692_, lean_object* v_c_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0(v_upperBound_2685_, v_args_2686_, v_ps_2687_, v_reason_2688_, v_inst_2689_, v_R_2690_, v_a_2691_, v_b_2692_, v_c_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec_ref(v_ps_2687_);
lean_dec_ref(v_args_2686_);
lean_dec(v_upperBound_2685_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0(lean_object* v_reason_2702_, lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_x_2703_, v_reason_2702_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0___boxed(lean_object* v_reason_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0(v_reason_2712_, v_x_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(lean_object* v_msg_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_toApplicative_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2795_; 
v___x_2730_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_2731_ = l_ReaderT_instMonad___redArg(v___x_2730_);
v_toApplicative_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2731_, 1);
lean_dec(v_unused_2796_);
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2795_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_toApplicative_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2795_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v_toFunctor_2736_; lean_object* v_toSeq_2737_; lean_object* v_toSeqLeft_2738_; lean_object* v_toSeqRight_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2793_; 
v_toFunctor_2736_ = lean_ctor_get(v_toApplicative_2732_, 0);
v_toSeq_2737_ = lean_ctor_get(v_toApplicative_2732_, 2);
v_toSeqLeft_2738_ = lean_ctor_get(v_toApplicative_2732_, 3);
v_toSeqRight_2739_ = lean_ctor_get(v_toApplicative_2732_, 4);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_toApplicative_2732_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v_toApplicative_2732_, 1);
lean_dec(v_unused_2794_);
v___x_2741_ = v_toApplicative_2732_;
v_isShared_2742_ = v_isSharedCheck_2793_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_toSeqRight_2739_);
lean_inc(v_toSeqLeft_2738_);
lean_inc(v_toSeq_2737_);
lean_inc(v_toFunctor_2736_);
lean_dec(v_toApplicative_2732_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2793_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___f_2745_; lean_object* v___f_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___f_2750_; lean_object* v___x_2752_; 
v___f_2743_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_2744_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2736_);
v___f_2745_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2745_, 0, v_toFunctor_2736_);
v___f_2746_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2746_, 0, v_toFunctor_2736_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___f_2745_);
lean_ctor_set(v___x_2747_, 1, v___f_2746_);
v___f_2748_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2748_, 0, v_toSeqRight_2739_);
v___f_2749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2749_, 0, v_toSeqLeft_2738_);
v___f_2750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2750_, 0, v_toSeq_2737_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 4, v___f_2748_);
lean_ctor_set(v___x_2741_, 3, v___f_2749_);
lean_ctor_set(v___x_2741_, 2, v___f_2750_);
lean_ctor_set(v___x_2741_, 1, v___f_2743_);
lean_ctor_set(v___x_2741_, 0, v___x_2747_);
v___x_2752_ = v___x_2741_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___f_2743_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v___f_2750_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v___f_2749_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v___f_2748_);
v___x_2752_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2754_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___f_2744_);
lean_ctor_set(v___x_2734_, 0, v___x_2752_);
v___x_2754_ = v___x_2734_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___f_2744_);
v___x_2754_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; lean_object* v_toApplicative_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2789_; 
v___x_2755_ = l_ReaderT_instMonad___redArg(v___x_2754_);
v_toApplicative_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2755_, 1);
lean_dec(v_unused_2790_);
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2789_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_toApplicative_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2789_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v_toFunctor_2760_; lean_object* v_toSeq_2761_; lean_object* v_toSeqLeft_2762_; lean_object* v_toSeqRight_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2787_; 
v_toFunctor_2760_ = lean_ctor_get(v_toApplicative_2756_, 0);
v_toSeq_2761_ = lean_ctor_get(v_toApplicative_2756_, 2);
v_toSeqLeft_2762_ = lean_ctor_get(v_toApplicative_2756_, 3);
v_toSeqRight_2763_ = lean_ctor_get(v_toApplicative_2756_, 4);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_toApplicative_2756_);
if (v_isSharedCheck_2787_ == 0)
{
lean_object* v_unused_2788_; 
v_unused_2788_ = lean_ctor_get(v_toApplicative_2756_, 1);
lean_dec(v_unused_2788_);
v___x_2765_ = v_toApplicative_2756_;
v_isShared_2766_ = v_isSharedCheck_2787_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_toSeqRight_2763_);
lean_inc(v_toSeqLeft_2762_);
lean_inc(v_toSeq_2761_);
lean_inc(v_toFunctor_2760_);
lean_dec(v_toApplicative_2756_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2787_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; lean_object* v___f_2773_; lean_object* v___f_2774_; lean_object* v___x_2776_; 
v___f_2767_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_2768_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_2760_);
v___f_2769_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2769_, 0, v_toFunctor_2760_);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2770_, 0, v_toFunctor_2760_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___f_2769_);
lean_ctor_set(v___x_2771_, 1, v___f_2770_);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toSeqRight_2763_);
v___f_2773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2773_, 0, v_toSeqLeft_2762_);
v___f_2774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2774_, 0, v_toSeq_2761_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 4, v___f_2772_);
lean_ctor_set(v___x_2765_, 3, v___f_2773_);
lean_ctor_set(v___x_2765_, 2, v___f_2774_);
lean_ctor_set(v___x_2765_, 1, v___f_2767_);
lean_ctor_set(v___x_2765_, 0, v___x_2771_);
v___x_2776_ = v___x_2765_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___f_2767_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v___f_2774_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v___f_2773_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v___f_2772_);
v___x_2776_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___f_2768_);
lean_ctor_set(v___x_2758_, 0, v___x_2776_);
v___x_2778_ = v___x_2758_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v___f_2768_);
v___x_2778_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_915__overap_2783_; lean_object* v___x_2784_; 
v___x_2779_ = l_ReaderT_instMonad___redArg(v___x_2778_);
v___x_2780_ = l_ReaderT_instMonad___redArg(v___x_2779_);
v___x_2781_ = lean_box(0);
v___x_2782_ = l_instInhabitedOfMonad___redArg(v___x_2780_, v___x_2781_);
v___x_915__overap_2783_ = lean_panic_fn(v___x_2782_, v_msg_2722_);
v___x_2784_ = lean_apply_7(v___x_915__overap_2783_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, lean_box(0));
return v___x_2784_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v_msg_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
return v_res_2805_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2808_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_2809_ = lean_unsigned_to_nat(40u);
v___x_2810_ = lean_unsigned_to_nat(49u);
v___x_2811_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__1));
v___x_2812_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__0));
v___x_2813_ = l_mkPanicMessageWithDecl(v___x_2812_, v___x_2811_, v___x_2810_, v___x_2809_, v___x_2808_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(lean_object* v_f_2814_, lean_object* v_e_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_ty_2824_; lean_object* v_body_2825_; uint8_t v___x_2828_; 
v___x_2828_ = l_Lean_Expr_hasFVar(v_e_2815_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_e_2815_);
lean_dec_ref(v_f_2814_);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
else
{
switch(lean_obj_tag(v_e_2815_))
{
case 1:
{
lean_object* v_fvarId_2831_; lean_object* v___x_2832_; 
v_fvarId_2831_ = lean_ctor_get(v_e_2815_, 0);
lean_inc(v_fvarId_2831_);
lean_dec_ref(v_e_2815_);
v___x_2832_ = lean_apply_8(v_f_2814_, v_fvarId_2831_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, lean_box(0));
return v___x_2832_;
}
case 2:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_e_2815_);
lean_dec_ref(v_f_2814_);
v___x_2833_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2);
v___x_2834_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v___x_2833_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2834_;
}
case 5:
{
lean_object* v_fn_2835_; lean_object* v_arg_2836_; lean_object* v___x_2837_; 
v_fn_2835_ = lean_ctor_get(v_e_2815_, 0);
lean_inc_ref(v_fn_2835_);
v_arg_2836_ = lean_ctor_get(v_e_2815_, 1);
lean_inc_ref(v_arg_2836_);
lean_dec_ref(v_e_2815_);
lean_inc(v___y_2821_);
lean_inc_ref(v___y_2820_);
lean_inc(v___y_2819_);
lean_inc_ref(v___y_2818_);
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
lean_inc_ref(v_f_2814_);
v___x_2837_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2814_, v_fn_2835_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_dec_ref(v___x_2837_);
v_e_2815_ = v_arg_2836_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2836_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_f_2814_);
return v___x_2837_;
}
}
case 6:
{
lean_object* v_binderType_2839_; lean_object* v_body_2840_; 
v_binderType_2839_ = lean_ctor_get(v_e_2815_, 1);
lean_inc_ref(v_binderType_2839_);
v_body_2840_ = lean_ctor_get(v_e_2815_, 2);
lean_inc_ref(v_body_2840_);
lean_dec_ref(v_e_2815_);
v_ty_2824_ = v_binderType_2839_;
v_body_2825_ = v_body_2840_;
goto v___jp_2823_;
}
case 7:
{
lean_object* v_binderType_2841_; lean_object* v_body_2842_; 
v_binderType_2841_ = lean_ctor_get(v_e_2815_, 1);
lean_inc_ref(v_binderType_2841_);
v_body_2842_ = lean_ctor_get(v_e_2815_, 2);
lean_inc_ref(v_body_2842_);
lean_dec_ref(v_e_2815_);
v_ty_2824_ = v_binderType_2841_;
v_body_2825_ = v_body_2842_;
goto v___jp_2823_;
}
case 8:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec_ref(v_e_2815_);
lean_dec_ref(v_f_2814_);
v___x_2843_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2);
v___x_2844_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v___x_2843_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2844_;
}
case 11:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref(v_e_2815_);
lean_dec_ref(v_f_2814_);
v___x_2845_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___closed__2);
v___x_2846_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0_spec__1(v___x_2845_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2846_;
}
default: 
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_e_2815_);
lean_dec_ref(v_f_2814_);
v___x_2847_ = lean_box(0);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
}
v___jp_2823_:
{
lean_object* v___x_2826_; 
lean_inc(v___y_2821_);
lean_inc_ref(v___y_2820_);
lean_inc(v___y_2819_);
lean_inc_ref(v___y_2818_);
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
lean_inc_ref(v_f_2814_);
v___x_2826_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2814_, v_ty_2824_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_dec_ref(v___x_2826_);
v_e_2815_ = v_body_2825_;
goto _start;
}
else
{
lean_dec_ref(v_body_2825_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_f_2814_);
return v___x_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0___boxed(lean_object* v_f_2849_, lean_object* v_e_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2849_, v_e_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(lean_object* v_f_2859_, lean_object* v_arg_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
switch(lean_obj_tag(v_arg_2860_))
{
case 0:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v_f_2859_);
v___x_2868_ = lean_box(0);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
return v___x_2869_;
}
case 1:
{
lean_object* v_fvarId_2870_; lean_object* v___x_2871_; 
v_fvarId_2870_ = lean_ctor_get(v_arg_2860_, 0);
lean_inc(v_fvarId_2870_);
lean_dec_ref(v_arg_2860_);
v___x_2871_ = lean_apply_8(v_f_2859_, v_fvarId_2870_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, lean_box(0));
return v___x_2871_;
}
default: 
{
lean_object* v_expr_2872_; lean_object* v___x_2873_; 
v_expr_2872_ = lean_ctor_get(v_arg_2860_, 0);
lean_inc_ref(v_expr_2872_);
lean_dec_ref(v_arg_2860_);
v___x_2873_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0_spec__0(v_f_2859_, v_expr_2872_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg___boxed(lean_object* v_f_2874_, lean_object* v_arg_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(v_f_2874_, v_arg_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(lean_object* v_reason_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___f_2893_; lean_object* v___x_2894_; 
v___f_2893_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2893_, 0, v_reason_2884_);
v___x_2894_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(v___f_2893_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg___boxed(lean_object* v_reason_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(v_reason_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0(uint8_t v_pu_2905_, lean_object* v_f_2906_, lean_object* v_arg_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___redArg(v_f_2906_, v_arg_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0___boxed(lean_object* v_pu_2916_, lean_object* v_f_2917_, lean_object* v_arg_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
uint8_t v_pu_boxed_2926_; lean_object* v_res_2927_; 
v_pu_boxed_2926_ = lean_unbox(v_pu_2916_);
v_res_2927_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg_spec__0(v_pu_boxed_2926_, v_f_2917_, v_arg_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(lean_object* v_upperBound_2928_, lean_object* v_ps_2929_, lean_object* v_args_2930_, lean_object* v_reason_2931_, lean_object* v_a_2932_, lean_object* v_b_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_a_2942_; uint8_t v___x_2946_; 
v___x_2946_ = lean_nat_dec_lt(v_a_2932_, v_upperBound_2928_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; 
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v_a_2932_);
lean_dec_ref(v_reason_2931_);
v___x_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_b_2933_);
return v___x_2947_;
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v_type_2950_; uint8_t v_borrow_2951_; lean_object* v___x_2952_; 
v___x_2948_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs_spec__0___redArg___closed__0);
v___x_2949_ = lean_array_get_borrowed(v___x_2948_, v_ps_2929_, v_a_2932_);
v_type_2950_ = lean_ctor_get(v___x_2949_, 2);
v_borrow_2951_ = lean_ctor_get_uint8(v___x_2949_, sizeof(void*)*3);
v___x_2952_ = lean_box(0);
if (v_borrow_2951_ == 0)
{
uint8_t v___x_2953_; 
v___x_2953_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_2950_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_array_fget_borrowed(v_args_2930_, v_a_2932_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v___y_2937_);
lean_inc_ref(v___y_2936_);
lean_inc(v___y_2935_);
lean_inc_ref(v___y_2934_);
lean_inc(v___x_2954_);
lean_inc_ref(v_reason_2931_);
v___x_2955_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(v_reason_2931_, v___x_2954_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_dec_ref(v___x_2955_);
v_a_2942_ = v___x_2952_;
goto v___jp_2941_;
}
else
{
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v_a_2932_);
lean_dec_ref(v_reason_2931_);
return v___x_2955_;
}
}
else
{
v_a_2942_ = v___x_2952_;
goto v___jp_2941_;
}
}
else
{
v_a_2942_ = v___x_2952_;
goto v___jp_2941_;
}
}
v___jp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_nat_add(v_a_2932_, v___x_2943_);
lean_dec(v_a_2932_);
v_a_2932_ = v___x_2944_;
v_b_2933_ = v_a_2942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg___boxed(lean_object* v_upperBound_2956_, lean_object* v_ps_2957_, lean_object* v_args_2958_, lean_object* v_reason_2959_, lean_object* v_a_2960_, lean_object* v_b_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(v_upperBound_2956_, v_ps_2957_, v_args_2958_, v_reason_2959_, v_a_2960_, v_b_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec_ref(v_args_2958_);
lean_dec_ref(v_ps_2957_);
lean_dec(v_upperBound_2956_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(lean_object* v_args_2970_, lean_object* v_ps_2971_, lean_object* v_reason_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2980_ = lean_unsigned_to_nat(0u);
v___x_2981_ = lean_array_get_size(v_args_2970_);
v___x_2982_ = lean_box(0);
v___x_2983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(v___x_2981_, v_ps_2971_, v_args_2970_, v_reason_2972_, v___x_2980_, v___x_2982_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v___x_2983_, 0);
lean_dec(v_unused_2991_);
v___x_2985_ = v___x_2983_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v___x_2983_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2982_);
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2982_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
else
{
return v___x_2983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams___boxed(lean_object* v_args_2992_, lean_object* v_ps_2993_, lean_object* v_reason_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(v_args_2992_, v_ps_2993_, v_reason_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
lean_dec_ref(v_ps_2993_);
lean_dec_ref(v_args_2992_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0(lean_object* v_upperBound_3003_, lean_object* v_ps_3004_, lean_object* v_args_3005_, lean_object* v_reason_3006_, lean_object* v_inst_3007_, lean_object* v_R_3008_, lean_object* v_a_3009_, lean_object* v_b_3010_, lean_object* v_c_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___redArg(v_upperBound_3003_, v_ps_3004_, v_args_3005_, v_reason_3006_, v_a_3009_, v_b_3010_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0___boxed(lean_object* v_upperBound_3020_, lean_object* v_ps_3021_, lean_object* v_args_3022_, lean_object* v_reason_3023_, lean_object* v_inst_3024_, lean_object* v_R_3025_, lean_object* v_a_3026_, lean_object* v_b_3027_, lean_object* v_c_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams_spec__0(v_upperBound_3020_, v_ps_3021_, v_args_3022_, v_reason_3023_, v_inst_3024_, v_R_3025_, v_a_3026_, v_b_3027_, v_c_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec_ref(v_args_3022_);
lean_dec_ref(v_ps_3021_);
lean_dec(v_upperBound_3020_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(lean_object* v_msg_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_options_3043_; lean_object* v_ref_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_options_3043_ = lean_ctor_get(v___y_3040_, 2);
v_ref_3044_ = lean_ctor_get(v___y_3040_, 5);
v___x_3045_ = lean_st_ref_get(v___y_3041_);
v___x_3046_ = lean_st_ref_get(v___y_3039_);
v___x_3047_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3038_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3070_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3070_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3070_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v_env_3052_; lean_object* v_lctx_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3068_; 
v_env_3052_ = lean_ctor_get(v___x_3045_, 0);
lean_inc_ref(v_env_3052_);
lean_dec(v___x_3045_);
v_lctx_3053_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v___x_3046_, 1);
lean_dec(v_unused_3069_);
v___x_3055_ = v___x_3046_;
v_isShared_3056_ = v_isSharedCheck_3068_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_lctx_3053_);
lean_dec(v___x_3046_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3068_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3057_ = lean_unbox(v_a_3048_);
lean_dec(v_a_3048_);
v___x_3058_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3053_, v___x_3057_);
lean_dec_ref(v_lctx_3053_);
v___x_3059_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar_spec__2___redArg___closed__2);
lean_inc_ref(v_options_3043_);
v___x_3060_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3060_, 0, v_env_3052_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
lean_ctor_set(v___x_3060_, 2, v___x_3058_);
lean_ctor_set(v___x_3060_, 3, v_options_3043_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set_tag(v___x_3055_, 3);
lean_ctor_set(v___x_3055_, 1, v_msg_3037_);
lean_ctor_set(v___x_3055_, 0, v___x_3060_);
v___x_3062_ = v___x_3055_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_msg_3037_);
v___x_3062_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
lean_inc(v_ref_3044_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v_ref_3044_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set_tag(v___x_3050_, 1);
lean_ctor_set(v___x_3050_, 0, v___x_3063_);
v___x_3065_ = v___x_3050_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v___x_3046_);
lean_dec(v___x_3045_);
lean_dec_ref(v_msg_3037_);
v_a_3071_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3047_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3047_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg___boxed(lean_object* v_msg_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(v_msg_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0(lean_object* v_00_u03b1_3086_, lean_object* v_msg_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(v_msg_3087_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___boxed(lean_object* v_00_u03b1_3096_, lean_object* v_msg_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0(v_00_u03b1_3096_, v_msg_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1(lean_object* v_msg_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_toApplicative_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3179_; 
v___x_3114_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_3115_ = l_ReaderT_instMonad___redArg(v___x_3114_);
v_toApplicative_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; 
v_unused_3180_ = lean_ctor_get(v___x_3115_, 1);
lean_dec(v_unused_3180_);
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3179_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_toApplicative_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3179_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_toFunctor_3120_; lean_object* v_toSeq_3121_; lean_object* v_toSeqLeft_3122_; lean_object* v_toSeqRight_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3177_; 
v_toFunctor_3120_ = lean_ctor_get(v_toApplicative_3116_, 0);
v_toSeq_3121_ = lean_ctor_get(v_toApplicative_3116_, 2);
v_toSeqLeft_3122_ = lean_ctor_get(v_toApplicative_3116_, 3);
v_toSeqRight_3123_ = lean_ctor_get(v_toApplicative_3116_, 4);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_toApplicative_3116_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v_toApplicative_3116_, 1);
lean_dec(v_unused_3178_);
v___x_3125_ = v_toApplicative_3116_;
v_isShared_3126_ = v_isSharedCheck_3177_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_toSeqRight_3123_);
lean_inc(v_toSeqLeft_3122_);
lean_inc(v_toSeq_3121_);
lean_inc(v_toFunctor_3120_);
lean_dec(v_toApplicative_3116_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3177_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___f_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___f_3132_; lean_object* v___f_3133_; lean_object* v___f_3134_; lean_object* v___x_3136_; 
v___f_3127_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_3128_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_3120_);
v___f_3129_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3129_, 0, v_toFunctor_3120_);
v___f_3130_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3130_, 0, v_toFunctor_3120_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___f_3129_);
lean_ctor_set(v___x_3131_, 1, v___f_3130_);
v___f_3132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3132_, 0, v_toSeqRight_3123_);
v___f_3133_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3133_, 0, v_toSeqLeft_3122_);
v___f_3134_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3134_, 0, v_toSeq_3121_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 4, v___f_3132_);
lean_ctor_set(v___x_3125_, 3, v___f_3133_);
lean_ctor_set(v___x_3125_, 2, v___f_3134_);
lean_ctor_set(v___x_3125_, 1, v___f_3127_);
lean_ctor_set(v___x_3125_, 0, v___x_3131_);
v___x_3136_ = v___x_3125_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___f_3127_);
lean_ctor_set(v_reuseFailAlloc_3176_, 2, v___f_3134_);
lean_ctor_set(v_reuseFailAlloc_3176_, 3, v___f_3133_);
lean_ctor_set(v_reuseFailAlloc_3176_, 4, v___f_3132_);
v___x_3136_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 1, v___f_3128_);
lean_ctor_set(v___x_3118_, 0, v___x_3136_);
v___x_3138_ = v___x_3118_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v___f_3128_);
v___x_3138_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; lean_object* v_toApplicative_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3173_; 
v___x_3139_ = l_ReaderT_instMonad___redArg(v___x_3138_);
v_toApplicative_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v___x_3139_, 1);
lean_dec(v_unused_3174_);
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3173_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_toApplicative_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3173_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v_toFunctor_3144_; lean_object* v_toSeq_3145_; lean_object* v_toSeqLeft_3146_; lean_object* v_toSeqRight_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3171_; 
v_toFunctor_3144_ = lean_ctor_get(v_toApplicative_3140_, 0);
v_toSeq_3145_ = lean_ctor_get(v_toApplicative_3140_, 2);
v_toSeqLeft_3146_ = lean_ctor_get(v_toApplicative_3140_, 3);
v_toSeqRight_3147_ = lean_ctor_get(v_toApplicative_3140_, 4);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_toApplicative_3140_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_toApplicative_3140_, 1);
lean_dec(v_unused_3172_);
v___x_3149_ = v_toApplicative_3140_;
v_isShared_3150_ = v_isSharedCheck_3171_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_toSeqRight_3147_);
lean_inc(v_toSeqLeft_3146_);
lean_inc(v_toSeq_3145_);
lean_inc(v_toFunctor_3144_);
lean_dec(v_toApplicative_3140_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3171_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___f_3158_; lean_object* v___x_3160_; 
v___f_3151_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_3152_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_3144_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toFunctor_3144_);
v___f_3154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3154_, 0, v_toFunctor_3144_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___f_3153_);
lean_ctor_set(v___x_3155_, 1, v___f_3154_);
v___f_3156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3156_, 0, v_toSeqRight_3147_);
v___f_3157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3157_, 0, v_toSeqLeft_3146_);
v___f_3158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3158_, 0, v_toSeq_3145_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 4, v___f_3156_);
lean_ctor_set(v___x_3149_, 3, v___f_3157_);
lean_ctor_set(v___x_3149_, 2, v___f_3158_);
lean_ctor_set(v___x_3149_, 1, v___f_3151_);
lean_ctor_set(v___x_3149_, 0, v___x_3155_);
v___x_3160_ = v___x_3149_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___f_3151_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v___f_3158_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v___f_3157_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v___f_3156_);
v___x_3160_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3162_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 1, v___f_3152_);
lean_ctor_set(v___x_3142_, 0, v___x_3160_);
v___x_3162_ = v___x_3142_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___f_3152_);
v___x_3162_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___f_3166_; lean_object* v___x_3957__overap_3167_; lean_object* v___x_3168_; 
v___x_3163_ = l_ReaderT_instMonad___redArg(v___x_3162_);
v___x_3164_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply_go___closed__0);
v___x_3165_ = l_instInhabitedOfMonad___redArg(v___x_3163_, v___x_3164_);
v___f_3166_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3166_, 0, v___x_3165_);
v___x_3957__overap_3167_ = lean_panic_fn(v___f_3166_, v_msg_3106_);
v___x_3168_ = lean_apply_7(v___x_3957__overap_3167_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, lean_box(0));
return v___x_3168_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1___boxed(lean_object* v_msg_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1(v_msg_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v_res_3189_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__0));
v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
return v___x_3192_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3194_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_3195_ = lean_unsigned_to_nat(26u);
v___x_3196_ = lean_unsigned_to_nat(258u);
v___x_3197_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__2));
v___x_3198_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0));
v___x_3199_ = l_mkPanicMessageWithDecl(v___x_3198_, v___x_3197_, v___x_3196_, v___x_3195_, v___x_3194_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(lean_object* v_k_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3208_; lean_object* v_paramMap_3209_; lean_object* v___x_3210_; 
v___x_3208_ = lean_st_ref_get(v_a_3202_);
v_paramMap_3209_ = lean_ctor_get(v___x_3208_, 1);
lean_inc_ref(v_paramMap_3209_);
lean_dec(v___x_3208_);
v___x_3210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap_spec__0___redArg(v_paramMap_3209_, v_k_3200_);
lean_dec_ref(v_paramMap_3209_);
if (lean_obj_tag(v___x_3210_) == 0)
{
if (lean_obj_tag(v_k_3200_) == 0)
{
lean_object* v_name_3211_; lean_object* v___x_3212_; 
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
v_name_3211_ = lean_ctor_get(v_k_3200_, 0);
lean_inc(v_name_3211_);
lean_dec_ref(v_k_3200_);
lean_inc(v_name_3211_);
v___x_3212_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_name_3211_, v_a_3206_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3226_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3226_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3226_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
if (lean_obj_tag(v_a_3213_) == 1)
{
lean_object* v_val_3217_; lean_object* v_params_3218_; lean_object* v___x_3220_; 
lean_dec(v_name_3211_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
v_val_3217_ = lean_ctor_get(v_a_3213_, 0);
lean_inc(v_val_3217_);
lean_dec_ref(v_a_3213_);
v_params_3218_ = lean_ctor_get(v_val_3217_, 3);
lean_inc_ref(v_params_3218_);
lean_dec(v_val_3217_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v_params_3218_);
v___x_3220_ = v___x_3215_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_params_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_del_object(v___x_3215_);
lean_dec(v_a_3213_);
v___x_3222_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__1);
v___x_3223_ = l_Lean_MessageData_ofName(v_name_3211_);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__0___redArg(v___x_3224_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
return v___x_3225_;
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec(v_name_3211_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
v_a_3227_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3212_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3212_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec_ref(v_k_3200_);
v___x_3235_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___closed__3);
v___x_3236_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo_spec__1(v___x_3235_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
return v___x_3236_;
}
}
else
{
lean_object* v_val_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec_ref(v_k_3200_);
v_val_3237_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3210_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_val_3237_);
lean_dec(v___x_3210_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 0);
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_val_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo___boxed(lean_object* v_k_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v_k_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall(lean_object* v_x_3254_, lean_object* v_v_3255_, lean_object* v_k_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
if (lean_obj_tag(v_v_3255_) == 9)
{
lean_object* v_fn_3267_; lean_object* v_args_3268_; uint8_t v___y_3270_; 
v_fn_3267_ = lean_ctor_get(v_v_3255_, 0);
v_args_3268_ = lean_ctor_get(v_v_3255_, 1);
if (lean_obj_tag(v_k_3256_) == 5)
{
lean_object* v_fvarId_3286_; lean_object* v_currDecl_3287_; uint8_t v___x_3288_; 
v_fvarId_3286_ = lean_ctor_get(v_k_3256_, 0);
v_currDecl_3287_ = lean_ctor_get(v_a_3257_, 1);
v___x_3288_ = lean_name_eq(v_currDecl_3287_, v_fn_3267_);
if (v___x_3288_ == 0)
{
v___y_3270_ = v___x_3288_;
goto v___jp_3269_;
}
else
{
uint8_t v___x_3289_; 
v___x_3289_ = l_Lean_instBEqFVarId_beq(v_x_3254_, v_fvarId_3286_);
v___y_3270_ = v___x_3289_;
goto v___jp_3269_;
}
}
else
{
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
goto v___jp_3264_;
}
v___jp_3269_:
{
if (v___y_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
return v___x_3272_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_inc(v_fn_3267_);
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_fn_3267_);
lean_inc(v_a_3262_);
lean_inc_ref(v_a_3261_);
lean_inc(v_a_3260_);
lean_inc_ref(v_a_3259_);
lean_inc(v_a_3258_);
lean_inc_ref(v_a_3257_);
v___x_3274_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v___x_3273_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
lean_inc(v_fn_3267_);
v___x_3276_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_fn_3267_);
v___x_3277_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(v_args_3268_, v_a_3275_, v___x_3276_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3275_);
return v___x_3277_;
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
v_a_3278_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3274_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3274_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
goto v___jp_3264_;
}
v___jp_3264_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = lean_box(0);
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall___boxed(lean_object* v_x_3290_, lean_object* v_v_3291_, lean_object* v_k_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall(v_x_3290_, v_v_3291_, v_k_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
lean_dec_ref(v_k_3292_);
lean_dec(v_v_3291_);
lean_dec(v_x_3290_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(lean_object* v_reason_3301_, lean_object* v_as_3302_, size_t v_i_3303_, size_t v_stop_3304_, lean_object* v_b_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
uint8_t v___x_3313_; 
v___x_3313_ = lean_usize_dec_eq(v_i_3303_, v_stop_3304_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = lean_array_uget_borrowed(v_as_3302_, v_i_3303_);
lean_inc(v___y_3311_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3309_);
lean_inc_ref(v___y_3308_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
lean_inc(v___x_3314_);
lean_inc_ref(v_reason_3301_);
v___x_3315_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArg(v_reason_3301_, v___x_3314_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; size_t v___x_3317_; size_t v___x_3318_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref(v___x_3315_);
v___x_3317_ = ((size_t)1ULL);
v___x_3318_ = lean_usize_add(v_i_3303_, v___x_3317_);
v_i_3303_ = v___x_3318_;
v_b_3305_ = v_a_3316_;
goto _start;
}
else
{
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_reason_3301_);
return v___x_3315_;
}
}
else
{
lean_object* v___x_3320_; 
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_reason_3301_);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_b_3305_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0___boxed(lean_object* v_reason_3321_, lean_object* v_as_3322_, lean_object* v_i_3323_, lean_object* v_stop_3324_, lean_object* v_b_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
size_t v_i_boxed_3333_; size_t v_stop_boxed_3334_; lean_object* v_res_3335_; 
v_i_boxed_3333_ = lean_unbox_usize(v_i_3323_);
lean_dec(v_i_3323_);
v_stop_boxed_3334_ = lean_unbox_usize(v_stop_3324_);
lean_dec(v_stop_3324_);
v_res_3335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(v_reason_3321_, v_as_3322_, v_i_boxed_3333_, v_stop_boxed_3334_, v_b_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec_ref(v_as_3322_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(lean_object* v_reason_3336_, lean_object* v_as_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = lean_array_get_size(v_as_3337_);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_nat_dec_lt(v___x_3345_, v___x_3346_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec_ref(v_reason_3336_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
return v___x_3349_;
}
else
{
uint8_t v___x_3350_; 
v___x_3350_ = lean_nat_dec_le(v___x_3346_, v___x_3346_);
if (v___x_3350_ == 0)
{
if (v___x_3348_ == 0)
{
lean_object* v___x_3351_; 
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec_ref(v_reason_3336_);
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3347_);
return v___x_3351_;
}
else
{
size_t v___x_3352_; size_t v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = ((size_t)0ULL);
v___x_3353_ = lean_usize_of_nat(v___x_3346_);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(v_reason_3336_, v_as_3337_, v___x_3352_, v___x_3353_, v___x_3347_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
return v___x_3354_;
}
}
else
{
size_t v___x_3355_; size_t v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = ((size_t)0ULL);
v___x_3356_ = lean_usize_of_nat(v___x_3346_);
v___x_3357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs_spec__0(v_reason_3336_, v_as_3337_, v___x_3355_, v___x_3356_, v___x_3347_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
return v___x_3357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs___boxed(lean_object* v_reason_3358_, lean_object* v_as_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(v_reason_3358_, v_as_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
lean_dec_ref(v_as_3359_);
return v_res_3367_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(lean_object* v_k_3368_, lean_object* v_t_3369_){
_start:
{
if (lean_obj_tag(v_t_3369_) == 0)
{
lean_object* v_k_3370_; lean_object* v_l_3371_; lean_object* v_r_3372_; uint8_t v___x_3373_; 
v_k_3370_ = lean_ctor_get(v_t_3369_, 1);
v_l_3371_ = lean_ctor_get(v_t_3369_, 3);
v_r_3372_ = lean_ctor_get(v_t_3369_, 4);
v___x_3373_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3368_, v_k_3370_);
switch(v___x_3373_)
{
case 0:
{
v_t_3369_ = v_l_3371_;
goto _start;
}
case 1:
{
uint8_t v___x_3375_; 
v___x_3375_ = 1;
return v___x_3375_;
}
default: 
{
v_t_3369_ = v_r_3372_;
goto _start;
}
}
}
else
{
uint8_t v___x_3377_; 
v___x_3377_ = 0;
return v___x_3377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg___boxed(lean_object* v_k_3378_, lean_object* v_t_3379_){
_start:
{
uint8_t v_res_3380_; lean_object* v_r_3381_; 
v_res_3380_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(v_k_3378_, v_t_3379_);
lean_dec(v_t_3379_);
lean_dec(v_k_3378_);
v_r_3381_ = lean_box(v_res_3380_);
return v_r_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1(lean_object* v_z_3382_, lean_object* v_as_3383_, size_t v_sz_3384_, size_t v_i_3385_, lean_object* v_b_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_a_3395_; uint8_t v___x_3399_; 
v___x_3399_ = lean_usize_dec_lt(v_i_3385_, v_sz_3384_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v_z_3382_);
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v_b_3386_);
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v_a_3402_; 
v___x_3401_ = lean_box(0);
v_a_3402_ = lean_array_uget(v_as_3383_, v_i_3385_);
if (lean_obj_tag(v_a_3402_) == 1)
{
lean_object* v_fvarId_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3413_; 
v_fvarId_3403_ = lean_ctor_get(v_a_3402_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_a_3402_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3405_ = v_a_3402_;
v_isShared_3406_ = v_isSharedCheck_3413_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_fvarId_3403_);
lean_dec(v_a_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3413_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_paramSet_3407_; uint8_t v___x_3408_; 
v_paramSet_3407_ = lean_ctor_get(v___y_3387_, 2);
v___x_3408_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(v_fvarId_3403_, v_paramSet_3407_);
if (v___x_3408_ == 0)
{
lean_del_object(v___x_3405_);
lean_dec(v_fvarId_3403_);
v_a_3395_ = v___x_3401_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3410_; 
lean_inc(v_z_3382_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set_tag(v___x_3405_, 2);
lean_ctor_set(v___x_3405_, 0, v_z_3382_);
v___x_3410_ = v___x_3405_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_z_3382_);
v___x_3410_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; 
lean_inc(v___y_3392_);
lean_inc_ref(v___y_3391_);
lean_inc(v___y_3390_);
lean_inc_ref(v___y_3389_);
v___x_3411_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_3403_, v___x_3410_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_dec_ref(v___x_3411_);
v_a_3395_ = v___x_3401_;
goto v___jp_3394_;
}
else
{
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v_z_3382_);
return v___x_3411_;
}
}
}
}
}
else
{
lean_dec(v_a_3402_);
v_a_3395_ = v___x_3401_;
goto v___jp_3394_;
}
}
v___jp_3394_:
{
size_t v___x_3396_; size_t v___x_3397_; 
v___x_3396_ = ((size_t)1ULL);
v___x_3397_ = lean_usize_add(v_i_3385_, v___x_3396_);
v_i_3385_ = v___x_3397_;
v_b_3386_ = v_a_3395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1___boxed(lean_object* v_z_3414_, lean_object* v_as_3415_, lean_object* v_sz_3416_, lean_object* v_i_3417_, lean_object* v_b_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
size_t v_sz_boxed_3426_; size_t v_i_boxed_3427_; lean_object* v_res_3428_; 
v_sz_boxed_3426_ = lean_unbox_usize(v_sz_3416_);
lean_dec(v_sz_3416_);
v_i_boxed_3427_ = lean_unbox_usize(v_i_3417_);
lean_dec(v_i_3417_);
v_res_3428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1(v_z_3414_, v_as_3415_, v_sz_boxed_3426_, v_i_boxed_3427_, v_b_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v_as_3415_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(lean_object* v_z_3429_, lean_object* v_args_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v___x_3438_; size_t v_sz_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3438_ = lean_box(0);
v_sz_3439_ = lean_array_size(v_args_3430_);
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__1(v_z_3429_, v_args_3430_, v_sz_3439_, v___x_3440_, v___x_3438_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; 
v_unused_3449_ = lean_ctor_get(v___x_3441_, 0);
lean_dec(v_unused_3449_);
v___x_3443_ = v___x_3441_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_dec(v___x_3441_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3438_);
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3438_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
else
{
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam___boxed(lean_object* v_z_3450_, lean_object* v_args_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(v_z_3450_, v_args_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec_ref(v_args_3451_);
return v_res_3459_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0(lean_object* v_00_u03b2_3460_, lean_object* v_k_3461_, lean_object* v_t_3462_){
_start:
{
uint8_t v___x_3463_; 
v___x_3463_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___redArg(v_k_3461_, v_t_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0___boxed(lean_object* v_00_u03b2_3464_, lean_object* v_k_3465_, lean_object* v_t_3466_){
_start:
{
uint8_t v_res_3467_; lean_object* v_r_3468_; 
v_res_3467_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam_spec__0(v_00_u03b2_3464_, v_k_3465_, v_t_3466_);
lean_dec(v_t_3466_);
lean_dec(v_k_3465_);
v_r_3468_ = lean_box(v_res_3467_);
return v_r_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue(lean_object* v_z_3469_, lean_object* v_v_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
switch(lean_obj_tag(v_v_3470_))
{
case 11:
{
lean_object* v_var_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v_var_3478_ = lean_ctor_get(v_v_3470_, 1);
lean_inc(v_var_3478_);
lean_dec_ref(v_v_3470_);
lean_inc(v_z_3469_);
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v_z_3469_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc_ref(v___x_3479_);
v___x_3480_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3469_, v___x_3479_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3481_; 
lean_dec_ref(v___x_3480_);
v___x_3481_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_var_3478_, v___x_3479_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
return v___x_3481_;
}
else
{
lean_dec_ref(v___x_3479_);
lean_dec(v_var_3478_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
return v___x_3480_;
}
}
case 12:
{
lean_object* v_var_3482_; lean_object* v_args_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_var_3482_ = lean_ctor_get(v_v_3470_, 0);
lean_inc(v_var_3482_);
v_args_3483_ = lean_ctor_get(v_v_3470_, 2);
lean_inc_ref(v_args_3483_);
lean_dec_ref(v_v_3470_);
lean_inc(v_z_3469_);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_z_3469_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc_ref(v___x_3484_);
lean_inc(v_z_3469_);
v___x_3485_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3469_, v___x_3484_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v___x_3486_; 
lean_dec_ref(v___x_3485_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
v___x_3486_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_var_3482_, v___x_3484_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v___x_3487_; 
lean_dec_ref(v___x_3486_);
v___x_3487_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(v_z_3469_, v_args_3483_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec_ref(v_args_3483_);
return v___x_3487_;
}
else
{
lean_dec_ref(v_args_3483_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
return v___x_3486_;
}
}
else
{
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_args_3483_);
lean_dec(v_var_3482_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
return v___x_3485_;
}
}
case 5:
{
lean_object* v_args_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v_args_3488_ = lean_ctor_get(v_v_3470_, 1);
lean_inc_ref(v_args_3488_);
lean_dec_ref(v_v_3470_);
lean_inc(v_z_3469_);
v___x_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3489_, 0, v_z_3469_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc(v_z_3469_);
v___x_3490_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3469_, v___x_3489_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; 
lean_dec_ref(v___x_3490_);
v___x_3491_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsIfParam(v_z_3469_, v_args_3488_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec_ref(v_args_3488_);
return v___x_3491_;
}
else
{
lean_dec_ref(v_args_3488_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
return v___x_3490_;
}
}
case 6:
{
lean_object* v_var_3492_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___x_3513_; lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3523_; 
v_var_3492_ = lean_ctor_get(v_v_3470_, 1);
lean_inc(v_var_3492_);
lean_dec_ref(v_v_3470_);
v___x_3513_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_var_3492_, v_a_3472_);
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3523_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3523_;
goto v_resetjp_3515_;
}
v___jp_3493_:
{
lean_object* v___x_3500_; lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3512_; 
v___x_3500_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_isOwned___redArg(v_z_3469_, v___y_3495_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3512_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3512_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
uint8_t v___x_3505_; 
v___x_3505_ = lean_unbox(v_a_3501_);
lean_dec(v_a_3501_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v_var_3492_);
lean_dec(v_z_3469_);
v___x_3506_ = lean_box(0);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3506_);
v___x_3508_ = v___x_3503_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_del_object(v___x_3503_);
v___x_3510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_z_3469_);
v___x_3511_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_var_3492_, v___x_3510_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v___x_3511_;
}
}
}
v_resetjp_3515_:
{
uint8_t v___x_3518_; 
v___x_3518_ = lean_unbox(v_a_3514_);
lean_dec(v_a_3514_);
if (v___x_3518_ == 0)
{
lean_del_object(v___x_3516_);
v___y_3494_ = v_a_3471_;
v___y_3495_ = v_a_3472_;
v___y_3496_ = v_a_3473_;
v___y_3497_ = v_a_3474_;
v___y_3498_ = v_a_3475_;
v___y_3499_ = v_a_3476_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3520_; 
lean_inc(v_z_3469_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set_tag(v___x_3516_, 3);
lean_ctor_set(v___x_3516_, 0, v_z_3469_);
v___x_3520_ = v___x_3516_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_z_3469_);
v___x_3520_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; 
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc(v_z_3469_);
v___x_3521_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3469_, v___x_3520_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_dec_ref(v___x_3521_);
v___y_3494_ = v_a_3471_;
v___y_3495_ = v_a_3472_;
v___y_3496_ = v_a_3473_;
v___y_3497_ = v_a_3474_;
v___y_3498_ = v_a_3475_;
v___y_3499_ = v_a_3476_;
goto v___jp_3493_;
}
else
{
lean_dec(v_var_3492_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
return v___x_3521_;
}
}
}
}
}
case 9:
{
lean_object* v_fn_3524_; lean_object* v_args_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_fn_3524_ = lean_ctor_get(v_v_3470_, 0);
lean_inc(v_fn_3524_);
v_args_3525_ = lean_ctor_get(v_v_3470_, 1);
lean_inc_ref(v_args_3525_);
lean_dec_ref(v_v_3470_);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_fn_3524_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc(v_a_3472_);
lean_inc_ref(v_a_3471_);
v___x_3527_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v___x_3526_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref(v___x_3527_);
lean_inc(v_z_3469_);
v___x_3529_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_z_3469_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc(v_z_3469_);
v___x_3530_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3469_, v___x_3529_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3538_; 
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v___x_3530_, 0);
lean_dec(v_unused_3539_);
v___x_3532_ = v___x_3530_;
v_isShared_3533_ = v_isSharedCheck_3538_;
goto v_resetjp_3531_;
}
else
{
lean_dec(v___x_3530_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3538_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 5);
lean_ctor_set(v___x_3532_, 0, v_z_3469_);
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_z_3469_);
v___x_3535_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3536_; 
v___x_3536_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(v_args_3525_, v_a_3528_, v___x_3535_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3528_);
lean_dec_ref(v_args_3525_);
return v___x_3536_;
}
}
}
else
{
lean_dec(v_a_3528_);
lean_dec_ref(v_args_3525_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
return v___x_3530_;
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v_args_3525_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
v_a_3540_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3527_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3527_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_3548_; lean_object* v_args_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_fvarId_3548_ = lean_ctor_get(v_v_3470_, 0);
lean_inc(v_fvarId_3548_);
v_args_3549_ = lean_ctor_get(v_v_3470_, 1);
lean_inc_ref(v_args_3549_);
lean_dec_ref(v_v_3470_);
lean_inc(v_z_3469_);
v___x_3550_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_z_3469_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc(v_z_3469_);
v___x_3551_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3469_, v___x_3550_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3560_; 
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v___x_3551_, 0);
lean_dec(v_unused_3561_);
v___x_3553_ = v___x_3551_;
v_isShared_3554_ = v_isSharedCheck_3560_;
goto v_resetjp_3552_;
}
else
{
lean_dec(v___x_3551_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3560_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set_tag(v___x_3553_, 6);
lean_ctor_set(v___x_3553_, 0, v_z_3469_);
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_z_3469_);
v___x_3556_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc_ref(v___x_3556_);
v___x_3557_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_fvarId_3548_, v___x_3556_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v___x_3558_; 
lean_dec_ref(v___x_3557_);
v___x_3558_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(v___x_3556_, v_args_3549_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec_ref(v_args_3549_);
return v___x_3558_;
}
else
{
lean_dec_ref(v___x_3556_);
lean_dec_ref(v_args_3549_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
return v___x_3557_;
}
}
}
}
else
{
lean_dec_ref(v_args_3549_);
lean_dec(v_fvarId_3548_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
return v___x_3551_;
}
}
case 10:
{
lean_object* v_args_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_args_3562_ = lean_ctor_get(v_v_3470_, 1);
lean_inc_ref(v_args_3562_);
lean_dec_ref(v_v_3470_);
lean_inc(v_z_3469_);
v___x_3563_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3563_, 0, v_z_3469_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc(v_z_3469_);
v___x_3564_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar(v_z_3469_, v___x_3563_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3572_; 
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v___x_3564_, 0);
lean_dec(v_unused_3573_);
v___x_3566_ = v___x_3564_;
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
else
{
lean_dec(v___x_3564_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set_tag(v___x_3566_, 7);
lean_ctor_set(v___x_3566_, 0, v_z_3469_);
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_z_3469_);
v___x_3569_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; 
v___x_3570_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgs(v___x_3569_, v_args_3562_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec_ref(v_args_3562_);
return v___x_3570_;
}
}
}
else
{
lean_dec_ref(v_args_3562_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_z_3469_);
return v___x_3564_;
}
}
default: 
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_v_3470_);
lean_dec(v_z_3469_);
v___x_3574_ = lean_box(0);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue___boxed(lean_object* v_z_3576_, lean_object* v_v_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue(v_z_3576_, v_v_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(lean_object* v_alt_3586_, lean_object* v_f_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
switch(lean_obj_tag(v_alt_3586_))
{
case 0:
{
lean_object* v_code_3595_; lean_object* v___x_3596_; 
v_code_3595_ = lean_ctor_get(v_alt_3586_, 2);
lean_inc_ref(v_code_3595_);
lean_dec_ref(v_alt_3586_);
v___x_3596_ = lean_apply_8(v_f_3587_, v_code_3595_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, lean_box(0));
return v___x_3596_;
}
case 1:
{
lean_object* v_code_3597_; lean_object* v___x_3598_; 
v_code_3597_ = lean_ctor_get(v_alt_3586_, 1);
lean_inc_ref(v_code_3597_);
lean_dec_ref(v_alt_3586_);
v___x_3598_ = lean_apply_8(v_f_3587_, v_code_3597_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, lean_box(0));
return v___x_3598_;
}
default: 
{
lean_object* v_code_3599_; lean_object* v___x_3600_; 
v_code_3599_ = lean_ctor_get(v_alt_3586_, 0);
lean_inc_ref(v_code_3599_);
lean_dec_ref(v_alt_3586_);
v___x_3600_ = lean_apply_8(v_f_3587_, v_code_3599_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, lean_box(0));
return v___x_3600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg___boxed(lean_object* v_alt_3601_, lean_object* v_f_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(v_alt_3601_, v_f_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0(uint8_t v_pu_3611_, lean_object* v_alt_3612_, lean_object* v_f_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(v_alt_3612_, v_f_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___boxed(lean_object* v_pu_3622_, lean_object* v_alt_3623_, lean_object* v_f_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v_pu_boxed_3632_; lean_object* v_res_3633_; 
v_pu_boxed_3632_ = lean_unbox(v_pu_3622_);
v_res_3633_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0(v_pu_boxed_3632_, v_alt_3623_, v_f_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3(lean_object* v_msg_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_toApplicative_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3707_; 
v___x_3642_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__0);
v___x_3643_ = l_ReaderT_instMonad___redArg(v___x_3642_);
v_toApplicative_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v___x_3643_, 1);
lean_dec(v_unused_3708_);
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3707_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_toApplicative_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3707_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_toFunctor_3648_; lean_object* v_toSeq_3649_; lean_object* v_toSeqLeft_3650_; lean_object* v_toSeqRight_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3705_; 
v_toFunctor_3648_ = lean_ctor_get(v_toApplicative_3644_, 0);
v_toSeq_3649_ = lean_ctor_get(v_toApplicative_3644_, 2);
v_toSeqLeft_3650_ = lean_ctor_get(v_toApplicative_3644_, 3);
v_toSeqRight_3651_ = lean_ctor_get(v_toApplicative_3644_, 4);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_toApplicative_3644_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v_toApplicative_3644_, 1);
lean_dec(v_unused_3706_);
v___x_3653_ = v_toApplicative_3644_;
v_isShared_3654_ = v_isSharedCheck_3705_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_toSeqRight_3651_);
lean_inc(v_toSeqLeft_3650_);
lean_inc(v_toSeq_3649_);
lean_inc(v_toFunctor_3648_);
lean_dec(v_toApplicative_3644_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3705_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___f_3655_; lean_object* v___f_3656_; lean_object* v___f_3657_; lean_object* v___f_3658_; lean_object* v___x_3659_; lean_object* v___f_3660_; lean_object* v___f_3661_; lean_object* v___f_3662_; lean_object* v___x_3664_; 
v___f_3655_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__1));
v___f_3656_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__2));
lean_inc_ref(v_toFunctor_3648_);
v___f_3657_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3657_, 0, v_toFunctor_3648_);
v___f_3658_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3658_, 0, v_toFunctor_3648_);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___f_3657_);
lean_ctor_set(v___x_3659_, 1, v___f_3658_);
v___f_3660_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3660_, 0, v_toSeqRight_3651_);
v___f_3661_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3661_, 0, v_toSeqLeft_3650_);
v___f_3662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3662_, 0, v_toSeq_3649_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 4, v___f_3660_);
lean_ctor_set(v___x_3653_, 3, v___f_3661_);
lean_ctor_set(v___x_3653_, 2, v___f_3662_);
lean_ctor_set(v___x_3653_, 1, v___f_3655_);
lean_ctor_set(v___x_3653_, 0, v___x_3659_);
v___x_3664_ = v___x_3653_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___f_3655_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v___f_3662_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v___f_3661_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v___f_3660_);
v___x_3664_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 1, v___f_3656_);
lean_ctor_set(v___x_3646_, 0, v___x_3664_);
v___x_3666_ = v___x_3646_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v___f_3656_);
v___x_3666_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v_toApplicative_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3701_; 
v___x_3667_ = l_ReaderT_instMonad___redArg(v___x_3666_);
v_toApplicative_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v___x_3667_, 1);
lean_dec(v_unused_3702_);
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3701_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_toApplicative_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3701_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v_toFunctor_3672_; lean_object* v_toSeq_3673_; lean_object* v_toSeqLeft_3674_; lean_object* v_toSeqRight_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3699_; 
v_toFunctor_3672_ = lean_ctor_get(v_toApplicative_3668_, 0);
v_toSeq_3673_ = lean_ctor_get(v_toApplicative_3668_, 2);
v_toSeqLeft_3674_ = lean_ctor_get(v_toApplicative_3668_, 3);
v_toSeqRight_3675_ = lean_ctor_get(v_toApplicative_3668_, 4);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_toApplicative_3668_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_toApplicative_3668_, 1);
lean_dec(v_unused_3700_);
v___x_3677_ = v_toApplicative_3668_;
v_isShared_3678_ = v_isSharedCheck_3699_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_toSeqRight_3675_);
lean_inc(v_toSeqLeft_3674_);
lean_inc(v_toSeq_3673_);
lean_inc(v_toFunctor_3672_);
lean_dec(v_toApplicative_3668_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3699_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___f_3681_; lean_object* v___f_3682_; lean_object* v___x_3683_; lean_object* v___f_3684_; lean_object* v___f_3685_; lean_object* v___f_3686_; lean_object* v___x_3688_; 
v___f_3679_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__3));
v___f_3680_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode_spec__3___closed__4));
lean_inc_ref(v_toFunctor_3672_);
v___f_3681_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3681_, 0, v_toFunctor_3672_);
v___f_3682_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3682_, 0, v_toFunctor_3672_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___f_3681_);
lean_ctor_set(v___x_3683_, 1, v___f_3682_);
v___f_3684_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3684_, 0, v_toSeqRight_3675_);
v___f_3685_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3685_, 0, v_toSeqLeft_3674_);
v___f_3686_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3686_, 0, v_toSeq_3673_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v___f_3684_);
lean_ctor_set(v___x_3677_, 3, v___f_3685_);
lean_ctor_set(v___x_3677_, 2, v___f_3686_);
lean_ctor_set(v___x_3677_, 1, v___f_3679_);
lean_ctor_set(v___x_3677_, 0, v___x_3683_);
v___x_3688_ = v___x_3677_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v___f_3679_);
lean_ctor_set(v_reuseFailAlloc_3698_, 2, v___f_3686_);
lean_ctor_set(v_reuseFailAlloc_3698_, 3, v___f_3685_);
lean_ctor_set(v_reuseFailAlloc_3698_, 4, v___f_3684_);
v___x_3688_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 1, v___f_3680_);
lean_ctor_set(v___x_3670_, 0, v___x_3688_);
v___x_3690_ = v___x_3670_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___f_3680_);
v___x_3690_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___f_3694_; lean_object* v___x_4789__overap_3695_; lean_object* v___x_3696_; 
v___x_3691_ = l_ReaderT_instMonad___redArg(v___x_3690_);
v___x_3692_ = lean_box(0);
v___x_3693_ = l_instInhabitedOfMonad___redArg(v___x_3691_, v___x_3692_);
v___f_3694_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3694_, 0, v___x_3693_);
v___x_4789__overap_3695_ = lean_panic_fn(v___f_3694_, v_msg_3634_);
v___x_3696_ = lean_apply_7(v___x_4789__overap_3695_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, lean_box(0));
return v___x_3696_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3___boxed(lean_object* v_msg_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3(v_msg_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(lean_object* v_as_3718_, size_t v_i_3719_, size_t v_stop_3720_, lean_object* v_b_3721_){
_start:
{
uint8_t v___x_3722_; 
v___x_3722_ = lean_usize_dec_eq(v_i_3719_, v_stop_3720_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; lean_object* v_fvarId_3724_; lean_object* v___x_3725_; size_t v___x_3726_; size_t v___x_3727_; 
v___x_3723_ = lean_array_uget_borrowed(v_as_3718_, v_i_3719_);
v_fvarId_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_fvarId_3724_);
v___x_3725_ = l_Lean_FVarIdSet_insert(v_b_3721_, v_fvarId_3724_);
v___x_3726_ = ((size_t)1ULL);
v___x_3727_ = lean_usize_add(v_i_3719_, v___x_3726_);
v_i_3719_ = v___x_3727_;
v_b_3721_ = v___x_3725_;
goto _start;
}
else
{
return v_b_3721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1___boxed(lean_object* v_as_3729_, lean_object* v_i_3730_, lean_object* v_stop_3731_, lean_object* v_b_3732_){
_start:
{
size_t v_i_boxed_3733_; size_t v_stop_boxed_3734_; lean_object* v_res_3735_; 
v_i_boxed_3733_ = lean_unbox_usize(v_i_3730_);
lean_dec(v_i_3730_);
v_stop_boxed_3734_ = lean_unbox_usize(v_stop_3731_);
lean_dec(v_stop_3731_);
v_res_3735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_as_3729_, v_i_boxed_3733_, v_stop_boxed_3734_, v_b_3732_);
lean_dec_ref(v_as_3729_);
return v_res_3735_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1(void){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3737_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__2));
v___x_3738_ = lean_unsigned_to_nat(61u);
v___x_3739_ = lean_unsigned_to_nat(347u);
v___x_3740_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__0));
v___x_3741_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap_goCode___closed__0));
v___x_3742_ = l_mkPanicMessageWithDecl(v___x_3741_, v___x_3740_, v___x_3739_, v___x_3738_, v___x_3737_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(lean_object* v_code_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
switch(lean_obj_tag(v_code_3743_))
{
case 0:
{
lean_object* v_decl_3751_; lean_object* v_k_3752_; lean_object* v___x_3753_; 
v_decl_3751_ = lean_ctor_get(v_code_3743_, 0);
lean_inc_ref(v_decl_3751_);
v_k_3752_ = lean_ctor_get(v_code_3743_, 1);
lean_inc_ref(v_k_3752_);
lean_dec_ref(v_code_3743_);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
lean_inc(v_a_3745_);
lean_inc_ref(v_a_3744_);
lean_inc_ref(v_k_3752_);
v___x_3753_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_k_3752_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_fvarId_3754_; lean_object* v_value_3755_; lean_object* v___x_3756_; 
lean_dec_ref(v___x_3753_);
v_fvarId_3754_ = lean_ctor_get(v_decl_3751_, 0);
lean_inc(v_fvarId_3754_);
v_value_3755_ = lean_ctor_get(v_decl_3751_, 3);
lean_inc(v_value_3755_);
lean_dec_ref(v_decl_3751_);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
lean_inc(v_a_3745_);
lean_inc_ref(v_a_3744_);
lean_inc(v_value_3755_);
lean_inc(v_fvarId_3754_);
v___x_3756_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectLetValue(v_fvarId_3754_, v_value_3755_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v___x_3757_; 
lean_dec_ref(v___x_3756_);
v___x_3757_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_preserveTailCall(v_fvarId_3754_, v_value_3755_, v_k_3752_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_k_3752_);
lean_dec(v_value_3755_);
lean_dec(v_fvarId_3754_);
return v___x_3757_;
}
else
{
lean_dec(v_value_3755_);
lean_dec(v_fvarId_3754_);
lean_dec_ref(v_k_3752_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v___x_3756_;
}
}
else
{
lean_dec_ref(v_k_3752_);
lean_dec_ref(v_decl_3751_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v___x_3753_;
}
}
case 2:
{
lean_object* v_decl_3758_; lean_object* v_k_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3788_; 
v_decl_3758_ = lean_ctor_get(v_code_3743_, 0);
v_k_3759_ = lean_ctor_get(v_code_3743_, 1);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_code_3743_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3761_ = v_code_3743_;
v_isShared_3762_ = v_isSharedCheck_3788_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_k_3759_);
lean_inc(v_decl_3758_);
lean_dec(v_code_3743_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3788_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v_fvarId_3763_; lean_object* v_params_3764_; lean_object* v_value_3765_; lean_object* v_decls_3766_; lean_object* v_currDecl_3767_; lean_object* v_paramSet_3768_; lean_object* v___y_3770_; lean_object* v___x_3778_; lean_object* v___x_3779_; uint8_t v___x_3780_; 
v_fvarId_3763_ = lean_ctor_get(v_decl_3758_, 0);
lean_inc(v_fvarId_3763_);
v_params_3764_ = lean_ctor_get(v_decl_3758_, 2);
lean_inc_ref(v_params_3764_);
v_value_3765_ = lean_ctor_get(v_decl_3758_, 4);
lean_inc_ref(v_value_3765_);
lean_dec_ref(v_decl_3758_);
v_decls_3766_ = lean_ctor_get(v_a_3744_, 0);
v_currDecl_3767_ = lean_ctor_get(v_a_3744_, 1);
v_paramSet_3768_ = lean_ctor_get(v_a_3744_, 2);
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = lean_array_get_size(v_params_3764_);
v___x_3780_ = lean_nat_dec_lt(v___x_3778_, v___x_3779_);
if (v___x_3780_ == 0)
{
lean_dec_ref(v_params_3764_);
lean_inc(v_paramSet_3768_);
v___y_3770_ = v_paramSet_3768_;
goto v___jp_3769_;
}
else
{
uint8_t v___x_3781_; 
v___x_3781_ = lean_nat_dec_le(v___x_3779_, v___x_3779_);
if (v___x_3781_ == 0)
{
if (v___x_3780_ == 0)
{
lean_dec_ref(v_params_3764_);
lean_inc(v_paramSet_3768_);
v___y_3770_ = v_paramSet_3768_;
goto v___jp_3769_;
}
else
{
size_t v___x_3782_; size_t v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = ((size_t)0ULL);
v___x_3783_ = lean_usize_of_nat(v___x_3779_);
lean_inc(v_paramSet_3768_);
v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3764_, v___x_3782_, v___x_3783_, v_paramSet_3768_);
lean_dec_ref(v_params_3764_);
v___y_3770_ = v___x_3784_;
goto v___jp_3769_;
}
}
else
{
size_t v___x_3785_; size_t v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = ((size_t)0ULL);
v___x_3786_ = lean_usize_of_nat(v___x_3779_);
lean_inc(v_paramSet_3768_);
v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3764_, v___x_3785_, v___x_3786_, v_paramSet_3768_);
lean_dec_ref(v_params_3764_);
v___y_3770_ = v___x_3787_;
goto v___jp_3769_;
}
}
v___jp_3769_:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
lean_inc(v_currDecl_3767_);
lean_inc_ref(v_decls_3766_);
v___x_3771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3771_, 0, v_decls_3766_);
lean_ctor_set(v___x_3771_, 1, v_currDecl_3767_);
lean_ctor_set(v___x_3771_, 2, v___y_3770_);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
lean_inc(v_a_3745_);
v___x_3772_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_value_3765_, v___x_3771_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3774_; 
lean_dec_ref(v___x_3772_);
lean_inc(v_currDecl_3767_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 1);
lean_ctor_set(v___x_3761_, 1, v_fvarId_3763_);
lean_ctor_set(v___x_3761_, 0, v_currDecl_3767_);
v___x_3774_ = v___x_3761_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_currDecl_3767_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_fvarId_3763_);
v___x_3774_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3775_; 
v___x_3775_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(v___x_3774_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_dec_ref(v___x_3775_);
v_code_3743_ = v_k_3759_;
goto _start;
}
else
{
lean_dec_ref(v_k_3759_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v___x_3775_;
}
}
}
else
{
lean_dec(v_fvarId_3763_);
lean_del_object(v___x_3761_);
lean_dec_ref(v_k_3759_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v___x_3772_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3789_; lean_object* v_args_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3819_; 
v_fvarId_3789_ = lean_ctor_get(v_code_3743_, 0);
v_args_3790_ = lean_ctor_get(v_code_3743_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_code_3743_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3792_ = v_code_3743_;
v_isShared_3793_ = v_isSharedCheck_3819_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_args_3790_);
lean_inc(v_fvarId_3789_);
lean_dec(v_code_3743_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3819_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_currDecl_3794_; lean_object* v___x_3796_; 
v_currDecl_3794_ = lean_ctor_get(v_a_3744_, 1);
lean_inc(v_fvarId_3789_);
lean_inc(v_currDecl_3794_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set_tag(v___x_3792_, 1);
lean_ctor_set(v___x_3792_, 1, v_fvarId_3789_);
lean_ctor_set(v___x_3792_, 0, v_currDecl_3794_);
v___x_3796_ = v___x_3792_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_currDecl_3794_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_fvarId_3789_);
v___x_3796_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; 
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
lean_inc(v_a_3745_);
lean_inc_ref(v_a_3744_);
v___x_3797_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_getParamInfo(v___x_3796_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
lean_inc(v_fvarId_3789_);
v___x_3799_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_fvarId_3789_);
lean_inc(v_a_3749_);
lean_inc_ref(v_a_3748_);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
lean_inc(v_a_3745_);
lean_inc_ref(v_a_3744_);
v___x_3800_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownArgsUsingParams(v_args_3790_, v_a_3798_, v___x_3799_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3808_; 
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v___x_3800_, 0);
lean_dec(v_unused_3809_);
v___x_3802_ = v___x_3800_;
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
else
{
lean_dec(v___x_3800_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 10);
lean_ctor_set(v___x_3802_, 0, v_fvarId_3789_);
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_fvarId_3789_);
v___x_3805_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; 
v___x_3806_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownParamsUsingArgs(v_args_3790_, v_a_3798_, v___x_3805_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3798_);
lean_dec_ref(v_args_3790_);
return v___x_3806_;
}
}
}
else
{
lean_dec(v_a_3798_);
lean_dec_ref(v_args_3790_);
lean_dec(v_fvarId_3789_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v___x_3800_;
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v_args_3790_);
lean_dec(v_fvarId_3789_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
v_a_3810_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3797_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3797_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3842_; 
v_cases_3820_ = lean_ctor_get(v_code_3743_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_code_3743_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3822_ = v_code_3743_;
v_isShared_3823_ = v_isSharedCheck_3842_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_cases_3820_);
lean_dec(v_code_3743_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3842_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v_alts_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_alts_3824_ = lean_ctor_get(v_cases_3820_, 3);
lean_inc_ref(v_alts_3824_);
lean_dec_ref(v_cases_3820_);
v___x_3825_ = lean_unsigned_to_nat(0u);
v___x_3826_ = lean_array_get_size(v_alts_3824_);
v___x_3827_ = lean_box(0);
v___x_3828_ = lean_nat_dec_lt(v___x_3825_, v___x_3826_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3830_; 
lean_dec_ref(v_alts_3824_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set_tag(v___x_3822_, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3827_);
v___x_3830_ = v___x_3822_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3827_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
else
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_nat_dec_le(v___x_3826_, v___x_3826_);
if (v___x_3832_ == 0)
{
if (v___x_3828_ == 0)
{
lean_object* v___x_3834_; 
lean_dec_ref(v_alts_3824_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set_tag(v___x_3822_, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3827_);
v___x_3834_ = v___x_3822_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3827_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
else
{
size_t v___x_3836_; size_t v___x_3837_; lean_object* v___x_3838_; 
lean_del_object(v___x_3822_);
v___x_3836_ = ((size_t)0ULL);
v___x_3837_ = lean_usize_of_nat(v___x_3826_);
v___x_3838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(v_alts_3824_, v___x_3836_, v___x_3837_, v___x_3827_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_alts_3824_);
return v___x_3838_;
}
}
else
{
size_t v___x_3839_; size_t v___x_3840_; lean_object* v___x_3841_; 
lean_del_object(v___x_3822_);
v___x_3839_ = ((size_t)0ULL);
v___x_3840_ = lean_usize_of_nat(v___x_3826_);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(v_alts_3824_, v___x_3839_, v___x_3840_, v___x_3827_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec_ref(v_alts_3824_);
return v___x_3841_;
}
}
}
}
case 5:
{
lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_code_3743_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v_code_3743_, 0);
lean_dec(v_unused_3851_);
v___x_3844_ = v_code_3743_;
v_isShared_3845_ = v_isSharedCheck_3850_;
goto v_resetjp_3843_;
}
else
{
lean_dec(v_code_3743_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3850_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3846_ = lean_box(0);
if (v_isShared_3845_ == 0)
{
lean_ctor_set_tag(v___x_3844_, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3846_);
v___x_3848_ = v___x_3844_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
case 6:
{
lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3859_; 
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_code_3743_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; 
v_unused_3860_ = lean_ctor_get(v_code_3743_, 0);
lean_dec(v_unused_3860_);
v___x_3853_ = v_code_3743_;
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
else
{
lean_dec(v_code_3743_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3855_ = lean_box(0);
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3855_);
v___x_3857_ = v___x_3853_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
case 8:
{
lean_object* v_k_3861_; 
v_k_3861_ = lean_ctor_get(v_code_3743_, 3);
lean_inc_ref(v_k_3861_);
lean_dec_ref(v_code_3743_);
v_code_3743_ = v_k_3861_;
goto _start;
}
case 9:
{
lean_object* v_k_3863_; 
v_k_3863_ = lean_ctor_get(v_code_3743_, 5);
lean_inc_ref(v_k_3863_);
lean_dec_ref(v_code_3743_);
v_code_3743_ = v_k_3863_;
goto _start;
}
default: 
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_dec_ref(v_code_3743_);
v___x_3865_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1, &l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1_once, _init_l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___closed__1);
v___x_3866_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__3(v___x_3865_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
return v___x_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___boxed(lean_object* v_code_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_code_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(lean_object* v_as_3876_, size_t v_i_3877_, size_t v_stop_3878_, lean_object* v_b_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
uint8_t v___x_3887_; 
v___x_3887_ = lean_usize_dec_eq(v_i_3877_, v_stop_3878_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3888_ = lean_array_uget_borrowed(v_as_3876_, v_i_3877_);
v___x_3889_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode___boxed), 8, 0);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___x_3888_);
v___x_3890_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__0___redArg(v___x_3888_, v___x_3889_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; size_t v___x_3892_; size_t v___x_3893_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref(v___x_3890_);
v___x_3892_ = ((size_t)1ULL);
v___x_3893_ = lean_usize_add(v_i_3877_, v___x_3892_);
v_i_3877_ = v___x_3893_;
v_b_3879_ = v_a_3891_;
goto _start;
}
else
{
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
return v___x_3890_;
}
}
else
{
lean_object* v___x_3895_; 
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v_b_3879_);
return v___x_3895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2___boxed(lean_object* v_as_3896_, lean_object* v_i_3897_, lean_object* v_stop_3898_, lean_object* v_b_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
size_t v_i_boxed_3907_; size_t v_stop_boxed_3908_; lean_object* v_res_3909_; 
v_i_boxed_3907_ = lean_unbox_usize(v_i_3897_);
lean_dec(v_i_3897_);
v_stop_boxed_3908_ = lean_unbox_usize(v_stop_3898_);
lean_dec(v_stop_3898_);
v_res_3909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__2(v_as_3896_, v_i_boxed_3907_, v_stop_boxed_3908_, v_b_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec_ref(v_as_3896_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl(lean_object* v_decl_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_value_3918_; 
v_value_3918_ = lean_ctor_get(v_decl_3910_, 1);
lean_inc_ref(v_value_3918_);
if (lean_obj_tag(v_value_3918_) == 0)
{
lean_object* v_toSignature_3919_; lean_object* v_code_3920_; lean_object* v_name_3921_; lean_object* v_params_3922_; lean_object* v_decls_3923_; lean_object* v_paramSet_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3953_; 
v_toSignature_3919_ = lean_ctor_get(v_decl_3910_, 0);
lean_inc_ref(v_toSignature_3919_);
lean_dec_ref(v_decl_3910_);
v_code_3920_ = lean_ctor_get(v_value_3918_, 0);
lean_inc_ref(v_code_3920_);
lean_dec_ref(v_value_3918_);
v_name_3921_ = lean_ctor_get(v_toSignature_3919_, 0);
lean_inc(v_name_3921_);
v_params_3922_ = lean_ctor_get(v_toSignature_3919_, 3);
lean_inc_ref(v_params_3922_);
lean_dec_ref(v_toSignature_3919_);
v_decls_3923_ = lean_ctor_get(v_a_3911_, 0);
v_paramSet_3924_ = lean_ctor_get(v_a_3911_, 2);
v_isSharedCheck_3953_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3953_ == 0)
{
lean_object* v_unused_3954_; 
v_unused_3954_ = lean_ctor_get(v_a_3911_, 1);
lean_dec(v_unused_3954_);
v___x_3926_ = v_a_3911_;
v_isShared_3927_ = v_isSharedCheck_3953_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_paramSet_3924_);
lean_inc(v_decls_3923_);
lean_dec(v_a_3911_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3953_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___y_3929_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3943_ = lean_unsigned_to_nat(0u);
v___x_3944_ = lean_array_get_size(v_params_3922_);
v___x_3945_ = lean_nat_dec_lt(v___x_3943_, v___x_3944_);
if (v___x_3945_ == 0)
{
lean_dec_ref(v_params_3922_);
v___y_3929_ = v_paramSet_3924_;
goto v___jp_3928_;
}
else
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_le(v___x_3944_, v___x_3944_);
if (v___x_3946_ == 0)
{
if (v___x_3945_ == 0)
{
lean_dec_ref(v_params_3922_);
v___y_3929_ = v_paramSet_3924_;
goto v___jp_3928_;
}
else
{
size_t v___x_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = ((size_t)0ULL);
v___x_3948_ = lean_usize_of_nat(v___x_3944_);
v___x_3949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3922_, v___x_3947_, v___x_3948_, v_paramSet_3924_);
lean_dec_ref(v_params_3922_);
v___y_3929_ = v___x_3949_;
goto v___jp_3928_;
}
}
else
{
size_t v___x_3950_; size_t v___x_3951_; lean_object* v___x_3952_; 
v___x_3950_ = ((size_t)0ULL);
v___x_3951_ = lean_usize_of_nat(v___x_3944_);
v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode_spec__1(v_params_3922_, v___x_3950_, v___x_3951_, v_paramSet_3924_);
lean_dec_ref(v_params_3922_);
v___y_3929_ = v___x_3952_;
goto v___jp_3928_;
}
}
v___jp_3928_:
{
lean_object* v___x_3931_; 
lean_inc(v_name_3921_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 2, v___y_3929_);
lean_ctor_set(v___x_3926_, 1, v_name_3921_);
v___x_3931_ = v___x_3926_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_decls_3923_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_name_3921_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v___y_3929_);
v___x_3931_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; 
lean_inc(v_a_3916_);
lean_inc_ref(v_a_3915_);
lean_inc(v_a_3914_);
lean_inc_ref(v_a_3913_);
lean_inc(v_a_3912_);
lean_inc_ref(v___x_3931_);
v___x_3932_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectCode(v_code_3920_, v___x_3931_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3940_; 
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; 
v_unused_3941_ = lean_ctor_get(v___x_3932_, 0);
lean_dec(v_unused_3941_);
v___x_3934_ = v___x_3932_;
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
else
{
lean_dec(v___x_3932_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v_name_3921_);
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_name_3921_);
v___x_3937_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3938_; 
v___x_3938_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_updateParamMap(v___x_3937_, v___x_3931_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v___x_3931_);
return v___x_3938_;
}
}
}
else
{
lean_dec_ref(v___x_3931_);
lean_dec(v_name_3921_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
return v___x_3932_;
}
}
}
}
}
else
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec_ref(v_value_3918_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec_ref(v_decl_3910_);
v___x_3955_ = lean_box(0);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl___boxed(lean_object* v_decl_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl(v_decl_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(lean_object* v_as_3966_, size_t v_i_3967_, size_t v_stop_3968_, lean_object* v_b_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
uint8_t v___x_3977_; 
v___x_3977_ = lean_usize_dec_eq(v_i_3967_, v_stop_3968_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = lean_array_uget_borrowed(v_as_3966_, v_i_3967_);
lean_inc(v___y_3975_);
lean_inc_ref(v___y_3974_);
lean_inc(v___y_3973_);
lean_inc_ref(v___y_3972_);
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3970_);
lean_inc(v___x_3978_);
v___x_3979_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_collectDecl(v___x_3978_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; size_t v___x_3981_; size_t v___x_3982_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref(v___x_3979_);
v___x_3981_ = ((size_t)1ULL);
v___x_3982_ = lean_usize_add(v_i_3967_, v___x_3981_);
v_i_3967_ = v___x_3982_;
v_b_3969_ = v_a_3980_;
goto _start;
}
else
{
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
return v___x_3979_;
}
}
else
{
lean_object* v___x_3984_; 
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
v___x_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3984_, 0, v_b_3969_);
return v___x_3984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0___boxed(lean_object* v_as_3985_, lean_object* v_i_3986_, lean_object* v_stop_3987_, lean_object* v_b_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
size_t v_i_boxed_3996_; size_t v_stop_boxed_3997_; lean_object* v_res_3998_; 
v_i_boxed_3996_ = lean_unbox_usize(v_i_3986_);
lean_dec(v_i_3986_);
v_stop_boxed_3997_ = lean_unbox_usize(v_stop_3987_);
lean_dec(v_stop_3987_);
v_res_3998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(v_as_3985_, v_i_boxed_3996_, v_stop_boxed_3997_, v_b_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
lean_dec_ref(v_as_3985_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step(lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_decls_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; 
v_decls_4006_ = lean_ctor_get(v_a_3999_, 0);
lean_inc_ref(v_decls_4006_);
v___x_4007_ = lean_unsigned_to_nat(0u);
v___x_4008_ = lean_array_get_size(v_decls_4006_);
v___x_4009_ = lean_box(0);
v___x_4010_ = lean_nat_dec_lt(v___x_4007_, v___x_4008_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; 
lean_dec_ref(v_decls_4006_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
return v___x_4011_;
}
else
{
uint8_t v___x_4012_; 
v___x_4012_ = lean_nat_dec_le(v___x_4008_, v___x_4008_);
if (v___x_4012_ == 0)
{
if (v___x_4010_ == 0)
{
lean_object* v___x_4013_; 
lean_dec_ref(v_decls_4006_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
v___x_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4009_);
return v___x_4013_;
}
else
{
size_t v___x_4014_; size_t v___x_4015_; lean_object* v___x_4016_; 
v___x_4014_ = ((size_t)0ULL);
v___x_4015_ = lean_usize_of_nat(v___x_4008_);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(v_decls_4006_, v___x_4014_, v___x_4015_, v___x_4009_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
lean_dec_ref(v_decls_4006_);
return v___x_4016_;
}
}
else
{
size_t v___x_4017_; size_t v___x_4018_; lean_object* v___x_4019_; 
v___x_4017_ = ((size_t)0ULL);
v___x_4018_ = lean_usize_of_nat(v___x_4008_);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step_spec__0(v_decls_4006_, v___x_4017_, v___x_4018_, v___x_4009_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
lean_dec_ref(v_decls_4006_);
return v___x_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step___boxed(lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step(v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go(lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v___x_4035_; 
lean_inc(v_a_4033_);
lean_inc_ref(v_a_4032_);
lean_inc(v_a_4031_);
lean_inc_ref(v_a_4030_);
lean_inc(v_a_4029_);
lean_inc_ref(v_a_4028_);
v___x_4035_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_step(v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4058_; 
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; 
v_unused_4059_ = lean_ctor_get(v___x_4035_, 0);
lean_dec(v_unused_4059_);
v___x_4037_ = v___x_4035_;
v_isShared_4038_ = v_isSharedCheck_4058_;
goto v_resetjp_4036_;
}
else
{
lean_dec(v___x_4035_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4058_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; uint8_t v_modified_4040_; 
v___x_4039_ = lean_st_ref_get(v_a_4029_);
v_modified_4040_ = lean_ctor_get_uint8(v___x_4039_, sizeof(void*)*2);
lean_dec(v___x_4039_);
if (v_modified_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4043_; 
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
v___x_4041_ = lean_box(0);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v___x_4041_);
v___x_4043_ = v___x_4037_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
else
{
lean_object* v___x_4045_; lean_object* v_owned_4046_; lean_object* v_paramMap_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4057_; 
lean_del_object(v___x_4037_);
v___x_4045_ = lean_st_ref_take(v_a_4029_);
v_owned_4046_ = lean_ctor_get(v___x_4045_, 0);
v_paramMap_4047_ = lean_ctor_get(v___x_4045_, 1);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4049_ = v___x_4045_;
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_paramMap_4047_);
lean_inc(v_owned_4046_);
lean_dec(v___x_4045_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
uint8_t v___x_4051_; lean_object* v___x_4053_; 
v___x_4051_ = 0;
if (v_isShared_4050_ == 0)
{
v___x_4053_ = v___x_4049_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_owned_4046_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_paramMap_4047_);
v___x_4053_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4054_; 
lean_ctor_set_uint8(v___x_4053_, sizeof(void*)*2, v___x_4051_);
v___x_4054_ = lean_st_ref_set(v_a_4029_, v___x_4053_);
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
return v___x_4035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go___boxed(lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go(v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer(lean_object* v_decls_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v___x_4074_; 
lean_inc(v_a_4072_);
lean_inc_ref(v_a_4071_);
lean_inc(v_a_4070_);
lean_inc_ref(v_a_4069_);
v___x_4074_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_mkInitParamMap(v_decls_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref(v___x_4074_);
v___x_4076_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4077_ = 0;
v___x_4078_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v_a_4075_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*2, v___x_4077_);
v___x_4079_ = lean_st_mk_ref(v___x_4078_);
v___x_4080_ = lean_box(1);
v___x_4081_ = lean_box(0);
v___x_4082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4082_, 0, v_decls_4068_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
lean_ctor_set(v___x_4082_, 2, v___x_4080_);
lean_inc(v___x_4079_);
v___x_4083_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_go(v___x_4082_, v___x_4079_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4092_; 
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v___x_4083_, 0);
lean_dec(v_unused_4093_);
v___x_4085_ = v___x_4083_;
v_isShared_4086_ = v_isSharedCheck_4092_;
goto v_resetjp_4084_;
}
else
{
lean_dec(v___x_4083_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4092_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4087_; lean_object* v_paramMap_4088_; lean_object* v___x_4090_; 
v___x_4087_ = lean_st_ref_get(v___x_4079_);
lean_dec(v___x_4079_);
v_paramMap_4088_ = lean_ctor_get(v___x_4087_, 1);
lean_inc_ref(v_paramMap_4088_);
lean_dec(v___x_4087_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v_paramMap_4088_);
v___x_4090_ = v___x_4085_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_paramMap_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v___x_4079_);
v_a_4094_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4083_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4083_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
else
{
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec_ref(v_decls_4068_);
return v___x_4074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer___boxed(lean_object* v_decls_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer(v_decls_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(lean_object* v_as_4109_, size_t v_i_4110_, size_t v_stop_4111_, lean_object* v_b_4112_, lean_object* v___y_4113_){
_start:
{
uint8_t v___x_4115_; 
v___x_4115_ = lean_usize_dec_eq(v_i_4110_, v_stop_4111_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = lean_array_uget_borrowed(v_as_4109_, v_i_4110_);
lean_inc(v___x_4116_);
v___x_4117_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v___x_4116_, v___y_4113_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; size_t v___x_4119_; size_t v___x_4120_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref(v___x_4117_);
v___x_4119_ = ((size_t)1ULL);
v___x_4120_ = lean_usize_add(v_i_4110_, v___x_4119_);
v_i_4110_ = v___x_4120_;
v_b_4112_ = v_a_4118_;
goto _start;
}
else
{
return v___x_4117_;
}
}
else
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v_b_4112_);
return v___x_4122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg___boxed(lean_object* v_as_4123_, lean_object* v_i_4124_, lean_object* v_stop_4125_, lean_object* v_b_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
size_t v_i_boxed_4129_; size_t v_stop_boxed_4130_; lean_object* v_res_4131_; 
v_i_boxed_4129_ = lean_unbox_usize(v_i_4124_);
lean_dec(v_i_4124_);
v_stop_boxed_4130_ = lean_unbox_usize(v_stop_4125_);
lean_dec(v_stop_4125_);
v_res_4131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_as_4123_, v_i_boxed_4129_, v_stop_boxed_4130_, v_b_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v_as_4123_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferBorrow___lam__0(lean_object* v___x_4132_, lean_object* v_decls_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; 
lean_inc(v___y_4137_);
lean_inc_ref(v___y_4136_);
lean_inc(v___y_4135_);
lean_inc_ref(v___y_4134_);
lean_inc_ref(v_decls_4133_);
v___x_4139_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer(v_decls_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4141_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref(v___x_4139_);
lean_inc(v___y_4137_);
v___x_4141_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_apply(v_decls_4133_, v_a_4140_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___y_4144_; lean_object* v___x_4161_; uint8_t v___x_4162_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
v___x_4161_ = lean_array_get_size(v_a_4142_);
v___x_4162_ = lean_nat_dec_lt(v___x_4132_, v___x_4161_);
if (v___x_4162_ == 0)
{
lean_dec(v_a_4142_);
lean_dec(v___y_4137_);
return v___x_4141_;
}
else
{
lean_object* v___x_4163_; uint8_t v___x_4164_; 
v___x_4163_ = lean_box(0);
v___x_4164_ = lean_nat_dec_le(v___x_4161_, v___x_4161_);
if (v___x_4164_ == 0)
{
if (v___x_4162_ == 0)
{
lean_dec(v_a_4142_);
lean_dec(v___y_4137_);
return v___x_4141_;
}
else
{
size_t v___x_4165_; size_t v___x_4166_; lean_object* v___x_4167_; 
lean_dec_ref(v___x_4141_);
v___x_4165_ = ((size_t)0ULL);
v___x_4166_ = lean_usize_of_nat(v___x_4161_);
v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_a_4142_, v___x_4165_, v___x_4166_, v___x_4163_, v___y_4137_);
lean_dec(v___y_4137_);
v___y_4144_ = v___x_4167_;
goto v___jp_4143_;
}
}
else
{
size_t v___x_4168_; size_t v___x_4169_; lean_object* v___x_4170_; 
lean_dec_ref(v___x_4141_);
v___x_4168_ = ((size_t)0ULL);
v___x_4169_ = lean_usize_of_nat(v___x_4161_);
v___x_4170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_a_4142_, v___x_4168_, v___x_4169_, v___x_4163_, v___y_4137_);
lean_dec(v___y_4137_);
v___y_4144_ = v___x_4170_;
goto v___jp_4143_;
}
}
v___jp_4143_:
{
if (lean_obj_tag(v___y_4144_) == 0)
{
lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_isSharedCheck_4151_ = !lean_is_exclusive(v___y_4144_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; 
v_unused_4152_ = lean_ctor_get(v___y_4144_, 0);
lean_dec(v_unused_4152_);
v___x_4146_ = v___y_4144_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_dec(v___y_4144_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v_a_4142_);
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4142_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec(v_a_4142_);
v_a_4153_ = lean_ctor_get(v___y_4144_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___y_4144_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___y_4144_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___y_4144_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
else
{
lean_dec(v___y_4137_);
return v___x_4141_;
}
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec_ref(v_decls_4133_);
v_a_4171_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4139_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4139_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferBorrow___lam__0___boxed(lean_object* v___x_4179_, lean_object* v_decls_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Compiler_LCNF_inferBorrow___lam__0(v___x_4179_, v_decls_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___x_4179_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0(lean_object* v_as_4198_, size_t v_i_4199_, size_t v_stop_4200_, lean_object* v_b_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___redArg(v_as_4198_, v_i_4199_, v_stop_4200_, v_b_4201_, v___y_4205_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0___boxed(lean_object* v_as_4208_, lean_object* v_i_4209_, lean_object* v_stop_4210_, lean_object* v_b_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
size_t v_i_boxed_4217_; size_t v_stop_boxed_4218_; lean_object* v_res_4219_; 
v_i_boxed_4217_ = lean_unbox_usize(v_i_4209_);
lean_dec(v_i_4209_);
v_stop_boxed_4218_ = lean_unbox_usize(v_stop_4210_);
lean_dec(v_stop_4210_);
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_inferBorrow_spec__0(v_as_4208_, v_i_boxed_4217_, v_stop_boxed_4218_, v_b_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec_ref(v_as_4208_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4286_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_infer_ownFVar___closed__2));
v___x_4287_ = 1;
v___x_4288_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_));
v___x_4289_ = l_Lean_registerTraceClass(v___x_4286_, v___x_4287_, v___x_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2____boxed(lean_object* v_a_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l___private_Lean_Compiler_LCNF_InferBorrow_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_InferBorrow_419080822____hygCtx___hyg_2_();
return v_res_4291_;
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
